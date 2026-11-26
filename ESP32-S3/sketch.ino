/*
 * ============================================================================
 *  BMS 蓝牙中继固件  (ESP32-S3 / Arduino-ESP32)
 * ============================================================================
 *
 *  功能：
 *    1. BLE Client  : 扫描并连接「蚂蚁 BMS」(广播名以 ANT 开头)，订阅 FFE1 通知，
 *                     每秒发送一帧读实时数据请求。
 *    2. BLE Server  : 对外广播一个「与蚂蚁 BMS 结构完全相同」的 GATT 服务
 *                     (FFE0 + FFE1 写/通知)，把 BMS 的原始通知帧逐字节转发出去。
 *                     **支持最多 3 台设备同时连接并同时读取数据。**
 *                     -> 手机官方 App 直连本机即可看到数据，无需改动 App。
 *    3. WiFi AP     : 热点 Ant-Bms / 12345678，**开机即开**，
 *                     浏览器打开 192.168.4.1 进入后台。
 *    4. 自动休眠    : 连续 3 分钟没有设备连到本机 WiFi，自动关闭 WiFi。
 *                     按 BOOT 键(GPIO0)可重新开启。
 *    5. Web 后台    : 扫描附近 ANT 设备、选择要中继的 BMS、设置中继 BLE 名称、
 *                     设置蓝牙发射功率(20/40/60/80/100%)、保存到 NVS。
 *
 *  关键设计（为什么能直接转发）：
 *    BMS 发出的通知已经是标准 ANT 帧：
 *        7E | 地址 | 功能码 | 寄存器(2B,小端) | 长度 | 数据 N B | CRC(2B,低字节在前) | AA 55
 *    CRC16-Modbus(初值0xFFFF, 多项式0xA001)，校验范围 = 地址..最后一个数据字节。
 *    因此本固件只做「重新组帧边界 → 分包转发」，不修改任何字节内容。
 *
 *  连接数说明：
 *    本机同时占用「1 条连 BMS + 最多 3 条手机连接」= 4 条 ACL 链路，
 *    与 BMS_Screen 工程的 CONFIG_BT_ACL_CONNECTIONS=4 一致。
 *
 *  依赖：arduino-esp32 core >= 2.0.0 (ESP32-S3 支持)
 * ============================================================================
 */

#include <WiFi.h>
#include <WebServer.h>
#include <DNSServer.h>
#include <Preferences.h>
#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <BLE2902.h>
/* esp_bt.h 在 3.3.4 的 sketch 路径下可正常解析（上一轮日志第 50 行未报错），
 * 它提供 esp_power_level_t / ESP_PWR_LVL_* / esp_ble_tx_power_set。
 * 注意：不要 include esp_gap_ble_api.h / esp_gatts_api.h —— 那两个找不到。 */
#include <esp_bt.h>

/* ------------------------------ 可改配置 ------------------------------ */
static const char* AP_SSID = "Ant-Bms";
static const char* AP_PASS = "12345678";

static const char* SVC_UUID  = "0000FFE0-0000-1000-8000-00805F9B34FB";
static const char* CHAR_UUID = "0000FFE1-0000-1000-8000-00805F9B34FB";

/* 通知分包长度：手机默认 MTU=23 -> 有效载荷 20 字节。
 * 官方 App 的解帧器是流式的，能自动拼接。多设备时固定 20 最稳。 */
static const size_t NOTIFY_CHUNK = 20;

/* 读实时数据的轮询帧长度字段（0xBE=190，与已验证的 BMS_Screen 一致） */
static const uint8_t POLL_REQ_LEN = 0xBE;
static const uint32_t POLL_INTERVAL_MS = 1000;

/* 最多同时接入的手机数量 */
static const int MAX_CONN = 3;

/* WiFi 无连接自动关闭：3 分钟 */
static const uint32_t WIFI_IDLE_MS = 180000UL;

/* BOOT 键（ESP32-S3 板上 GPIO0）
 * 注意：官方 core 的 pins_arduino.h 里已经定义了 BOOT_PIN（const uint8_t），
 * 这里再用同名常量会报 redefinition，所以改名。 */
static const int RELAY_BTN_PIN = 0;

/* ------------------------------ 全局状态 ------------------------------ */
Preferences prefs;

String cfgBmsMac    = "";
String cfgBmsName   = "";
String cfgRelayName = "ANT-RELAY";
uint8_t cfgTxPercent = 80;           // 20/40/60/80/100，默认 80

WebServer server(80);
DNSServer dns;

BLEClient*  bmsClient = nullptr;
BLERemoteCharacteristic* bmsCh = nullptr;
volatile bool bmsConnected = false;

BLEServer* pServer = nullptr;
BLECharacteristic* pTxCh = nullptr;
bool bleInited = false;

volatile uint32_t gFramesFromBms = 0;
volatile uint32_t gFramesToPhone = 0;
volatile uint32_t gDropBytes     = 0;

/* ---------------------------- WiFi 状态 ---------------------------- */
bool wifiOn = false;
bool wifiIdleCounting = false;
uint32_t wifiIdleStart = 0;

/* ---------------------------- 连接计数 ---------------------------- */
/* 不再自己维护 conn_id 列表：既然发送走 notify()（库内部遍历所有 peer），
 * 连接数直接问 BLEServer 即可，避免自维护状态与协议栈不一致。 */
int getConnCount() {
  return (pServer != nullptr) ? (int)pServer->getConnectedCount() : 0;
}

/* ---------------------------- CRC16-Modbus ---------------------------- */
uint16_t crc16Modbus(const uint8_t* p, size_t n) {
  uint16_t crc = 0xFFFF;
  for (size_t i = 0; i < n; i++) {
    crc ^= p[i];
    for (int b = 0; b < 8; b++) {
      crc = (crc & 1) ? ((crc >> 1) ^ 0xA001) : (crc >> 1);
    }
  }
  return crc;
}

/* 组「短帧」：7E addr fc regLo regHi reqLen crcLo crcHi AA 55 */
size_t buildShortFrame(uint8_t* out, uint8_t addr, uint8_t fc,
                       uint16_t reg, uint8_t reqLen) {
  size_t p = 0;
  out[p++] = 0x7E;
  out[p++] = addr;
  out[p++] = fc;
  out[p++] = (uint8_t)(reg & 0xFF);
  out[p++] = (uint8_t)((reg >> 8) & 0xFF);
  out[p++] = reqLen;
  uint16_t c = crc16Modbus(out + 1, p - 1);
  out[p++] = (uint8_t)(c & 0xFF);
  out[p++] = (uint8_t)((c >> 8) & 0xFF);
  out[p++] = 0xAA;
  out[p++] = 0x55;
  return p;
}

/* ========================= 发射功率（5 档） ========================= */
/* ESP32-S3 功放只有离散档位：-12/-9/-6/-3/0/+3/+6/+9 dBm。
 *
 * 这里**直接使用** esp_bt.h 提供的 API，不做任何自声明：
 * 上一轮编译日志显示 esp_bt.h 是可见的（第 50 行未报错，
 * 只有第 51 行的 esp_gap_ble_api.h 找不到），所以
 * esp_power_level_t / ESP_PWR_LVL_* / esp_ble_tx_power_set 都是可用的。
 *
 * 若再自声明 extern "C" int esp_ble_tx_power_set(int,int)，
 * 会与头文件里的真实原型冲突（C 链接不允许重载），反而编不过。 */
static esp_power_level_t percentToPwrLevel(uint8_t pct) {
  if (pct <= 20) return ESP_PWR_LVL_N6;   /* -6 dBm */
  if (pct <= 40) return ESP_PWR_LVL_N0;   /*  0 dBm */
  if (pct <= 60) return ESP_PWR_LVL_P3;   /* +3 dBm */
  if (pct <= 80) return ESP_PWR_LVL_P6;   /* +6 dBm */
  return ESP_PWR_LVL_P9;                  /* +9 dBm */
}

static const char* percentToDbmText(uint8_t pct) {
  if (pct <= 20) return "-6 dBm";
  if (pct <= 40) return "0 dBm";
  if (pct <= 60) return "+3 dBm";
  if (pct <= 80) return "+6 dBm";
  return "+9 dBm";
}

void applyTxPower(uint8_t pct) {
  cfgTxPercent = pct;
  esp_power_level_t lv = percentToPwrLevel(pct);
  esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_ADV, lv);      /* 广播包 */
  esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_DEFAULT, lv);  /* 已建连接 */
  esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_SCAN, lv);     /* 扫描 */
  Serial.printf("[PWR] 发射功率 %u%% (%s)\n", (unsigned)pct, percentToDbmText(pct));
}


/* ========================= 向上（手机）转发 ========================= */
/*
 * 只用 Arduino BLE 库的公开 API，不碰任何 IDF 底层符号。
 *
 * 原因（由 3.3.4 编译器的报错确认）：
 *   - BLEServer 在 3.3.4 里没有公开 getGattsIf()
 *   - esp_ble_gatts_send_indicate 在 sketch 的 include 路径下未声明
 * 所以不能手动逐连接发送。
 *
 * 改用 setValue() + notify()：3.x 的 BLECharacteristic::notify() 内部会遍历
 * BLEServer 的所有已连接 peer（getPeerDevices）逐个发送，因此**多台手机可以同时收到**，
 * 不需要我们自己拿 gatts_if。这是库内部做法，各版本都一致。
 */
void notifyToPhones(const uint8_t* data, size_t len) {
  if (pTxCh == nullptr || pServer == nullptr) return;
  if (pServer->getConnectedCount() == 0) return;   /* 无手机连接，不必组包 */

  for (size_t off = 0; off < len; off += NOTIFY_CHUNK) {
    size_t c = len - off;
    if (c > NOTIFY_CHUNK) c = NOTIFY_CHUNK;

    pTxCh->setValue((uint8_t*)(data + off), c);
    pTxCh->notify();

    /* 给协议栈留出排空时间，否则发送队列溢出导致丢包 */
    delay(6);
  }
}
/* ======================= 从 BMS 收到的字节流重组 ======================= */
static uint8_t rxbuf[1024];
static size_t  rxlen = 0;

/* 待转发队列：BLE 通知回调跑在协议栈任务里，**不能**在里面 delay，
 * 否则阻塞 BT 栈可能触发断连。回调只负责组帧+入队，主循环负责发送。 */
static const int PEND_MAX = 4;
static uint8_t pendBuf[PEND_MAX][256];
static uint16_t pendLen[PEND_MAX];
static int pendHead = 0, pendTail = 0, pendCount = 0;
static portMUX_TYPE pendMux = portMUX_INITIALIZER_UNLOCKED;

void enqueueFrame(const uint8_t* f, size_t n) {
  if (n > 256) n = 256;
  portENTER_CRITICAL(&pendMux);
  if (pendCount == PEND_MAX) {          /* 队列满：丢最旧，保最新 */
    pendHead = (pendHead + 1) % PEND_MAX;
    pendCount--;
  }
  memcpy(pendBuf[pendTail], f, n);
  pendLen[pendTail] = (uint16_t)n;
  pendTail = (pendTail + 1) % PEND_MAX;
  pendCount++;
  portEXIT_CRITICAL(&pendMux);
}

void transferPending() {
  uint8_t local[256];
  uint16_t len = 0;
  for (;;) {
    portENTER_CRITICAL(&pendMux);
    if (pendCount == 0) { portEXIT_CRITICAL(&pendMux); break; }
    len = pendLen[pendHead];
    memcpy(local, pendBuf[pendHead], len);
    pendHead = (pendHead + 1) % PEND_MAX;
    pendCount--;
    portEXIT_CRITICAL(&pendMux);

    notifyToPhones(local, len);
    gFramesToPhone++;
  }
}

void pumpFrames() {
  while (rxlen > 0) {
    if (rxbuf[0] != 0x7E) {
      size_t k = 1;
      while (k < rxlen && rxbuf[k] != 0x7E) k++;
      gDropBytes += k;
      memmove(rxbuf, rxbuf + k, rxlen - k);
      rxlen -= k;
      continue;
    }
    if (rxlen < 6) return;

    uint8_t fc = rxbuf[2];
    bool isShort = (fc < 0x10);
    size_t dlen  = isShort ? 0 : rxbuf[5];
    size_t body  = 8 + dlen;                       /* 6 头 + dlen 数据 + 2 CRC */

    if (rxlen < body + 2) return;

    uint16_t expect = crc16Modbus(rxbuf + 1, 5 + dlen);
    uint16_t got = (uint16_t)rxbuf[body - 2] | ((uint16_t)rxbuf[body - 1] << 8);
    if (expect != got || rxbuf[body] != 0xAA || rxbuf[body + 1] != 0x55) {
      gDropBytes++;
      memmove(rxbuf, rxbuf + 1, rxlen - 1);
      rxlen--;
      continue;
    }

    gFramesFromBms++;
    enqueueFrame(rxbuf, body + 2);

    memmove(rxbuf, rxbuf + body + 2, rxlen - (body + 2));
    rxlen -= (body + 2);
  }
}

void feedFromBms(const uint8_t* d, size_t n) {
  while (n > 0) {
    size_t space = sizeof(rxbuf) - rxlen;
    if (space == 0) {
      gDropBytes += rxlen / 2;
      memmove(rxbuf, rxbuf + rxlen / 2, rxlen - rxlen / 2);
      rxlen -= rxlen / 2;
      space = sizeof(rxbuf) - rxlen;
    }
    size_t c = (n < space) ? n : space;
    memcpy(rxbuf + rxlen, d, c);
    rxlen += c;
    d += c;
    n -= c;
    pumpFrames();
  }
}

/* ============================ BLE Client 侧 ============================ */
static void bmsNotifyCb(BLERemoteCharacteristic* ch, uint8_t* data, size_t len, bool isNotify) {
  (void)ch; (void)isNotify;
  feedFromBms(data, len);
}

class BmsClientCb : public BLEClientCallbacks {
  void onConnect(BLEClient* c) override { (void)c; Serial.println("[BMS] 已连接"); }
  void onDisconnect(BLEClient* c) override {
    (void)c;
    bmsConnected = false;
    bmsCh = nullptr;
    Serial.println("[BMS] 连接断开");
  }
};

bool connectBms() {
  if (bmsConnected) return true;
  if (cfgBmsMac.length() != 17) return false;

  if (bmsClient == nullptr) {
    bmsClient = BLEDevice::createClient();
    bmsClient->setClientCallbacks(new BmsClientCb());
    bmsClient->setMTU(517);
  }

  /* BLEAddress 的构造签名各版本不同：
   *   core 2.x : BLEAddress(std::string)
   *   core 3.x : BLEAddress(String) —— 传 std::string 会报 no matching constructor
   * 传 String 是最保险的：3.x 直接匹配，2.x 有 String→std::string 的隐式转换。 */
  BLEAddress addr(cfgBmsMac);
  if (!bmsClient->connect(addr)) return false;

  BLERemoteService* svc = bmsClient->getService(SVC_UUID);
  if (svc == nullptr) { bmsClient->disconnect(); return false; }

  bmsCh = svc->getCharacteristic(CHAR_UUID);
  if (bmsCh == nullptr) { bmsClient->disconnect(); return false; }

  if (!bmsCh->canNotify()) { bmsClient->disconnect(); return false; }
  bmsCh->registerForNotify(bmsNotifyCb);

  bmsConnected = true;
  rxlen = 0;
  Serial.printf("[BMS] 就绪 %s (%s)\n", cfgBmsName.c_str(), cfgBmsMac.c_str());
  return true;
}

void pollBms() {
  if (!bmsConnected || bmsCh == nullptr) return;
  uint8_t f[16];
  size_t n = buildShortFrame(f, 0xA1, 0x01, 0x0000, POLL_REQ_LEN);
  bmsCh->writeValue(f, n, true);
}

/* ==================== 连接后读取设备名（GAP 0x2A00） ==================== */
/* 为什么需要这个：
 *   BLE 设备名有两个来源 —— 广播包里的 Local Name（AD type 0x08/0x09），
 *   或 GAP 服务(0x1800) 下的 Device Name 特征(0x2A00)。
 *   很多设备（含部分 BMS）**广播包里根本不放名字**，官方 App 之所以能显示，
 *   是它连上以后去读 0x2A00 拿到的。
 *   读这个特征**不需要配对/绑定**，只要设备可连接即可。
 *
 * 该函数会临时建立一条连接，读完立即断开，不影响主链路。
 * 为省内存，探针客户端只创建一次并复用。
 */
static BLEClient* probeClient = nullptr;

bool readRemoteDeviceName(const String& mac, String& outName, String& err) {
  outName = "";
  err = "";
  if (mac.length() != 17) { err = "地址格式不对"; return false; }

  /* 正在中继 BMS 时不要抢占射频 */
  if (bmsConnected) { err = "正在中继 BMS，请先暂停再读取"; return false; }

  if (probeClient == nullptr) {
    probeClient = BLEDevice::createClient();
    if (probeClient == nullptr) { err = "创建客户端失败"; return false; }
  }

  BLEDevice::stopAdvertising();          /* 让出射频，提高连接成功率 */
  delay(120);

  bool ok = false;
  if (!probeClient->connect(BLEAddress(mac))) {
    err = "连接失败（设备可能已被其他主机占用）";
  } else {
    /* GAP 服务 0x1800 → Device Name 特征 0x2A00 */
    BLERemoteService* gap = probeClient->getService(
        BLEUUID("00001800-0000-1000-8000-00805F9B34FB"));
    if (gap == nullptr) {
      err = "设备没有 GAP 服务";
    } else {
      BLERemoteCharacteristic* ch = gap->getCharacteristic(
          BLEUUID("00002A00-0000-1000-8000-00805F9B34FB"));
      if (ch == nullptr) {
        err = "设备没有名称特征";
      } else if (!ch->canRead()) {
        err = "名称特征不可读";
      } else {
        /* readValue() 在不同版本返回 String 或 std::string，
         * 统一用 .c_str() 包一层，两种都能编过。 */
        String v(ch->readValue().c_str());
        v.trim();
        if (v.length() > 0) { outName = v; ok = true; }
        else err = "设备名称为空";
      }
    }
    probeClient->disconnect();
  }

  delay(150);
  BLEDevice::startAdvertising();         /* 恢复广播 */
  return ok;
}

/* ============================ BLE Server 侧 ============================ */
volatile bool gNeedRestartAdv = false;

/* 连接/断开只做日志：连接数由 BLEServer::getConnectedCount() 提供，
 * 不再自己维护 id 列表（发送由 notify() 内部遍历所有 peer 完成）。 */
class PhoneServerCb : public BLEServerCallbacks {
  void onConnect(BLEServer* s) override {
    (void)s;
    Serial.printf("[Phone] 连接，当前 %d/%d\n", getConnCount(), MAX_CONN);
  }
  void onDisconnect(BLEServer* s) override {
    (void)s;
    Serial.printf("[Phone] 断开，剩余 %d/%d\n", getConnCount(), MAX_CONN);
    gNeedRestartAdv = true;            /* 回调里禁止 delay，交主循环重启广播 */
  }
};

void initBle() {
  /* BLEDevice::init 各版本签名不同：
   *   core 2.x : init(std::string)
   *   core 3.x : init(String) 或 init(const char*)
   * 用 c_str() 走 const char* 分支，两个版本都能匹配。 */
  BLEDevice::init(cfgRelayName.c_str());
  BLEDevice::setMTU(517);

  pServer = BLEDevice::createServer();
  pServer->setCallbacks(new PhoneServerCb());

  BLEService* svc = pServer->createService(SVC_UUID);
  pTxCh = svc->createCharacteristic(
      CHAR_UUID,
      BLECharacteristic::PROPERTY_READ |
      BLECharacteristic::PROPERTY_WRITE |
      BLECharacteristic::PROPERTY_WRITE_NR |
      BLECharacteristic::PROPERTY_NOTIFY);
  pTxCh->addDescriptor(new BLE2902());
  svc->start();

  BLEAdvertising* adv = BLEDevice::getAdvertising();
  adv->addServiceUUID(SVC_UUID);
  adv->setScanResponse(true);
  adv->setMinPreferred(0x06);
  BLEDevice::startAdvertising();

  bleInited = true;
  applyTxPower(cfgTxPercent);

  Serial.printf("[BLE] 广播名 = %s\n", cfgRelayName.c_str());
}

/* 运行时改广播名。
 *
 * 3.3.4 的 sketch 路径下 esp_ble_gap_set_device_name() 不可用，
 * BLEDevice 也没有 setDeviceName()。BLE 库只在 init() 时把名字写进广播包，
 * 之后没有公开接口能改。
 *
 * 因此这里改配置并持久化，重启广播让配置生效；但设备名要真正变化需要重启模块
 * （BLE 协议栈不支持无重启改名）。页面与串口会明确提示这一点。 */
void applyRelayName(const String& nm) {
  cfgRelayName = nm;
  BLEDevice::stopAdvertising();
  delay(120);
  BLEDevice::startAdvertising();
  Serial.printf("[BLE] 中继名已保存为 %s（广播名需重启模块后生效）\n",
                cfgRelayName.c_str());
}

/* ============================== WiFi 控制 ============================== */
/* ---------------------- 已保存的 BMS 地址表（LRU，最多 5 台） ---------------------- */
/* 必须定义在 handleSave / bmsConnTick / loadCfg 之前，否则前向引用编译失败。 */
static const int CFG_MAX = 5;

struct BmsEntry {
  String mac;
  String name;
};

static BmsEntry gBmsList[CFG_MAX];
static int      gBmsCount = 0;

void bmsRemember(const String& mac, const String& name);   /* 后置定义 */
void bmsForget(const String& mac);

/* ---------------------------- 扫描结果存储 ---------------------------- */
/* 上限必须够大：周围设备多时（手机、耳机、手环…）20 个名额很容易被占满，
 * 后出现的 BMS 就会被静默丢弃，表现为「别的都能扫到，就是没有 BMS」。 */
static const int SCAN_MAX = 40;

struct ScanItem {
  String addr;
  String name;
  int    rssi;
  bool   isAnt;
  bool   hasName;
  bool   guessed;      /* 名字是从厂商数据里推断出来的 */
  bool   cached;       /* 名字来自本机缓存的已保存设备（对应 Android 的 device.name 缓存） */
};

static ScanItem gScanList[SCAN_MAX];
static volatile int gScanCount   = 0;   /* 已记录设备数 */
static volatile int gScanRawCount = 0;  /* 收到的广播回调总数（含重复） */
static volatile bool gScanning   = false;
static volatile bool gScanDone   = true;  /* 扫描是否已结束 */

/* 连接状态机状态常量。
 * 必须用 #define 且放在最前面：handleSave() 在 bmsConnTick() 之前就引用了
 * BC_IDLE，宏没有「前向声明」这回事，定义晚于使用就会报
 * "'BC_IDLE' was not declared in this scope"。 */
#define BC_IDLE      0
#define BC_DIRECT    1
#define BC_SCANNING  2

/* 连接状态机用的全局量（定义在此，供 handleSave 提前引用） */
static uint32_t gNextTryAt = 0;
static int      gTryIndex  = 0;
static int      gAttempt   = 0;
static int      gConnState = BC_IDLE;

void handleRoot();
void handleScan();
void handleSave();
void handleStatus();
void handleWifiCtl();
void bmsConnTick();                /* 状态机在文件后部定义，loop() 里调用 */

/* 路由只在 setup 里注册一次；wifiStart/wifiStop 只管 socket 与射频 */
bool routesRegistered = false;

void wifiStart() {
  if (wifiOn) return;
  WiFi.mode(WIFI_AP);
  WiFi.softAP(AP_SSID, AP_PASS);
  IPAddress ip = WiFi.softAPIP();
  dns.start(53, "*", ip);
  server.begin();                 /* 重新打开监听（stop() 只关 socket，路由列表仍保留）*/
  wifiOn = true;
  wifiIdleCounting = false;
  Serial.printf("[WiFi] 已开启 热点 %s / %s  IP=%s\n",
                AP_SSID, AP_PASS, ip.toString().c_str());
}

void wifiStop() {
  if (!wifiOn) return;
  dns.stop();
  server.stop();                  /* 先关 Web 监听，避免残留 socket */
  WiFi.softAPdisconnect(true);
  WiFi.mode(WIFI_OFF);
  wifiOn = false;
  wifiIdleCounting = false;
  Serial.println("[WiFi] 3 分钟无连接，已自动关闭。按 BOOT 键可重新开启。");
}

/* ============================== Web 页面 ============================== */
const char PAGE_TMPL[] PROGMEM = R"HTML(<!doctype html>
<html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>BMS 蓝牙中继</title>
<style>
body{font-family:system-ui,-apple-system,sans-serif;margin:0;padding:16px;
     background:#f5f6f8;color:#222;max-width:640px}
h1{font-size:19px;margin:4px 0 14px}
.card{background:#fff;border-radius:10px;padding:14px;margin-bottom:12px;
      box-shadow:0 1px 3px rgba(0,0,0,.08)}
h2{font-size:15px;margin:0 0 10px;color:#444}
.row{display:flex;gap:8px;align-items:center;margin:8px 0;flex-wrap:wrap}
button{padding:9px 14px;font-size:14px;border:0;border-radius:8px;
       background:#2563eb;color:#fff}
button.sec{background:#e5e7eb;color:#111}
button:disabled{opacity:.5}
input,select{padding:9px;font-size:14px;border:1px solid #d0d4da;border-radius:8px}
input{flex:1}
.dev{padding:9px;border:1px solid #e0e3e8;border-radius:8px;margin:6px 0;
     cursor:pointer;font-size:14px}
.dev.sel{border-color:#2563eb;background:#eff4ff}
.mut{color:#6b7280;font-size:12px;line-height:1.7}
.ok{color:#16a34a;font-weight:600}
.bad{color:#dc2626;font-weight:600}
</style></head><body>
<h1>BMS 蓝牙中继</h1>

<div class="card">
  <h2>运行状态</h2>
  <div id="st" class="mut">读取中…</div>
</div>

<div class="card">
  <h2>1. 选择中继设备</h2>
  <div class="row">
    <button id="bs" onclick="doScan()">扫描附近蓝牙设备</button>
  </div>
  <div class="row">
    <input id="q" type="text" placeholder="搜索：名称或地址（如 ANT、C4:1A）"
           oninput="renderDevices()" autocomplete="off">
  </div>
  <div id="list" class="mut">尚未扫描</div>
  <div class="mut">已选中：<b id="sel">—</b></div>
</div>

<div class="card">
  <h2>2. 中继 BLE 名称</h2>
  <div class="row">
    <input id="relay" maxlength="24" placeholder="ANT-RELAY">
  </div>
  <div class="mut">手机官方 App 搜索时看到的名字。必须以 <b>ANT</b> 开头才能被识别。</div>
</div>

<div class="card">
  <h2>3. 蓝牙发射功率（信号强度）</h2>
  <div class="row">
    <select id="txp" style="flex:1">
      <option value="20">20%　— 一格（-6 dBm）</option>
      <option value="40">40%　— 两格（0 dBm）</option>
      <option value="60">60%　— 三格（+3 dBm）</option>
      <option value="80">80%　— 四格（+6 dBm，默认）</option>
      <option value="100">100% — 满格（+9 dBm）</option>
    </select>
  </div>
  <div class="mut">档位越高覆盖越远、耗电略增。默认 <b>80%</b>。改完需点保存。</div>
</div>

<div class="card">
  <h2>4. 保存配置</h2>
  <div class="row">
    <button onclick="doSave()">保存配置</button>
  </div>
  <div id="msg" class="mut"></div>
</div>

<div class="card">
  <h2>WiFi 热点</h2>
  <div id="wi" class="mut">—</div>
  <div class="row" style="margin-top:8px">
    <button class="sec" onclick="wifiCtl('on')">重新计时</button>
    <button class="sec" onclick="wifiCtl('off')">立即关闭 WiFi</button>
  </div>
  <div class="mut">连续 3 分钟无设备连接会自动关闭。关闭后按板上 <b>BOOT</b> 键可重新开启。</div>
</div>

<script>
var chosen=""; var chosenName="";
function st(){
 fetch('/status').then(r=>r.json()).then(j=>{
  var bms='BMS：'+(j.bmsConnected?'<span class="ok">已连接</span>':'<span class="bad">未连接</span>');
  document.getElementById('st').innerHTML=
    bms+'<br>目标：'+(j.bms||'未设置')
   +'<br>中继名：'+j.relay+'　发射功率：'+j.txp+'%（'+j.dbm+'）'
   +'<br>手机连接：<b>'+j.conn+'</b> / '+j.connMax+' 台'
   +'<br>收到帧 '+j.framesIn+' · 转发帧 '+j.framesOut+' · 丢弃 '+j.drop;
  if(!chosen && j.mac) { chosen=j.mac; chosenName=j.bmsName; }
  if(chosen && document.getElementById('sel').textContent==='—')
    document.getElementById('sel').textContent=chosen+(chosenName?' ('+chosenName+')':'');
  var ri=document.getElementById('relay');
  if(!ri.value) ri.value=j.relay;
  var tp=document.getElementById('txp');
  if(!tp.dataset.touched) tp.value=String(j.txp);

  var w='';
  if(j.wifiOn){
    w='状态：<span class="ok">已开启</span>　热点 <b>'+j.ssid+'</b>　已连设备 '+j.sta+' 台';
    if(j.sta>0) w+='<br>有设备连接中，自动关闭计时已暂停';
    else w+='<br>无设备连接，剩余 <b>'+j.wifiLeft+' 秒</b> 后自动关闭';
  } else {
    w='状态：<span class="bad">已关闭</span>（按 BOOT 键重新开启）';
  }
  document.getElementById('wi').innerHTML=w;
 }).catch(()=>{});
}
function doScan(){
 var b=document.getElementById('bs'); b.disabled=true; b.textContent='扫描中（约14秒）…';
 document.getElementById('list').textContent='正在扫描，请稍候…';
 fetch('/scan').then(r=>r.json()).then(j=>{
   if(j.scanning){document.getElementById('list').textContent='扫描进行中，请稍后再试';
     b.disabled=false;b.textContent='重新扫描';return;}
   window.allDevices = j.list || [];
   window.scanMeta = {raw: j.raw||0, count: j.count||0, savedMac: j.savedMac||''};
   renderDevices();
   b.disabled=false; b.textContent='重新扫描';
 }).catch(e=>{
   document.getElementById('list').textContent='扫描请求失败：'+e;
   b.disabled=false; b.textContent='重新扫描';
 });
}

/* 只负责“把 allDevices 按搜索框过滤后画出来”，不发请求 */
function renderDevices(){
 var L=document.getElementById('list');
 var devs=window.allDevices||[];
 var meta=window.scanMeta||{raw:0,count:0,savedMac:''};
 L.innerHTML='';

 if(!devs.length){
   L.textContent = meta.raw>0 ? '没有发现任何蓝牙设备。' : '尚未扫描，或射频未收到任何广播。';
   return;
 }

 var q=(document.getElementById('q').value||'').trim().toUpperCase();
 var shown=0, ants=0;

 // 统计（不受搜索影响）
 devs.forEach(d=>{ if(d.ant) ants++; });

 devs.forEach(d=>{
   var hay=(d.name+' '+d.addr).toUpperCase();
   if(q && hay.indexOf(q)<0) return;
   shown++;

   var e=document.createElement('div');
   e.className='dev'+(d.addr==chosen?' sel':'');
   var tag   = d.ant ? '<span style="color:#16a34a;font-weight:600"> [ANT]</span>' : '';
   var warn  = (!d.hasName) ? '<span style="color:#f59e0b"> [无名称]</span>' : '';
   var gtag  = d.guess ? '<span style="color:#8b5cf6;font-weight:600"> [厂商数据]</span>' : '';
   var ctag  = d.cached ? '<span style="color:#0ea5e9;font-weight:600"> [已保存]</span>' : '';
   var saved = (d.addr==meta.savedMac) ? '<span style="color:#2563eb;font-weight:600"> [当前目标]</span>' : '';
   e.innerHTML='<b>'+d.name+'</b>'+tag+warn+gtag+ctag+saved
               +'<br><span style="color:#6b7280;font-size:12px">'
               +d.addr+'　RSSI '+d.rssi+' dBm</span>';
   e.onclick=function(){
     chosen=d.addr; chosenName=d.name;
     document.getElementById('sel').textContent=chosen+' ('+d.name+')';
     document.querySelectorAll('.dev').forEach(x=>x.classList.remove('sel'));
     e.classList.add('sel');
   };

   /* 无名称的设备：提供"连上去读名称"的按钮（读 GAP 0x2A00） */
   if(!d.hasName){
     var btn=document.createElement('button');
     btn.textContent='读取名称';
     btn.style.marginTop='6px';
     btn.style.fontSize='12px';
     btn.style.padding='5px 10px';
     btn.onclick=function(ev){ ev.stopPropagation(); readName(d.addr, btn); };
     e.appendChild(btn);
   }

   L.appendChild(e);
 });

 if(!shown){
   var none=document.createElement('div');
   none.className='mut';
   none.textContent='没有匹配「'+q+'」的设备，共扫到 '+devs.length+' 台，可清空搜索框查看全部。';
   L.appendChild(none);
   return;
 }

 var sum=document.createElement('div');
 sum.className='mut'; sum.style.marginTop='8px';
 sum.innerHTML='共 '+devs.length+' 台'+(q?('，匹配 '+shown+' 台'):'')
   +'，按信号强度排序。点任意一条即可选中。'
   +(ants>0?('<br>其中 <b style="color:#16a34a">'+ants+'</b> 台广播名含 ANT。'):'');
 L.appendChild(sum);
}
document.getElementById('txp').addEventListener('change',function(){
  this.dataset.touched='1';
});
function doSave(){
 var m=document.getElementById('msg');
 var fd=new URLSearchParams();
 fd.append('mac',chosen);
 fd.append('name',chosenName);
 fd.append('relay',document.getElementById('relay').value);
 fd.append('txp',document.getElementById('txp').value);
 m.textContent='保存中…';
 fetch('/save',{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},
                body:fd.toString()})
  .then(r=>r.text()).then(t=>{m.textContent=t;st();})
  .catch(()=>{m.textContent='保存失败';});
}
/* 连上去读设备名（GAP 0x2A00）。成功后回填列表并选中 */
function readName(addr, btn){
 var old = btn ? btn.textContent : '';
 if(btn){ btn.disabled=true; btn.textContent='读取中…'; }
 fetch('/name?addr='+encodeURIComponent(addr)).then(r=>r.json()).then(j=>{
   if(j.ok){
     (window.allDevices||[]).forEach(d=>{
       if(d.addr==addr){ d.name=j.name; d.hasName=true; }
     });
     if(btn){ btn.disabled=false; btn.textContent=old; }
     renderDevices();
   } else {
     if(btn){ btn.disabled=false; btn.textContent=old; }
     alert('读取失败：'+(j.err||'未知原因'));
   }
 }).catch(e=>{
   if(btn){ btn.disabled=false; btn.textContent=old; }
   alert('请求失败：'+e);
 });
}

function wifiCtl(a){
 fetch('/wifi?act='+a).then(r=>r.text()).then(()=>st()).catch(()=>{});
}
st(); setInterval(st,2000);
</script></body></html>)HTML";

/* ------------- 从厂商自定义数据里提取名称 ------------- */
/* 为什么需要：
 *   标准设备名在 AD type 0x08/0x09（Local Name），Arduino 的 getName() 只读这个。
 *   但不少国产 BMS 把名字塞在 **厂商自定义数据（AD type 0xFF）** 里，
 *   官方 App 自己按私有格式解析，所以它「扫描阶段就能显示名字」，
 *   而我们的 getName() 返回空 —— 这就是差异的根源。
 *
 * 做法：把厂商数据当成字节流，找连续可打印字符（含 UTF-8 中文），
 *   取最长的一段作为名字。属于启发式推断，界面上会标 [厂商数据]。
 */
static String extractVendorName(BLEAdvertisedDevice& dev) {
  String raw(dev.getManufacturerData().c_str());
  if (raw.length() == 0) return String("");

  String best = "";
  String cur  = "";
  for (unsigned int i = 0; i < raw.length(); i++) {
    uint8_t c = (uint8_t)raw[i];
    /* 允许 ASCII 可见字符与 UTF-8 高位字节，排除控制字符 */
    if (c >= 0x20 && c != 0x7F) {
      cur += (char)c;
    } else {
      if (cur.length() > best.length() && cur.length() >= 4) best = cur;
      cur = "";
    }
  }
  if (cur.length() > best.length() && cur.length() >= 4) best = cur;
  return best;
}
/* 3.3.4 的实际签名（编译器报错原文给出）：
 *     virtual void onResult(BLEAdvertisedDevice advertisedDevice) = 0;
 *
 * 设计要点（针对"扫不到任何设备"）：
 *  1. **不过滤**：所有带地址的广播都记下来，ANT 设备只打个标记。
 *     之前的实现要求「名字非空 且 以 ANT 开头」，两个条件任一不满足就丢弃，
 *     结果用户无法区分"没扫到"和"被过滤掉"。
 *  2. 名字为空的设备也保留（用地址当显示名），并标注 hasName=false，
 *     因为 BMS 的名字可能只在 scan response 里，时序不对就取不到。
 *  3. 记录 rawCount（收到的广播总数），前端可据此判断射频是否工作。
 */
class ScanCb : public BLEAdvertisedDeviceCallbacks {
public:
  void onResult(BLEAdvertisedDevice dev) override {
    gScanRawCount++;

    String addr = String(dev.getAddress().toString().c_str());
    if (addr.length() < 11) return;

    String nm = String(dev.getName().c_str());
    bool hasName = (nm.length() > 0);
    bool guessed = false;

    /* 标准 Local Name 没有时，尝试从厂商自定义数据(0xFF)里找名字。
     * 官方 App 能"扫描阶段就显示名字"，往往就是因为它解析了这一段。 */
    if (!hasName) {
      String vn = extractVendorName(dev);
      if (vn.length() > 0) {
        nm = vn;
        hasName = true;
        guessed = true;
      }
    }

    String up = nm; up.toUpperCase();
    bool isAnt = hasName && (up.startsWith("ANT") || up.indexOf("ANT") >= 0);

    /* 去重 + 【合并名字】
     * 同一设备会被回调两次：先 ADV_IND（常无名字），后 SCAN_RSP（名字在这里）。
     * 旧代码在此处直接 return，只更新 RSSI，导致后到的名字被丢弃，
     * 表里永远显示"(无名称)"。这就是"App 能显示名字，我们显示无名称"的原因。 */
    for (int i = 0; i < gScanCount; i++) {
      if (gScanList[i].addr == addr) {
        gScanList[i].rssi = dev.getRSSI();
        if (hasName && !gScanList[i].hasName) {     /* 补上后到的名字 */
          gScanList[i].name    = nm;
          gScanList[i].hasName = true;
          gScanList[i].isAnt   = isAnt;
          gScanList[i].guessed = guessed;
          Serial.printf("[Scan] 补到名字 %s -> %s%s\n",
                        addr.c_str(), nm.c_str(), isAnt ? "  <== ANT" : "");
        }
        return;
      }
    }
    if (gScanCount >= SCAN_MAX) return;

    ScanItem& it = gScanList[gScanCount++];
    it.addr    = addr;
    it.name    = hasName ? nm : String("(无名称)");
    it.rssi    = dev.getRSSI();
    it.isAnt   = isAnt;
    it.hasName = hasName;
    it.guessed = guessed;
    it.cached  = false;

    Serial.printf("[Scan] %s  %s  rssi=%d%s%s\n",
                  addr.c_str(), it.name.c_str(), it.rssi,
                  guessed ? "  <厂商数据>" : "",
                  isAnt ? "  <== ANT" : "");
  }
};

/* ============================== 状态 JSON ============================== */
uint32_t wifiLeftSec() {
  if (!wifiOn) return 0;
  if (WiFi.softAPgetStationNum() > 0) return WIFI_IDLE_MS / 1000;
  if (!wifiIdleCounting) return WIFI_IDLE_MS / 1000;
  uint32_t used = millis() - wifiIdleStart;
  if (used >= WIFI_IDLE_MS) return 0;
  return (WIFI_IDLE_MS - used) / 1000;
}

String statusJson() {
  String s = "{";
  s += "\"bmsConnected\":" + String(bmsConnected ? 1 : 0);
  s += ",\"bms\":\"" + cfgBmsName + " " + cfgBmsMac + "\"";
  s += ",\"bmsName\":\"" + cfgBmsName + "\"";
  s += ",\"mac\":\"" + cfgBmsMac + "\"";
  s += ",\"relay\":\"" + cfgRelayName + "\"";
  s += ",\"txp\":" + String(cfgTxPercent);
  s += ",\"dbm\":\"" + String(percentToDbmText(cfgTxPercent)) + "\"";
  s += ",\"conn\":" + String(getConnCount()) + ",\"connMax\":" + String(MAX_CONN);
  s += ",\"framesIn\":" + String(gFramesFromBms);
  s += ",\"framesOut\":" + String(gFramesToPhone);
  s += ",\"drop\":" + String(gDropBytes);
  s += ",\"wifiOn\":" + String(wifiOn ? 1 : 0);
  s += ",\"ssid\":\"" + String(AP_SSID) + "\"";
  s += ",\"sta\":" + String(wifiOn ? (int)WiFi.softAPgetStationNum() : 0);
  s += ",\"wifiLeft\":" + String(wifiLeftSec());
  s += "}";
  return s;
}

/* ============================== HTTP 处理 ============================== */
void handleRoot() {
  server.send(200, "text/html; charset=utf-8", FPSTR(PAGE_TMPL));
}

void handleScan() {
  /* 正在扫描就直接返回“进行中”，不要返回空数组骗前端 */
  if (gScanning) {
    server.send(200, "application/json", "{\"scanning\":true}");
    return;
  }

  /* 清空上一轮结果 */
  gScanCount = 0;
  gScanRawCount = 0;

  BLEScan* sc = BLEDevice::getScan();
  /* 第二个参数 wantDuplicates **必须为 true**。
   * 它控制"同一地址的重复上报是否交给回调"。
   * 设为 false 时，ADV_IND（无名）先到并被采纳，随后 SCAN_RSP（带名字）
   * 会被库当作重复上报直接丢弃 —— 结果是永远拿不到名字。
   * 这正是"能扫到设备、但显示无名称"的直接原因。 */
  sc->setAdvertisedDeviceCallbacks(new ScanCb(), true);
  sc->setActiveScan(true);        /* 主动扫描，发 SCAN_REQ 索取 scan response 里的名字 */
  sc->setInterval(100);
  sc->setWindow(99);              /* 99/100 占空比，尽量不漏包 */
  sc->setDuplicateFilter(false);  /* 控制器层也关掉重复过滤 */

  Serial.println("[Scan] 开始扫描 8 秒…");
  gScanning = true;
  gScanDone = false;

  /* 【关键】扫描前先停掉自己的广播。
   * ESP32-S3 只有一个 BLE 控制器：同时"对外广播 + 扫描"时，射频时隙被广播占走，
   * 扫描窗口被压缩，实测会表现为"一台都扫不到"。停播后扫描占空比才能达到 99%。 */
  BLEDevice::stopAdvertising();
  delay(200);

  /* 【关键】若当前正连着 BMS，也要临时断开。
   * 已建立的 BLE 连接会周期性占用时隙（连接间隔），同样会挤掉扫描窗口。
   * 扫描完由主循环的 connectBms() 自动重连回去。 */
  bool wasConnected = bmsConnected;
  if (wasConnected) {
    Serial.println("[Scan] 临时断开 BMS 以释放射频…");
    if (bmsClient != nullptr) bmsClient->disconnect();
    bmsConnected = false;
    bmsCh = nullptr;
    delay(300);
  }

  /* 阻塞扫描：分两轮、每轮 7 秒，结果合并到同一张表。
   * 为什么要两轮：BMS 这类设备的广播间隔可能较长（几百 ms 到 2 s），
   * 单轮短扫描容易整轮都没撞上它的广播点；两轮能显著提高命中率。
   * 期间 loop() 不跑，Web 请求会排队，但换来结果确定、无并发问题。 */
  sc->start(7, false);
  while (sc->isScanning()) delay(50);
  sc->stop();
  sc->clearResults();

  Serial.printf("[Scan] 第 1 轮结束：回调 %d 次，累计 %d 台\n",
                gScanRawCount, gScanCount);

  sc->start(7, false);
  while (sc->isScanning()) delay(50);
  sc->stop();
  sc->clearResults();

  /* 扫描结束，恢复广播（手机才能重新看到中继） */
  BLEDevice::startAdvertising();
  if (wasConnected) {
    Serial.println("[Scan] 扫描结束，BMS 将由主循环自动重连");
  }

  gScanning = false;
  gScanDone = true;

  Serial.printf("[Scan] 结束：广播回调 %d 次，去重后 %d 台\n",
                gScanRawCount, gScanCount);

  /* 按 RSSI 从强到弱排序（纯展示顺序，不筛选、不丢弃任何设备）。
   * 目的：设备多时把距离近的排前面，BMS 通常在附近，一眼能看到。 */
  for (int i = 1; i < gScanCount; i++) {
    ScanItem key = gScanList[i];
    int j = i - 1;
    while (j >= 0 && gScanList[j].rssi < key.rssi) {
      gScanList[j + 1] = gScanList[j];
      j--;
    }
    gScanList[j + 1] = key;
  }

  /* 用本机缓存的名称回填。
   * 对应 Android 的 result.device.name —— 系统蓝牙栈会缓存设备名，
   * 所以官方 App 即使广播里没有名字，也能显示上次连过的名字。
   * 我们这边等价物就是 NVS 里的 gBmsList（连上时记下的名字）。 */
  for (int i = 0; i < gScanCount; i++) {
    if (gScanList[i].hasName) continue;
    for (int k = 0; k < gBmsCount; k++) {
      if (gBmsList[k].mac == gScanList[i].addr && gBmsList[k].name.length() > 0) {
        gScanList[i].name    = gBmsList[k].name;
        gScanList[i].hasName = true;
        gScanList[i].cached  = true;
        gScanList[i].isAnt   = true;
        break;
      }
    }
  }

  /* 手工拼 JSON，避免 String 反复 substring 出错 */
  String out = "{";
  out += "\"scanning\":false,";
  out += "\"raw\":" + String(gScanRawCount) + ",";
  out += "\"count\":" + String(gScanCount) + ",";
  out += "\"savedMac\":\"" + cfgBmsMac + "\",";   /* 前端用它标出「当前目标」 */
  out += "\"list\":[";
  for (int i = 0; i < gScanCount; i++) {
    if (i) out += ",";
    out += "{";
    out += "\"addr\":\"" + gScanList[i].addr + "\",";
    out += "\"name\":\"" + gScanList[i].name + "\",";
    out += "\"rssi\":" + String(gScanList[i].rssi) + ",";
    out += "\"ant\":" + String(gScanList[i].isAnt ? 1 : 0) + ",";
    out += "\"guess\":" + String(gScanList[i].guessed ? 1 : 0) + ",";
    out += "\"cached\":" + String(gScanList[i].cached ? 1 : 0) + ",";
    out += "\"hasName\":" + String(gScanList[i].hasName ? 1 : 0);
    out += "}";
  }
  out += "]}";

  server.send(200, "application/json", out);
}

void handleSave() {
  String mac   = server.arg("mac");
  String relay = server.arg("relay");
  String name  = server.arg("name");
  String txp   = server.arg("txp");
  mac.trim(); relay.trim(); name.trim(); txp.trim();

  bool changedMac = (mac.length() == 17 && mac != cfgBmsMac);

  /* 记住这台 BMS（写表头 + 落盘），并设为当前目标 */
  if (mac.length() == 17) {
    bmsRemember(mac, name);
    cfgBmsMac  = mac;
    cfgBmsName = (name.length() > 0) ? name : String("BMS");
  }

  if (relay.length() >= 3 && relay != cfgRelayName) {
    String up = relay; up.toUpperCase();
    if (!up.startsWith("ANT")) {
      Serial.println("[Cfg] 警告：中继名未以 ANT 开头，官方 App 可能识别不到");
    }
    prefs.begin("relay", false);
    prefs.putString("rname", relay);
    prefs.end();
    applyRelayName(relay);
  }

  if (txp.length() > 0) {
    int p = txp.toInt();
    if (p > 0 && p <= 100) {
      prefs.begin("relay", false);
      prefs.putUChar("txp", (uint8_t)p);
      prefs.end();
      applyTxPower((uint8_t)p);
      if (bleInited) {
        BLEDevice::stopAdvertising();
        delay(80);
        BLEDevice::startAdvertising();
      }
    }
  }

  if (changedMac) {
    /* 换目标：断开当前连接，让状态机立即重新开始 */
    if (bmsClient != nullptr && bmsConnected) bmsClient->disconnect();
    bmsConnected = false;
    bmsCh = nullptr;
    rxlen = 0;
    gTryIndex  = 0;
    gAttempt   = 0;
    gConnState = BC_IDLE;
    gNextTryAt = millis() + 300;      /* 300ms 后立即开始连新目标 */
  }

  server.send(200, "text/plain; charset=utf-8", "已保存，正在应用配置");
}

void handleStatus() { server.send(200, "application/json", statusJson()); }

/* /name?addr=xx:xx:... —— 连接该设备并读取 GAP 名称特征(0x2A00) */
void handleReadName() {
  String addr = server.arg("addr");
  addr.trim();

  String nm, err;
  bool ok = readRemoteDeviceName(addr, nm, err);

  String out = "{";
  out += "\"ok\":" + String(ok ? 1 : 0);
  out += ",\"name\":\"" + nm + "\"";
  out += ",\"err\":\"" + err + "\"";
  out += "}";
  server.send(200, "application/json", out);
}

void handleWifiCtl() {
  String act = server.arg("act");
  if (act == "off") {
    server.send(200, "text/plain; charset=utf-8", "WiFi 已关闭");
    delay(150);
    wifiStop();
    return;
  }
  wifiIdleCounting = false;
  wifiIdleStart = millis();
  server.send(200, "text/plain; charset=utf-8", "计时已重置");
}

void handleNotFound() {
  server.sendHeader("Location", String("http://") + WiFi.softAPIP().toString(), true);
  server.send(302, "text/plain", "");
}

void registerRoutes() {
  server.on("/", HTTP_GET, handleRoot);
  server.on("/scan", HTTP_GET, handleScan);
  server.on("/save", HTTP_POST, handleSave);
  server.on("/status", HTTP_GET, handleStatus);
  server.on("/name", HTTP_GET, handleReadName);
  server.on("/wifi", HTTP_GET, handleWifiCtl);
  server.onNotFound(handleNotFound);
  routesRegistered = true;
  Serial.println("[Web] 路由已注册");
}

void initWifi() {
  registerRoutes();
  wifiStart();                   /* wifiStart 内部会 server.begin()，开机默认开启 */
}

/* ================================ 配置 ================================ */
/* BMS 地址表结构体与 gBmsList/gBmsCount 已在前方定义（供 handleSave 提前引用）。
 * 这里只放实现。 */

/* 把一台设备写入表头（已存在则提到最前），并落盘 */
void bmsRemember(const String& mac, const String& name) {
  if (mac.length() != 17) return;
  /* 先移除同地址旧项 */
  for (int i = 0; i < gBmsCount; i++) {
    if (gBmsList[i].mac == mac) {
      for (int j = i; j < gBmsCount - 1; j++) gBmsList[j] = gBmsList[j + 1];
      gBmsCount--;
      break;
    }
  }
  /* 插到最前（若已满，丢掉最后一个） */
  int n = (gBmsCount < CFG_MAX) ? gBmsCount : CFG_MAX - 1;
  for (int j = n; j > 0; j--) gBmsList[j] = gBmsList[j - 1];
  gBmsList[0].mac  = mac;
  gBmsList[0].name = (name.length() > 0) ? name : String("BMS");
  gBmsCount = n + 1;

  /* 持久化：mac0/name0 是最新，依次写入 */
  prefs.begin("relay", false);
  for (int i = 0; i < CFG_MAX; i++) {
    if (i < gBmsCount) {
      prefs.putString(("m" + String(i)).c_str(), gBmsList[i].mac);
      prefs.putString(("n" + String(i)).c_str(), gBmsList[i].name);
    } else {
      prefs.remove(("m" + String(i)).c_str());
      prefs.remove(("n" + String(i)).c_str());
    }
  }
  prefs.end();
  Serial.printf("[Cfg] 已记住 %s (%s)，表内 %d 台\n", mac.c_str(), name.c_str(), gBmsCount);
}

void bmsForget(const String& mac) {
  for (int i = 0; i < gBmsCount; i++) {
    if (gBmsList[i].mac == mac) {
      for (int j = i; j < gBmsCount - 1; j++) gBmsList[j] = gBmsList[j + 1];
      gBmsCount--;
      break;
    }
  }
  prefs.begin("relay", false);
  for (int i = 0; i < CFG_MAX; i++) {
    if (i < gBmsCount) {
      prefs.putString(("m" + String(i)).c_str(), gBmsList[i].mac);
      prefs.putString(("n" + String(i)).c_str(), gBmsList[i].name);
    } else {
      prefs.remove(("m" + String(i)).c_str());
      prefs.remove(("n" + String(i)).c_str());
    }
  }
  prefs.end();
}

void loadCfg() {
  prefs.begin("relay", false);
  gBmsCount = 0;
  for (int i = 0; i < CFG_MAX; i++) {
    String m = prefs.getString(("m" + String(i)).c_str(), "");
    String n = prefs.getString(("n" + String(i)).c_str(), "");
    if (m.length() == 17) {
      gBmsList[gBmsCount].mac  = m;
      gBmsList[gBmsCount].name = n;
      gBmsCount++;
    }
  }
  cfgBmsMac    = gBmsCount > 0 ? gBmsList[0].mac : String("");
  cfgBmsName   = gBmsCount > 0 ? gBmsList[0].name : String("");
  cfgRelayName = prefs.getString("rname", "ANT-RELAY");
  cfgTxPercent = prefs.getUChar("txp", 80);
  prefs.end();
  if (cfgTxPercent != 20 && cfgTxPercent != 40 && cfgTxPercent != 60 &&
      cfgTxPercent != 80 && cfgTxPercent != 100) {
    cfgTxPercent = 80;
  }
  Serial.printf("[Cfg] 记忆 %d 台 BMS，首选=%s  Relay=%s  Power=%u%%\n",
                gBmsCount, cfgBmsMac.c_str(), cfgRelayName.c_str(),
                (unsigned)cfgTxPercent);
  for (int i = 0; i < gBmsCount; i++) {
    Serial.printf("      [%d] %s  %s\n", i, gBmsList[i].mac.c_str(),
                  gBmsList[i].name.c_str());
  }
}

/* ====================== BMS 自动连接状态机（无上限重连） ====================== */
/*
 * 状态：
 *   IDLE    —— 刚启动/刚断开，等待退避后开始一轮尝试
 *   DIRECT  —— 按保存的地址表逐一直连
 *   SCANNING—— 直连全失败，开扫描找表内地址（8 秒一轮，循环不停）
 *
 * 行为保证（对应需求）：
 *   1. 记住连过的地址（最多 5 台，LRU），开机自动尝试
 *   2. 连不上就一直循环重试，**不设次数上限**，不进入永久放弃状态
 *   3. 已连上后断开，自动回到 IDLE 重新连接
 */
/* 状态机全局量（gConnState/gNextTryAt/gTryIndex/gAttempt）与
 * BC_IDLE/BC_DIRECT/BC_SCANNING 均已在文件前部定义，这里只写逻辑。 */

static uint32_t gConnOkAt = 0;      /* 连上时刻，用于判断"连上就断" */
static int      gScanHits = 0;      /* 扫描轮次计数，仅日志用 */

/* 连接成功后调用：更新 LRU、复位退避 */
static void onBmsConnected(const String& mac, const String& name) {
  bmsRemember(mac, name);                /* 提到表头并落盘 */
  cfgBmsMac  = mac;
  cfgBmsName = name;
  gConnOkAt  = millis();
  gAttempt   = 0;
  gTryIndex  = 0;
  gConnState = BC_IDLE;                  /* 已连上，状态机暂停在 IDLE */
  Serial.printf("[Conn] 已连接 %s (%s)\n", mac.c_str(), name.c_str());
}

/* 指数退避：1s,2s,4s,8s,15s 封顶。永不放弃。 */
static uint32_t backoffMs(int attempt) {
  uint32_t ms = 1000UL << (attempt > 4 ? 4 : attempt);
  return ms > 15000UL ? 15000UL : ms;
}

/* 主循环里调用，非阻塞推进状态机 */
void bmsConnTick() {
  /* 已连接：只监控是否还活着 */
  if (bmsConnected) return;

  uint32_t now = millis();

  /* 扫描进行中（配置页触发的扫描），让路 */
  if (gScanning) return;

  /* 还没到重试时刻 */
  if ((int32_t)(now - gNextTryAt) < 0) return;

  /* ---- 1. 先按保存的地址表顺序直连 ---- */
  if (gBmsCount > 0 && gTryIndex < gBmsCount) {
    const String mac  = gBmsList[gTryIndex].mac;
    const String name = gBmsList[gTryIndex].name;
    Serial.printf("[Conn] 直连尝试 %d/%d：%s (%s)\n",
                  gTryIndex + 1, gBmsCount, mac.c_str(), name.c_str());

    String savedMac = cfgBmsMac;
    cfgBmsMac = mac;                     /* connectBms 读 cfgBmsMac */
    bool ok = connectBms();
    cfgBmsMac = savedMac;

    if (ok) {
      onBmsConnected(mac, name);
      return;
    }
    gTryIndex++;
    gNextTryAt = now + 800;              /* 下一台稍等一下再试 */
    return;
  }

  /* ---- 2. 地址表都试过了，进入扫描模式 ---- */
  if (gConnState != BC_SCANNING) {
    gConnState = BC_SCANNING;
    gScanHits  = 0;
    gAttempt++;
    uint32_t wait = backoffMs(gAttempt);
    gNextTryAt = now + wait;
    Serial.printf("[Conn] 直连全部失败，%u ms 后开始扫描（第 %d 轮）\n",
                  (unsigned)wait, gAttempt);
    return;
  }

  /* ---- 3. 扫描一轮，找表内地址 ---- */
  gScanHits++;
  Serial.printf("[Conn] 扫描第 %d 轮，寻找已保存的 BMS…\n", gScanHits);

  /* 扫描会占用射频，需先停播（与 handleScan 同理） */
  BLEDevice::stopAdvertising();
  delay(100);

  gScanCount = 0;
  gScanRawCount = 0;
  BLEScan* sc = BLEDevice::getScan();
  sc->setAdvertisedDeviceCallbacks(new ScanCb(), true);   /* true：允许重复上报，才能收到带名字的 SCAN_RSP */
  sc->setActiveScan(true);
  sc->setInterval(100);
  sc->setWindow(99);
  sc->setDuplicateFilter(false);
  sc->start(4, false);                   /* 自动重连用 4 秒短扫，避免拖太久 */
  uint32_t t0 = millis();
  while (sc->isScanning() && millis() - t0 < 6000) delay(30);
  sc->stop();
  sc->clearResults();
  BLEDevice::startAdvertising();

  /* 在扫到的设备里找表内地址 */
  int hit = -1;
  for (int i = 0; i < gScanCount; i++) {
    for (int k = 0; k < gBmsCount; k++) {
      if (gScanList[i].addr == gBmsList[k].mac) { hit = k; break; }
    }
    if (hit >= 0) break;
  }

  if (hit >= 0) {
    const String mac  = gBmsList[hit].mac;
    const String name = gBmsList[hit].name;
    Serial.printf("[Conn] 扫描到目标 %s，立即连接\n", mac.c_str());
    String savedMac = cfgBmsMac;
    cfgBmsMac = mac;
    bool ok = connectBms();
    cfgBmsMac = savedMac;
    if (ok) { onBmsConnected(mac, name); return; }
  } else {
    Serial.printf("[Conn] 本轮未扫到目标（扫到 %d 台设备）\n", gScanCount);
  }

  /* 无论是否扫到，都从表头重新开始直连，形成无限循环 */
  gTryIndex = 0;
  if (gScanHits >= 3) {                  /* 连续 3 轮扫描无果后加大间隔 */
    gAttempt++;
    gScanHits = 0;
  }
  gConnState = BC_IDLE;
  gNextTryAt = now + backoffMs(gAttempt);
}

/* ================================ setup ================================ */
void setup() {
  Serial.begin(115200);
  delay(300);
  Serial.println("\n=== BMS Relay (ESP32-S3) ===");

  pinMode(RELAY_BTN_PIN, INPUT_PULLUP);

  loadCfg();
  initBle();
  initWifi();
}

/* ================================ loop ================================ */
void loop() {
  /* ---- WiFi 自动关闭状态机 ---- */
  if (wifiOn) {
    dns.processNextRequest();
    server.handleClient();

    if (WiFi.softAPgetStationNum() > 0) {
      wifiIdleCounting = false;            /* 有设备连着 -> 暂停计时 */
    } else {
      if (!wifiIdleCounting) {
        wifiIdleCounting = true;
        wifiIdleStart = millis();
      } else if (millis() - wifiIdleStart >= WIFI_IDLE_MS) {
        wifiStop();
      }
    }
  }

  /* ---- BOOT 键：重新开启 WiFi / 重置计时 ---- */
  static bool bootLast = HIGH;
  static uint32_t bootDownAt = 0;
  bool bootNow = digitalRead(RELAY_BTN_PIN);
  if (bootLast == HIGH && bootNow == LOW) bootDownAt = millis();
  if (bootLast == LOW && bootNow == HIGH) {
    if (millis() - bootDownAt > 60) {
      if (!wifiOn) {
        wifiStart();                       /* 路由已注册过，只重新开射频和监听 */
      } else {
        wifiIdleCounting = false;
        wifiIdleStart = millis();
        Serial.println("[WiFi] BOOT 键：重新计时");
      }
    }
  }
  bootLast = bootNow;

  /* ---- 转发 BMS 帧给手机 ---- */
  if (bmsConnected) transferPending();

  /* ---- 手机断开后重启广播（回调里不能 delay）---- */
  if (gNeedRestartAdv) {
    gNeedRestartAdv = false;
    delay(350);
    BLEDevice::startAdvertising();
  }

  /* ---- 每秒轮询 BMS ---- */
  static uint32_t tPoll = 0;
  if (millis() - tPoll >= POLL_INTERVAL_MS) {
    tPoll = millis();
    pollBms();
  }

  /* ---- BMS 连接状态机（无上限重连）---- */
  bmsConnTick();

  delay(2);
}
