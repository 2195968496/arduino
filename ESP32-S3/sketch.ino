##
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

/* 说明：不需要单独 #include <esp_bt.h> / <esp_gap_ble_api.h> / <esp_gatts_api.h>。
 * 这三个是 ESP-IDF 的底层头文件，不是 Arduino 库；而 BLEDevice.h 内部已经
 * 包含了它们（esp_bt.h、esp_gap_ble_api.h、esp_gatts_api.h），
 * 所以 esp_power_level_t / ESP_PWR_LVL_* / esp_ble_tx_power_set /
 * esp_gatt_if_t / esp_ble_gatts_send_indicate 这些符号都已可见。
 * 在本文件里重复 include 反而会因为不同 core 版本的搜索路径差异报 file not found。 */

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

/* ---------------------------- 多连接跟踪 ---------------------------- */
static uint16_t connIds[MAX_CONN];
static volatile int connCount = 0;
static portMUX_TYPE connMux = portMUX_INITIALIZER_UNLOCKED;

void addConn(uint16_t id) {
  portENTER_CRITICAL(&connMux);
  bool found = false;
  for (int i = 0; i < connCount; i++) if (connIds[i] == id) found = true;
  if (!found && connCount < MAX_CONN) connIds[connCount++] = id;
  portEXIT_CRITICAL(&connMux);
}

void removeConn(uint16_t id) {
  portENTER_CRITICAL(&connMux);
  for (int i = 0; i < connCount; i++) {
    if (connIds[i] == id) {
      for (int j = i; j < connCount - 1; j++) connIds[j] = connIds[j + 1];
      connCount--;
      break;
    }
  }
  portEXIT_CRITICAL(&connMux);
}

int getConnCount() { return connCount; }

int snapshotConns(uint16_t* out) {
  portENTER_CRITICAL(&connMux);
  int n = connCount;
  for (int i = 0; i < n; i++) out[i] = connIds[i];
  portEXIT_CRITICAL(&connMux);
  return n;
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
/* 百分比 -> dBm 档位数值。
 * ESP32-S3 支持 -12/-9/-6/-3/0/+3/+6/+9 dBm，IDF 里用 esp_power_level_t 枚举表示，
 * 但极简 core 里这个类型/常量可能没暴露。这里直接用底层整数值：
 *   -6dBm = 4, 0dBm = 7, +3dBm = 8, +6dBm = 9, +9dBm = 10
 * （顺序对应 ESP_PWR_LVL_N12=0 … ESP_PWR_LVL_P9=10）
 * 若你的 core 有完整枚举，用常量名同样得到这些值。 */
static int percentToPwrLevelInt(uint8_t pct) {
  if (pct <= 20) return 4;   /* -6 dBm */
  if (pct <= 40) return 7;   /*  0 dBm */
  if (pct <= 60) return 8;   /* +3 dBm */
  if (pct <= 80) return 9;   /* +6 dBm */
  return 10;                 /* +9 dBm */
}

static const char* percentToDbmText(uint8_t pct) {
  if (pct <= 20) return "-6 dBm";
  if (pct <= 40) return "0 dBm";
  if (pct <= 60) return "+3 dBm";
  if (pct <= 80) return "+6 dBm";
  return "+9 dBm";
}

/* esp_ble_tx_power_set 也可能未声明，自声明原型（参数用 int 避免枚举依赖）*/
extern "C" esp_err_t esp_ble_tx_power_set(int type, int power_level);

void applyTxPower(uint8_t pct) {
  int lv = percentToPwrLevelInt(pct);
  esp_ble_tx_power_set(0, lv);      /* 0 = ESP_BLE_PWR_TYPE_ADV   广播包 */
  esp_ble_tx_power_set(1, lv);      /* 1 = ESP_BLE_PWR_TYPE_DEFAULT 连接 */
  esp_ble_tx_power_set(2, lv);      /* 2 = ESP_BLE_PWR_TYPE_SCAN    扫描 */
  cfgTxPercent = pct;
  Serial.printf("[PWR] 发射功率 %u%% (%s)\n", (unsigned)pct, percentToDbmText(pct));
}

/* ========================= 向上（手机）转发 ========================= */
/* 本文件用到的 IDF 符号在这个 core 里没有声明，这里做兼容处理。
 *
 * RELAY_MULTI_CONN = 1 : 用 IDF 底层接口逐连接发送，支持 3 台同时收
 * RELAY_MULTI_CONN = 0 : 退回 Arduino 原生 notify()，只支持单台
 *
 * 如果编译期报 esp_gatt_if_t 之类类型不存在，或链接期报 undefined reference，
 * 就把这里改成 0 —— 功能降级为单设备，但一定能编过。
 */
#define RELAY_MULTI_CONN 1

#if RELAY_MULTI_CONN
/* 自声明原型，避免 undeclared identifier。
 * 参数一律用基础整数类型，彻底避开对 IDF 枚举/结构体类型的依赖。 */
extern "C" {
esp_err_t esp_ble_gatts_send_indicate(uint8_t gatts_if,
                                      uint16_t conn_id,
                                      uint16_t attr_handle,
                                      uint16_t value_len,
                                      uint8_t *value,
                                      bool need_confirm);
esp_err_t esp_ble_gatts_register_callback(void (*callback)(int event,
                                                           uint8_t gatts_if,
                                                           void* param));
}
#endif

/* GATTS 接口号：用 uint8_t，避免依赖 esp_gatt_if_t */
static uint8_t gGattsIf = 0;
static bool gGattsIfReady = false;

/* 直接挂一次 GATTS 注册回调，从 ESP_GATTS_REG_EVT 里取 gatts_if。
 * ESP_GATTS_REG_EVT 的枚举值是 0，用数字避免依赖枚举类型。 */
static void relayGattsRegCb(int event, uint8_t gatts_if, void* param) {
  (void)param;
  if (event == 0) {                    /* ESP_GATTS_REG_EVT == 0 */
    gGattsIf = gatts_if;
    gGattsIfReady = true;
    Serial.printf("[BLE] GATTS 接口号 = %u\n", (unsigned)gatts_if);
  }
}

void notifyToPhones(const uint8_t* data, size_t len) {
  if (pTxCh == nullptr || pServer == nullptr) return;

#if RELAY_MULTI_CONN
  if (!gGattsIfReady) return;          /* 接口号还没抓到就先不发 */
  uint16_t handle = pTxCh->getHandle();
#else
  (void)len;
#endif

  uint16_t ids[MAX_CONN];
  int n = snapshotConns(ids);
  if (n == 0) return;                  /* 无手机连接，不必组包 */

  for (size_t off = 0; off < len; off += NOTIFY_CHUNK) {
    size_t c = len - off;
    if (c > NOTIFY_CHUNK) c = NOTIFY_CHUNK;

#if RELAY_MULTI_CONN
    /* 逐连接发送：Arduino 原生 notify() 只作用于一个 conn_id，
       多设备必须直接调 IDF 接口指定目标连接。 */
    for (int i = 0; i < n; i++) {
      esp_ble_gatts_send_indicate(gGattsIf, ids[i], handle, (uint16_t)c,
                                  (uint8_t*)(data + off), false);
    }
#else
    /* 单连接降级模式：只发往当前活动的连接 */
    pTxCh->setValue((uint8_t*)(data + off), c);
    pTxCh->notify();
#endif

    /* 给协议栈留出排空时间，否则发送队列(默认32项)溢出导致丢包 */
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

/* ============================ BLE Server 侧 ============================ */
volatile bool gNeedRestartAdv = false;

/* 注意：这里必须用 BLEServer 给出的真实 conn_id。
 * esp_ble_gatts_send_indicate() 的 conn_id 参数是协议栈内部句柄，
 * 用自造序号会导致发送失败（且不报错，只是手机收不到）。
 * 你的编译报错里没有出现 getConnId，说明这个 core 是提供的，直接用。 */
class PhoneServerCb : public BLEServerCallbacks {
  void onConnect(BLEServer* s) override {
    uint16_t id = s->getConnId();
    addConn(id);
    Serial.printf("[Phone] 连接 conn_id=%u，当前 %d/%d\n",
                  (unsigned)id, getConnCount(), MAX_CONN);
  }
  void onDisconnect(BLEServer* s) override {
    uint16_t id = s->getConnId();
    removeConn(id);
    Serial.printf("[Phone] 断开 conn_id=%u，剩余 %d/%d\n",
                  (unsigned)id, getConnCount(), MAX_CONN);
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

  /* 注册 GATTS 回调，从 ESP_GATTS_REG_EVT 里抓 gatts_if
   * （不依赖 BLEServer::getGattsIf，那个在某些 core 未公开）*/
  esp_ble_gatts_register_callback(relayGattsRegCb);

  BLEAdvertising* adv = BLEDevice::getAdvertising();
  adv->addServiceUUID(SVC_UUID);
  adv->setScanResponse(true);
  adv->setMinPreferred(0x06);
  BLEDevice::startAdvertising();

  bleInited = true;
  applyTxPower(cfgTxPercent);

  Serial.printf("[BLE] 广播名 = %s\n", cfgRelayName.c_str());
}

void applyRelayName(const String& nm) {
  cfgRelayName = nm;
  BLEDevice::stopAdvertising();
  delay(120);
  /* esp_ble_gap_set_device_name 在某些精简 core 里没有声明。
   * BLEDevice 提供的是 setDeviceName/ init 两种途径；改名其实只需
   * 重新 init 广播名，但 init 不能重入。折中：用 BLEDevice::setDeviceName（若可用），
   * 否则仅重启广播（广播包里的名字由 init 时确定，改名需重启模块才彻底生效）。 */
#if defined(ESP_ARDUINO_VERSION_MAJOR) && ESP_ARDUINO_VERSION_MAJOR >= 3
  BLEDevice::setDeviceName(nm);
#else
  extern "C" esp_err_t esp_ble_gap_set_device_name(const char* name);
  esp_ble_gap_set_device_name(nm.c_str());
#endif
  delay(120);
  BLEDevice::startAdvertising();
  Serial.printf("[BLE] 广播名已改为 %s\n", cfgRelayName.c_str());
}

/* ============================== WiFi 控制 ============================== */
String scanJson = "[]";
volatile bool gScanning = false;

void handleRoot();
void handleScan();
void handleSave();
void handleStatus();
void handleWifiCtl();

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
  <h2>1. 选择中继设备（蚂蚁 BMS）</h2>
  <div class="row">
    <button id="bs" onclick="doScan()">扫描附近 ANT 设备</button>
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
 var b=document.getElementById('bs'); b.disabled=true; b.textContent='扫描中（约6秒）…';
 document.getElementById('list').textContent='正在扫描…';
 fetch('/scan').then(r=>r.json()).then(j=>{
   var L=document.getElementById('list'); L.innerHTML='';
   if(!j.length){L.textContent='未发现 ANT 设备，请确认 BMS 已上电且在附近';}
   j.forEach(d=>{
     var e=document.createElement('div');
     e.className='dev'+(d.addr==chosen?' sel':'');
     e.innerHTML='<b>'+d.name+'</b><br><span style="color:#6b7280;font-size:12px">'
                 +d.addr+'　RSSI '+d.rssi+'</span>';
     e.onclick=function(){
       chosen=d.addr; chosenName=d.name;
       document.getElementById('sel').textContent=chosen+' ('+d.name+')';
       document.querySelectorAll('.dev').forEach(x=>x.classList.remove('sel'));
       e.classList.add('sel');
     };
     L.appendChild(e);
   });
   b.disabled=false; b.textContent='重新扫描';
 }).catch(()=>{b.disabled=false;b.textContent='重新扫描';});
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
function wifiCtl(a){
 fetch('/wifi?act='+a).then(r=>r.text()).then(()=>st()).catch(()=>{});
}
st(); setInterval(st,2000);
</script></body></html>)HTML";

/* ============================== 扫描回调 ============================== */
/* onResult 的虚函数签名在不同 core 里不一致（传值 / 传指针），而且
 * 具体是哪种无法靠版本宏判断（遇到过 3.x 版本号却仍用传值的构建）。
 *
 * 解决办法：两个重载都不写 override 关键字，都提供。
 *   - 编译器会自动把与基类虚函数匹配的那个识别为覆写；
 *   - 另一个只是普通的额外重载，不影响；
 *   - 这样无论基类是传值还是传指针，本类都不是抽象类，可正常 new。
 */
class ScanCb : public BLEAdvertisedDeviceCallbacks {
public:
  void onResult(BLEAdvertisedDevice dev) { handleDev(&dev); }
  void onResult(BLEAdvertisedDevice* dev) { if (dev) handleDev(dev); }

  void handleDev(BLEAdvertisedDevice* dev) {
    if (!gScanning) return;
    String nm = String(dev->getName().c_str());
    if (nm.length() == 0) return;
    String up = nm; up.toUpperCase();
    if (!up.startsWith("ANT")) return;

    String item = String("{\"name\":\"") + nm + "\",\"addr\":\"" +
                  String(dev->getAddress().toString().c_str()) +
                  "\",\"rssi\":" + String(dev->getRSSI()) + "}";
    if (scanJson == "[]") scanJson = "[" + item + "]";
    else                  scanJson = scanJson.substring(0, scanJson.length() - 1) + "," + item + "]";
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
  if (gScanning) { server.send(200, "application/json", scanJson); return; }
  scanJson = "[]";
  gScanning = true;
  BLEScan* sc = BLEDevice::getScan();
  sc->setAdvertisedDeviceCallbacks(new ScanCb(), false);
  sc->setActiveScan(true);
  sc->setInterval(100);
  sc->setWindow(99);
  Serial.println("[Scan] 开始扫描 ANT 设备…");
  sc->start(6);
  sc->clearResults();
  gScanning = false;
  Serial.printf("[Scan] 结束，JSON 长度 %d\n", scanJson.length());
  server.send(200, "application/json", scanJson);
}

void handleSave() {
  String mac   = server.arg("mac");
  String relay = server.arg("relay");
  String name  = server.arg("name");
  String txp   = server.arg("txp");
  mac.trim(); relay.trim(); name.trim(); txp.trim();

  bool changedMac = (mac.length() == 17 && mac != cfgBmsMac);
  if (mac.length() == 17) {
    prefs.putString("mac", mac);
    cfgBmsMac = mac;
  }
  if (name.length() > 0) {
    prefs.putString("bname", name);
    cfgBmsName = name;
  }

  if (relay.length() >= 3 && relay != cfgRelayName) {
    String up = relay; up.toUpperCase();
    if (!up.startsWith("ANT")) {
      Serial.println("[Cfg] 警告：中继名未以 ANT 开头，官方 App 可能识别不到");
    }
    prefs.putString("rname", relay);
    applyRelayName(relay);
  }

  if (txp.length() > 0) {
    int p = txp.toInt();
    if (p > 0 && p <= 100) {
      prefs.putUChar("txp", (uint8_t)p);
      applyTxPower((uint8_t)p);
      /* 广播包功率改动需重启广播才在部分版本生效 */
      if (bleInited) {
        BLEDevice::stopAdvertising();
        delay(80);
        BLEDevice::startAdvertising();
      }
    }
  }

  if (changedMac) {
    if (bmsClient != nullptr && bmsConnected) bmsClient->disconnect();
    bmsConnected = false;
    bmsCh = nullptr;
    rxlen = 0;
  }
  server.send(200, "text/plain; charset=utf-8", "已保存，正在应用配置");
}

void handleStatus() { server.send(200, "application/json", statusJson()); }

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
void loadCfg() {
  prefs.begin("relay", false);
  cfgBmsMac    = prefs.getString("mac", "");
  cfgBmsName   = prefs.getString("bname", "");
  cfgRelayName = prefs.getString("rname", "ANT-RELAY");
  cfgTxPercent = prefs.getUChar("txp", 80);
  prefs.end();
  if (cfgTxPercent != 20 && cfgTxPercent != 40 && cfgTxPercent != 60 &&
      cfgTxPercent != 80 && cfgTxPercent != 100) {
    cfgTxPercent = 80;
  }
  Serial.printf("[Cfg] BMS=%s Relay=%s Power=%u%%\n",
                cfgBmsMac.c_str(), cfgRelayName.c_str(), (unsigned)cfgTxPercent);
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

  /* ---- BMS 掉线重连 ---- */
  static uint32_t tReconn = 0;
  if (!bmsConnected && cfgBmsMac.length() == 17 && !gScanning) {
    if (millis() - tReconn >= 5000) {
      tReconn = millis();
      connectBms();
    }
  }

  delay(2);
}
