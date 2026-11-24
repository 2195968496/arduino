# Build the Firmware Binaries Automatically
> ⚠️ Only the unified .ino file is supported
1. Fork the repository
2. Go to repository settings > general > actions from the bottom check
   ✓ Read and write permissions
   ✓ Allow GitHub Actions to create and approve pull requests
3. Edit and paste your code inside `sketch.ino` or make any filename.ino 
4. Go to actions > general build > run workflows > select board > run
5. The compiled firmware is located in the release section

## Add Custom Libraries
> Find inside `.github/workflows/general.yml` and add another libraries.
```
arduino-cli lib install "ArduinoJson"
arduino-cli lib install "PubSubClient"
arduino-cli lib install "RTClib"
```


