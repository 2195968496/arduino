## Build the Firmware Binaries Automatically
> ⚠️ Only a unified .ino file is supported
1. Fork the repository
2. Go to the fork repository settings > actions > general then from the bottom just check
   - ✓ Read and write permissions
   - ✓ Allow GitHub Actions to create and approve pull requests
3. Next edit and paste your code inside `sketch.ino` or make any filename.ino 
4. Go to actions > general build > run workflows > select board > run
5. The compiled firmware is located on the release section

## Add Custom Libraries
> Find inside `.github/workflows/general.yml` and add another libraries.
```
arduino-cli lib install "ArduinoJson"
arduino-cli lib install "PubSubClient"
arduino-cli lib install "RTClib"
```


