// INKBIRD INT-14-BW Gateway FF03 PER-PROBE BATTERY + TARGET + FF01 RECOVERY - NimBLE MTU 517
// Seeed XIAO ESP32-S3, Arduino ESP32, NimBLE-Arduino 2.x
#include <Arduino.h>
#include <WiFi.h>
#include <WebServer.h>
#include <NimBLEDevice.h>
extern "C" {
#include "host/ble_gap.h"
}
#include <vector>
#include <math.h>
#include <time.h>
#include <sys/time.h>
// Session authentication implemented below (CRC8 DVB-S2 + CDMA2000).

// Production: normally no raw BLE frames, no periodic bulk GATT reads.
// Set to true temporarily when diagnosing a problem.
constexpr bool INKBIRD_DIAGNOSTICS = false;
constexpr bool INKBIRD_PERIODIC_GATT_READS = false;
constexpr bool INKBIRD_AUTH_FALLBACK = false; // no init before confirmed 02 FC 00

const char* WIFI_SSID = "ANPASSEN!!";
const char* WIFI_PASS = "ANPASSEN!!";
const char* INKBIRD_MAC = "ANPASSEN!!";

const char* SERVICE_UUID = "0000ff00-0000-1000-8000-00805f9b34fb";
const char* CHAR_UUIDS[6] = {
  "0000ff01-0000-1000-8000-00805f9b34fb",
  "0000ff02-0000-1000-8000-00805f9b34fb",
  "0000ff03-0000-1000-8000-00805f9b34fb",
  "0000ff04-0000-1000-8000-00805f9b34fb",
  "0000ff05-0000-1000-8000-00805f9b34fb",
  "0000ff06-0000-1000-8000-00805f9b34fb"
};

constexpr uint32_t BLE_RETRY_MS = 15000;
constexpr uint32_t WIFI_RETRY_MS = 15000;
// FF01 reports are not strictly periodic; observed intervals occasionally exceed 20 s.
// Keep both REST endpoints and plan44's application-side freshness check in sync.
constexpr uint32_t DATA_TIMEOUT_MS = 60000;
// FF01 recovery runs only in loop(), after authenticated initialization.
// Avoid reconnecting on the already observed ~25-second FF01 notification gaps.
constexpr uint32_t FF01_RESUBSCRIBE_AFTER_MS = 45000;
constexpr uint32_t FF01_RECONNECT_AFTER_MS = 90000;
constexpr uint32_t CHALLENGE_TIMEOUT_MS = 8000;
constexpr uint32_t INIT_COMMAND_GAP_MS = 220; // unused in v3.4
constexpr uint32_t INIT_START_DELAY_MS = 500;
constexpr uint32_t APP_READ_INTERVAL_MS = 60000; // only used when INKBIRD_PERIODIC_GATT_READS=true
constexpr uint32_t ACK_TIMEOUT_MS = 8000;
constexpr uint32_t FF02_READ_DELAYS_MS[] = {100, 300, 700}; // relative to each 01 FB write
constexpr uint32_t AUTH_RESPONSE_DELAY_MS = 100;
// Diagnostic trials, one request per BLE connection. The next reconnect
// tests another delay; no repeated authentication commands in a session.
constexpr uint32_t CHALLENGE_DELAYS_MS[] = {200};
constexpr uint8_t CHALLENGE_TRIALS = sizeof(CHALLENGE_DELAYS_MS) / sizeof(CHALLENGE_DELAYS_MS[0]);

struct Probe { float core; float ambient; bool active; };
// FF02 response type 0x02 reports the configured target for each probe.
// A target is kept independently of FF01 telemetry and cleared on reconnect.
struct TargetTemperature { float value; bool valid; uint16_t raw; };
TargetTemperature targets[4] = {};
char reportedTemperatureUnit = '?'; // FF02 type 0x04: 'C' or 'F' (device setting)
// On this INT-14-BW, FF02 target data itself is Fahrenheit x10,
// independently of the user's displayed Celsius unit (49C -> 1200, 54C -> 1290).

// FF03 status: experimental 11-byte INT-14-BW layout (4 x LE16 + 3 global).
// The published reverse-engineering spec describes a DIFFERENT 56-byte byte-array.
// Therefore the following 11-byte bit masks are HYPOTHESES, NOT PROVEN FLAGS.
// Verify with a real Cook Done alarm before relying on automation.
constexpr uint16_t FF03_COOK_DONE_MASK = 0x0010;  // proposed bit 4
constexpr uint16_t FF03_BATTERY_MASK   = 0x4000;  // proposed bit 14
constexpr uint32_t FF03_STATUS_TIMEOUT_MS = 120000;
bool probeCookDone[4] = {false,false,false,false};
bool probeCookDoneKnown[4] = {false,false,false,false};
bool probeBatteryAlarm[4] = {false,false,false,false};
bool probeBatteryKnown[4] = {false,false,false,false};
bool batteryAlarmKnown = false;
bool batteryAlarm = false;
uint16_t ff03StatusWords[4] = {0,0,0,0};
uint8_t ff03LastRaw[16] = {};
size_t ff03LastRawLen = 0;
const char* ff03DecodeName = "none";
size_t lastFF03Length = 0;
uint32_t lastBatteryReportMs = 0;
uint32_t unknownFF03Reports = 0;

Probe probes[4];
uint8_t lastRaw[64] = {};
size_t lastRawLen = 0;
uint32_t lastTelemetryMs = 0;
bool haveTelemetry = false;
uint32_t ff01NotifyCount = 0;  // guarded by dataMux
bool ff01RecoveryAttempted = false; // loop()-only
uint32_t ff01RecoveryAttempts = 0;
uint32_t ff01WatchdogReconnects = 0;
portMUX_TYPE dataMux = portMUX_INITIALIZER_UNLOCKED;

WebServer server(80);
NimBLEClient* bleClient = nullptr;
NimBLERemoteCharacteristic* controlChar = nullptr;
NimBLERemoteCharacteristic* chars[6] = {};

volatile bool disconnectPending = false;
volatile int disconnectReason = -1;
volatile uint32_t disconnectAt = 0;
volatile uint32_t disconnectCount = 0;
volatile uint32_t connectedAt = 0;
uint32_t connectCount = 0, failedConnectCount = 0;
uint32_t lastBleAttempt = 0, lastWifiAttempt = 0;
bool bleConnecting = false;
bool additionalSubscriptionsDone = false;
uint32_t challengeRequestAt = 0;
bool fdReadDone = false;
bool statusReadDone = false;
size_t initCommandIndex = 0;
bool combinedInitSent = false;
uint32_t lastLinkLogMs = 0;
uint32_t lastAppReadMs = 0;
uint32_t appReadCycles = 0;
volatile uint32_t ff02NotificationCount = 0;
volatile uint32_t ff02LastNotificationMs = 0;
uint32_t ff02WriteCount = 0;
uint32_t ff02WriteFailures = 0;
uint32_t challengeTrialNumber = 0;
uint8_t activeChallengeTrial = 0;
uint32_t activeChallengeDelayMs = 0;

// Application-level FF02 challenge/response; independent of BLE SMP bonding.
// Shared with the INT-12-BW protocol; INT-14-BW behavior is the test target.
volatile bool authChallengePending = false;
volatile bool authAckSeen = false;
volatile bool authAckRejected = false;
volatile uint32_t authChallengeReceivedAt = 0;
uint8_t authChallenge[6] = {};
portMUX_TYPE challengeMux = portMUX_INITIALIZER_UNLOCKED;
uint32_t authRequestAt = 0;
uint32_t authResponseAt = 0;
uint8_t authRequestCount = 0;
bool authVerified = false;
bool authResponseSent = false;
bool authInitFallback = false;
uint32_t authReadyAt = 0;
uint8_t authReadIndex = 0;
uint32_t authAckReadAt = 0;
uint8_t authAckReadIndex = 0;
uint32_t ff02ValidReadFrames = 0;

uint8_t crc8msb(const uint8_t* bytes, size_t count, uint8_t poly, uint8_t initial) {
  uint8_t crc = initial;
  for (size_t i = 0; i < count; i++) {
    crc ^= bytes[i];
    for (uint8_t bit = 0; bit < 8; bit++) crc = (crc & 0x80) ? uint8_t((crc << 1) ^ poly) : uint8_t(crc << 1);
  }
  return crc;
}

void buildAuthResponse(const uint8_t challengeBytes[6], uint8_t result[9]) {
  struct timeval tv;
  gettimeofday(&tv, nullptr);
  const uint16_t ms = uint16_t(tv.tv_usec / 1000);
  const uint32_t sec = uint32_t(tv.tv_sec);
  result[0] = 0x08;
  result[1] = 0xFC;
  result[2] = uint8_t(ms);
  result[3] = uint8_t(ms >> 8);
  for (int i=0;i<4;i++) result[4+i] = uint8_t(sec >> (8*i));
  const uint8_t inner = crc8msb(result + 2, 6, 0xD5, 0x00);
  const uint8_t cdma = crc8msb(challengeBytes, 6, 0x9B, 0xFF);
  uint8_t combined[8];
  memcpy(combined, result + 2, 6);
  combined[6] = inner;
  combined[7] = cdma;
  result[8] = crc8msb(combined, sizeof(combined), 0xD5, 0x00);
}

bool authSelfTest() {
  const uint8_t vectorChallenge[6] = {0x2A,0x19,0xE1,0x1E,0x78,0xAA};
  const uint8_t vectorTime[6] = {0xE2,0x01,0x9F,0x5A,0x18,0x6A};
  const uint8_t expected = 0x78;
  const uint8_t inner = crc8msb(vectorTime, 6, 0xD5, 0x00);
  const uint8_t cdma = crc8msb(vectorChallenge, 6, 0x9B, 0xFF);
  uint8_t mixed[8]; memcpy(mixed, vectorTime, 6); mixed[6]=inner; mixed[7]=cdma;
  return crc8msb(mixed, 8, 0xD5, 0x00) == expected;
}

// Forward declaration required before logLink() (Arduino auto-prototypes are unreliable here).
bool connected();

// ESP-IDF/NimBLE GAP connection descriptor: read-only diagnostics.
void logLink(const char* phase) {
  if (!connected()) return;
  uint16_t handle = bleClient->getConnHandle();
  ble_gap_conn_desc desc = {};
  int rc = ble_gap_conn_find(handle, &desc);
  if (rc != 0) {
    Serial.printf("[DIAG] %s GAP lookup failed rc=%d handle=%u\n", phase, rc, (unsigned)handle);
    return;
  }
  Serial.printf("[DIAG] %s handle=%u interval=%.2f ms latency=%u supervision=%u ms\n",
                phase, (unsigned)handle, desc.conn_itvl * 1.25f,
                (unsigned)desc.conn_latency, (unsigned)desc.supervision_timeout * 10);
  Serial.printf("[DIAG] %s encrypted=%d authenticated=%d bonded=%d key_size=%u MTU=%u\n",
                phase, desc.sec_state.encrypted, desc.sec_state.authenticated,
                desc.sec_state.bonded, (unsigned)desc.sec_state.key_size,
                (unsigned)bleClient->getMTU());
}

// Handshake stages, processed only in loop(), never in BLE notification callback.
enum AuthStage : uint8_t { AUTH_IDLE, AUTH_SETTLE, AUTH_INIT_COMMANDS, AUTH_READ_STATUS, AUTH_READY, AUTH_FAILED };
// Explicit prototypes: prevent Arduino auto-prototype before AuthStage declaration.
const char* authName(AuthStage s);
bool connected();

volatile AuthStage authStage = AUTH_IDLE;
uint32_t authStepMs = 0;
uint32_t lastFF02ReadMs = 0;
uint32_t ff02ReadCount = 0;
uint32_t ff02ReadErrors = 0;
String lastFF02ReadHex = "";
uint8_t challenge[6] = {};
portMUX_TYPE authMux = portMUX_INITIALIZER_UNLOCKED;

String hexBytes(const uint8_t* p, size_t n) {
  String s;
  for (size_t i = 0; i < n; ++i) {
    if (i) s += ' ';
    if (p[i] < 16) s += '0';
    s += String(p[i], HEX);
  }
  s.toUpperCase();
  return s;
}

bool connected() { return bleClient && bleClient->isConnected(); }

const char* authName(AuthStage s) {
  switch (s) {
    case AUTH_IDLE: return "idle";
    case AUTH_SETTLE: return "settle";
    case AUTH_INIT_COMMANDS: return "init_commands";
    case AUTH_READ_STATUS: return "read_status";
    case AUTH_READY: return "ready_diagnostic";
    default: return "failed";
  }
}

float temperature(const uint8_t* p) {
  int16_t raw = (int16_t)((uint16_t)p[0] | ((uint16_t)p[1] << 8));
  if (raw == 32766 || raw == 32767 || raw == (int16_t)0x8000) return NAN;
  return raw / 10.0f;
}

void onTelemetry(NimBLERemoteCharacteristic*, uint8_t* p, size_t n, bool) {
  if (n < 16) return;
  Probe decoded[4];
  for (int i = 0; i < 4; ++i) {
    decoded[i].core = temperature(p + i * 4);
    decoded[i].ambient = temperature(p + i * 4 + 2);
    decoded[i].active = isfinite(decoded[i].core) && isfinite(decoded[i].ambient)
      && decoded[i].core >= -40 && decoded[i].core <= 350
      && decoded[i].ambient >= -40 && decoded[i].ambient <= 350;
  }
  portENTER_CRITICAL(&dataMux);
  memcpy(probes, decoded, sizeof(decoded));
  lastRawLen = min(n, sizeof(lastRaw));
  memcpy(lastRaw, p, lastRawLen);
  lastTelemetryMs = millis();
  haveTelemetry = true;
  ++ff01NotifyCount;
  portEXIT_CRITICAL(&dataMux);
  if (INKBIRD_DIAGNOSTICS) {
    Serial.printf("[BLE] FF01: %s\n", hexBytes(p, n).c_str());
    for (int i = 0; i < 4; ++i) {
      if (decoded[i].active) Serial.printf("[TEMP] Sonde %d: Core %.1f C / Ambient %.1f C\n", i+1, decoded[i].core, decoded[i].ambient);
      else Serial.printf("[TEMP] Sonde %d: inaktiv\n", i+1);
    }
  }
}

// Parse both FF02 notifications and active GATT reads using the same frame decoder.
void parseFF02(const uint8_t* p, size_t n, const char* source) {
  if (!p || n < 3) return;
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[RX] t=%lu FF02 %s (%u): %s\n", (unsigned long)millis(), source, (unsigned)n, hexBytes(p, n > 32 ? 32 : n).c_str());
  // A frame may contain multiple concatenated LEN/TYPE/PAYLOAD records.
  size_t offset = 0;
  while (offset + 2 <= n) {
    const uint8_t frameLen = p[offset];
    if (frameLen < 1 || offset + 1u + frameLen > n) break;
    const uint8_t type = p[offset + 1];
    if (type == 0xFB && frameLen == 7) {
      portENTER_CRITICAL(&challengeMux);
      memcpy(authChallenge, p + offset + 2, 6);
      authChallengePending = true;
      authChallengeReceivedAt = millis();
      portEXIT_CRITICAL(&challengeMux);
      Serial.println("[AUTH] 07 FB Challenge empfangen");
    } else if (type == 0x02 && frameLen >= 9) {
      // FF02 target temperature report: LEN=09 TYPE=02 MASK MODE HIGHlo HIGHhi LOWlo LOWhi DEG FOOD
      // The high target is a LE16 in tenths; unit is supplied separately by type 0x04.
      const uint8_t* payload = p + offset + 2;
      const uint8_t mask = payload[0];
      const uint16_t rawHigh = uint16_t(payload[2]) | (uint16_t(payload[3]) << 8);
      // Only publish a single-probe mask with a plausible positive setpoint.
      int idx = -1;
      if (mask == 0x01) idx = 0;
      if (mask == 0x02) idx = 1;
      if (mask == 0x04) idx = 2;
      if (mask == 0x08) idx = 3;
      if (idx >= 0) {
        portENTER_CRITICAL(&dataMux);
        targets[idx].raw = rawHigh;
        targets[idx].valid = rawHigh > 0 && rawHigh < 6000;
        // Verified with the user's INKBIRD app: raw 1200 = 49C,
        // raw 1290 = 54C. Thus raw/10 is Fahrenheit, not Celsius.
        const float fahrenheit = float(rawHigh) / 10.0f;
        const float celsius = (fahrenheit - 32.0f) * (5.0f / 9.0f);
        targets[idx].valid = rawHigh > 320 && rawHigh < 7000 &&
                             isfinite(celsius) && celsius >= -40.0f && celsius <= 350.0f;
        targets[idx].value = celsius;
        portEXIT_CRITICAL(&dataMux);
        Serial.printf("[TARGET] Sonde %d raw=%u fahrenheit=%.1f celsius=%.1f valid=%d\n",
                      idx+1, (unsigned)rawHigh, fahrenheit, celsius, targets[idx].valid);
      }
    } else if (type == 0x04 && frameLen >= 2) {
      // The device unit report may precede or follow the target reports.
      char unit = char(p[offset+2]);
      if (unit == 'C' || unit == 'F') reportedTemperatureUnit = unit;
    } else if (type == 0xFC && frameLen == 2) {
      if (p[offset+2] == 0x00) {
        authAckSeen = true;
        Serial.println("[AUTH] 02 FC 00 ACK empfangen");
      } else {
        authAckRejected = true;
        Serial.printf("[AUTH] 02 FC Fehlercode=%u\n", p[offset+2]);
      }
    }
    offset += size_t(frameLen) + 1;
  }
}

void onControl(NimBLERemoteCharacteristic* chr, uint8_t* p, size_t n, bool isNotify) {
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[CCCD] FF02 callback handle=0x%04X mode=%s len=%u\n",
                (unsigned)chr->getHandle(), isNotify ? "NOTIFY" : "INDICATE", (unsigned)n);
  ff02NotificationCount++;
  ff02LastNotificationMs = millis();
  parseFF02(p, n, "NOTIFY");
}

// nRF Connect confirmed that 01 FB can be followed by a readable
// 07 FB challenge on FF02. NimBLE may return a 512-byte padded buffer:
// inspect only the actual frame header/length, never treat zeros as a frame.
void readFF02(const char* reason) {
  if (!connected() || !controlChar || !controlChar->canRead()) return;
  ++ff02ReadCount;
  NimBLEAttValue v = controlChar->readValue();
  size_t n = v.size();
  const uint8_t* p = v.data();
  size_t shown = n > 24 ? 24 : n;
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[AUTH-READ] %s read=%lu len=%u prefix=%s\n", reason,
                (unsigned long)ff02ReadCount, (unsigned)n,
                (p && shown) ? hexBytes(p, shown).c_str() : "<empty>");
  if (!p || n < 3 || p[0] == 0 || p[0] > 32 || size_t(p[0]) + 1 > n) {
    ++ff02ReadErrors;
    return;
  }
  ++ff02ValidReadFrames;
  parseFF02(p, size_t(p[0]) + 1, "READ");
}

void pollFF02Challenge(uint32_t now) {
  if (!authRequestAt || authChallengePending || authResponseSent || authVerified) return;
  if (authReadIndex >= 3) return;
  if (now - authRequestAt < FF02_READ_DELAYS_MS[authReadIndex]) return;
  ++authReadIndex; // increment before potentially blocking GATT read
  readFF02("challenge");
}

void pollFF02Ack(uint32_t now) {
  if (!authResponseSent || authAckSeen || authAckRejected || !authResponseAt) return;
  if (authAckReadIndex >= 3) return;
  if (now - authResponseAt < FF02_READ_DELAYS_MS[authAckReadIndex]) return;
  ++authAckReadIndex;
  readFF02("auth-ack");
}

// Verify the actual Client Characteristic Configuration Descriptor (0x2902).
// For FF02 notifications, CCCD must contain 01 00 (little endian).
// A successful subscribe() alone does not prove the peripheral accepted it.
bool verifyFF02CCCD(const char* phase) {
  if (!controlChar) return false;
  NimBLERemoteDescriptor* cccd = controlChar->getDescriptor(NimBLEUUID((uint16_t)0x2902));
  if (!cccd) {
    Serial.printf("[CCCD] %s FF02 descriptor 0x2902 MISSING\n", phase);
    return false;
  }
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[CCCD] %s descriptor handle=0x%04X\n", phase, (unsigned)cccd->getHandle());
  NimBLEAttValue value = cccd->readValue();
  if (value.size() < 2) {
    Serial.printf("[CCCD] %s READ failed/short len=%u\n", phase, (unsigned)value.size());
    return false;
  }
  const uint16_t flags = uint16_t(value.data()[0]) | (uint16_t(value.data()[1]) << 8);
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[CCCD] %s READ=%s notifications=%d indications=%d\n", phase,
                hexBytes(value.data(), value.size()).c_str(), (flags & 1) != 0, (flags & 2) != 0);
  return (flags & 1) != 0;
}

// Decode FF03 without interpreting short reports using the 56-byte-array layout.
// For observed 11-byte frames test proposed 4 x little-endian 16-bit words.
// Preserve the original >=64-byte alternative for compatibility.
void parseBatteryStatusFF03(const uint8_t* p, size_t n) {
  if (!p || n == 0) return;
  bool changed = false;
  bool anyAlarm = false;
  uint32_t now = millis();
  portENTER_CRITICAL(&dataMux);
  lastFF03Length = n;
  ff03LastRawLen = n < sizeof(ff03LastRaw) ? n : sizeof(ff03LastRaw);
  memcpy(ff03LastRaw, p, ff03LastRawLen);
  if (n == 11) {
    // Experimental interpretation: 8 bytes for four probes, 3 global bytes.
    // E.g. 01 10 -> 0x1001, bit4 clear; 11 10 -> bit4 set.
    ff03DecodeName = "le16_bitfield_experimental";
    for (int i = 0; i < 4; ++i) {
      uint16_t word = uint16_t(p[i*2]) | (uint16_t(p[i*2+1]) << 8);
      ff03StatusWords[i] = word;
      bool cook = (word & FF03_COOK_DONE_MASK) != 0;
      bool battery = (word & FF03_BATTERY_MASK) != 0;
      if (!probeCookDoneKnown[i] || probeCookDone[i] != cook ||
          !probeBatteryKnown[i] || probeBatteryAlarm[i] != battery) changed = true;
      probeCookDone[i] = cook;
      probeCookDoneKnown[i] = true;
      probeBatteryAlarm[i] = battery;
      probeBatteryKnown[i] = true;
      if (battery) anyAlarm = true;
    }
    batteryAlarm = anyAlarm;
    batteryAlarmKnown = true;
    lastBatteryReportMs = now;
  } else if (n >= 64 && n <= 128) {
    // Older documented byte-array scheme: one byte per boolean flag.
    ff03DecodeName = "legacy_byte_array";
    for (int i=0; i<4; ++i) {
      bool cook = p[16*i + 4] != 0;
      bool battery = p[16*i + 14] != 0;
      if (!probeCookDoneKnown[i] || probeCookDone[i] != cook ||
          !probeBatteryKnown[i] || probeBatteryAlarm[i] != battery) changed = true;
      probeCookDone[i] = cook;
      probeCookDoneKnown[i] = true;
      probeBatteryAlarm[i] = battery;
      probeBatteryKnown[i] = true;
      ff03StatusWords[i] = 0;
      if (battery) anyAlarm = true;
    }
    batteryAlarm = anyAlarm;
    batteryAlarmKnown = true;
    lastBatteryReportMs = now;
  } else {
    ff03DecodeName = "unsupported";
    ++unknownFF03Reports;
    batteryAlarmKnown = false;
    for (int i=0; i<4; ++i) {
      probeBatteryKnown[i] = false;
      probeCookDoneKnown[i] = false;
    }
  }
  portEXIT_CRITICAL(&dataMux);
  if (changed || INKBIRD_DIAGNOSTICS) {
    Serial.printf("[FF03] len=%u encoding=%s raw=%s\n", (unsigned)n,
                  ff03DecodeName, hexBytes(p, n < 16 ? n : 16).c_str());
    if (n == 11) {
      Serial.printf("[FF03] status=0x%04X 0x%04X 0x%04X 0x%04X; CookDone=%d,%d,%d,%d; Batteriealarm=%d\n",
                    ff03StatusWords[0], ff03StatusWords[1], ff03StatusWords[2], ff03StatusWords[3],
                    probeCookDone[0], probeCookDone[1], probeCookDone[2], probeCookDone[3], batteryAlarm);
    }
  }
}

void onOther(NimBLERemoteCharacteristic* chr, uint8_t* p, size_t n, bool) {
  if (chr == chars[2]) {
    parseBatteryStatusFF03(p, n);
  }
  if (INKBIRD_DIAGNOSTICS) {
    String uuid = String(chr->getUUID().toString().c_str());
    Serial.printf("[BLE] t=%lu %s RX (%u Bytes): %s\n",
                  (unsigned long)millis(), uuid.c_str(), (unsigned)n, hexBytes(p, n).c_str());
  }

}

class ClientCallbacks : public NimBLEClientCallbacks {
  void onConnect(NimBLEClient*) override {
    connectedAt = millis();
    Serial.println("[BLE] CONNECTED");
  }
  void onMTUChange(NimBLEClient*, uint16_t mtu) override {
    Serial.printf("[MTU] Async exchange completed, effective ATT MTU=%u\n", (unsigned)mtu);
  }
  void onDisconnect(NimBLEClient*, int reason) override {
    disconnectReason = reason;
    disconnectAt = millis();
    disconnectCount++;
    disconnectPending = true;
    authStage = AUTH_IDLE;
  }
} callbacks;

bool writeControl(const uint8_t* p, size_t n) {
  if (!connected() || !controlChar || !controlChar->canWriteNoResponse()) {
    Serial.println("[BLE] FF02 WRITE_NR nicht verfuegbar");
    return false;
  }
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[BLE] t=%lu FF02 TX (WRITE_NR): %s\n",
                (unsigned long)millis(), hexBytes(p, n).c_str());
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[GATT] FF02 write target value_handle=0x%04X\n", (unsigned)controlChar->getHandle());
  ff02WriteCount++;
  uint32_t txStart = millis();
  bool ok = controlChar->writeValue(p, n, false);
  if (!ok) ff02WriteFailures++;
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[DIAG] WRITE_NR API duration=%lu ms (no remote acknowledgement)\n", (unsigned long)(millis() - txStart));
  if (!ok || INKBIRD_DIAGNOSTICS) Serial.printf("[BLE] Schreibresultat: %s\n", ok ? "OK" : "FEHLER");
  return ok;
}

bool connectInkbird() {
  if (bleConnecting || connected()) return connected();
  bleConnecting = true;
  lastBleAttempt = millis();
  authStage = AUTH_IDLE;
  lastFF02ReadMs = 0;
  ff02ReadCount = 0;
  ff02ReadErrors = 0;
  lastFF02ReadHex = "";
  controlChar = nullptr;
  additionalSubscriptionsDone = false;
  challengeRequestAt = 0;
  fdReadDone = false;
  statusReadDone = false;
  initCommandIndex = 0;
  combinedInitSent = false;
  lastLinkLogMs = 0;
  lastAppReadMs = 0;
  appReadCycles = 0;
  authChallengePending = false;
  authAckSeen = false;
  authAckRejected = false;
  authChallengeReceivedAt = 0;
  authRequestAt = 0;
  authResponseAt = 0;
  authRequestCount = 0;
  authVerified = false;
  // Never treat previous-connection FF01 data as fresh after a reconnect.
  ff01RecoveryAttempted = false;
  // Never expose old setpoints after BLE reconnect before new FF02 reports.
  portENTER_CRITICAL(&dataMux);
  haveTelemetry = false;
  lastTelemetryMs = 0;
  memset(probes, 0, sizeof(probes));
  lastRawLen = 0;
  memset(targets, 0, sizeof(targets));
  memset(probeCookDone, 0, sizeof(probeCookDone));
  memset(probeCookDoneKnown, 0, sizeof(probeCookDoneKnown));
  memset(probeBatteryAlarm, 0, sizeof(probeBatteryAlarm));
  memset(probeBatteryKnown, 0, sizeof(probeBatteryKnown));
  batteryAlarmKnown = false;
  batteryAlarm = false;
  memset(ff03StatusWords, 0, sizeof(ff03StatusWords));
  memset(ff03LastRaw, 0, sizeof(ff03LastRaw));
  ff03LastRawLen = 0;
  ff03DecodeName = "none";
  lastFF03Length = 0;
  lastBatteryReportMs = 0;
  unknownFF03Reports = 0;
  portEXIT_CRITICAL(&dataMux);
  reportedTemperatureUnit = '?';
  authResponseSent = false;
  authInitFallback = false;
  authReadyAt = 0;
  authReadIndex = 0;
  authAckReadIndex = 0;
  authAckReadAt = 0;
  ff02ValidReadFrames = 0;
  ff02NotificationCount = 0;
  ff02LastNotificationMs = 0;
  for (auto& c : chars) c = nullptr;
  Serial.println("[BLE] Verbinde INKBIRD...");
  if (bleClient) {
    NimBLEDevice::deleteClient(bleClient);
    bleClient = nullptr;
  }
  bleClient = NimBLEDevice::createClient();
  if (!bleClient) { failedConnectCount++; bleConnecting = false; return false; }
  bleClient->setClientCallbacks(&callbacks, false);
  // v3.6.0: KEINE eigenen Connection-Parameter vorgeben.
  // NimBLE-Defaults verwenden und Parameterupdates des Peripherals zulassen.
  // Kontrollierter Test: Android verwendet BALANCED, nicht unsere 50ms/0 Vorgabe.
  if (INKBIRD_DIAGNOSTICS) Serial.println("[DIAG] Default Connection-Parameter (kein setConnectionParams)");
  NimBLEAddress address(INKBIRD_MAC, BLE_ADDR_PUBLIC);
  // Disable the default automatic MTU exchange so this connection starts
  // exactly one explicit exchange at a known point (NimBLE-Arduino 2.x).
  if (!bleClient->connect(address, true, false, false)) {
    Serial.println("[BLE] Verbindungsaufbau fehlgeschlagen");
    failedConnectCount++;
    bleConnecting = false;
    return false;
  }
  // exchangeMTU() is NON-BLOCKING. A true return value means "request accepted",
  // not "MTU negotiated". Wait for the asynchronous onMTUChange event/getMTU.
  // The tested Bluedroid v3 configuration negotiated ATT MTU=517 before 01 FB.
  Serial.printf("[MTU] Connected, ATT MTU initially=%u; requesting 517 now\n",
                (unsigned)bleClient->getMTU());
  bool mtuRequested = bleClient->exchangeMTU();
  Serial.printf("[MTU] exchangeMTU() request accepted=%d (asynchronous)\n", mtuRequested);
  if (!mtuRequested) {
    Serial.println("[MTU] ERROR: Could not initiate exchange");
    bleClient->disconnect(); failedConnectCount++; bleConnecting = false; return false;
  }
  uint32_t mtuWaitStarted = millis();
  while (bleClient->isConnected() && bleClient->getMTU() == 23 &&
         (uint32_t)(millis() - mtuWaitStarted) < 8000) {
    delay(20); // Let the BLE host task process ATT Exchange MTU Response.
  }
  const uint16_t negotiatedMtu = bleClient->isConnected() ? bleClient->getMTU() : 0;
  Serial.printf("[MTU] Exchange result: negotiated=%u, elapsed=%lu ms, connected=%d\n",
                (unsigned)negotiatedMtu,
                (unsigned long)(millis() - mtuWaitStarted), bleClient->isConnected());
  if (negotiatedMtu != 517) {
    Serial.println("[MTU] FATAL: effective ATT MTU != 517; authentication not started");
    if (bleClient->isConnected()) bleClient->disconnect();
    failedConnectCount++; bleConnecting = false; return false;
  }
  Serial.println("[MTU] SUCCESS: ATT MTU 517 negotiated before GATT discovery and FF02 auth");
  NimBLERemoteService* svc = bleClient->getService(NimBLEUUID(SERVICE_UUID));
  if (!svc) {
    Serial.println("[BLE] Service FF00 fehlt");
    bleClient->disconnect();
    failedConnectCount++; bleConnecting = false; return false;
  }
  for (int i = 0; i < 6; ++i) chars[i] = svc->getCharacteristic(NimBLEUUID(CHAR_UUIDS[i]));
  controlChar = chars[1];
  if (INKBIRD_DIAGNOSTICS) {
    Serial.println("[GATT] Discovered characteristic value handles:");
    for (int i = 0; i < 6; ++i) {
      if (chars[i]) Serial.printf("[GATT] FF%02X value_handle=0x%04X notify=%d writeNR=%d\n", i+1, (unsigned)chars[i]->getHandle(), chars[i]->canNotify(), chars[i]->canWriteNoResponse());
    }
  }
  if (!chars[0] || !controlChar) {
    Serial.println("[BLE] FF01 oder FF02 fehlt");
    bleClient->disconnect();
    failedConnectCount++; bleConnecting = false; return false;
  }
  if (INKBIRD_DIAGNOSTICS) logLink("nach Service Discovery");
  // MTU 517 was negotiated before service discovery (Windows/working Bluedroid order).
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[MTU] Vor Challenge: ATT MTU=%u\n", (unsigned)bleClient->getMTU());
  // Match nRF Connect: subscribe FF02 first, verify CCCD 01 00,
  // then subscribe telemetry/other characteristics. Never send 01 FB before verification.
  Serial.println("[CCCD] Subscribe FF02 FIRST; verify 0x2902 before challenge");
  bool ff02Subscribed = controlChar->subscribe(true, onControl);
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[CCCD] FF02 subscribe() returned %s\n", ff02Subscribed ? "OK" : "FAIL");
  if (!ff02Subscribed || !verifyFF02CCCD("after subscribe")) {
    Serial.println("[CCCD] FF02 notification subscription NOT CONFIRMED - abort session");
    bleClient->disconnect(); failedConnectCount++; bleConnecting=false; return false;
  }
  Serial.println("[CCCD] FF02 subscription CONFIRMED (01 00)");
  // Leave FF01/FF03-FF06 unsubscribed until the challenge phase finishes.
  // The original app may perform further operations; this isolates nRF Connect order.
  additionalSubscriptionsDone = false;
  Serial.println("[BLE] FF02 bereit, MTU 517 ausgehandelt");
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[BLE] FF02 Properties: WRITE=%d WRITE_NR=%d NOTIFY=%d READ=%d\n",
                controlChar->canWrite(), controlChar->canWriteNoResponse(),
                controlChar->canNotify(), controlChar->canRead());
  connectCount++;
  authStage = AUTH_SETTLE;
  authStepMs = millis();
  Serial.println("[AUTH] FF02 CCCD bestaetigt; Challenge-Request folgt in 5 s");
  bleConnecting = false;
  return true;
}

// The APK assembles one 45-byte message: 8-byte time frame + 37-byte queries.
// Time encoding inferred from INT14Tools.timeService() analysis; still requires device verification.
const uint8_t INIT_TAIL[] = {
  0x01,0x04, 0x02,0x02,0x01, 0x02,0x02,0x02, 0x02,0x02,0x04,
  0x02,0x02,0x08, 0x01,0x06, 0x02,0x0A,0xFF, 0x01,0x0C,
  0x01,0x15, 0x01,0x24, 0x02,0x26,0x01, 0x02,0x26,0x02,
  0x02,0x26,0x04, 0x02,0x26,0x08
};
static_assert(sizeof(INIT_TAIL)==37, "Expected 37 static init bytes");
uint32_t initCompletedAt = 0;

bool sendCombinedInit() {
  if (bleClient->getMTU() < 48) {
    Serial.printf("[INIT] NICHT GESENDET: MTU=%u, benoetigt >=48 fuer 45-Byte WRITE_NR\n", (unsigned)bleClient->getMTU());
    return false;
  }
  struct timeval tv;
  gettimeofday(&tv, nullptr);
  if (tv.tv_sec < 1700000000) {
    Serial.println("[INIT] NICHT GESENDET: NTP-Zeit ungueltig");
    return false;
  }
  uint32_t secs = (uint32_t)tv.tv_sec;
  uint16_t millisPart = (uint16_t)(tv.tv_usec / 1000);
  uint8_t payload[45] = {0x07, 0x19};
  for (int i=0;i<4;i++) payload[2+i] = (uint8_t)(secs >> (8*i));
  payload[6] = (uint8_t)millisPart;
  payload[7] = (uint8_t)(millisPart >> 8);
  memcpy(payload+8, INIT_TAIL, sizeof(INIT_TAIL));
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[INIT] Unix=%lu ms=%u, combined 45 bytes, MTU=%u\n",
      (unsigned long)secs, (unsigned)millisPart, (unsigned)bleClient->getMTU());
  return writeControl(payload, sizeof(payload));
}

void readDiagnosticCharacteristic(int index) {
  if (!connected() || !chars[index] || !chars[index]->canRead()) {
    Serial.printf("[READ] FF%02X nicht lesbar\n", index+1);
    return;
  }
  // NimBLE readValue may return a large fixed-size value; print a bounded prefix.
  NimBLEAttValue v = chars[index]->readValue();
  if (index == 2 && v.size() > 0) parseBatteryStatusFF03(v.data(), v.size());
  const size_t shown = v.size() > 64 ? 64 : v.size();
  if (INKBIRD_DIAGNOSTICS) {
    Serial.printf("[READ] FF%02X len=%u prefix(%u)=%s%s\n", index+1,
                  (unsigned)v.size(), (unsigned)shown,
                  hexBytes(v.data(), shown).c_str(), v.size()>shown ? " ..." : "");
  }
}

// Complete normal gateway setup only after the FF02 challenge test.
// This is deliberately NOT run during the first authentication attempt.
bool completeNormalSetup() {
  if (additionalSubscriptionsDone) return true;
  if (!connected() || !controlChar) return false;
  Serial.println("[INIT] Authentifizierung bestaetigt; FF01/FF03-FF06 werden abonniert (MTU bleibt 517)");
  bool exchanged = (bleClient->getMTU() == 517);
  if (INKBIRD_DIAGNOSTICS) Serial.printf("[MTU] already negotiated pre-auth=%d negotiated=%u\n", exchanged, (unsigned)bleClient->getMTU());
  if (bleClient->getMTU() < 48) {
    Serial.println("[V4] MTU <48; kombinierte Init nicht moeglich");
    return false;
  }
  for (int i=0; i<6; ++i) {
    if (i == 1 || !chars[i] || !chars[i]->canNotify()) continue;
    bool ok = chars[i]->subscribe(true, i==0 ? onTelemetry : onOther);
    Serial.printf("[BLE] FF%02X Notifications %s\n", i+1, ok ? "aktiv" : "FEHLER");
  }
  if (!verifyFF02CCCD("after delayed subscriptions")) {
    Serial.println("[V4] FF02 CCCD nach spaeter Subscription ungueltig");
    return false;
  }
  additionalSubscriptionsDone = true;
  if (INKBIRD_DIAGNOSTICS) logLink("nach Subscriptions");
  return true;
}

// FF01 notification watchdog: reconnect only if the temperature channel stops.
// The rest of BLE authentication (MTU 517 / FF02 challenge) is unchanged.
void monitorFF01() {
  if (!connected() || !authVerified || authStage != AUTH_READY || !additionalSubscriptionsDone) return;
  uint32_t now = millis();
  uint32_t stamp = 0;
  bool available = false;
  portENTER_CRITICAL(&dataMux);
  stamp = lastTelemetryMs;
  available = haveTelemetry;
  portEXIT_CRITICAL(&dataMux);
  // Before first telemetry use the time when full initialization finished.
  uint32_t age = (uint32_t)(now - (available ? stamp : initCompletedAt));
  if (age < FF01_RESUBSCRIBE_AFTER_MS) {
    // The first successfully received notification restores the normal state.
    if (available) ff01RecoveryAttempted = false;
    return;
  }
  if (!ff01RecoveryAttempted) {
    ff01RecoveryAttempted = true;
    ++ff01RecoveryAttempts;
    Serial.printf("[FF01] Keine Temperaturdaten seit %lu ms; erneuere Subscription (Versuch %lu)\n",
                  (unsigned long)age, (unsigned long)ff01RecoveryAttempts);
    if (chars[0] && chars[0]->canNotify()) {
      bool ok = chars[0]->subscribe(true, onTelemetry);
      Serial.printf("[FF01] subscribe() = %s\n", ok ? "OK" : "FEHLER");
    }
  }
  if (age >= FF01_RECONNECT_AFTER_MS) {
    ++ff01WatchdogReconnects;
    Serial.printf("[FF01] Seit %lu ms keine neuen Temperaturdaten; kontrollierter BLE-Reconnect #%lu\n",
                  (unsigned long)age, (unsigned long)ff01WatchdogReconnects);
    // The next connection redoes MTU 517, challenge/ACK and subscriptions.
    bleClient->disconnect();
  }
}

void handleAuth() {
  if (!connected() || !controlChar) return;
  uint32_t now = millis();
  if (authStage == AUTH_INIT_COMMANDS || authStage == AUTH_READ_STATUS || authStage == AUTH_READY) {
    // Notifications are the primary path, as verified with nRF Connect.
    // Do not inject active reads during the challenge exchange.
  }
  if (authStage == AUTH_SETTLE) {
    if (now - authStepMs < 5000) return; // same 5-second delay as successful Bluedroid v3
    const uint8_t request[] = {0x01,0xFB};
    Serial.printf("[AUTH] Phase 1: 01 FB after verified CCCD; t=%lu ms\n", (unsigned long)millis());
    if (!writeControl(request, sizeof(request))) { authStage=AUTH_FAILED; return; }
    authRequestCount = 1;
    authRequestAt = millis();
    authReadIndex = 0;
    authStage = AUTH_INIT_COMMANDS;
  }
  if (authStage == AUTH_INIT_COMMANDS) {
    bool haveChallenge = false;
    uint8_t challengeCopy[6];
    portENTER_CRITICAL(&challengeMux);
    if (authChallengePending) {
      memcpy(challengeCopy, authChallenge, 6);
      authChallengePending = false;
      haveChallenge = true;
    }
    portEXIT_CRITICAL(&challengeMux);
    if (haveChallenge && !authResponseSent) {
      uint8_t reply[9];
      buildAuthResponse(challengeCopy, reply);
      Serial.printf("[AUTH] Phase 2: 08 FC Antwort: %s\n", hexBytes(reply, sizeof(reply)).c_str());
      if (!writeControl(reply, sizeof(reply))) { authStage=AUTH_FAILED; return; }
      authResponseSent = true;
      authResponseAt = millis();
      authAckReadIndex = 0;
    }
    if (authAckSeen && !authVerified) {
      authVerified = true;
      Serial.println("[AUTH] ERFOLG: 02 FC 00; Initialisierung startet");
    }
    if (authAckRejected) {
      Serial.println("[AUTH] Antwort vom Thermometer abgelehnt");
      authStage = AUTH_FAILED;
      return;
    }
    // Fallback preserves the working temperature telemetry and provides a
    // second, single challenge trial after the combined init (diagnostic).
    if (INKBIRD_AUTH_FALLBACK && !authVerified && !authInitFallback && now - authRequestAt >= 3500) {
      authInitFallback = true;
      Serial.printf("[AUTH] Noch keine ACK/Challenge nach %lu ms; sende kombinierte Init\n", (unsigned long)(now-authRequestAt));
    }
    if (!authVerified && authRequestAt && (uint32_t)(now - authRequestAt) > 12000) {
      Serial.println("[AUTH] Timeout: keine gueltige Bestaetigung, neuer Verbindungsversuch");
      authStage = AUTH_FAILED;
      bleClient->disconnect();
      return;
    }
    if (authVerified || (INKBIRD_AUTH_FALLBACK && authInitFallback)) {
      if (!combinedInitSent) {
        if (!completeNormalSetup()) { authStage=AUTH_FAILED; return; }
        combinedInitSent = true;
        if (!sendCombinedInit()) { authStage=AUTH_FAILED; return; }
        authStepMs = millis();
      }
      authStage = AUTH_READ_STATUS;
    }
  }
  if (authStage == AUTH_READ_STATUS) {
    if (now - authStepMs < 500) return;
    if (!statusReadDone) {
      statusReadDone = true;
      readDiagnosticCharacteristic(2);
      if (INKBIRD_DIAGNOSTICS) readDiagnosticCharacteristic(3);
      if (!authVerified && authRequestCount == 1 && !authResponseSent) {
        const uint8_t request[] = {0x01,0xFB};
        Serial.println("[AUTH] Phase 3: zweite 01 FB Anfrage nach Init (einmalig)");
        writeControl(request, sizeof(request));
        authRequestCount = 2;
        authRequestAt = millis();
        authReadIndex = 0;
      }
      authReadyAt = millis();
      Serial.println("[AUTH] Beobachte FF02 ACK und Challenge");
    }
    if (authAckSeen && !authVerified) {
      authVerified = true;
      Serial.println("[AUTH] ERFOLG: 02 FC 00 nach Init");
    }
    if (authChallengePending && !authResponseSent) {
      uint8_t challengeCopy[6];
      portENTER_CRITICAL(&challengeMux);
      memcpy(challengeCopy, authChallenge, 6);
      authChallengePending = false;
      portEXIT_CRITICAL(&challengeMux);
      uint8_t reply[9];
      buildAuthResponse(challengeCopy, reply);
      Serial.printf("[AUTH] 08 FC Antwort nach Init: %s\n", hexBytes(reply, sizeof(reply)).c_str());
      if (writeControl(reply, sizeof(reply))) {
        authResponseSent = true;
        authResponseAt = millis();
        authAckReadIndex = 0;
      }
    }
    if (now - authReadyAt > 4000) {
      authStage = AUTH_READY;
      initCompletedAt = millis();
      lastAppReadMs = initCompletedAt;
      Serial.printf("[AUTH] Status: verified=%d challenge_received=%d response_sent=%d ff02_notifications=%lu\n",
                    authVerified, authResponseSent, authResponseSent, (unsigned long)ff02NotificationCount);
    }
  }
  // Handle an ACK arriving via active READ after the diagnostic stage.
  if (authStage == AUTH_READY && authAckSeen && !authVerified) {
    authVerified = true;
    Serial.println("[AUTH] ERFOLG: 02 FC 00 (READ/NOTIFY) nach Init");
  }
  if (authStage == AUTH_READY && authChallengePending && !authResponseSent) {
    uint8_t challengeCopy[6];
    portENTER_CRITICAL(&challengeMux);
    memcpy(challengeCopy, authChallenge, 6);
    authChallengePending = false;
    portEXIT_CRITICAL(&challengeMux);
    uint8_t reply[9];
    buildAuthResponse(challengeCopy, reply);
    Serial.printf("[AUTH] Spaete Challenge: 08 FC %s\n", hexBytes(reply, sizeof(reply)).c_str());
    if (writeControl(reply, sizeof(reply))) {
      authResponseSent = true;
      authResponseAt = millis();
      authAckReadIndex = 0;
    }
  }
}

void setupHttp() {
  server.on("/health", HTTP_GET, []() {
    String s = "{\"device\":\"INT-14-BW\",\"wifi_connected\":";
    s += WiFi.status() == WL_CONNECTED ? "true" : "false";
    s += ",\"ble_connected\":";
    s += connected() ? "true" : "false";
    s += ",\"authenticated\":";
    s += authVerified ? "true" : "false";
    s += ",\"ip\":\"" + WiFi.localIP().toString() + "\"}";
    server.send(200, "application/json", s);
  });
  server.on("/api/ble-status", HTTP_GET, []() {
    String s = "{\"connected\":";
    s += connected() ? "true" : "false";
    s += ",\"auth_state\":\"" + String(authName(authStage)) + "\"";
    s += ",\"successful_connections\":" + String(connectCount);
    s += ",\"failed_connections\":" + String(failedConnectCount);
    s += ",\"disconnect_count\":" + String(disconnectCount);
    s += ",\"last_disconnect_reason\":" + String(disconnectReason);
    s += ",\"authenticated\":" + String(authVerified ? "true" : "false");
    s += ",\"auth_requests\":" + String(authRequestCount);
    s += ",\"auth_response_sent\":" + String(authResponseSent ? "true" : "false");
    s += ",\"ff02_notify_count\":" + String(ff02NotificationCount);
    s += ",\"ff02_last_notify_ms\":" + String(ff02LastNotificationMs);
    s += ",\"challenge_trial_number\":" + String(challengeTrialNumber);
    s += ",\"challenge_trial_mode\":" + String(activeChallengeTrial);
    s += ",\"challenge_delay_ms\":" + String(activeChallengeDelayMs);
    s += ",\"ff02_write_count\":" + String(ff02WriteCount);
    s += ",\"ff02_write_failures\":" + String(ff02WriteFailures);
    s += ",\"ff02_read_count\":" + String(ff02ReadCount);
    s += ",\"ff02_valid_read_frames\":" + String(ff02ValidReadFrames);
    s += ",\"ff02_empty_reads\":" + String(ff02ReadErrors);
    uint32_t telemetryStamp;
    bool telemetrySeen;
    portENTER_CRITICAL(&dataMux);
    telemetryStamp = lastTelemetryMs;
    telemetrySeen = haveTelemetry;
    portEXIT_CRITICAL(&dataMux);
    s += ",\"telemetry_age_ms\":";
    if (telemetrySeen) s += String((uint32_t)(millis() - telemetryStamp));
    else s += "null";
    s += ",\"telemetry_timeout_ms\":" + String(DATA_TIMEOUT_MS);
    s += ",\"ff01_notify_count\":" + String(ff01NotifyCount);
    s += ",\"ff01_recovery_attempts\":" + String(ff01RecoveryAttempts);
    s += ",\"ff01_watchdog_reconnects\":" + String(ff01WatchdogReconnects);
    s += ",\"ff01_resubscribe_after_ms\":" + String(FF01_RESUBSCRIBE_AFTER_MS);
    s += ",\"ff01_reconnect_after_ms\":" + String(FF01_RECONNECT_AFTER_MS);
    s += ",\"connection_uptime_ms\":";
    s += connected() ? String(millis() - connectedAt) : "null";
    s += "}";
    server.send(200, "application/json", s);
  });
  // Simple plan44/P44Script-friendly response. Only fresh, authenticated
  // measurements are exported. 503 means: do not publish stale temperatures.
  server.on("/api/plan44", HTTP_GET, []() {
    Probe copy[4]; TargetTemperature targetCopy[4]; uint32_t stamp; bool available;
    bool batteryKnownCopy, batteryAlarmCopy;
    bool cookDoneCopy[4], cookDoneKnownCopy[4];
    bool probeBatteryCopy[4], probeBatteryKnownCopy[4];
    size_t ff03LenCopy; uint32_t batteryMsCopy;
    portENTER_CRITICAL(&dataMux);
    memcpy(copy, probes, sizeof(copy));
    memcpy(targetCopy, targets, sizeof(targetCopy));
    stamp = lastTelemetryMs; available = haveTelemetry;
    for (int i=0; i<4; ++i) {
      cookDoneCopy[i] = probeCookDone[i];
      cookDoneKnownCopy[i] = probeCookDoneKnown[i];
      probeBatteryCopy[i] = probeBatteryAlarm[i];
      probeBatteryKnownCopy[i] = probeBatteryKnown[i];
    }
    batteryKnownCopy = batteryAlarmKnown;
    batteryAlarmCopy = batteryAlarm;
    ff03LenCopy = lastFF03Length;
    batteryMsCopy = lastBatteryReportMs;
    portEXIT_CRITICAL(&dataMux);
    const bool fresh = connected() && authVerified && available &&
                       ((uint32_t)(millis() - stamp) < DATA_TIMEOUT_MS);
    if (!fresh) {
      // Provide precise reason instead of conflating BLE auth and telemetry age.
      const bool linkOk = connected();
      const bool sessionOk = authVerified;
      const uint32_t ageMs = available ? (uint32_t)(millis() - stamp) : 0;
      const char* reason = "telemetry_stale";
      if (!linkOk) reason = "ble_disconnected";
      else if (!sessionOk) reason = "not_authenticated";
      else if (!available) reason = "no_temperature_data";
      String errorJson = "{\"online\":false,\"error\":\"";
      errorJson += reason;
      errorJson += "\",\"connected\":";
      errorJson += linkOk ? "true" : "false";
      errorJson += ",\"authenticated\":";
      errorJson += sessionOk ? "true" : "false";
      errorJson += ",\"have_telemetry\":";
      errorJson += available ? "true" : "false";
      errorJson += ",\"age_ms\":";
      errorJson += available ? String(ageMs) : String("null");
      errorJson += ",\"timeout_ms\":" + String(DATA_TIMEOUT_MS) + "}";
      server.send(503, "application/json", errorJson);
      return;
    }
    String json = "{\"online\":true,\"authenticated\":true,\"age_ms\":" + String((uint32_t)(millis()-stamp));
    json += ",\"target_unit\":\"" + String(reportedTemperatureUnit) + "\"";
    json += ",\"target_encoding\":\"raw_fahrenheit_div_10_to_celsius_verified_2_points\"";
    // Unknown is null, never OK. No guessed battery threshold.
    json += ",\"battery_alarm\":";
    if (batteryKnownCopy && batteryMsCopy != 0 && (uint32_t)(millis()-batteryMsCopy) < 120000) {
      if (batteryAlarmCopy) json += "true";
      else json += "false";
    } else {
      json += "null";
    }
    json += ",\"battery_alarm_source\":\"FF03_11byte_bit14_experimental\"";
    json += ",\"battery_station_alarm\":null"; // Station battery protocol not decoded
    json += ",\"battery_ff03_len\":" + String((unsigned)ff03LenCopy);
    json += ",\"ff03_decode\":\"" + String(ff03LenCopy == 11 ? "le16_bitfield_experimental" : (ff03LenCopy >= 64 && ff03LenCopy <= 128 ? "legacy_byte_array" : "unsupported")) + "\"";
    for (int i = 0; i < 4; ++i) {
      json += ",\"probe" + String(i+1) + "_active\":" + String(copy[i].active ? "true" : "false");
      json += ",\"probe" + String(i+1) + "_core\":" + (copy[i].active ? String(copy[i].core, 1) : String("null"));
      json += ",\"probe" + String(i+1) + "_ambient\":" + (copy[i].active ? String(copy[i].ambient, 1) : String("null"));
      // Target setpoint: independent of current probe connection state.
      json += ",\"probe" + String(i+1) + "_target\":" +
              (targetCopy[i].valid ? String(targetCopy[i].value, 1) : String("null"));
      json += ",\"probe" + String(i+1) + "_target_raw\":" +
              (targetCopy[i].valid ? String(targetCopy[i].raw) : String("null"));
      // Per-probe battery alarm from FF03. Unknown/stale means null, never assume OK.
      json += ",\"probe" + String(i+1) + "_battery_alarm\":";
      if (probeBatteryKnownCopy[i] && batteryMsCopy != 0 &&
          (uint32_t)(millis()-batteryMsCopy) < FF03_STATUS_TIMEOUT_MS) {
        json += probeBatteryCopy[i] ? "true" : "false";
      } else {
        json += "null";
      }
      // Unknown on short, missing or stale FF03; NEVER infer cook done from core >= target.
      json += ",\"probe" + String(i+1) + "_cook_done\":";
      if (cookDoneKnownCopy[i] && batteryMsCopy != 0 &&
          (uint32_t)(millis()-batteryMsCopy) < 120000) {
        json += cookDoneCopy[i] ? "true" : "false";
      } else {
        json += "null";
      }
    }
    json += "}";
    server.send(200, "application/json", json);
  });
  server.on("/api/battery-debug", HTTP_GET, []() {
    bool batteryKnownCopy, batteryAlarmCopy, probeBattery[4], probeBatteryValid[4];
    bool cookFlags[4], cookKnown[4];
    uint16_t words[4];
    uint8_t raw[16];
    size_t length, rawLength;
    uint32_t stamp, shortReports;
    portENTER_CRITICAL(&dataMux);
    batteryKnownCopy = batteryAlarmKnown;
    batteryAlarmCopy = batteryAlarm;
    length = lastFF03Length;
    rawLength = ff03LastRawLen;
    memcpy(raw, ff03LastRaw, rawLength);
    stamp = lastBatteryReportMs;
    shortReports = unknownFF03Reports;
    for (int i=0; i<4; ++i) {
      words[i] = ff03StatusWords[i];
      probeBattery[i] = probeBatteryAlarm[i];
      probeBatteryValid[i] = probeBatteryKnown[i];
      cookFlags[i] = probeCookDone[i];
      cookKnown[i] = probeCookDoneKnown[i];
    }
    portEXIT_CRITICAL(&dataMux);
    bool fresh = stamp != 0 && ((uint32_t)(millis()-stamp) < FF03_STATUS_TIMEOUT_MS);
    String s = "{\"ff03_len\":" + String((unsigned)length);
    s += ",\"ff03_raw\":\"" + hexBytes(raw,rawLength) + "\"";
    s += ",\"ff03_encoding\":\"" + String(length == 11 ? "le16_bitfield_experimental" : (length >= 64 && length <= 128 ? "legacy_byte_array" : "unsupported")) + "\"";
    s += ",\"ff03_age_ms\":";
    if (stamp != 0) s += String((uint32_t)(millis()-stamp)); else s += "null";
    s += ",\"ff03_fresh\":" + String(fresh ? "true" : "false");
    s += ",\"unknown_ff03_reports\":" + String((unsigned long)shortReports);
    s += ",\"battery_known\":" + String(batteryKnownCopy && fresh ? "true" : "false");
    s += ",\"battery_alarm\":";
    if (batteryKnownCopy && fresh) s += batteryAlarmCopy ? "true" : "false";
    else s += "null";
    s += ",\"status_words_hex\":[";
    for (int i=0; i<4; ++i) {
      if (i) s += ',';
      char wordString[7];
      snprintf(wordString,sizeof(wordString),"0x%04X",words[i]);
      if (length == 11) s += String("\"") + wordString + "\"";
      else s += "null";
    }
    s += "],\"probe_battery_alarm\":[";
    for (int i=0; i<4; ++i) {
      if (i) s += ',';
      if (probeBatteryValid[i] && fresh) s += probeBattery[i] ? "true" : "false";
      else s += "null";
    }
    s += "],\"cook_done\":[";
    for (int i=0; i<4; ++i) {
      if (i) s += ',';
      if (cookKnown[i] && fresh) s += cookFlags[i] ? "true" : "false";
      else s += "null";
    }
    s += "],\"bitfield_warning\":\"11-byte bit positions are unverified; verify against real cook alarm\"}";
    server.send(200, "application/json", s);
  });
  server.on("/api/debug", HTTP_GET, []() {
    uint8_t raw[64]; size_t len; uint32_t stamp; bool available;
    portENTER_CRITICAL(&dataMux);
    len = lastRawLen; memcpy(raw, lastRaw, len);
    stamp = lastTelemetryMs; available = haveTelemetry;
    portEXIT_CRITICAL(&dataMux);
    String s = "{\"raw_ff01\":\"" + hexBytes(raw, len) + "\"";
    s += ",\"length\":" + String(len);
    s += ",\"age_ms\":";
    s += available ? String(millis() - stamp) : "null";
    s += ",\"auth_state\":\"" + String(authName(authStage)) + "\"}";
    server.send(200, "application/json", s);
  });
  server.on("/api/temperatures", HTTP_GET, []() {
    Probe copy[4]; uint32_t stamp; bool available;
    portENTER_CRITICAL(&dataMux);
    memcpy(copy, probes, sizeof(copy));
    stamp = lastTelemetryMs; available = haveTelemetry;
    portEXIT_CRITICAL(&dataMux);
    bool fresh = available && connected() && authVerified && (millis() - stamp < DATA_TIMEOUT_MS);
    if (!fresh) {
      server.send(503, "application/json", "{\"error\":\"no_fresh_ble_data\"}");
      return;
    }
    String s = "{\"device\":\"INT-14-BW\",\"connected\":true,\"fresh\":true,\"age_ms\":";
    s += String(millis() - stamp) + ",\"unit\":\"celsius\",\"probes\":[";
    for (int i = 0; i < 4; ++i) {
      if (i) s += ',';
      s += "{\"id\":" + String(i+1) + ",\"active\":";
      s += copy[i].active ? "true" : "false";
      s += ",\"core\":";
      s += copy[i].active ? String(copy[i].core, 1) : "null";
      s += ",\"ambient\":";
      s += copy[i].active ? String(copy[i].ambient, 1) : "null";
      s += '}';
    }
    s += "]}";
    server.send(200, "application/json", s);
  });
  server.begin();
  Serial.println("[HTTP] REST-Server gestartet");
}

void setup() {
  Serial.begin(115200);
  uint32_t start = millis();
  while (!Serial && millis() - start < 10000) delay(10);
  delay(300);
  Serial.println("\n====================================\n INKBIRD INT-14-BW Gateway v4.6.4 NimBLE FF03 PER-PROBE BATTERY\n Seeed XIAO ESP32-S3\n====================================");
  for (auto& p : probes) { p.core = NAN; p.ambient = NAN; p.active = false; }
  WiFi.mode(WIFI_STA);
  WiFi.setSleep(false);
  WiFi.begin(WIFI_SSID, WIFI_PASS);
  Serial.print("[WIFI] Verbinde");
  start = millis();
  while (WiFi.status() != WL_CONNECTED && millis() - start < 20000) {
    Serial.print('.'); delay(500);
  }
  Serial.println();
  if (WiFi.status() == WL_CONNECTED) {
    Serial.printf("[WIFI] IP-Adresse: %s / RSSI: %d dBm\n", WiFi.localIP().toString().c_str(), WiFi.RSSI());
    configTime(0, 0, "pool.ntp.org", "time.cloudflare.com", "time.google.com");
    start = millis();
    while (time(nullptr) < 1700000000 && millis() - start < 10000) delay(200);
    Serial.println(time(nullptr) >= 1700000000 ? "[NTP] Uhrzeit synchronisiert" : "[NTP] Keine gueltige Uhrzeit");
  } else Serial.println("[WIFI] Verbindung fehlgeschlagen");
  Serial.printf("[AUTH] CRC reference vector: %s\n", authSelfTest() ? "PASS" : "FAIL");
  Serial.println("[AUTH] MTU517 -> FF02 CCCD -> wait 5s -> 01 FB -> 08 FC -> 02 FC 00");
  NimBLEDevice::init("InkbirdGateway");
  // MTU 517 required: exchangeMTU() immediately after connect, BEFORE FF02 auth.
  bool mtuSet = NimBLEDevice::setMTU(517);
  Serial.printf("[BLE] Requested ATT MTU=517, setMTU=%s\n", mtuSet ? "OK" : "FEHLER");
  setupHttp();
  Serial.println("[SYSTEM] Gateway gestartet");
}

void loop() {
  server.handleClient();
  uint32_t now = millis();
  if (disconnectPending) {
    disconnectPending = false;
    Serial.printf("[BLE] DISCONNECTED Grund: %d (0x%02X), Dauer: %lu s, Gesamt: %lu\n",
                  disconnectReason, (unsigned)(disconnectReason & 0xff),
                  (unsigned long)((disconnectAt - connectedAt) / 1000),
                  (unsigned long)disconnectCount);
    Serial.printf("[APP-READ] Abbruch nach %lu Lesezyklen\n", (unsigned long)appReadCycles);
  }
  if (WiFi.status() != WL_CONNECTED && now - lastWifiAttempt >= WIFI_RETRY_MS) {
    lastWifiAttempt = now;
    Serial.println("[WIFI] Reconnect...");
    WiFi.reconnect();
    if (time(nullptr) < 1700000000) configTime(0, 0, "pool.ntp.org", "time.cloudflare.com", "time.google.com");
  }
  if (!connected() && !bleConnecting && now - lastBleAttempt >= BLE_RETRY_MS) {
    if (time(nullptr) >= 1700000000) {
      connectInkbird();
    } else {
      lastBleAttempt = now;
      Serial.println("[AUTH] Warte auf gueltige Uhrzeit vor BLE-Authentifizierung");
    }
  }
  if (connected()) {
    handleAuth();
    monitorFF01();
    // Original-App: INT14HomePresenter.handleMessage() liest FF03 und FF04
    // wiederholt. Der genaue Zeitabstand ist im DEX noch nicht verifiziert;
    // 5 s ist ein ausdrücklich diagnostisch gewähltes Intervall.
    // Keine unbestätigten Keepalive- oder Pairing-Befehle senden.
    if (authStage == AUTH_READY && millis() - lastAppReadMs >= APP_READ_INTERVAL_MS) {
      lastAppReadMs = millis();
      ++appReadCycles;
      // FF03 status GATT read every 60 s; read FF04 bulk only in debug mode.
      if (INKBIRD_DIAGNOSTICS) {
        Serial.printf("[APP-READ] cycle=%lu uptime=%lu ms FF03\n",
                      (unsigned long)appReadCycles,
                      (unsigned long)(millis() - connectedAt));
      }
      readDiagnosticCharacteristic(2);
      if (INKBIRD_PERIODIC_GATT_READS && connected()) readDiagnosticCharacteristic(3);
    }
    if (INKBIRD_DIAGNOSTICS && millis() - lastLinkLogMs >= 5000) {
      lastLinkLogMs = millis();
      logLink("periodisch");
    }
  }
  delay(10);
}
