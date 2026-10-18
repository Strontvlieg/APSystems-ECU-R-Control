#!/usr/bin/env python3
"""APSystems ECU-R Control (Modbus TCP): monitoring and control application.

Windows: double-click this .pyw file; requires Python 3.10+ with Tkinter.
No additional packages required. Modbus writes require explicit confirmation.

All communication runs on ONE worker (sequentially; no parallel Modbus
requests). Monitoring uses FC03. Confirmed controls, including production
OFF/ON, use FC16. Unit ID, model, and serial number are verified before
every write and each written value is read back for confirmation.
An FC16 ACK alone does not prove actual AC limiting or shutdown.
On the tested ECU-R, production and limit commands affect the entire system,
regardless of the addressed Unit ID. This was confirmed in a field test.

The graph includes only complete scan cycles; missing data creates gaps.
Monitoring tries two contiguous FC03 blocks per inverter; unsupported ranges
fall back to four SunSpec-model-aligned blocks or smaller reads per Unit ID.
Totals update after each Unit ID using the latest available readings;
a failed read immediately removes that Unit ID from aggregate totals.
The first scan after manual Connect has no inter-inverter delays.
From the second scan onward, the selected interval (default 1 second) is
applied between inverters and between consecutive complete scans."""

from dataclasses import dataclass
from datetime import datetime
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
import math
import csv
import ipaddress
from collections import deque
from itertools import count
import queue
import socket
import struct
import sys
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, ttk


# At Connect, scan Modbus Unit IDs from 1 through the selected maximum.
# Only detected DS3 inverters are subsequently polled.
ECU_IP = "192.168.4.4"
ECU_PORT = 502
SCAN_START_ID = 1
SCAN_MAX_ID_DEFAULT = 20
SCAN_MAX_ID_ALLOWED = 247
TIMEOUT_SECONDS = 3.0  # Normal polling and confirmed write operations.
DISCOVERY_TIMEOUT_SECONDS = 0.1  # Initial Modbus ID discovery only (100 ms).

def parse_scan_max_id(text):
    """Highest Unit ID in the discovery scan; the starting ID is always 1."""
    try:
        maximum = int(str(text).strip())
    except ValueError as exc:
        raise ValueError('Enter a maximum Modbus ID between 1 and 247.') from exc
    if not SCAN_START_ID <= maximum <= SCAN_MAX_ID_ALLOWED:
        raise ValueError('The maximum Modbus ID must be between 1 and 247.')
    return maximum


# Nominal AC watt-equivalent for each manually selected inverter model.
# All detected inverters use the selected model rating for the display.
# The ECU-R receives a PERCENTAGE, potentially affecting undetected units.
INVERTER_RATINGS_W = {'DS3-L': 730, 'DS3': 880, 'DS3-H': 960}
DEFAULT_INVERTER_MODEL = 'DS3-L'

REG_SUNSPEC = 40000
REG_MODEL = 40020
REG_SERIAL = 40052
REG_INVERTER_MODEL = 40070
REG_AC_WATTS = 40084
REG_OPERATING_STATE = 40108     # SunSpec model 101, St: values 1 through 8.
REG_CONTROLS_MODEL = 40184
REG_CONN = 40188              # SunSpec Conn: 0=stop, 1=start, FC16 after confirmation.
REG_WMAXLIMPCT = 40189
REG_WMAXLIM_ENA = 40193
REG_WMAXLIMPCT_SF = 40207
REG_DC_MODEL = 40212            # Model 114, length 48 (APsystems Rev 3.3)
REG_DC_WATT_1 = 40246          # DCW1: IEEE754 float32 across two registers
REG_DC_WATT_2 = 40248          # DCW2: IEEE754 float32 across two registers

# All eight operating states documented in APsystems SunSpec Modbus Rev 3.3
# (register 40108). Unknown state codes remain visible.
OPERATING_STATES = {
    1: ("OFF", "Switched off"),
    2: ("SLEEPING", "Sleeping"),
    3: ("STARTING", "Starting up"),
    4: ("MPPT", "Normal MPPT operation"),
    5: ("THROTTLED", "Power curtailed"),
    6: ("SHUTTING_DOWN", "Shutting down"),
    7: ("FAULT", "Fault"),
    8: ("STANDBY", "Standby"),
}


def format_operating_state(code):
    """Show the operating mode without its numeric SunSpec code in the table."""
    if code == 0xFFFF:
        return "Unavailable (65535)"
    if code in OPERATING_STATES:
        name, _description = OPERATING_STATES[code]
        return name
    return f"Unknown (code {code})"


MODBUS_EXCEPTIONS = {
    1: "unsupported function",
    2: "register unavailable or not writable",
    3: "invalid register value",
    4: "device failure",
    6: "device busy",
}


class ModbusError(Exception):
    pass


class ModbusResponseError(ModbusError):
    """A valid exception response from the ECU, not a communication failure."""

    def __init__(self, function, code):
        self.function = function
        self.code = code
        super().__init__(
            f"Modbus exception {code}: {MODBUS_EXCEPTIONS.get(code, 'unknown')}"
        )


@dataclass(frozen=True)
class WriteVerification:
    acknowledged: bool
    reconnected: bool


def signed16(value):
    return value - 65536 if value >= 0x8000 else value


def words_to_text(words):
    raw = b"".join(struct.pack(">H", word) for word in words)
    return raw.split(b"\0", 1)[0].decode("ascii", "replace").strip()


def format_percent(percent):
    """Show integer percentages without decimals; preserve real fractions."""
    if percent == percent.to_integral_value():
        return str(int(percent))
    return format(percent.normalize(), "f")


def ieee754_float32(words):
    """SunSpec model 114: high word first, network byte order, IEEE754."""
    if len(words) != 2:
        raise ValueError("Exactly two Modbus registers are required for float32.")
    value = struct.unpack(">f", struct.pack(">HH", *words))[0]
    if not math.isfinite(value) or value < 0:
        return None
    return Decimal(str(value))


def percent_to_raw(text, scale_factor):
    """Convert an integer percentage to a raw uint16 register value."""
    try:
        percent = Decimal(str(text).strip().replace(",", "."))
    except InvalidOperation as exc:
        raise ValueError("Enter a valid whole percentage, such as 35.") from exc
    if not percent.is_finite() or percent < 0 or percent > 100:
        raise ValueError("The percentage must be between 0 and 100.")
    if percent != percent.to_integral_value():
        raise ValueError("Use a whole percentage without decimals.")
    raw_decimal = percent / (Decimal(10) ** scale_factor)
    if raw_decimal != raw_decimal.to_integral_value():
        raise ValueError("This percentage cannot be represented exactly in the register.")
    raw = int(raw_decimal)
    if not 0 <= raw <= 65534:
        raise ValueError("The calculated register value is invalid.")
    return raw, percent


class ModbusTCP:
    """Minimal Modbus TCP client supporting FC03 and FC16."""

    def __init__(self, unit_id, timeout_seconds=TIMEOUT_SECONDS):
        if not isinstance(unit_id, int) or not 1 <= unit_id <= 247:
            raise ValueError("Invalid Modbus Unit ID.")
        self.unit_id = unit_id
        if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
            raise ValueError("Modbus timeout must be positive and finite.")
        self.timeout_seconds = timeout_seconds
        self.sock = None
        self.transaction = 0

    def __enter__(self):
        self.reconnect()
        return self


    def close(self):
        sock, self.sock = self.sock, None
        if sock is not None:
            try:
                sock.close()
            except OSError:
                pass


    def reconnect(self):
        """Never reuse a potentially corrupted TCP stream after a connection failure."""
        self.close()
        sock = socket.create_connection((ECU_IP, ECU_PORT), self.timeout_seconds)
        try:
            sock.settimeout(self.timeout_seconds)
        except OSError:
            sock.close()
            raise
        self.sock = sock

    def __exit__(self, exc_type, exc, tb):
        self.close()

    def _receive_exact(self, count):
        data = bytearray()
        while len(data) < count:
            piece = self.sock.recv(count - len(data))
            if not piece:
                raise ModbusError("The ECU closed the TCP connection.")
            data.extend(piece)
        return bytes(data)

    def _request(self, function, payload):
        if not 1 <= self.unit_id <= 247:
            raise ModbusError("Invalid Unit ID; broadcasts are not allowed.")
        if self.sock is None:
            raise ModbusError("No TCP connection to the ECU.")
        self.transaction = (self.transaction % 65535) + 1
        transaction = self.transaction
        pdu = bytes([function]) + payload
        request = struct.pack(">HHHB", transaction, 0, len(pdu) + 1, self.unit_id) + pdu
        self.sock.sendall(request)
        header = self._receive_exact(7)
        tid, protocol, length, unit = struct.unpack(">HHHB", header)
        if not 2 <= length <= 254:
            raise ModbusError("Invalid Modbus TCP response length.")
        response = self._receive_exact(length - 1)
        if tid != transaction or protocol != 0 or unit != self.unit_id:
            raise ModbusError("Modbus response has the wrong Unit ID or transaction ID.")
        if response[0] == function | 0x80:
            if len(response) != 2:
                raise ModbusError("Malformed Modbus exception response.")
            code = response[1]
            raise ModbusResponseError(function, code)
        if response[0] != function:
            raise ModbusError("Unexpected Modbus function code in response.")
        return response

    def read(self, address, count=1):
        if not (0 <= address <= 65535 and 1 <= count <= 125
                and address + count <= 65536):
            raise ValueError("Invalid read range.")
        response = self._request(3, struct.pack(">HH", address, count))
        if len(response) != 2 + count * 2 or response[1] != count * 2:
            raise ModbusError("Invalid Modbus read response length.")
        return struct.unpack(">" + "H" * count, response[2:])

    def write_fc16_one(self, address, value):
        """Write exactly ONE register using FC16, never FC06."""
        if not (0 <= address <= 65535 and 0 <= value <= 65535):
            raise ValueError("Invalid write address or value.")
        response = self._request(16, struct.pack(">HHBH", address, 1, 2, value))
        if len(response) != 5:
            raise ModbusError("Invalid FC16 write response length.")
        echoed_address, echoed_count = struct.unpack(">HH", response[1:])
        if echoed_address != address or echoed_count != 1:
            raise ModbusError("Write response does not confirm the requested register.")


@dataclass(frozen=True)
class DeviceIdentity:
    unit_id: int
    model: str
    serial: str


@dataclass
class DeviceState:
    model: str
    serial: str
    conn: int
    raw_limit: int
    scale: int
    enabled: int
    watts: Decimal | None
    operating_state: int
    dc1_watts: Decimal | None = None
    dc2_watts: Decimal | None = None

    @property
    def dc_total_watts(self):
        """Provide a DC total only when BOTH DC inputs were read successfully."""
        if self.dc1_watts is None or self.dc2_watts is None:
            return None
        return self.dc1_watts + self.dc2_watts

    @property
    def limit_percent(self):
        if self.raw_limit == 0xFFFF:
            return None
        return Decimal(self.raw_limit) * (Decimal(10) ** self.scale)


def read_identity(client):
    """Verify the Unit ID reports a SunSpec DS3 device with model 123."""
    signature = client.read(REG_SUNSPEC, 4)
    if signature[:2] != (0x5375, 0x6E53) or signature[2] != 1:
        raise ModbusError("SunSpec signature or Common Model is missing.")
    model = words_to_text(client.read(REG_MODEL, 16))
    serial = words_to_text(client.read(REG_SERIAL, 16))
    if not model.upper().startswith("DS3") or not serial:
        raise ModbusError("This Modbus address does not identify as a DS3 inverter.")
    if client.read(REG_CONTROLS_MODEL, 2) != (123, 24):
        raise ModbusError("SunSpec model 123 is missing or has an unexpected layout.")
    return DeviceIdentity(client.unit_id, model, serial)


def read_state(client):
    identity = read_identity(client)
    model, serial = identity.model, identity.serial
    controls = client.read(REG_CONTROLS_MODEL, 10)
    if controls[0] != 123 or controls[1] != 24:
        raise ModbusError("SunSpec model 123 is missing or has an unexpected layout.")
    sf = signed16(client.read(REG_WMAXLIMPCT_SF)[0])
    if not -4 <= sf <= 4:
        raise ModbusError("Unexpected power scale factor.")
    watts = None
    operating_state = 0xFFFF
    if client.read(REG_INVERTER_MODEL, 1)[0] == 101:
        raw_watts, raw_watts_sf = client.read(REG_AC_WATTS, 2)
        sf_watts = signed16(raw_watts_sf)
        if raw_watts != 0x8000 and -4 <= sf_watts <= 4:
            watts = Decimal(signed16(raw_watts)) * (Decimal(10) ** sf_watts)
        operating_state = client.read(REG_OPERATING_STATE)[0]
    dc1_watts = None
    dc2_watts = None
    # This ECU exposes SunSpec model 114 at address 40212.
    # Decode DC registers only when the model number and length match.
    # A Modbus exception for the optional DC model must not prevent
    # other readings; a communication failure still fails the status read.
    try:
        if client.read(REG_DC_MODEL, 2) == (114, 48):
            dc_words = client.read(REG_DC_WATT_1, 4)
            dc1_watts = ieee754_float32(dc_words[:2])
            dc2_watts = ieee754_float32(dc_words[2:])
    except ModbusResponseError as exc:
        # Only explicitly unsupported FC03 / missing DC registers
        # are optional. Timeouts, disconnected sockets, invalid frames,
        # device failures, and busy exceptions must be reported as read errors.
        if exc.function != 3 or exc.code not in (1, 2):
            raise
    return DeviceState(
        model=model,
        serial=serial,
        conn=controls[REG_CONN - REG_CONTROLS_MODEL],
        raw_limit=controls[REG_WMAXLIMPCT - REG_CONTROLS_MODEL],
        scale=sf,
        enabled=controls[REG_WMAXLIM_ENA - REG_CONTROLS_MODEL],
        watts=watts,
        operating_state=operating_state,
        dc1_watts=dc1_watts,
        dc2_watts=dc2_watts,
    )


# Fast polling groups identity + AC, and controls + DC, respectively.
# Both cross SunSpec model boundaries and stay below FC03's 125-word limit.
# Some ECU-R firmware rejects such reads: fall back to the existing four
# model-aligned blocks, with smaller per-section reads as a final fallback.
# Capabilities are cached separately for each Unit ID and cleared on disconnect.
TWO_BLOCK_POLL_RANGES = (
    (REG_MODEL, REG_OPERATING_STATE + 1 - REG_MODEL),
    (REG_CONTROLS_MODEL, REG_DC_WATT_2 + 2 - REG_CONTROLS_MODEL),
)

# Four compact FC03 blocks stay within their SunSpec model boundaries.
# When firmware rejects a large block, fall back to smaller reads
# once per Unit ID; remember that capability for the session.
POLL_BLOCKS = {
    'identity': (REG_MODEL, REG_SERIAL + 16 - REG_MODEL),
    'controls': (REG_CONTROLS_MODEL, REG_WMAXLIMPCT_SF + 1 - REG_CONTROLS_MODEL),
    'ac': (REG_INVERTER_MODEL, REG_OPERATING_STATE + 1 - REG_INVERTER_MODEL),
    'dc': (REG_DC_MODEL, REG_DC_WATT_2 + 2 - REG_DC_MODEL),
}


def _read_compatible_block(client, capabilities, section, decode, legacy):
    """Attempt a block read; fall back per Unit ID/section on exceptions 1/2/3.

    A timeout, malformed frame, or other communication error must NOT
    trigger a silent fallback: the read error must remain visible."""
    if capabilities.get(section) is not False:
        start, count = POLL_BLOCKS[section]
        try:
            words = client.read(start, count)
        except ModbusResponseError as exc:
            if exc.function != 3 or exc.code not in (1, 2, 3):
                raise
            capabilities[section] = False
        else:
            return decode(words)
    return legacy()


def _read_monitor_state_four_blocks(client, expected, capabilities):
    """Read model, serial, AC, controls, and DC with four FC03 blocks.

    Each block remains within its SunSpec model boundaries. Device identity
    is verified on every scan; if it changes, no measurements for the
    former identity are displayed.

    Separate read_state and read_identity checks for FC16 safety remain
    in place, including immediate verification before writing."""
    if client.unit_id != expected.unit_id:
        raise ModbusError('Target Unit ID does not match the detected inverter.')

    def decode_identity(words):
        offset = REG_SERIAL - REG_MODEL
        return DeviceIdentity(client.unit_id,
                              words_to_text(words[:16]),
                              words_to_text(words[offset:offset + 16]))

    def legacy_identity():
        model = words_to_text(client.read(REG_MODEL, 16))
        serial = words_to_text(client.read(REG_SERIAL, 16))
        return DeviceIdentity(client.unit_id, model, serial)

    identity = _read_compatible_block(client, capabilities, 'identity',
                                      decode_identity, legacy_identity)
    if identity != expected:
        raise ModbusError(f'Identity mismatch for ID {expected.unit_id}: '
                          f'expected {expected.model} / {expected.serial}, '
                          f'received {identity.model} / {identity.serial}.')

    def decode_controls(words):
        if words[:2] != (123, 24):
            raise ModbusError('SunSpec model 123 is missing or has an unexpected layout.')
        return words[:10], signed16(words[REG_WMAXLIMPCT_SF - REG_CONTROLS_MODEL])

    def legacy_controls():
        controls = client.read(REG_CONTROLS_MODEL, 10)
        if controls[:2] != (123, 24):
            raise ModbusError('SunSpec model 123 is missing or has an unexpected layout.')
        return controls, signed16(client.read(REG_WMAXLIMPCT_SF)[0])

    controls, sf = _read_compatible_block(client, capabilities, 'controls',
                                          decode_controls, legacy_controls)
    if not -4 <= sf <= 4:
        raise ModbusError('Unexpected power scale factor.')

    def ac_values(raw_watts, raw_scale, operating):
        watts = None
        sf_watts = signed16(raw_scale)
        if raw_watts != 0x8000 and -4 <= sf_watts <= 4:
            watts = Decimal(signed16(raw_watts)) * (Decimal(10) ** sf_watts)
        return watts, operating

    def decode_ac(words):
        if words[0] != 101:
            return None, 0xFFFF
        offset = REG_AC_WATTS - REG_INVERTER_MODEL
        return ac_values(words[offset], words[offset + 1],
                         words[REG_OPERATING_STATE - REG_INVERTER_MODEL])

    def legacy_ac():
        if client.read(REG_INVERTER_MODEL)[0] != 101:
            return None, 0xFFFF
        raw_watts, raw_scale = client.read(REG_AC_WATTS, 2)
        operating = client.read(REG_OPERATING_STATE)[0]
        return ac_values(raw_watts, raw_scale, operating)

    watts, operating_state = _read_compatible_block(client, capabilities, 'ac',
                                                    decode_ac, legacy_ac)

    def decode_dc(words):
        if words[:2] != (114, 48):
            return None, None
        offset = REG_DC_WATT_1 - REG_DC_MODEL
        return (ieee754_float32(words[offset:offset + 2]),
                ieee754_float32(words[offset + 2:offset + 4]))

    def legacy_dc():
        try:
            if client.read(REG_DC_MODEL, 2) == (114, 48):
                dc_words = client.read(REG_DC_WATT_1, 4)
                return (ieee754_float32(dc_words[:2]),
                        ieee754_float32(dc_words[2:]))
        except ModbusResponseError as exc:
            if exc.function != 3 or exc.code not in (1, 2):
                raise
        return None, None

    dc1, dc2 = _read_compatible_block(client, capabilities, 'dc',
                                      decode_dc, legacy_dc)
    return DeviceState(
        model=identity.model,
        serial=identity.serial,
        conn=controls[REG_CONN - REG_CONTROLS_MODEL],
        raw_limit=controls[REG_WMAXLIMPCT - REG_CONTROLS_MODEL],
        scale=sf,
        enabled=controls[REG_WMAXLIM_ENA - REG_CONTROLS_MODEL],
        watts=watts,
        operating_state=operating_state,
        dc1_watts=dc1,
        dc2_watts=dc2,
    )



def _read_monitor_state_two_blocks(client, expected):
    """Read two contiguous FC03 ranges; validate identity before the second.

    40020..40108 (89 words): model/serial and AC power/operating mode.
    40184..40249 (66 words): controls/limit and both DC inputs.
    These ranges cross SunSpec model boundaries; some firmware rejects them.
    """
    first_start, first_count = TWO_BLOCK_POLL_RANGES[0]
    first = client.read(first_start, first_count)
    serial_offset = REG_SERIAL - first_start
    identity = DeviceIdentity(
        client.unit_id,
        words_to_text(first[:16]),
        words_to_text(first[serial_offset:serial_offset + 16]),
    )
    if identity != expected:
        raise ModbusError(
            f'Identity mismatch for ID {expected.unit_id}: '
            f'expected {expected.model} / {expected.serial}, '
            f'received {identity.model} / {identity.serial}.'
        )

    second_start, second_count = TWO_BLOCK_POLL_RANGES[1]
    second = client.read(second_start, second_count)
    if second[:2] != (123, 24):
        raise ModbusError('SunSpec model 123 is missing or has an unexpected layout.')
    scale = signed16(second[REG_WMAXLIMPCT_SF - second_start])
    if not -4 <= scale <= 4:
        raise ModbusError('Unexpected power scale factor.')

    watts = None
    operating_state = 0xFFFF
    if first[REG_INVERTER_MODEL - first_start] == 101:
        watts_offset = REG_AC_WATTS - first_start
        raw_watts, raw_scale = first[watts_offset:watts_offset + 2]
        watts_sf = signed16(raw_scale)
        if raw_watts != 0x8000 and -4 <= watts_sf <= 4:
            watts = Decimal(signed16(raw_watts)) * (Decimal(10) ** watts_sf)
        operating_state = first[REG_OPERATING_STATE - first_start]

    dc1 = None
    dc2 = None
    dc_offset = REG_DC_MODEL - second_start
    if second[dc_offset:dc_offset + 2] == (114, 48):
        dc_words_offset = REG_DC_WATT_1 - second_start
        dc_words = second[dc_words_offset:dc_words_offset + 4]
        dc1 = ieee754_float32(dc_words[:2])
        dc2 = ieee754_float32(dc_words[2:])

    return DeviceState(
        model=identity.model,
        serial=identity.serial,
        conn=second[REG_CONN - second_start],
        raw_limit=second[REG_WMAXLIMPCT - second_start],
        scale=scale,
        enabled=second[REG_WMAXLIM_ENA - second_start],
        watts=watts,
        operating_state=operating_state,
        dc1_watts=dc1,
        dc2_watts=dc2,
    )


def read_monitor_state(client, expected, capabilities):
    """Prefer two FC03 reads per inverter; safely cache unsupported ranges.

    Only explicit FC03 Modbus exceptions 1/2/3 trigger fallback. Timeouts,
    protocol errors, other Modbus exceptions, and identity mismatches remain
    visible polling errors; do not silently repeat those requests.
    The independent FC16 write-verification path is intentionally untouched.
    """
    if client.unit_id != expected.unit_id:
        raise ModbusError('Target Unit ID does not match the detected inverter.')
    if capabilities.get('two_blocks') is not False:
        try:
            state = _read_monitor_state_two_blocks(client, expected)
        except ModbusResponseError as exc:
            if exc.function != 3 or exc.code not in (1, 2, 3):
                raise
            capabilities['two_blocks'] = False
        else:
            capabilities['two_blocks'] = True
            return state
    return _read_monitor_state_four_blocks(client, expected, capabilities)


def ensure_safe_identity(state, identity, duplicate_serials=()):
    """Allow writing only to a unique, freshly verified device identity."""
    if identity is None:
        raise ValueError("No inverter selected.")
    if identity.serial in duplicate_serials:
        raise ValueError(
            f"Write blocked: serial number {identity.serial} is "
            "reported by multiple Unit IDs."
        )
    if state.serial != identity.serial or state.model != identity.model:
        raise ValueError(
            "Write blocked: device identity differs from the "
            f"discovery for Unit {identity.unit_id}. "
            f"Found: {state.model!r} / {state.serial!r}; "
            f"expected: {identity.model!r} / {identity.serial!r}."
        )
    if not state.model.upper().startswith("DS3"):
        raise ValueError(f"Write blocked: unexpected model {state.model!r}.")


def ensure_safe_to_write(state, identity, duplicate_serials=()):
    """Additional safety checks for percentage-based power limiting."""
    ensure_safe_identity(state, identity, duplicate_serials)
    if state.scale != -1:
        raise ValueError("Write blocked: scale factor is not -1.")
    if state.raw_limit == 0xFFFF:
        raise ValueError("Write blocked: current limit value is invalid.")
    if state.enabled not in (0, 1):
        raise ValueError("Write blocked: power limiting state is unknown.")


def ensure_safe_production_write(state, identity, duplicate_serials=()):
    """Switching Conn requires valid identity and known 0/1 state, not limit SF."""
    ensure_safe_identity(state, identity, duplicate_serials)
    if state.conn not in (0, 1):
        raise ValueError("Write blocked: production state (40188) is unknown.")


def write_and_verify(client, address, value, identity):
    """Write only once, then read back, including after an ambiguous response.

    A NEW TCP connection is used after communication/protocol errors.
    The same Unit ID, model, and serial are reverified. Matching register
    values do not prove the requested physical AC response."""
    if identity is None or client.unit_id != identity.unit_id:
        raise ValueError("Write blocked: target Unit ID and identity do not match.")
    acknowledged = True
    need_reconnect = False
    reconnected = False
    write_problem = None
    try:
        client.write_fc16_one(address, value)
    except ModbusResponseError:
        # Do not conceal an explicit rejection and never retry the write.
        raise
    except (OSError, ModbusError) as exc:
        acknowledged = False
        write_problem = str(exc)
        need_reconnect = True
        client.close()

    last_actual = None
    last_error = None
    for attempt in range(5):
        try:
            if need_reconnect:
                client.reconnect()
                actual_identity = read_identity(client)
                if actual_identity != identity:
                    client.close()
                    raise ValueError(
                        f"Post-write verification stopped: identity of Unit {identity.unit_id} "
                        "changed. No further registers were written."
                    )
                need_reconnect = False
                reconnected = True
            last_actual = client.read(address)[0]
            last_error = None
            if last_actual == value:
                return WriteVerification(acknowledged, reconnected)
        except ModbusResponseError as exc:
            raise ModbusError(
                f"Register {address}: post-write readback was rejected ({exc}). "
                "The write was not retried; its outcome remains unconfirmed."
            ) from exc
        except (OSError, ModbusError) as exc:
            last_error = str(exc)
            need_reconnect = True
            client.close()
        if attempt < 4:
            time.sleep(0.5)

    detail = (f"last read error: {last_error}" if last_error is not None else
              f"requested {value}, read back {last_actual}")
    if write_problem is not None:
        detail += f"; no valid write response: {write_problem}"
    raise ModbusError(
        f"Register {address}: change not confirmed ({detail}). "
        "No automatic retry; check the status."
    )

# ---------------------------------------------------------------------------
# Monitoring and recording; retain the verified Modbus core.
# ---------------------------------------------------------------------------

# Delay between two consecutive inverter polls, INCLUDING the transition
# from the last Unit ID to the first. Not the delay between Modbus frames.
SCAN_PAUSE_DEFAULT = 1.0
SCAN_PAUSE_OPTIONS = ('0.1', '0.25', '0.5', '1', '2', '5')
MAX_LOG_RECORDS = 120000
LOG_REQUEST_IDS = count(1)  # Unique identifier for each transaction, including across TCP sessions.
MAX_LOG_ROWS = 850
MAX_GRAPH_SECONDS = 7200

# Uniform spacing between the outer dashboard panels.
SECTION_GAP = 6
CONTROL_COLUMN_WIDTH = 260  # Connection panel exactly as wide as Power Control.

BG = '#091320'
PANEL = '#101e2b'
PANEL_DARK = '#0d1925'
INPUT = '#142638'
LINE = '#2a4154'
TEXT = '#ecf3fb'
MUTED = '#9cadbf'
GREEN = '#46d77a'
BLUE = '#69a5ff'
YELLOW = '#f5bd57'
RED = '#f17676'


def style_windows_titlebar(root):
    """Apply a dark Windows title bar without changing Tk widgets.

    Windows 11 supports custom title and border colors. On Windows 10,
    request the dark DWM title bar where available. Other operating systems
    keep their original window decoration."""
    if sys.platform != 'win32':
        return
    try:
        import ctypes
        from ctypes import wintypes

        user32 = ctypes.WinDLL('user32', use_last_error=True)
        dwmapi = ctypes.WinDLL('dwmapi', use_last_error=True)
        user32.GetAncestor.argtypes = (wintypes.HWND, wintypes.UINT)
        user32.GetAncestor.restype = wintypes.HWND
        dwm = dwmapi.DwmSetWindowAttribute
        dwm.argtypes = (wintypes.HWND, wintypes.DWORD,
                        ctypes.c_void_p, wintypes.DWORD)
        dwm.restype = ctypes.c_long

        # Tk's winfo_id is not always the HWND of the actual title bar.
        hwnd = user32.GetAncestor(root.winfo_id(), 2)  # GA_ROOT
        if not hwnd:
            return

        def set_attribute(attribute, value):
            data = ctypes.c_uint32(value)
            return dwm(hwnd, attribute, ctypes.byref(data),
                       ctypes.sizeof(data)) == 0

        # Prefer the dark title bar, including on supported Windows 10 builds.
        if not set_attribute(20, 1):  # DWMWA_USE_IMMERSIVE_DARK_MODE
            set_attribute(19, 1)      # Alternative attribute number for older builds.

        def colorref(color):
            # DWM uses COLORREF (0x00BBGGRR), not RGB (0xRRGGBB).
            rgb = color.lstrip('#')
            return (int(rgb[4:6], 16) << 16 |
                    int(rgb[2:4], 16) << 8 |
                    int(rgb[0:2], 16))

        # Windows 11 (build 22000+); ignored on older systems.
        set_attribute(35, colorref(BG))    # DWMWA_CAPTION_COLOR
        set_attribute(36, colorref(TEXT))  # DWMWA_TEXT_COLOR
        set_attribute(34, colorref(LINE))  # DWMWA_BORDER_COLOR
    except (OSError, AttributeError, tk.TclError):
        # The app and controls must not depend on OS title bar support.
        pass


def timestamp():
    return datetime.now().strftime('%H:%M:%S.%f')[:-3]


def watts_number(watts):
    """Round a Decimal to text without the W unit."""
    if watts is None:
        return '---'
    return str(int(watts.to_integral_value(rounding=ROUND_HALF_UP)))


def table_watts(watts):
    """Include W in table cells, not headings; unavailable values use ---."""
    return f'{watts_number(watts)} W' if watts is not None else '---'


def nominal_limit_watts(percent, inverter_count, rated_watts_per_inverter):
    """Estimated nominal wattage for the selected model, not measured AC."""
    p = Decimal(str(percent))
    if not p.is_finite() or not 0 <= p <= 100:
        raise ValueError('Limit percentage is outside the range 0..100.')
    if inverter_count < 1:
        return None  # No detected units means no reliable rated watt estimate.
    rated_watts = inverter_count * rated_watts_per_inverter
    return (Decimal(rated_watts) * p / Decimal(100)).quantize(
        Decimal('1'), rounding=ROUND_HALF_UP)


def watt_label(watts):
    """Format wattage without thousands separators to avoid ambiguity."""
    return f'{int(watts)} W'


def nominal_limit_label(percent, inverter_count, rated_watts_per_inverter):
    watts = nominal_limit_watts(percent, inverter_count, rated_watts_per_inverter)
    return watt_label(watts) if watts is not None else '---'


def slider_percent_from_state(state):
    """Round a valid register limit to the nearest whole slider percentage."""
    percent = state.limit_percent if state is not None else None
    if percent is None or not percent.is_finite() or not 0 <= percent <= 100:
        return None
    return int(percent.to_integral_value(rounding=ROUND_HALF_UP))


def limit_mode(state):
    if state is None or state.enabled not in (0, 1):
        return 'UNKNOWN'
    return 'OFF' if state.enabled == 0 else 'ACTIVE'


def raw_hex(values):
    return '[' + ','.join(f'{word:04X}' for word in values) + ']'


@dataclass
class LogRecord:
    """One record per Modbus transaction; pending completes on the same row."""
    request_id: int
    stamp: str                  # Timestamp at the beginning of the request.
    unit: int
    request: str                # E.g. FC03 40246 (4) or FC16 40193 (1) = 1.
    response: str               # PENDING..., register data, ACK, or error.
    elapsed_ms: float | None   # Time elapsed between request and completed response.
    function: str               # FC03 or FC16, to keep the log limited to protocol transactions.
    status: str                 # pending / ok / error.


@dataclass(frozen=True)
class Command:
    action: str  # set / disable / start / stop
    identity: DeviceIdentity
    percent: str | None
    duplicates: frozenset[str]


class LoggedModbusTCP(ModbusTCP):
    """Record REQUEST and RESPONSE/error in ONE row per Modbus transaction."""

    def __init__(self, unit_id, emit, timeout_seconds=TIMEOUT_SECONDS):
        super().__init__(unit_id, timeout_seconds=timeout_seconds)
        self.emit = emit

    def _start_log(self, request, function):
        request_id = next(LOG_REQUEST_IDS)
        stamp = timestamp()
        self.emit(LogRecord(request_id, stamp, self.unit_id, request,
                            'PENDING...', None, function, 'pending'))
        # Start immediately before the actual read/write, excluding TCP setup.
        return request_id, stamp, time.monotonic()

    def _finish_log(self, request_id, stamp, request, function,
                    started, response, status):
        elapsed = (time.monotonic() - started) * 1000
        self.emit(LogRecord(request_id, stamp, self.unit_id, request,
                            response, elapsed, function, status))

    @staticmethod
    def _error_response(exc):
        if isinstance(exc, (socket.timeout, TimeoutError)):
            return f'TIMEOUT: {exc}' if str(exc) else 'TIMEOUT'
        if isinstance(exc, ModbusResponseError):
            return f'EXCEPTION: {exc}'
        return f'ERROR: {exc}'

    def read(self, address, count=1):
        request = f'FC03 {address} ({count})'
        request_id, stamp, started = self._start_log(request, 'FC03')
        try:
            values = super().read(address, count)
        except (OSError, ValueError, ModbusError) as exc:
            self._finish_log(request_id, stamp, request, 'FC03', started,
                             self._error_response(exc), 'error')
            raise
        self._finish_log(request_id, stamp, request, 'FC03', started,
                         raw_hex(values), 'ok')
        return values

    def write_fc16_one(self, address, value):
        request = f'FC16 {address}(1)={value}'
        request_id, stamp, started = self._start_log(request, 'FC16')
        try:
            result = super().write_fc16_one(address, value)
        except (OSError, ValueError, ModbusError) as exc:
            self._finish_log(request_id, stamp, request, 'FC16', started,
                             self._error_response(exc), 'error')
            raise
        self._finish_log(request_id, stamp, request, 'FC16', started,
                         'ACK', 'ok')
        return result


def verify_identity_now(client, expected):
    actual = read_identity(client)
    if actual != expected:
        raise ModbusError(f'Unit {expected.unit_id}: identity changed; write blocked. '
                          f'Expected {expected.serial}, read {actual.serial}.')


class OperatingModeHelpTip:
    """Windows-style tooltip for the Operating mode table heading only.

    Its numeric codes come directly from OPERATING_STATES, the same mapping
    used to decode the Modbus operating state for the table."""

    def __init__(self, table):
        self.table = table
        self.column = f"#{list(table['columns']).index('operating') + 1}"
        self.timer = None
        self.popup = None
        table.bind('<Motion>', self._motion, add='+')
        table.bind('<Leave>', self.hide, add='+')
        table.bind('<ButtonPress>', self.hide, add='+')
        table.bind('<Destroy>', self.hide, add='+')

    def _on_heading(self, x, y):
        return (self.table.identify_region(x, y) == 'heading'
                and self.table.identify_column(x) == self.column)

    def _motion(self, event):
        if not self._on_heading(event.x, event.y):
            self.hide()
        elif self.timer is None and self.popup is None:
            # Hovering over the table heading briefly shows the help text.
            self.timer = self.table.after(550, self._show)

    def _show(self):
        self.timer = None
        if not self.table.winfo_exists():
            return
        px, py = self.table.winfo_pointerxy()
        if not self._on_heading(px - self.table.winfo_rootx(),
                                py - self.table.winfo_rooty()):
            return

        # Compact Windows-style tooltip; no modal dialog or focus change.
        background, foreground = '#fffde8', '#262626'
        popup = tk.Toplevel(self.table)
        popup.withdraw()
        popup.overrideredirect(True)
        try:
            popup.wm_attributes('-topmost', True)
        except tk.TclError:
            pass
        box = tk.Frame(popup, bg=background, highlightbackground='#999999',
                       highlightthickness=1, bd=0)
        box.pack(fill='both', expand=True)
        tk.Label(box, text='Operating mode (register 40108)', bg=background,
                 fg=foreground, font=('Segoe UI', 9, 'bold'), anchor='w').grid(
                     row=0, column=0, columnspan=2, sticky='w',
                     padx=10, pady=(8, 5))
        for row, (code, (name, meaning)) in enumerate(OPERATING_STATES.items(), start=1):
            tk.Label(box, text=f'{code}  {name}', bg=background,
                     fg=foreground, font=('Consolas', 9), anchor='w').grid(
                         row=row, column=0, sticky='w', padx=(10, 13), pady=1)
            tk.Label(box, text=meaning, bg=background, fg=foreground,
                     font=('Segoe UI', 9), anchor='w').grid(
                         row=row, column=1, sticky='w', padx=(0, 10), pady=1)
        tk.Label(box, text='65535 = status unavailable', bg=background,
                 fg='#555555', font=('Segoe UI', 8), anchor='w').grid(
                     row=len(OPERATING_STATES) + 1, column=0, columnspan=2,
                     sticky='w', padx=10, pady=(5, 8))

        popup.update_idletasks()
        screen_w = self.table.winfo_screenwidth()
        screen_h = self.table.winfo_screenheight()
        x = max(0, min(px + 14, screen_w - popup.winfo_reqwidth() - 6))
        y = py + 20
        if y + popup.winfo_reqheight() > screen_h - 6:
            y = max(0, py - popup.winfo_reqheight() - 12)
        popup.geometry(f'+{x}+{y}')
        self.popup = popup
        popup.deiconify()

    def hide(self, _event=None):
        if self.timer is not None:
            try:
                self.table.after_cancel(self.timer)
            except tk.TclError:
                pass
            self.timer = None
        if self.popup is not None:
            popup, self.popup = self.popup, None
            try:
                popup.destroy()
            except tk.TclError:
                pass


class PowerMonitor:
    def __init__(self, root):
        self.root = root
        self.root.title('APSystems ECU-R Control (Modbus TCP)')
        # Fixed initial size; do not automatically resize to the screen.
        self.root.geometry('1200x900')
        # The initial 1200x900 window size is also the minimum size.
        self.root.minsize(1200, 900)
        self.root.configure(bg=BG)
        self.root.protocol('WM_DELETE_WINDOW', self.close)

        self.events = queue.Queue()
        self.devices = {}
        self.states = {}
        self.errors = {}
        self.duplicate_serials = set()
        self.block_capabilities = {}  # Unit ID -> rejected read blocks, remembered only for this session
        self.selected_unit = None
        self.busy = False
        self.current_task = None
        self.pending_command = None
        self.confirm_active = False
        self.discovery_pending = False
        self.first_poll_after_connect = False
        self.scan_unit = None  # ID currently being polled or targeted by the scan.
        self.next_poll_due = float('inf')
        self.poll_started = None
        self.history = deque(maxlen=1500)
        self.log_records = deque(maxlen=MAX_LOG_RECORDS)
        self.log_index = {}  # request_id -> existing log record; one row per request.
        self.log_visible = 0
        # The user starts and stops the monitoring session manually.
        # Each Modbus operation still uses its own TCP connection.
        self.connected = False
        self.connecting = False
        self.disconnect_requested = False
        self.closing = False  # On exit, wait silently for the current Modbus operation.
        self.stop_requested = threading.Event()

        self.ip_var = tk.StringVar(value=ECU_IP)
        self.port_var = tk.StringVar(value=str(ECU_PORT))
        self.sum_dc_var = tk.StringVar(value='--- W')
        self.sum_ac_var = tk.StringVar(value='--- W')
        # Detail rows below the large DC and AC power values.
        # Derived statistics use only the existing Modbus readings.
        self.dc1_total_var = tk.StringVar(value='---')
        self.dc2_total_var = tk.StringVar(value='---')
        self.active_inputs_var = tk.StringVar(value='---')
        self.producing_units_var = tk.StringVar(value='---')
        self.conversion_ratio_var = tk.StringVar(value='---')
        self.nominal_used_var = tk.StringVar(value='---')
        # The last measurement time and cycle duration appear above the inverter table.
        self.last_measurement_var = tk.StringVar(value='---')
        self.cycle_duration_var = tk.StringVar(value='---')
        self.interval_var = tk.StringVar(value=f'{SCAN_PAUSE_DEFAULT:g}')
        self.scan_max_var = tk.StringVar(value=str(SCAN_MAX_ID_DEFAULT))
        self.scan_max_id = SCAN_MAX_ID_DEFAULT  # Captured at Connect; workers never access Tk variables.
        self.inverter_model_var = tk.StringVar(value=DEFAULT_INVERTER_MODEL)
        self.inverter_model = DEFAULT_INVERTER_MODEL
        self.rated_watts_per_inverter = INVERTER_RATINGS_W[DEFAULT_INVERTER_MODEL]
        # The Tk slider displays W and %, using integer 0..100% steps.
        # Only a separately confirmed button action can send FC16.
        self.target_var = tk.IntVar(value=100)
        self.target_watts_var = tk.StringVar(value='---')
        self.target_percent_var = tk.StringVar(value='100%')
        self.reported_mode_var = tk.StringVar(value='---')
        self.reported_watts_var = tk.StringVar(value='---')
        self.route_id_var = tk.StringVar(value='---')
        self.target_initialized = False
        self.production_write_enabled = False
        self.production_drawn = None
        self.target_var.trace_add('write', self._on_slider_changed)
        self.graph_span_var = tk.StringVar(value='30 minutes')

        self._style()
        self._build()
        self._update_controls()
        # Adjust the native Windows title bar after constructing the window.
        self.root.after(100, lambda: style_windows_titlebar(self.root))
        self.root.after(80, self._drain_events)
        self.root.after(100, self._poll_tick)
        # Never connect or discover devices automatically on startup.

    def _style(self):
        style = ttk.Style(self.root)
        try:
            style.theme_use('clam')
        except tk.TclError:
            pass
        # Clam's default Combobox colors change to near-white on hover/press.
        # Make the field, arrow button and borders the same flat dark color,
        # including when hovered or focused. Keep disabled text muted.
        steady_fill = [('disabled', INPUT), ('pressed', INPUT),
                       ('active', INPUT), ('focus', INPUT), ('readonly', INPUT)]
        for name, padding in (('Dark.TCombobox', (5, 5)),
                              ('Compact.TCombobox', (4, 1))):
            style.configure(name, fieldbackground=INPUT, background=INPUT,
                            foreground=TEXT, arrowcolor=TEXT,
                            selectbackground=INPUT, selectforeground=TEXT,
                            bordercolor=INPUT, lightcolor=INPUT, darkcolor=INPUT,
                            troughcolor=INPUT, relief='flat', borderwidth=0,
                            padding=padding)
            style.map(name,
                      fieldbackground=steady_fill, background=steady_fill,
                      bordercolor=steady_fill, lightcolor=steady_fill,
                      darkcolor=steady_fill, troughcolor=steady_fill,
                      selectbackground=steady_fill,
                      foreground=[('disabled', MUTED), ('readonly', TEXT)],
                      selectforeground=[('disabled', MUTED), ('readonly', TEXT)],
                      arrowcolor=[('disabled', MUTED), ('readonly', TEXT)])
        # A ttk.Combobox popdown has its OWN frame and listbox borders.
        # The clam theme normally draws a light one-pixel outline even when
        # the closed combobox has no border. Remove that outline as well.
        style.configure('ComboboxPopdownFrame', background=INPUT,
                        bordercolor=INPUT, lightcolor=INPUT, darkcolor=INPUT,
                        borderwidth=0, relief='flat')
        # Also cover dropdowns created lazily by Tk after the UI is built.
        self.root.option_add('*TCombobox*Listbox.borderWidth', 0)
        self.root.option_add('*TCombobox*Listbox.highlightThickness', 0)
        # Use the same row height for the inverter table and Modbus log.
        # Keep the established log row height on smaller screens.
        self.table_row_height = 20 if self.root.winfo_screenheight() >= 900 else 16
        # Treeviews and scrollbars need the same dark styling.
        # Without explicit colors, the clam theme uses white scrollbars.
        for orientation in ('Vertical', 'Horizontal'):
            scrollbar_style = f'Dark.{orientation}.TScrollbar'
            style.configure(scrollbar_style,
                            background='#294358', troughcolor=PANEL_DARK,
                            bordercolor=PANEL_DARK, lightcolor='#294358',
                            darkcolor='#294358', arrowcolor=TEXT,
                            relief='flat', borderwidth=0, arrowsize=11, width=12)
            style.map(scrollbar_style,
                      background=[('pressed', '#48657c'), ('active', '#36546c')],
                      arrowcolor=[('disabled', MUTED), ('active', 'white')])
        style.configure('Monitor.Treeview', background=PANEL_DARK, fieldbackground=PANEL_DARK,
                        foreground=TEXT, borderwidth=0, relief='flat',
                        bordercolor=LINE, lightcolor=LINE, darkcolor=LINE,
                        rowheight=self.table_row_height, font=('Segoe UI', 9))
        style.configure('Monitor.Treeview.Heading', background='#20364a', foreground=TEXT,
                        bordercolor=LINE, lightcolor=LINE, darkcolor=LINE,
                        relief='flat', font=('Segoe UI', 9, 'bold'), padding=(4, 7))
        style.map('Monitor.Treeview', background=[('selected', '#274660')],
                  foreground=[('selected', 'white')],
                  bordercolor=[('focus', LINE), ('!focus', LINE)])
        # Column headers must not light up on mouse hover or click.
        # Apply the same fixed colors to both Treeview tables.
        style.configure('Log.Treeview', background=PANEL_DARK, fieldbackground=PANEL_DARK,
                        foreground=TEXT, borderwidth=0, relief='flat',
                        bordercolor=LINE, lightcolor=LINE, darkcolor=LINE,
                        rowheight=self.table_row_height,
                        font=('Consolas', 9))
        style.configure('Log.Treeview.Heading', background='#20364a', foreground=TEXT,
                        bordercolor=LINE, lightcolor=LINE, darkcolor=LINE,
                        relief='flat', font=('Segoe UI', 9, 'bold'),
                        padding=(4, 5 if self.root.winfo_screenheight() >= 900 else 2))
        for heading_style in ('Monitor.Treeview.Heading', 'Log.Treeview.Heading'):
            style.map(heading_style,
                      background=[('pressed', '#20364a'), ('active', '#20364a')],
                      foreground=[('pressed', TEXT), ('active', TEXT)],
                      relief=[('pressed', 'flat'), ('active', 'flat')],
                      bordercolor=[('pressed', LINE), ('active', LINE)],
                      lightcolor=[('pressed', LINE), ('active', LINE)],
                      darkcolor=[('pressed', LINE), ('active', LINE)])
        style.map('Log.Treeview', background=[('selected', '#274660')],
                  foreground=[('selected', 'white')],
                  bordercolor=[('focus', LINE), ('!focus', LINE)])
        # The 'Scan through ID' dropdown has its own dark scrollbar.
        # Keep its color unchanged on hover and click.
        style.configure('Scan.Vertical.TScrollbar',
                        background='#294358', troughcolor=PANEL_DARK,
                        bordercolor=PANEL_DARK, lightcolor='#294358',
                        darkcolor='#294358', arrowcolor=TEXT,
                        relief='flat', borderwidth=0, arrowsize=11, width=12)
        style.map('Scan.Vertical.TScrollbar',
                  background=[('pressed', '#294358'), ('active', '#294358')],
                  arrowcolor=[('disabled', MUTED), ('pressed', TEXT), ('active', TEXT)])
        self.root.option_add('*TCombobox*Listbox.background', INPUT)
        self.root.option_add('*TCombobox*Listbox.foreground', TEXT)
        self.root.option_add('*TCombobox*Listbox.selectBackground', '#274660')

    def _flatten_combobox_dropdown(self, combo, scrollbar_style=None):
        """Remove the separate popdown's light border, including on Windows."""
        try:
            popdown = str(self.root.tk.call('ttk::combobox::PopdownWindow', str(combo)))
            self.root.tk.call(popdown, 'configure', '-background', INPUT,
                              '-borderwidth', 0, '-highlightthickness', 0)
            self.root.tk.call(f'{popdown}.f.l', 'configure',
                              '-background', INPUT, '-foreground', TEXT,
                              '-borderwidth', 0, '-highlightthickness', 0,
                              '-selectborderwidth', 0, '-relief', 'flat')
            # Tk uses one pixel of grid padding around the listbox; set its
            # other edges to zero, while keeping the same background behind it.
            self.root.tk.call('grid', 'configure', f'{popdown}.f.l', '-pady', 0)
            self.root.tk.call('grid', 'configure', f'{popdown}.f.sb',
                              '-padx', 0, '-pady', 0)
            if scrollbar_style:
                self.root.tk.call(f'{popdown}.f.sb', 'configure',
                                  '-style', scrollbar_style)
        except tk.TclError:
            # Older Tk variants still keep a working native dropdown.
            pass

    def _frame(self, parent, bg=PANEL, **kwargs):
        return tk.Frame(parent, bg=bg, highlightbackground=LINE,
                        highlightcolor=LINE, highlightthickness=1, bd=0,
                        takefocus=0, **kwargs)

    @staticmethod
    def _label(parent, text, fg=TEXT, size=10, bold=False, **kwargs):
        return tk.Label(parent, text=text, bg=parent.cget('bg'), fg=fg,
                        font=('Segoe UI', size, 'bold' if bold else 'normal'), **kwargs)

    def _button(self, parent, title, command, primary=False):
        color = '#1b65d3' if primary else '#20384e'
        button = tk.Button(parent, text=title, command=command, bg=color,
                           fg='white', activebackground='#357fe6' if primary else '#2d4b67',
                           activeforeground='white', disabledforeground='#8092a3',
                           relief='flat', bd=0, padx=12, pady=6,
                           font=('Segoe UI', 9), cursor='hand2')
        return button

    def _make_stat(self, parent, heading, var, color, detail_rows):
        """Large wattage with compact detail rows."""
        card = self._frame(parent)
        # Reduce wasted space between the heading and the large wattage;
        # this raises the details and leaves more room at the bottom.
        self._label(card, heading, size=11, bold=True, bd=0, pady=0).pack(
            anchor='w', padx=12, pady=(3, 0))
        # Keep the existing wattage font size.
        self._label(card, '', fg=color, size=20, bold=True, bd=0, pady=0,
                    textvariable=var).pack(fill='x')
        for row_items in detail_rows:
            line = tk.Frame(card, bg=PANEL)
            line.pack(fill='x', padx=12)
            if len(row_items) == 1:
                caption, value_var = row_items[0]
                self._label(line, caption, fg=MUTED, size=8).pack(side='left')
                self._label(line, '', textvariable=value_var, size=8).pack(side='right')
            else:
                for side, (caption, value_var) in zip(('left', 'right'), row_items):
                    pair = tk.Frame(line, bg=PANEL)
                    pair.pack(side=side)
                    self._label(pair, caption, fg=MUTED, size=8).pack(side='left')
                    self._label(pair, '', textvariable=value_var,
                                size=8).pack(side='left', padx=(4, 0))
        return card

    def _build(self):
        # Fixed main panel without whole-window scrollbars.
        # Only the tables have vertical scrollbars.
        compact = self.root.winfo_screenheight() < 900
        main = tk.Frame(self.root, bg=BG, padx=9, pady=8)
        main.pack(fill='both', expand=True)
        main.grid_columnconfigure(0, weight=1)
        # The chart and log retain a fixed height of about six
        # text rows; extra window height goes to the inverter table.
        main.grid_rowconfigure(1, weight=1)
        main.grid_rowconfigure(2, weight=0)
        main.grid_rowconfigure(3, weight=0)

        heading = tk.Frame(main, bg=BG)
        heading.grid(row=0, column=0, sticky='ew', pady=(0, 4 if compact else 7))
        self._label(heading, 'APSystems ECU-R Control (Modbus TCP)',
                    size=14, bold=True).pack(side='left')

        # Two fixed areas: measurements/inverters on the left, controls on the right.
        # The first three status panels share the width of the inverter table.
        dashboard = tk.Frame(main, bg=BG)
        dashboard.grid(row=1, column=0, sticky='nsew', pady=(0, SECTION_GAP))
        dashboard.grid_columnconfigure(0, weight=1)
        dashboard.grid_columnconfigure(1, minsize=CONTROL_COLUMN_WIDTH)
        dashboard.grid_rowconfigure(1, weight=1, minsize=(255 if not compact else 205))

        # The first three panels divide the width of the inverter table.
        # Connection stays exactly as wide as the Power Control sidebar;
        # their left edges therefore line up.
        top = tk.Frame(dashboard, bg=BG)
        top.grid(row=0, column=0, columnspan=2, sticky='ew',
                 pady=(0, SECTION_GAP))
        for column in (0, 2, 4):
            top.grid_columnconfigure(column, weight=1, uniform='dashboard_left_cards')
        top.grid_columnconfigure(6, minsize=CONTROL_COLUMN_WIDTH)
        for column in (1, 3, 5):
            top.grid_columnconfigure(column, minsize=SECTION_GAP)
        # All four panels share enough height for the three Inverter settings.
        top.grid_rowconfigure(0, minsize=124)
        self._make_stat(top, 'DC Total', self.sum_dc_var, GREEN, (
            (('PV input 1', self.dc1_total_var),),
            (('PV input 2', self.dc2_total_var),),
            (('Active PV inputs', self.active_inputs_var),),
        )).grid(row=0, column=0, sticky='nsew')
        self._make_stat(top, 'AC Total', self.sum_ac_var, BLUE, (
            (('Conversion efficiency', self.conversion_ratio_var),),
            (('Current power output', self.nominal_used_var),),
            (('Active inverters', self.producing_units_var),),
        )).grid(row=0, column=2, sticky='nsew')

        # The user chooses the inverter type before connecting. Its nominal
        # rating affects watt estimates, not the Modbus request or write values.
        # Scan interval remains adjustable while polling; the ID range is fixed
        # at Connect. Last measurement and cycle time stay above the table.
        cycle = self._frame(top)
        cycle.grid(row=0, column=4, sticky='nsew')
        self._label(cycle, 'Inverter', size=11, bold=True).pack(
            anchor='w', padx=12, pady=(4, 1))
        scan_fields = tk.Frame(cycle, bg=PANEL)
        scan_fields.pack(fill='x', padx=12, pady=(2, 0))
        scan_fields.grid_columnconfigure(0, weight=1)
        self._label(scan_fields, 'Model:', size=9, fg=MUTED).grid(
            row=0, column=0, sticky='w', pady=(0, 5))
        # Use the same width and grid column for all three selectors, so
        # their left edges and dropdown arrows line up exactly.
        selector_width = 7
        self.inverter_model_combo = ttk.Combobox(
            scan_fields, textvariable=self.inverter_model_var,
            values=tuple(INVERTER_RATINGS_W), width=selector_width,
            state='readonly', style='Compact.TCombobox')
        self.inverter_model_combo.grid(row=0, column=1,
                                       sticky='w', pady=(0, 5), padx=(0, 5))
        self._label(scan_fields, 'Scan interval (s):', size=9, fg=MUTED).grid(
            row=1, column=0, sticky='w', pady=(0, 5))
        self.interval_combo = ttk.Combobox(
            scan_fields, textvariable=self.interval_var, values=SCAN_PAUSE_OPTIONS,
            width=selector_width, state='readonly', style='Compact.TCombobox')
        self.interval_combo.grid(row=1, column=1, sticky='w', pady=(0, 5), padx=(0, 5))
        self.interval_combo.bind('<<ComboboxSelected>>', self._pause_changed)
        self._label(scan_fields, 'Scan through ID:', size=9, fg=MUTED).grid(
            row=2, column=0, sticky='w')
        # All valid Unit IDs; always start at 1; free-form entry is disabled.
        self.scan_max_combo = ttk.Combobox(
            scan_fields, textvariable=self.scan_max_var,
            values=tuple(str(unit) for unit in range(SCAN_START_ID, SCAN_MAX_ID_ALLOWED + 1)),
            width=selector_width, state='readonly', style='Compact.TCombobox')
        self.scan_max_combo.grid(row=2, column=1, sticky='w', padx=(0, 5))
        # All three comboboxes retain the same flat, dark popdown styling.
        self._flatten_combobox_dropdown(self.inverter_model_combo)
        self._flatten_combobox_dropdown(self.interval_combo)
        self._flatten_combobox_dropdown(self.scan_max_combo,
                                        'Scan.Vertical.TScrollbar')

        # Compact connection fields: IP and port entries have equal widths.
        # Connect/Disconnect sits on the right, centered between both rows.
        # Keep button width constant when its label changes.
        connection = self._frame(top)
        connection.grid(row=0, column=6, sticky='nsew')
        self._label(connection, 'Connection', size=11, bold=True).pack(
            anchor='w', padx=12, pady=(6, 3))
        address_fields = tk.Frame(connection, bg=PANEL)
        address_fields.pack(fill='x', padx=9, pady=(9, 0))
        address_fields.grid_columnconfigure(1, weight=1)
        self._label(address_fields, 'ECU-R:', fg=MUTED, size=9).grid(
            row=0, column=0, sticky='w', padx=(0, 5), pady=(0, 7))
        self.host_entry = tk.Entry(
            address_fields, textvariable=self.ip_var, bg=INPUT,
            fg=TEXT, insertbackground=TEXT, relief='flat', width=12,
            readonlybackground=INPUT, highlightbackground=LINE,
            highlightcolor=LINE, font=('Consolas', 9))
        self.host_entry.grid(row=0, column=1, sticky='ew', pady=(0, 7))
        self._label(address_fields, 'Port:', fg=MUTED, size=9).grid(
            row=1, column=0, sticky='w', padx=(0, 5))
        self.port_entry = tk.Entry(
            address_fields, textvariable=self.port_var, bg=INPUT,
            fg=TEXT, insertbackground=TEXT, relief='flat', width=12,
            readonlybackground=INPUT, highlightbackground=LINE,
            highlightcolor=LINE, font=('Consolas', 9))
        self.port_entry.grid(row=1, column=1, sticky='ew')
        self.connect_button = self._button(
            address_fields, 'Connect', self.toggle_connection)
        self.connect_button.configure(font=('Segoe UI', 8), width=10, padx=5, pady=5)
        self.connect_button.grid(row=0, column=2, rowspan=2,
                                 sticky='e', padx=(16, 0))
        # Connect/Disconnect remains the visible connection indicator.

        # Power Control spans the full height of the inverter overview.
        # There is no separate Inverter settings panel in this sidebar.
        sidebar = tk.Frame(dashboard, bg=BG, width=CONTROL_COLUMN_WIDTH)
        sidebar.grid(row=1, column=1, sticky='nsew')
        sidebar.grid_propagate(False)
        sidebar.grid_columnconfigure(0, weight=1)
        sidebar.grid_rowconfigure(0, weight=1)

        table_card = self._frame(dashboard)
        table_card.grid(row=1, column=0, sticky='nsew', padx=(0, SECTION_GAP))
        header = tk.Frame(table_card, bg=PANEL)
        header.pack(fill='x', padx=10, pady=(4 if compact else 7, 2 if compact else 3))
        self._label(header, 'Inverters', size=11, bold=True).pack(side='left')
        # The last completed scan has compact details on the right.
        header_measurements = tk.Frame(header, bg=PANEL)
        header_measurements.pack(side='right')
        for caption, variable in (
                ('Last reading:', self.last_measurement_var),
                ('Cycle time:', self.cycle_duration_var)):
            info = tk.Frame(header_measurements, bg=PANEL)
            info.pack(side='left', padx=(0, 18) if caption == 'Last reading:' else (0, 0))
            self._label(info, caption, size=9, fg=MUTED).pack(side='left')
            self._label(info, '', size=9, textvariable=variable).pack(side='left', padx=(5, 0))

        table_box = tk.Frame(table_card, bg=PANEL)
        table_box.pack(fill='both', expand=True, padx=5, pady=(0, 4 if compact else 6))
        cols = ('scan', 'id', 'serial', 'status', 'operating', 'dc1', 'dc2', 'dct', 'ac',
                'mode', 'limit', 'time_ms', 'time')
        self.table = ttk.Treeview(table_box, columns=cols, show='headings',
                                  style='Monitor.Treeview', selectmode='browse',
                                  height=(6 if self.root.winfo_screenheight() >= 900 else 5))
        # Distribute available width, leaving separation between
        # AC / limiting and read duration / timestamp.
        # Left-align text, right-align numbers, center short status values.
        specs = [
            ('scan', '', 20, 'center'),  # Marker for the current/next Unit ID.
            ('id', 'ID', 30, 'center'),
            ('serial', 'Serial number', 104, 'w'),
            ('status', 'Status', 55, 'center'),
            ('operating', 'Operating mode', 112, 'w'),
            ('dc1', 'DC1', 62, 'e'),
            ('dc2', 'DC2', 62, 'e'),
            ('dct', 'DC total', 83, 'e'),
            ('ac', 'AC', 71, 'e'),
            ('mode', 'Limiting', 84, 'center'),
            ('limit', 'Limit', 64, 'e'),
            ('time_ms', 'Read time', 69, 'e'),
            ('time', 'Last', 67, 'center')
        ]
        for c, title, width, anchor in specs:
            self.table.heading(c, text=title, anchor=anchor)
            self.table.column(c, width=width,
                              minwidth=24 if c == 'scan' else (104 if c == 'serial'
                                        else (30 if c == 'id' else 45)),
                              anchor=anchor, stretch=c in ('serial', 'operating', 'dct', 'ac'))
        self.table.tag_configure('ok', foreground=TEXT)
        self.table.tag_configure('err', foreground=RED)
        self.table.tag_configure('waiting', foreground=MUTED)
        self.table.tag_configure('limited', foreground=YELLOW)
        tscroll = ttk.Scrollbar(table_box, orient='vertical',
                                style='Dark.Vertical.TScrollbar', command=self.table.yview)
        # All columns fit within the default window width.
        # No horizontal scrollbar; retain the vertical one.
        self.table.configure(yscrollcommand=tscroll.set)
        self.table.pack(side='left', fill='both', expand=True)
        tscroll.pack(side='right', fill='y')
        self.table.bind('<<TreeviewSelect>>', self._on_table_select)
        # Windows-style tooltip when hovering over the column heading.
        self.operating_mode_help = OperatingModeHelpTip(self.table)

        control = self._frame(sidebar)
        control.grid(row=0, column=0, sticky='nsew')
        top_line = tk.Frame(control, bg=PANEL)
        top_line.pack(fill='x', padx=11, pady=(9, 6))
        self._label(top_line, 'Power Control', size=11, bold=True).pack(side='left')

        # This ECU-R applies limiting and production commands system-wide.
        # The selection determines ONLY which Modbus Unit ID receives the command.
        route_line = tk.Frame(control, bg=PANEL)
        route_line.pack(fill='x', padx=12, pady=(0, 4))
        self._label(route_line, 'Modbus via ID', fg=MUTED, size=9).pack(side='left')
        self._label(route_line, '', textvariable=self.route_id_var,
                    size=9, bold=True).pack(side='right')

        # Production controls sit directly below Modbus via ID,
        # as a separate section above power limiting.
        tk.Frame(control, bg=LINE, height=1).pack(fill='x', padx=12, pady=(0, 8))
        # The two buttons touch; only the read-back Conn value
        # determines which button is visually selected.
        production_line = tk.Frame(control, bg=PANEL)
        production_line.pack(fill='x', padx=12, pady=(0, 2))
        self._label(production_line, 'Inverter production', size=9,
                    bold=True).pack(anchor='w')
        production_status_row = tk.Frame(production_line, bg=PANEL)
        production_status_row.pack(fill='x', pady=(2, 0))
        self._label(production_status_row, 'All inverters to', fg=MUTED,
                    size=8).pack(side='left')
        # OFF/ON is aligned with 'All inverters to' on the same row.
        production_pair = tk.Frame(production_status_row, bg=LINE, padx=1, pady=1)
        production_pair.pack(side='right')
        button_style = dict(
            fg='white', activeforeground='white',
            relief='flat', bd=0, highlightthickness=0,
            padx=9, pady=3, font=('Segoe UI', 8, 'bold'),
            takefocus=1, cursor='arrow')
        self.production_off_button = tk.Button(
            production_pair, text='OFF', command=lambda: self.confirm_production_state(0),
            **button_style)
        self.production_off_button.pack(side='left', padx=(0, 1))
        self.production_on_button = tk.Button(
            production_pair, text='ON', command=lambda: self.confirm_production_state(1),
            **button_style)
        self.production_on_button.pack(side='left')

        # Power limiting is the second, separate control section.
        tk.Frame(control, bg=LINE, height=1).pack(fill='x', padx=12, pady=(4, 8))
        self._label(control, 'Inverter power', size=9, bold=True).pack(
            anchor='w', padx=12, pady=(0, 6))
        for caption, variable in (
                ('Limiting', self.reported_mode_var),
                ('Register limit', self.reported_watts_var)):
            line = tk.Frame(control, bg=PANEL)
            line.pack(fill='x', padx=12, pady=(0, 4))
            self._label(line, caption, fg=MUTED, size=9).pack(side='left')
            self._label(line, '', textvariable=variable, size=9, bold=True).pack(side='right')

        limit_line = tk.Frame(control, bg=PANEL)
        limit_line.pack(fill='x', padx=12, pady=(8, 3))
        self._label(limit_line, 'New limit', size=9, bold=True).pack(side='left')
        # The new W and % values are small, muted, and not bold.
        limit_values = tk.Frame(control, bg=PANEL)
        limit_values.pack(fill='x', padx=12, pady=(0, 3))
        self._label(limit_values, '', size=9, bold=False, fg=MUTED,
                    textvariable=self.target_watts_var).pack(side='left')
        self._label(limit_values, '', size=9, bold=False, fg=MUTED,
                    textvariable=self.target_percent_var).pack(side='right')

        # Each slider step represents 1% of the detected inverters' rated power.
        # The slider only changes the GUI; it never writes Modbus registers.
        self.limit_scale = tk.Scale(
            control, from_=0, to=100, resolution=1, showvalue=False,
            orient='horizontal', variable=self.target_var,
            bg=PANEL, fg=TEXT, troughcolor=INPUT, activebackground=PANEL,
            highlightthickness=0, bd=0, relief='flat', sliderrelief='raised',
            sliderlength=19, length=211, width=19)
        self.limit_scale.pack(fill='x', padx=10, pady=(0, 7))

        action_row = tk.Frame(control, bg=PANEL)
        action_row.pack(fill='x', padx=12, pady=(0, 8))
        self.apply_button = self._button(action_row, 'Set limit',
                                         self.confirm_set)
        self.apply_button.pack(side='left', fill='x', expand=True, padx=(0, 4))
        self.disable_button = self._button(action_row, 'Disable limit',
                                           self.confirm_disable)
        self.disable_button.pack(side='left', fill='x', expand=True)

        graph_card = self._frame(main)
        graph_card.grid(row=2, column=0, sticky='nsew', pady=(0, SECTION_GAP))
        graph_head = tk.Frame(graph_card, bg=PANEL)
        graph_head.pack(fill='x', padx=10, pady=(2 if compact else 4, 0))
        self._label(graph_head, 'Power history', size=11, bold=True).pack(side='left')
        self._button(graph_head, 'Clear graph', self.clear_graph).pack(side='right')
        self.graph_span_combo = ttk.Combobox(
            graph_head, textvariable=self.graph_span_var,
            values=('10 minutes', '30 minutes', '60 minutes', '120 minutes'),
            width=14, state='readonly', style='Dark.TCombobox')
        self.graph_span_combo.pack(side='right', padx=(7, 7))
        self._flatten_combobox_dropdown(self.graph_span_combo)
        self._label(graph_head, 'Time range', fg=MUTED, size=9).pack(side='right')
        # Six equal table-row heights in pixels, independent of window size.
        graph_height = 6 * self.table_row_height
        self.graph = tk.Canvas(graph_card, bg=PANEL_DARK, bd=0, highlightthickness=0,
                               height=graph_height)
        self.graph.pack(fill='both', expand=True, padx=8, pady=(3 if compact else 5, 4 if compact else 8))
        self.graph.bind('<Configure>', lambda _event: self.draw_graph())
        self.graph_span_var.trace_add('write', lambda *_args: self.draw_graph())

        log_card = self._frame(main)
        log_card.grid(row=3, column=0, sticky='nsew')
        log_head = tk.Frame(log_card, bg=PANEL)
        log_head.pack(fill='x', padx=10, pady=(2 if compact else 5, 1 if compact else 3))
        self._label(log_head, 'Modbus log', size=11, bold=True).pack(side='left')
        self._button(log_head, 'Save log', self.save_log).pack(side='right')
        self._button(log_head, 'Clear log', self.clear_log).pack(side='right', padx=(0, 6))
        lbox = tk.Frame(log_card, bg=PANEL)
        lbox.pack(fill='both', expand=True, padx=6, pady=(0, 3 if compact else 6))
        lcols = ('stamp', 'unit', 'request', 'response', 'elapsed')
        self.log_table = ttk.Treeview(lbox, columns=lcols, show='headings',
                                      style='Log.Treeview', height=6)
        # Compact fixed columns leave as much space as possible for Response.
        # The full Response is also available by double-clicking a row.
        for col, title, width, anchor in (
            ('stamp', 'Time', 108, 'w'),
            ('unit', 'ID', 36, 'center'),
            ('request', 'Request', 158, 'w'),
            ('response', 'Response', 510, 'w'),
            ('elapsed', 'Time (ms)', 76, 'e')):
            self.log_table.heading(col, text=title, anchor=anchor)
            self.log_table.column(col, width=width, minwidth=42, anchor=anchor,
                                  stretch=col == 'response')
        for name, color in (('pending', MUTED), ('ok', TEXT), ('error', RED)):
            self.log_table.tag_configure(name, foreground=color)
        ly = ttk.Scrollbar(lbox, orient='vertical',
                           style='Dark.Vertical.TScrollbar', command=self.log_table.yview)
        # The log columns fit the default window; scroll vertically only.
        self.log_table.configure(yscrollcommand=ly.set)
        self.log_table.grid(row=0, column=0, sticky='nsew')
        self.log_table.bind('<Double-1>', self._show_log_details)
        ly.grid(row=0, column=1, sticky='ns')
        lbox.grid_rowconfigure(0, weight=1)
        lbox.grid_columnconfigure(0, weight=1)

    def emit(self, record):
        # Only FC03/FC16 transactions belong in the Modbus command log.
        # REQUEST and RESPONSE share their request_id.
        if isinstance(record, LogRecord) and record.function in ('FC03', 'FC16'):
            self.events.put(('log', record))


    def toggle_connection(self):
        """One button to manually start or stop the monitoring connection."""
        if self.connected:
            self.disconnect()
        elif not self.connecting and not self.disconnect_requested:
            self.connect_and_discover()

    def _set_address_fields(self, state):
        """Lock IP, port, inverter model, and scan range on Connect/Disconnect."""
        self._set_widget_state(self.host_entry, state)
        self._set_widget_state(self.port_entry, state)
        # The combobox returns to readonly, not editable, on disconnect.
        self._set_widget_state(self.scan_max_combo,
                               'readonly' if state == 'normal' else 'disabled')
        self._set_widget_state(self.inverter_model_combo,
                               'readonly' if state == 'normal' else 'disabled')

    def connect_and_discover(self):
        global ECU_IP, ECU_PORT
        if (self.connected or self.connecting or self.disconnect_requested
                or self.busy or self.pending_command or self.confirm_active):
            return
        ip = self.ip_var.get().strip()
        try:
            ipaddress.IPv4Address(ip)
            port = int(self.port_var.get().strip())
            if not 1 <= port <= 65535:
                raise ValueError
        except ValueError:
            messagebox.showerror('Connection settings',
                                 'Enter a valid IPv4 address and port (1..65535).',
                                 parent=self.root)
            return
        try:
            scan_max_id = parse_scan_max_id(self.scan_max_var.get())
        except ValueError as exc:
            messagebox.showerror('Invalid scan range', str(exc), parent=self.root)
            self.scan_max_combo.focus_set()
            return
        selected_model = self.inverter_model_var.get()
        if selected_model not in INVERTER_RATINGS_W:
            messagebox.showerror('Invalid inverter model',
                                 'Select a supported DS3 inverter model.',
                                 parent=self.root)
            self.inverter_model_combo.focus_set()
            return
        self.inverter_model = selected_model
        self.rated_watts_per_inverter = INVERTER_RATINGS_W[selected_model]
        self.scan_max_id = scan_max_id  # Fixed for this connection and device discovery scan.
        ECU_IP, ECU_PORT = ip, port
        self.stop_requested.clear()
        self._set_scan_unit(None)
        self.first_poll_after_connect = True
        self.connecting = True
        self.disconnect_requested = False
        self.devices.clear()
        self.states.clear()
        self.errors.clear()
        self.duplicate_serials.clear()
        self.block_capabilities.clear()
        self.selected_unit = None
        self.history.clear()
        self._replace_table_devices()
        self._clear_totals()
        self.last_measurement_var.set('---')
        self.cycle_duration_var.set('---')
        self.next_poll_due = float('inf')
        self.draw_graph()
        self._set_address_fields('readonly')
        self._launch('discover')

    def disconnect(self):
        """Stop starting new commands; safely finish the current read."""
        if (not self.connected or self.disconnect_requested or self.confirm_active
                or self.pending_command is not None or self.current_task == 'command'):
            return
        self.disconnect_requested = True
        self.connected = False
        self.stop_requested.set()
        self._set_scan_unit(None)
        self.first_poll_after_connect = False
        self.discovery_pending = False
        self.next_poll_due = float('inf')
        if not self.busy:
            self._finish_disconnect()
        else:
            self._update_controls()

    def _finish_disconnect(self):
        """End the session, retaining saved Modbus log entries."""
        if self.busy:
            return
        self.disconnect_requested = False
        self.connecting = False
        self.connected = False
        self._set_scan_unit(None)
        self.discovery_pending = False
        self.first_poll_after_connect = False
        self.next_poll_due = float('inf')
        self.poll_started = None
        self.devices.clear()
        self.states.clear()
        self.errors.clear()
        self.duplicate_serials.clear()
        self.block_capabilities.clear()
        self.selected_unit = None
        self._replace_table_devices()
        self._clear_totals()
        self.last_measurement_var.set('---')
        self.cycle_duration_var.set('---')
        self._set_address_fields('normal')
        self._update_controls()

    def _launch(self, task, command=None):
        if self.busy:
            return False
        self.busy = True
        self.current_task = task
        if task == 'command':
            # No polling takes place while writing.
            self._set_scan_unit(None)
        self._update_controls()
        gap = None
        if task == 'poll':
            # The first scan after Connect has no intermediate delays. Then
            # use the selected delay, including between complete scan cycles.
            # Read this value only in the GUI thread.
            gap = 0.0 if self.first_poll_after_connect else self._interval()
            self.first_poll_after_connect = False
            self.poll_started = time.monotonic()
            self.next_poll_due = float('inf')
        threading.Thread(target=self._worker, args=(task, command, gap), daemon=True).start()
        return True

    def _worker(self, task, command, gap):
        try:
            if task == 'discover':
                self._worker_discover()
            elif task == 'poll':
                self._worker_poll(gap)
            elif task == 'command':
                self._worker_command(command)
            else:
                raise ValueError('Unknown worker task.')
        except Exception as exc:
            # Unexpected programming errors must not leave the worker locked.
            self.events.put(('task_error', (task, f'{type(exc).__name__}: {exc}')))
        finally:
            self.events.put(('done', task))

    def _worker_discover(self):
        # Check TCP reachability once before discovery to avoid waiting
        # at every possible Unit ID when offline. Close this socket immediately.
        with socket.create_connection((ECU_IP, ECU_PORT), TIMEOUT_SECONDS) as probe:
            probe.settimeout(TIMEOUT_SECONDS)
        self.events.put(('tcp_connected', None))
        found = []
        for unit in range(SCAN_START_ID, self.scan_max_id + 1):
            if self.stop_requested.is_set():
                break
            try:
                # Fast discovery: 100 ms for TCP connect and each FC03 response.
                # Regular scans and FC16 writes retain their 3-second timeout.
                with LoggedModbusTCP(unit, self.emit,
                                     timeout_seconds=DISCOVERY_TIMEOUT_SECONDS) as client:
                    identity = read_identity(client)
                    found.append(identity)
            except (OSError, ValueError, ModbusError):
                continue
        if not self.stop_requested.is_set():
            self.events.put(('discovered', found))

    def _worker_poll(self, gap):
        """Poll Unit IDs in sequence; pause for gap seconds (first scan: 0).

        After the last ID, the GUI schedules the next scan after the
        configured delay. Disconnect interrupts the delay immediately."""
        snapshot = tuple(sorted(self.devices.values(), key=lambda device: device.unit_id))
        for index, identity in enumerate(snapshot):
            if self.stop_requested.is_set():
                break
            # Show the next Unit ID already during the delay.
            # All GUI updates pass through the event queue.
            self.events.put(('poll_position', identity.unit_id))
            if index and self.stop_requested.wait(gap):
                break
            if self.stop_requested.is_set():
                break
            start = time.monotonic()
            unit = identity.unit_id
            try:
                with LoggedModbusTCP(unit, self.emit) as client:
                    state = read_monitor_state(
                        client, identity, self.block_capabilities[unit])
                duration = (time.monotonic() - start) * 1000
                self.events.put(('reading', (unit, state, None, duration)))
            except (OSError, ValueError, ModbusError) as exc:
                duration = (time.monotonic() - start) * 1000
                self.events.put(('reading', (unit, None, str(exc), duration)))

    def _worker_command(self, command):
        identity = command.identity
        unit = identity.unit_id
        try:
            with LoggedModbusTCP(unit, self.emit) as client:
                before = read_state(client)
                if command.action in ('start', 'stop'):
                    ensure_safe_production_write(before, identity, command.duplicates)
                else:
                    ensure_safe_to_write(before, identity, command.duplicates)
                if command.action == 'set':
                    raw, _ = percent_to_raw(command.percent, before.scale)
                    # Write register values only when they actually differ.
                    # An enabled limit with the same value does not need FC16.
                    if before.raw_limit != raw:
                        verify_identity_now(client, identity)
                        self._write_checked(client, identity, REG_WMAXLIMPCT, raw)
                    if before.enabled != 1:
                        verify_identity_now(client, identity)
                        self._write_checked(client, identity, REG_WMAXLIM_ENA, 1)
                elif command.action == 'disable':
                    if before.enabled != 0:
                        verify_identity_now(client, identity)
                        self._write_checked(client, identity, REG_WMAXLIM_ENA, 0)
                elif command.action in ('start', 'stop'):
                    target_conn = 1 if command.action == 'start' else 0
                    # Avoid redundant FC16 if an external change has already
                    # set the requested production state.
                    if before.conn != target_conn:
                        verify_identity_now(client, identity)
                        self._write_checked(client, identity, REG_CONN, target_conn)
                else:
                    raise ValueError('Unknown write operation.')
                after = read_state(client)
                if after.serial != identity.serial or after.model != identity.model:
                    raise ModbusError('Identity changed after writing!')
                if command.action == 'set' and (after.raw_limit != raw or after.enabled != 1):
                    raise ModbusError('Limit or limiting status was not stable after the write.')
                if command.action == 'disable' and after.enabled != 0:
                    raise ModbusError('Disabling the limit was not confirmed.')
                if command.action in ('start', 'stop') and after.conn != target_conn:
                    raise ModbusError('Production status 40188 was not confirmed.')
                self.events.put(('command_state', (unit, after)))
        except (OSError, ValueError, ModbusError) as exc:
            self.events.put(('command_error', str(exc)))

    def _write_checked(self, client, identity, address, value):
        verification = write_and_verify(client, address, value, identity)
        if not verification.acknowledged:
            self.events.put(('write_warning',
                f'Register {address}: no valid FC16 response, but after reconnecting '
                'the requested value was read back. The command was not retried.'))
        elif verification.reconnected:
            self.events.put(('write_warning',
                f'Register {address}: reconnected after a read error and '
                'successfully verified the register value.'))

    def _drain_events(self):
        count = 0
        while count < 450:
            try:
                name, data = self.events.get_nowait()
            except queue.Empty:
                break
            count += 1
            # When closing, wait only for the worker to finish.
            # Do not open dialogs, start commands, or update widgets.
            if self.closing:
                if name == 'done' and self.current_task == data:
                    self.busy = False
                    self.current_task = None
                    self.root.destroy()
                    return
                continue
            if name == 'log':
                self._append_log(data)
            elif name == 'tcp_connected':
                if not self.disconnect_requested:
                    self.connecting = False
                    self.connected = True
                    self._update_controls()
            elif name == 'discovered':
                if not self.disconnect_requested:
                    self._apply_discovery(data)
            elif name == 'poll_position':
                if self.connected and not self.disconnect_requested and self.current_task == 'poll':
                    self._set_scan_unit(data)
            elif name == 'reading':
                unit, state, error, elapsed_ms = data
                self.states[unit] = state
                self.errors[unit] = error
                self._show_device_row(unit, elapsed_ms)
                # Refresh AC and DC totals after each individual inverter read.
                # Other IDs retain their most recently read values.
                self._refresh_totals()
                if unit == self.selected_unit:
                    self._update_control_status()
            elif name == 'command_state':
                unit, state = data
                self.states[unit] = state
                self.errors.pop(unit, None)
                self._show_device_row(unit, None)
                self._refresh_totals()
                self._update_control_status()
            elif name == 'command_error':
                messagebox.showerror('Modbus write error',
                    'The command may have been partially executed. Do not retry automatically.\n\n'
                    + data, parent=self.root)
            elif name == 'write_warning':
                messagebox.showwarning('Modbus read-back verification', data,
                                       parent=self.root)
            elif name == 'task_error':
                task, error = data
                if task == 'discover':
                    self.connecting = False
                    self.connected = False
                    self.last_measurement_var.set('---')
                    self.cycle_duration_var.set('---')
                    self._set_address_fields('normal')
                    if not self.disconnect_requested:
                        messagebox.showerror(
                            'Connection failed',
                            f'Could not connect to the ECU or read the inverters.\n\n{error}',
                            parent=self.root)
                elif task == 'poll':
                    # An unexpected read error must not remain invisible.
                    self.next_poll_due = float('inf')
                    self.stop_requested.set()
                    messagebox.showerror(
                        'Scan cycle stopped',
                        f'The polling cycle failed.\n\n{error}\n\n'
                        'Disconnect and reconnect to continue.',
                        parent=self.root)
            elif name == 'done':
                if name and self.current_task == data:
                    self.busy = False
                    self.current_task = None
                    if self.disconnect_requested:
                        self._finish_disconnect()
                    else:
                        if data == 'discover':
                            self.connecting = False
                            self.discovery_pending = bool(self.connected and self.devices)
                        elif data == 'poll':
                            self._finish_poll()
                            # During automatic polling, move the scan marker immediately
                            # to the first ID and keep it there during the delay.
                            self._mark_next_round()
                        elif data == 'command':
                            # After a confirmed write, poll all IDs again.
                            self.next_poll_due = 0.0
                            self._mark_next_round()
                        self._run_pending()
                        self._update_controls()
        self.root.after(75 if count >= 450 else 120, self._drain_events)

    def _apply_discovery(self, found):
        self.devices = {ident.unit_id: ident for ident in found}
        self.block_capabilities = {ident.unit_id: {} for ident in found}
        counts = {}
        for identity in found:
            counts[identity.serial] = counts.get(identity.serial, 0) + 1
        self.duplicate_serials = {s for s, count in counts.items() if count > 1}
        self.states = {uid: None for uid in self.devices}
        self.errors = {uid: None for uid in self.devices}
        self.selected_unit = (10 if 10 in self.devices else
                              next(iter(self.devices), None))
        self._replace_table_devices()
        if self.duplicate_serials:
            messagebox.showwarning(
                'Duplicate serial number',
                'The same serial number was read from multiple Modbus IDs. '
                'Writes to those IDs are blocked.', parent=self.root)
        if not found:
            self.next_poll_due = float('inf')
            messagebox.showwarning(
                'No inverters found',
                f'The ECU-R is reachable, but no supported DS3 inverters were found at Modbus IDs {SCAN_START_ID} through '
                f'{self.scan_max_id}.',
                parent=self.root)
        self._update_controls()
        self._update_control_status()

    def _replace_table_devices(self):
        self.scan_unit = None
        self.table.delete(*self.table.get_children())
        for unit, ident in sorted(self.devices.items()):
            self.table.insert('', 'end', iid=str(unit), values=('', unit, ident.serial, 'WAITING',
                              '---', '---', '---', '---', '---',
                              '---', '---', '---', '---'), tags=('waiting',))
        if self.selected_unit is not None:
            self.table.selection_set(str(self.selected_unit))
        # A new session or ID list requires synchronization with the
        # actual register limit; never write automatically.
        self.target_initialized = False
        self.target_var.set(100)
        self.target_watts_var.set(nominal_limit_label(100, len(self.devices), self.rated_watts_per_inverter))
        self._update_control_status()

    def _set_scan_unit(self, unit):
        """Move the scan marker without redrawing other table values.

        The marker points to the next ID even during the configured delay.
        It is independent of the row selected for power control."""
        previous = self.scan_unit
        if previous == unit:
            return
        self.scan_unit = unit
        if previous is not None and self.table.exists(str(previous)):
            self.table.set(str(previous), 'scan', '')
        if unit is not None and self.table.exists(str(unit)):
            self.table.set(str(unit), 'scan', '▶')

    def _mark_next_round(self):
        """Show the first ID while waiting for the next automatic scan.

        For manual/stopped polling and queued write commands the marker
        stays empty. Works with nonconsecutive Unit IDs."""
        if (self.connected and not self.disconnect_requested
                and self.devices
                and self.pending_command is None and not self.confirm_active
                and not self.stop_requested.is_set()
                and math.isfinite(self.next_poll_due)):
            self._set_scan_unit(min(self.devices))
        else:
            self._set_scan_unit(None)

    def _show_device_row(self, unit, elapsed):
        if not self.table.exists(str(unit)):
            return
        state = self.states.get(unit)
        error = self.errors.get(unit)
        serial = self.devices[unit].serial
        if state is None:
            values = ('▶' if self.scan_unit == unit else '',
                      unit, serial, 'NO DATA' if error else 'WAITING', '---',
                      '---', '---', '---', '---', '---', '---',
                      f'{elapsed:.0f} ms' if elapsed is not None else '---', timestamp()[:8])
            tag = 'err' if error else 'waiting'
        else:
            pct = (f'{format_percent(state.limit_percent)}%'
                   if state.limit_percent is not None else '---')
            values = ('▶' if self.scan_unit == unit else '',
                      unit, serial, 'OK', format_operating_state(state.operating_state),
                      table_watts(state.dc1_watts), table_watts(state.dc2_watts),
                      table_watts(state.dc_total_watts), table_watts(state.watts),
                      limit_mode(state), pct,
                      f'{elapsed:.0f} ms' if elapsed is not None else '---', timestamp()[:8])
            tag = 'limited' if state.enabled == 1 else 'ok'
        self.table.item(str(unit), values=values, tags=(tag,))

    def _refresh_totals(self):
        """Refresh the dashboard after every read without additional Modbus requests.

        Each ID uses its most recently successful state. If the latest read
        fails, exclude that ID immediately from aggregate totals.
        Measurement times may differ between IDs during a scan."""
        found = len(self.devices)
        valid = [state for state in self.states.values() if state is not None]
        ac = [state.watts for state in valid]
        dc = [state.dc_total_watts for state in valid]
        ac_valid = sum(w is not None for w in ac)
        dc_valid = sum(w is not None for w in dc)
        ac_sum = sum((w for w in ac if w is not None), Decimal(0))
        dc_sum = sum((w for w in dc if w is not None), Decimal(0))
        dc1_sum = sum((state.dc1_watts for state in valid
                       if state.dc1_watts is not None), Decimal(0))
        dc2_sum = sum((state.dc2_watts for state in valid
                       if state.dc2_watts is not None), Decimal(0))

        # Show aggregate counts and percentages only when every inverter
        # has a valid measurement. A missing Modbus reading must not
        # be interpreted as zero production.
        ac_complete = found > 0 and ac_valid == found
        dc_complete = found > 0 and dc_valid == found
        input_count = sum(
            (state.dc1_watts > 0) + (state.dc2_watts > 0)
            for state in valid
            if state.dc1_watts is not None and state.dc2_watts is not None
        ) if dc_complete else None
        producer_count = sum(state.watts > 0 for state in valid) if ac_complete else None
        if ac_complete and dc_complete and dc_sum > 0:
            # An instantaneous AC/DC ratio, not a guaranteed efficiency figure.
            ratio = (ac_sum * 100 / dc_sum).quantize(
                Decimal('0.1'), rounding=ROUND_HALF_UP)
            ratio_label = f'{ratio}%'
        else:
            ratio_label = '---'
        if ac_complete:
            # Use the model manually selected for this connection.
            discovered_nominal_watts = found * self.rated_watts_per_inverter
            nominal = (ac_sum * 100 / Decimal(discovered_nominal_watts)).quantize(
                Decimal('0.1'), rounding=ROUND_HALF_UP)
            nominal_label = f'{nominal}%'
        else:
            nominal_label = '---'

        totals = (
            (self.sum_ac_var, f'{watts_number(ac_sum)} W' if ac_valid else '--- W'),
            (self.sum_dc_var, f'{watts_number(dc_sum)} W' if dc_valid else '--- W'),
            (self.dc1_total_var, f'{watts_number(dc1_sum)} W' if dc_valid else '---'),
            (self.dc2_total_var, f'{watts_number(dc2_sum)} W' if dc_valid else '---'),
            (self.active_inputs_var,
             f'{input_count} / {found * 2}' if input_count is not None else '---'),
            (self.producing_units_var,
             f'{producer_count} / {found}' if producer_count is not None else '---'),
            (self.conversion_ratio_var, ratio_label),
            (self.nominal_used_var, nominal_label),
        )
        # Avoid unnecessary redraws when a value has not changed.
        for variable, new_text in totals:
            if variable.get() != new_text:
                variable.set(new_text)

        return found, len(valid), ac_valid, dc_valid, ac_sum, dc_sum

    def _finish_poll(self):
        if self.poll_started is None:
            return
        elapsed = time.monotonic() - self.poll_started
        found, _, ac_valid, dc_valid, ac_sum, dc_sum = self._refresh_totals()
        stamp = datetime.now()
        self.last_measurement_var.set(f'{stamp:%H:%M:%S}')
        self.cycle_duration_var.set(f'{elapsed:.1f} s')
        full = (found > 0 and ac_valid == found and dc_valid == found)
        self.history.append((stamp.timestamp(), float(dc_sum) if full else None,
                             float(ac_sum) if full else None))
        self._trim_history()
        self.draw_graph()
        self._update_control_status()
        # There is no extra fixed gap between complete scans: use the
        # same adjustable delay from the last ID to the first ID of the next scan.
        self.next_poll_due = (
            time.monotonic() + self._interval()
            if (self.connected and self.devices and
                    not self.stop_requested.is_set()) else float('inf'))

    def _clear_totals(self):
        self.sum_ac_var.set('--- W')
        self.sum_dc_var.set('--- W')
        for var in (self.dc1_total_var, self.dc2_total_var):
            var.set('---')
        for var in (self.active_inputs_var, self.producing_units_var,
                    self.conversion_ratio_var, self.nominal_used_var):
            var.set('---')

    def _poll_tick(self):
        if (self.connected and not self.disconnect_requested and
                not self.stop_requested.is_set() and
                not self.busy and not self.confirm_active and not self.pending_command
                and self.devices
                and time.monotonic() >= self.next_poll_due):
            self._launch('poll')
        self.root.after(100, self._poll_tick)

    def _interval(self):
        try:
            value = float(self.interval_var.get().replace(',', '.'))
            if 0.1 <= value <= 5 and math.isfinite(value):
                return value
        except ValueError:
            pass
        return SCAN_PAUSE_DEFAULT

    def _pause_changed(self, _event=None):
        if self.connected and self.devices and not self.busy:
            self.next_poll_due = time.monotonic() + self._interval()


    def _run_pending(self):
        if (not self.connected or self.disconnect_requested or self.busy
                or self.confirm_active):
            return
        if self.pending_command is not None:
            command, self.pending_command = self.pending_command, None
            self._launch('command', command)
        elif self.discovery_pending:
            self.discovery_pending = False
            self._launch('poll')


    def _on_table_select(self, _event=None):
        selected = self.table.selection()
        if selected:
            unit = int(selected[0])
            if unit in self.devices and unit != self.selected_unit:
                self._select_unit(unit)

    def _select_unit(self, unit):
        if unit not in self.devices or self.confirm_active or self.pending_command:
            return
        self.selected_unit = unit
        self.table.selection_set(str(unit))
        # When changing the selected Unit ID, the slider may adopt the
        # associated stored limit. During regular polling, preserve any
        # slider value selected by the user but not yet sent.
        self.target_initialized = False
        self._update_control_status()
        self._update_controls()

    def _on_slider_changed(self, *_args):
        """Update local W and % labels only; never initiate a write."""
        pct = min(100, max(0, self.target_var.get()))
        self.target_watts_var.set(nominal_limit_label(pct, len(self.devices), self.rated_watts_per_inverter))
        self.target_percent_var.set(f'{pct}%')

    def _set_target_from_state(self, state):
        pct = slider_percent_from_state(state)
        if pct is None:
            return
        self.target_var.set(pct)
        self.target_watts_var.set(nominal_limit_label(pct, len(self.devices), self.rated_watts_per_inverter))
        self.target_initialized = True

    def _update_control_status(self):
        self.route_id_var.set(str(self.selected_unit) if self.selected_unit is not None else '---')
        state = self.states.get(self.selected_unit)
        if state is None:
            self.reported_mode_var.set('---')
            self.reported_watts_var.set('---')
            self._draw_production_buttons()
            return
        self.reported_mode_var.set(limit_mode(state))
        pct = state.limit_percent
        if pct is not None and pct.is_finite() and 0 <= pct <= 100:
            # Calculated register setting, NOT measured AC output.
            self.reported_watts_var.set(
                f'{nominal_limit_label(pct, len(self.devices), self.rated_watts_per_inverter)} ({format_percent(pct)}%)')
        else:
            self.reported_watts_var.set('Unknown')
        if not self.target_initialized:
            self._set_target_from_state(state)
        self._draw_production_buttons()

    def _draw_production_buttons(self):
        """Highlight OFF/ON strictly from the read-back Conn register value."""
        state = self.states.get(self.selected_unit)
        conn = state.conn if state is not None and state.conn in (0, 1) else None
        can_click = self.production_write_enabled and conn in (0, 1)
        display = (conn, can_click)
        if display == self.production_drawn:
            return
        self.production_drawn = display
        neutral = '#20384e'
        for value, button, selected_color, muted_color in (
                (0, self.production_off_button, '#934952', '#69474f'),
                (1, self.production_on_button, '#237c52', '#2d614c')):
            selected = conn == value
            color = (selected_color if can_click else muted_color) if selected else neutral
            button.configure(
                bg=color, activebackground=color,
                fg='white' if selected else '#aebfce',
                disabledforeground='#e1e8ee' if selected else '#8294a4',
                cursor='hand2' if can_click else 'arrow')
            self._set_widget_state(
                button, 'normal' if can_click else 'disabled')

    @staticmethod
    def _set_widget_state(widget, wanted):
        """Avoid unnecessary Tk/ttk widget redraws."""
        if str(widget.cget('state')) != wanted:
            widget.configure(state=wanted)

    def _update_controls(self):
        identity = self.devices.get(self.selected_unit)
        state = self.states.get(self.selected_unit)
        can_write = (self.connected and not self.disconnect_requested and
                     identity is not None and state is not None
                     and not self.pending_command and not self.confirm_active
                     and self.current_task not in ('command', 'discover'))
        if can_write:
            try:
                ensure_safe_to_write(state, identity, self.duplicate_serials)
            except ValueError:
                can_write = False
        # The user may confirm a command during a regular polling cycle;
        # execution is safely queued until the current scan finishes.
        for b in (self.apply_button, self.disable_button):
            self._set_widget_state(b, 'normal' if can_write else 'disabled')
        self._set_widget_state(self.limit_scale, 'normal' if can_write else 'disabled')
        # Production has a separate check; the limit registers do not
        # need to be valid to switch Conn.
        can_production_write = (self.connected and not self.disconnect_requested and
                                identity is not None and state is not None
                                and not self.pending_command and not self.confirm_active
                                and self.current_task not in ('command', 'discover'))
        if can_production_write:
            try:
                ensure_safe_production_write(state, identity, self.duplicate_serials)
            except ValueError:
                can_production_write = False
        self.production_write_enabled = can_production_write
        self._draw_production_buttons()
        # Redraw Connect/Disconnect only when its state changes.
        label = 'Disconnect' if self.connected else 'Connect'
        if self.connect_button.cget('text') != label:
            self.connect_button.configure(text=label)
        # Disconnect remains available during FC03 polling/discovery,
        # but not during FC16 writing or a confirmation dialog.
        allow_connection = (not self.confirm_active and self.pending_command is None
                            and not self.disconnect_requested and
                            (self.current_task not in ('command',)
                             and (self.current_task != 'discover' or self.connected)))
        self._set_widget_state(self.connect_button,
                               'normal' if allow_connection else 'disabled')
        # Only lock/unlock IP, port, and scan range when connecting/disconnecting,
        # never during individual polls, to prevent flickering.

    def _validate_command(self, production=False):
        if not self.connected or self.disconnect_requested:
            raise ValueError('Connect to the ECU manually first.')
        identity = self.devices.get(self.selected_unit)
        state = self.states.get(self.selected_unit)
        if identity is None or state is None:
            raise ValueError('No valid status is available for the selected inverter.')
        if production:
            ensure_safe_production_write(state, identity, self.duplicate_serials)
        else:
            ensure_safe_to_write(state, identity, self.duplicate_serials)
        return identity

    def confirm_production_state(self, desired):
        """Require confirmation for OFF/ON without preemptively coloring a button."""
        if not self.production_write_enabled or desired not in (0, 1):
            return
        try:
            identity = self._validate_command(production=True)
            current = self.states[identity.unit_id].conn
        except ValueError as exc:
            messagebox.showerror('Production control unavailable',
                                 str(exc), parent=self.root)
            return
        if current == desired:
            return  # Already confirmed by Modbus; avoid a redundant FC16 write.
        action = 'stop' if desired == 0 else 'start'
        word = 'OFF' if desired == 0 else 'ON'
        msg = (f'ECU: {ECU_IP}:{ECU_PORT}\n'
               f'Modbus via Unit ID: {identity.unit_id}\n'
               f'Model: {identity.model}\nSerial number: {identity.serial}\n\n'
               f'Switch production {word} for the entire installation?\n'
               f'FC16: register 40188 = {desired}.\n\n'
               'Important: on the tested ECU-R, this command switches all '
               'inverters together, including units not found in the scan, '
               'even when addressed to a single Unit ID.\n\n'
               'The command will be sent once and read back for verification. Continue?')
        self._confirm_and_queue('Inverter production (FC16)', msg,
                                Command(action, identity, None,
                                        frozenset(self.duplicate_serials)))

    def confirm_set(self):
        try:
            identity = self._validate_command()
            raw, percent = percent_to_raw(str(self.target_var.get()),
                                           self.states[identity.unit_id].scale)
        except ValueError as exc:
            messagebox.showerror('Invalid limit', str(exc), parent=self.root)
            return
        count = len(self.devices)
        target_watts = nominal_limit_label(percent, count, self.rated_watts_per_inverter)
        rated_watts = watt_label(count * self.rated_watts_per_inverter)
        msg = (f'ECU: {ECU_IP}:{ECU_PORT}\n'
               f'Modbus via Unit ID: {identity.unit_id}\n'
               f'Model: {identity.model}\nSerial number: {identity.serial}\n\n'
               f'Estimated nominal limit: {target_watts} '
               f'({format_percent(percent)}% of {rated_watts})\n'
               f'Based on {count} detected {self.inverter_model} inverters '
               f'at {self.rated_watts_per_inverter} W each.\n'
               f'Register 40189 = {raw}\n'
               'Enable power limiting (40193 = 1)\n\n'
               'Important: the ECU-R may apply the percentage system-wide, '
               'including inverters missed by the scan. The watt estimate '
               'does not guarantee the physical AC output; changes may take '
               'several minutes.\n\n'
               'Only changed register values will be written. Continue?')
        if percent == 0:
            msg += '\n\n0 W does not guarantee physical AC shutdown.'
        self._confirm_and_queue('Set limit (FC16)', msg,
                                Command('set', identity, str(percent),
                                        frozenset(self.duplicate_serials)))

    def confirm_disable(self):
        try:
            identity = self._validate_command()
        except ValueError as exc:
            messagebox.showerror('Cannot disable limit', str(exc), parent=self.root)
            return
        msg = (f'ECU: {ECU_IP}:{ECU_PORT}\n'
               f'Modbus via Unit ID: {identity.unit_id}\n'
               f'Serial number: {identity.serial}\n\n'
               'Disable power limiting (40193 = 0).\n'
               'The stored percentage value will be preserved.\n\n'
               'This ECU-R applies the limit system-wide.\n\n'
               'Execute this write operation?')
        self._confirm_and_queue('Disable power limiting (FC16)', msg,
                                Command('disable', identity, None,
                                        frozenset(self.duplicate_serials)))

    def _confirm_and_queue(self, title, message, command):
        if self.confirm_active or self.pending_command is not None:
            return
        self.confirm_active = True
        self._update_controls()
        try:
            approved = messagebox.askyesno(title, message,
                                           icon='warning', default='no', parent=self.root)
        finally:
            self.confirm_active = False
        if approved:
            self.pending_command = command
            self._run_pending()
        self._update_controls()

    def _trim_history(self):
        cutoff = datetime.now().timestamp() - MAX_GRAPH_SECONDS - 300
        while self.history and self.history[0][0] < cutoff:
            self.history.popleft()

    def clear_graph(self):
        self.history.clear()
        self.draw_graph()

    @staticmethod
    def _nice_ceiling(ymax):
        if ymax <= 0:
            return 100
        raw = ymax / 4
        scale = 10 ** math.floor(math.log10(raw))
        step = next((t * scale for t in (1, 2, 5, 10) if t * scale >= raw), 10 * scale)
        return step * 4

    def draw_graph(self):
        c = self.graph
        c.delete('all')
        width, height = c.winfo_width(), c.winfo_height()
        if width < 120 or height < 90:
            return
        left, right, top, bottom = 62, 12, 9, 26
        plot_width = width - left - right
        plot_height = height - top - bottom
        time_span = int(self.graph_span_var.get().split()[0]) * 60
        newest = self.history[-1][0] if self.history else datetime.now().timestamp()
        oldest = newest - time_span
        data = [record for record in self.history if record[0] >= oldest]
        scale_y = self._nice_ceiling(max((max(dc or 0, ac or 0) for _, dc, ac in data),
                                          default=0))
        for i in range(5):
            y = top + plot_height * i / 4
            c.create_line(left, y, width-right, y, fill='#294052', width=1)
            label = int(scale_y * (4-i) / 4)
            c.create_text(left-8, y, text=f'{label:,}',
                          fill=MUTED, anchor='e', font=('Segoe UI', 9))
        for i in range(7):
            x = left + plot_width * i / 6
            c.create_line(x, top, x, top+plot_height, fill='#203548')
            t = datetime.fromtimestamp(oldest + time_span * i / 6)
            c.create_text(x, height-11, text=t.strftime('%H:%M'),
                          fill=MUTED, font=('Segoe UI', 9))
        c.create_text(12, top+12, text='W', anchor='w', fill=MUTED,
                      font=('Segoe UI', 9))
        if not data:
            c.create_text(width/2, height/2, text='Waiting for the first complete scan cycle',
                          fill=MUTED, font=('Segoe UI', 11))
            return
        for index, color in ((1, GREEN), (2, BLUE)):
            segment = []
            for record in data:
                t, dc, ac = record
                value = record[index]
                if value is None:
                    if len(segment) >= 4:
                        c.create_line(*segment, fill=color, width=2, smooth=False)
                    segment = []
                    continue
                x = left + (t-oldest) / time_span * plot_width
                y = top + plot_height * (1 - max(0, value) / scale_y)
                segment.extend((x, y))
            if len(segment) >= 4:
                c.create_line(*segment, fill=color, width=2, smooth=False)
            elif len(segment) == 2:
                x, y = segment
                c.create_oval(x-3, y-3, x+3, y+3, fill=color, outline=color)

    def _append_log(self, event):
        # REQUEST and RESPONSE share one request_id and one log row.
        row = self.log_index.get(event.request_id)
        if row is None:
            if event.status != 'pending':
                # E.g. a response arriving after 'Clear log': do not append an orphan row.
                return
            if len(self.log_records) == MAX_LOG_RECORDS:
                old = self.log_records.popleft()
                self.log_index.pop(old.request_id, None)
            self.log_records.append(event)
            self.log_index[event.request_id] = event
            row = event
        elif event.status != 'pending':
            row.response = event.response
            row.elapsed_ms = event.elapsed_ms
            row.status = event.status
        self._insert_log(row)

    def _insert_log(self, row):
        iid = str(row.request_id)
        values = (row.stamp, str(row.unit), row.request, row.response,
                  f'{row.elapsed_ms:.1f}' if row.elapsed_ms is not None else '')
        if self.log_table.exists(iid):
            self.log_table.item(iid, values=values, tags=(row.status,))
        else:
            self.log_table.insert('', 'end', iid=iid, values=values, tags=(row.status,))
            self.log_visible += 1
            if self.log_visible > MAX_LOG_ROWS:
                children = self.log_table.get_children()
                for old_id in children[:self.log_visible - MAX_LOG_ROWS]:
                    self.log_table.delete(old_id)
                self.log_visible = len(self.log_table.get_children())
        # Automatically follow the newest Modbus transaction, without a checkbox.
        if self.log_table.exists(iid):
            self.log_table.see(iid)

    def _show_log_details(self, event):
        """Show complete register data even when it cannot fit in one table row."""
        item_id = self.log_table.identify_row(event.y)
        if not item_id:
            return
        try:
            record = self.log_index.get(int(item_id))
        except ValueError:
            return
        if record is None:
            return

        popup = tk.Toplevel(self.root)
        popup.title(f'Modbus transaction - ID {record.unit}')
        popup.configure(bg=BG)
        popup.geometry('760x330')
        popup.minsize(540, 260)
        popup.transient(self.root)

        area = tk.Frame(popup, bg=PANEL, padx=12, pady=11)
        area.pack(fill='both', expand=True, padx=8, pady=8)
        self._label(area, f'{record.stamp}  |  ID {record.unit}',
                    size=11, bold=True).pack(anchor='w', pady=(0, 8))
        self._label(area, f'Request: {record.request}', size=10).pack(anchor='w')
        duration = (f'{record.elapsed_ms:.1f} ms'
                    if record.elapsed_ms is not None else 'No response yet')
        self._label(area, f'Elapsed time: {duration}',
                    size=10, fg=MUTED).pack(anchor='w', pady=(2, 8))
        self._label(area, 'Response (full)', size=10, bold=True).pack(anchor='w')
        full_response = record.response
        if full_response.startswith('[') and full_response.endswith(']'):
            words = full_response[1:-1].split(',')
            # Wrap register words across several lines for readability.
            shown_response = '\n'.join('  '.join(words[i:i + 10])
                                        for i in range(0, len(words), 10))
        else:
            shown_response = full_response
        response_frame = tk.Frame(area, bg=PANEL_DARK)
        response_frame.pack(fill='both', expand=True, pady=(5, 7))
        box = tk.Text(response_frame, bg=PANEL_DARK,
                      fg=RED if record.status == 'error' else TEXT,
                      insertbackground=TEXT, font=('Consolas', 10), wrap='word',
                      relief='flat', height=7, padx=8, pady=7)
        scrollbar = ttk.Scrollbar(response_frame, orient='vertical',
                                  style='Dark.Vertical.TScrollbar', command=box.yview)
        box.configure(yscrollcommand=scrollbar.set)
        box.pack(side='left', fill='both', expand=True)
        scrollbar.pack(side='right', fill='y')
        box.insert('1.0', shown_response)
        box.configure(state='disabled')
        buttons = tk.Frame(area, bg=PANEL)
        buttons.pack(fill='x')

        def copy_full():
            popup.clipboard_clear()
            popup.clipboard_append(full_response)

        self._button(buttons, 'Copy response', copy_full).pack(side='left')
        self._button(buttons, 'Close', popup.destroy).pack(side='right')

    def clear_log(self):
        self.log_records.clear()
        self.log_index.clear()
        self.log_table.delete(*self.log_table.get_children())
        self.log_visible = 0

    def save_log(self):
        if not self.log_records:
            messagebox.showinfo('Save log', 'There are no transactions yet.', parent=self.root)
            return
        path = filedialog.asksaveasfilename(
            parent=self.root, title='Save Modbus log',
            initialfile=f'apsystems_commandolog_{datetime.now():%Y%m%d_%H%M%S}.csv',
            defaultextension='.csv', filetypes=[('CSV file', '*.csv')])
        if not path:
            return
        try:
            with open(path, 'w', encoding='utf-8-sig', newline='') as f:
                writer = csv.writer(f, delimiter=';')
                writer.writerow(['timestamp', 'unit_id', 'request', 'response', 'time_ms'])
                for entry in self.log_records:
                    writer.writerow((entry.stamp, entry.unit, entry.request,
                                     entry.response,
                                     f'{entry.elapsed_ms:.3f}'
                                     if entry.elapsed_ms is not None else ''))
        except OSError as exc:
            messagebox.showerror('Save log', str(exc), parent=self.root)
            return


    def close(self):
        """End the session automatically after any in-progress Modbus operation.

        Scanning stops after its current Modbus request. An FC16 write that
        has already started is allowed to finish; a queued write is cancelled.
        Do not require a separate Disconnect confirmation."""
        if self.closing:
            return
        self.closing = True
        self.stop_requested.set()
        self.connected = False
        self.connecting = False
        self.disconnect_requested = True
        self.discovery_pending = False
        self.pending_command = None  # Cancel any write that has not started yet.
        self.next_poll_due = float('inf')
        self._set_scan_unit(None)
        if self.busy:
            self._update_controls()
            return
        self.root.destroy()


def main():
    root = tk.Tk()
    PowerMonitor(root)
    root.mainloop()


if __name__ == '__main__':
    main()
