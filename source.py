
import re
import sys
import json
import os
import threading
import time
import urllib.request
import copy
import struct
import queue
import functools
import itertools
import argparse
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
import ctypes
from ctypes import wintypes, c_long
try:
    _ntdll = ctypes.WinDLL('ntdll', use_last_error=True)
    _kernel32 = ctypes.windll.kernel32
    _NtSuspendProcess = _ntdll.NtSuspendProcess
    _NtSuspendProcess.argtypes = [wintypes.HANDLE]
    _NtSuspendProcess.restype = c_long
    _NtResumeProcess = _ntdll.NtResumeProcess
    _NtResumeProcess.argtypes = [wintypes.HANDLE]
    _NtResumeProcess.restype = c_long
    _IS_WINDOWS = True
except (AttributeError, OSError):
    _IS_WINDOWS = False
try:
    import pymem
    import pymem.process
    import pymem.pattern
    _HAS_PYMEM = True
except ImportError:
    _HAS_PYMEM = False
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
_RE_RBX_VERSION = re.compile('(version-[0-9a-fA-F]+)', re.IGNORECASE)
OFFSETS_URL = 'https://sites.google.com/view/sqosdkwaskwsdfoq'
def _http_get(url: str, timeout: int=12) -> str:
    req = urllib.request.Request(url, headers={'User-Agent': 'Bread/1.0'})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode('utf-8', errors='ignore')
PATTERNS = [b'H\x83\xec8H\x8b\r....L\x8d\x05', b'H\x83\xec(H\x8b\r....\xe8....H\x8b\r', b'H\x8b\r....H\x85\xc9t.H\x83\xc1']
FFLAG_PREFIXES: dict = {'DFString': 8, 'FString': 7, 'DFInt': 5, 'FInt': 4, 'DFLog': 5, 'FLog': 4, 'DFFlag': 6, 'FFlag': 5}
_PREFIX_SORTED = sorted(FFLAG_PREFIXES.items(), key=lambda kv: len(kv[0]), reverse=True)
OFF_FFLAG_VALUE_PTR = 192
OFF_MAP_END = 0
OFF_MAP_LIST = 16
OFF_MAP_MASK = 40
OFF_ENTRY_FORWARD = 8
OFF_ENTRY_STRING = 16
OFF_ENTRY_GET_SET = 48
OFF_STR_SIZE = 16
OFF_STR_ALLOC = 24
HF_SINGLETON_PTR = 134089288
FNV_BASIS = 14695981039346656037
FNV_PRIME = 1099511628211
PTR_MIN = 65536
PTR_MAX = 140737488355327
CHAIN_DEPTH_LIMIT = 64
BUCKET_COUNT = 32768
BUCKET_STRIDE = 16
BUCKET_ARRAY_SZ = BUCKET_COUNT * BUCKET_STRIDE
MAX_NODES_TOTAL = 1000000
MAX_CHAIN_DEPTH = 128
ENUM_CHUNK_SZ = 4096
GS_TYPE_OFFSET = 184
GS_TYPE_BOOL = 0
GS_TYPE_INT = 1
GS_TYPE_LOG = 2
GS_TYPE_STRING = 3
_RE_SINGLETON = re.compile('FFlagList::Pointer\\s*=\\s*(0x[0-9a-fA-F]+)')
_RE_SINGLETON2 = re.compile('namespace\\s+FFlagOffsets\\s*\\{[^}]*?uintptr_t\\s+FFlagList\\s*=\\s*(0x[0-9a-fA-F]+)', re.DOTALL)
_RE_VALUEGETSET = re.compile('namespace\\s+FFlagOffsets\\s*\\{[^}]*?uintptr_t\\s+ValueGetSet\\s*=\\s*(0x[0-9a-fA-F]+)', re.DOTALL)
_RE_FLAGTOVALUE = re.compile('namespace\\s+FFlagOffsets\\s*\\{[^}]*?uintptr_t\\s+FlagToValue\\s*=\\s*(0x[0-9a-fA-F]+)', re.DOTALL)
_RE_FLAG = re.compile('uintptr_t\\s+(\\w+)\\s*=\\s*(0x[0-9a-fA-F]+)')
_STRUCT_NAMES = frozenset({'MapSize', 'StringOffset', 'FirstNode', 'StringCapacity', 'List', 'NodeForward', 'LastNode', 'EntrySize', 'NodePair', 'StringSize', 'FFlagList', 'MapBuckets', 'NodeBackward', 'FlagToValue', 'ValueGetSet', 'Pair', 'MapMask', 'MapList', 'FLogSetGet', 'MapEnd', 'GetSet', 'ToFlag', 'BucketStride', 'StringAlloc', 'ToValue', 'Key'})
C = {'bg': '#1C0F06', 'surface': '#2A1608', 'card': '#3E2210', 'border': '#7A4E20', 'accent': '#F5C418', 'accent2': '#D4A020', 'success': '#4CAF50', 'error': '#EF5350', 'warning': '#FF9800', 'text': '#FFF3DC', 'dim': '#A07840', 'btn_text': '#1C0F06'}
_SESSION_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bread_session.json')
@dataclass
class InjectionConfig:
    """\n    Controls dual-mode injection behaviour.\n\n    timed_mode   : bool  — True = timed batch, False = instant (default)\n    batch_size   : int   — flags per batch in timed mode (default 100)\n    batch_delay  : float — seconds between batches in timed mode (default 5.0)\n    fast_throttle: float — inter-write sleep in instant mode (default 0, safe)\n    """
    timed_mode: bool = False
    batch_size: int = 100
    batch_delay: float = 5.0
    fast_throttle: float = 0.0
def load_flags_from_file(path: str) -> dict:
    stat_size = os.path.getsize(path)
    with open(path, 'r', encoding='utf-8') as f:
        raw = json.load(f)
    if not isinstance(raw, dict):
        raise ValueError('JSON must be a flat {flag: value} object.')
    else:
        if stat_size <= 524288:
            return {k: str(v) for k, v in raw.items()}
        else:
            result = {}
            for k, v in raw.items():
                result[k] = str(v)
            return result
_PROCESS_QUERY_LIMITED = 4096
_PROCESS_VM_READ = 16
_STILL_ACTIVE = 259
def find_roblox_validated() -> int:
    # irreducible cflow, using cdg fallback
    if not _HAS_PYMEM or not _IS_WINDOWS:
        return 0
    else:
        candidates = []
        try:
            for p in pymem.process.list_processes():
                name = p.szExeFile.decode('utf-8', 'ignore').lower()
                if 'robloxplayerbeta.exe' in name and p.th32ProcessID:
                        candidates.append(p.th32ProcessID)
        except Exception:
            return 0
        k32 = ctypes.windll.kernel32
        for pid in candidates:
            pass
    h = k32.OpenProcess(_PROCESS_QUERY_LIMITED | _PROCESS_VM_READ, False, pid)
    if not h:
        continue
    exit_code = ctypes.c_ulong(0)
    alive = k32.GetExitCodeProcess(h, ctypes.byref(exit_code)) and exit_code.value == _STILL_ACTIVE
    if not alive:
        pass
    k32.CloseHandle(h)
    continue
    buf = (ctypes.c_char * 8)()
    written = ctypes.c_size_t(0)
    readable = k32.ReadProcessMemory(h, ctypes.c_void_p(4096), buf, 8, ctypes.byref(written))
    k32.CloseHandle(h)
    if readable and written.value > 0:
        return pid
    return 0
    except Exception:
        pass
    pass
    pass
class BatchInjector:
    pass
    def __init__(self, core: 'BreadCore', config: InjectionConfig, log_cb=None, progress_cb=None, done_cb=None):
        self.core = core
        self.config = config
        self._log = log_cb or (lambda msg, lvl='info': None)
        self._progress = progress_cb or (lambda done, total, ok, fail: None)
        self._done = done_cb or (lambda ok, fail: None)
        self._abort_evt = threading.Event()
        self._thread = None
        self.running = False
    def start(self, flags: dict):
        if self.running:
            return
        else:
            self._abort_evt.clear()
            self.running = True
            self._thread = threading.Thread(target=self._run, args=(flags,), daemon=True)
            self._thread.start()
    def abort(self):
        self._abort_evt.set()
    def _run(self, flags: dict):
        # irreducible cflow, using cdg fallback
        total_flags = len(flags)
        total_ok = 0
        total_fail = 0
        if not self.config.timed_mode:
            self._log(f'Instant injection — {total_flags:,} flags (single batch).', 'accent')
            def _pcb(done, total, ok, fail):
                self._progress(done, total, ok, fail)
            ok, fail, lines = self.core.inject(flags, 'singleton', progress_cb=_pcb)
            for line in lines:
                self._log(line, 'ok' if line.startswith('[OK]') else 'err')
            total_ok = ok
            total_fail = fail
            bsize = max(1, self.config.batch_size)
            bdelay = max(0.0, self.config.batch_delay)
            items = list(flags.items())
            chunks = [dict(items[i:i + bsize]) for i in range(0, len(items), bsize)]
            n_chunks = len(chunks)
            self._log(f'Timed batch injection — {total_flags:,} flags, {n_chunks} batch(es) × {bsize} flags, {bdelay:.1f}s inter-batch delay.', 'accent')
            done_so_far = 0
            for batch_idx, chunk in enumerate(chunks, start=1):
                    if self._abort_evt.is_set():
                        self._log(f'Injection aborted after batch {batch_idx - 1}/{n_chunks}.', 'warn')
                        break
                    self._log(f'Batch {batch_idx}/{n_chunks} — {len(chunk)} flags…', 'info')
                    batch_start = done_so_far
                    def _pcb(done, total, ok, fail, _base=batch_start, _tot=total_flags):
                        self._progress(_base + done, _tot, ok, fail)
                    ok, fail, lines = self.core.inject(chunk, 'singleton', progress_cb=_pcb)
                    done_so_far += len(chunk)
                    total_ok += ok
                    total_fail += fail
                    for line in lines:
                        self._log(line, 'ok' if line.startswith('[OK]') else 'err')
                    self._log(f'Batch {batch_idx}/{n_chunks} complete — {ok} OK / {fail} FAIL.', 'ok' if fail == 0 else 'warn')
                    if batch_idx < n_chunks and (not self._abort_evt.is_set()):
                            self._log(f'Waiting {bdelay:.1f}s before next batch…', 'info')
                            deadline = time.monotonic() + bdelay
                            while time.monotonic() < deadline:
                                if not self._abort_evt.is_set():
                                    time.sleep(min(0.25, deadline - time.monotonic()))
                            self.running = False
                            self._log(f'After fallback Results:\n  Applied: {total_ok:,}\n  Failed:  {total_fail:,}', 'ok' if total_fail == 0 else 'warn')
                            self._done(total_ok, total_fail)
            except Exception as exc:
                    self._log(f'BatchInjector fatal error: {exc}', 'err')
                    total_fail += total_flags - total_ok
@functools.lru_cache(maxsize=8192)
def _parse_flag_key(raw_key: str) -> tuple:
    for prefix, plen in _PREFIX_SORTED:
        if raw_key.startswith(prefix):
            return (raw_key[plen:], prefix)
    return (raw_key, '')
def _u64(data: bytes, off: int) -> int:
    if off + 8 > len(data):
        return 0
    else:
        return struct.unpack_from('<Q', data, off)[0]
def _ptr_valid(p: int) -> bool:
    return PTR_MIN <= p <= PTR_MAX
def _strip_prefix(name: str) -> str:
    for prefix, plen in _PREFIX_SORTED:
        if name.startswith(prefix):
            return name[plen:]
    return name
class OffsetStore:
    def __init__(self):
        self.singleton_ptr_rva = HF_SINGLETON_PTR
        self.to_flag_offset = OFF_ENTRY_GET_SET
        self.to_value_offset = OFF_FFLAG_VALUE_PTR
        self.flag_rvas = {}
        self.roblox_version = ''
        self.source = 'hardcoded (message_4)'
        self.last_updated = 'never'
        self._lock = threading.Lock()
    def set_roblox_version(self, ver: str):
        with self._lock:
            self.roblox_version = ver
    def _load_cpp_header(self, text: str) -> int:
        """\n        Parse both the legacy format (FFlagList::Pointer = 0x...) and the\n        message_(4).txt namespace format:\n\n            namespace FFlagOffsets {\n                uintptr_t FFlagList   = 0x7FE0A48;\n                uintptr_t ValueGetSet = 0x30;\n                uintptr_t FlagToValue = 0xC0;\n            }\n            namespace FFlags {\n                uintptr_t SomeFlagName = 0xABCD;\n                ...\n            }\n        """
        with self._lock:
            if (m := _RE_SINGLETON.search(text)):
                self.singleton_ptr_rva = int(m.group(1), 16)
            else:
                if (m := _RE_SINGLETON2.search(text)):
                    self.singleton_ptr_rva = int(m.group(1), 16)
            if (m := _RE_VALUEGETSET.search(text)):
                self.to_flag_offset = int(m.group(1), 16)
            if (m := _RE_FLAGTOVALUE.search(text)):
                self.to_value_offset = int(m.group(1), 16)
            rvas = {m.group(1): int(m.group(2), 16) for m in _RE_FLAG.finditer(text)}
            self.flag_rvas = rvas
            self.last_updated = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            return len(rvas)
    def fetch_and_load(self, version: str='') -> tuple:
        try:
            text = _http_get(OFFSETS_URL)
            count = self._load_cpp_header(text)
            with self._lock:
                self.source = 'remote (sites.google.com)'
            return (True, f'[remote] Loaded {count:,} flag RVAs from hosted file | singleton @ 0x{self.singleton_ptr_rva:X}', count)
        except Exception as remote_err:
            pass
        else:
            pass
        script_dir = os.path.dirname(os.path.abspath(__file__))
        candidates = [os.path.join(script_dir, 'message_(4).txt'), os.path.join(script_dir, 'message_4.txt'), os.path.join(script_dir, 'offsets.txt')]
        try:
            for fname in os.listdir(script_dir):
                if fname.lower().startswith('message_') and fname.lower().endswith('.txt'):
                        p = os.path.join(script_dir, fname)
                        if p not in candidates:
                            candidates.append(p)
        except Exception:
            pass
        for path in candidates:
            if os.path.isfile(path):
                try:
                    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                        text = f.read()
                    count = self._load_cpp_header(text)
                    with self._lock:
                        self.source = f'local file ({os.path.basename(path)})'
                    return (True, f'[local] Remote failed — loaded {count:,} RVAs from {os.path.basename(path)} | singleton @ 0x{self.singleton_ptr_rva:X}', count)
                except Exception:
                    pass
                else:
                    pass
        with self._lock:
            self.source = 'hardcoded (all sources failed)'
            self.last_updated = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        return (True, f'[fallback] Remote + local failed — using hardcoded offsets | singleton @ 0x{self.singleton_ptr_rva:X}', 0)
    def get_flag_rva(self, bare: str) -> int:
        with self._lock:
            return self.flag_rvas.get(bare, 0)
class BreadCore:
    """\n    Memory injection engine for Bread.\n    (formerly SkidStrapCore — renamed + offset fixes applied)\n    """
    def __init__(self, offsets: OffsetStore):
        self.offsets = offsets
        self.pm = None
        self.pid = 0
        self.base = 0
        self.module = None
        self.h_process = None
        self._detected_version = ''
        self._cached_singleton = 0
        self._map_end = 0
        self._map_list = 0
        self._map_mask = 0
        self._flag_cache = {}
        self._vptr_cache = {}
        self._hash_cache = {}
        self._in_bulk_inject = False
        self._lock = threading.Lock()
        self._write_lock = threading.Lock()
        self._map_generation = 0
        self._gs_generation = {}
        self._known_map_list = 0
        self._known_map_mask = 0
        self._game_transitioning = False
        self._transition_deadline = 0.0
    def find_roblox(self) -> int:
        pid = find_roblox_validated()
        if pid:
            return pid
        else:
            if not _HAS_PYMEM:
                return 0
            else:
                try:
                    for p in pymem.process.list_processes():
                        name = p.szExeFile.decode('utf-8', 'ignore').lower()
                        if 'robloxplayerbeta.exe' in name and p.th32ProcessID:
                            else:
                                return p.th32ProcessID
                except Exception:
                    return 0
                return 0
    def attach(self) -> bool:
        if not _HAS_PYMEM:
            return False
        else:
            pid = self.find_roblox()
            if not pid:
                return False
            else:
                try:
                    self.pid = pid
                    self.pm = pymem.Pymem(pid)
                    self.h_process = self.pm.process_handle
                    self.module = pymem.process.module_from_name(self.h_process, 'RobloxPlayerBeta.exe')
                    self.base = self.module.lpBaseOfDll
                    self._invalidate_cache()
                    self._detect_and_store_version()
                except Exception:
                    return False
                return True
    def _detect_and_store_version(self):
        try:
            buf_size = ctypes.c_ulong(1024)
            buf = ctypes.create_unicode_buffer(buf_size.value)
            _kernel32.QueryFullProcessImageNameW(self.h_process, 0, buf, ctypes.byref(buf_size))
            if (m := _RE_RBX_VERSION.search(buf.value)):
                ver = m.group(1).lower()
                self.offsets.set_roblox_version(ver)
                self._detected_version = ver
            else:
                self._detected_version = ''
        except Exception:
            self._detected_version = ''
    def detach(self):
        self.pm = None
        self.pid = 0
        self.base = 0
        self._invalidate_cache()
    def _invalidate_cache(self):
        self._cached_singleton = 0
        self._map_end = self._map_list = self._map_mask = 0
        self._flag_cache.clear()
        self._vptr_cache.clear()
        self._hash_cache.clear()
        self._gs_generation.clear()
        self._known_map_list = 0
        self._known_map_mask = 0
        self._map_generation += 1
    def _rb(self, addr: int, size: int) -> bytes:
        try:
            return self.pm.read_bytes(addr, size)
        except Exception:
            return b''
    def _rb_u64(self, addr: int) -> int:
        d = self._rb(addr, 8)
        return _u64(d, 0) if len(d) == 8 else 0
    def _write_raw(self, addr: int, data: bytes) -> bool:
        try:
            buf = (ctypes.c_char * len(data))(*data)
            written = ctypes.c_size_t(0)
            ok = _kernel32.WriteProcessMemory(self.h_process, ctypes.c_void_p(addr), buf, len(data), ctypes.byref(written))
            return bool(ok) and written.value == len(data)
        except Exception:
            return False
    def _verified_write(self, addr: int, data: bytes) -> bool:
        # irreducible cflow, using cdg fallback
        if self._game_transitioning and time.time() < self._transition_deadline:
            return False
        if self._in_bulk_inject:
            for _ in range(2):
                if self._write_raw(addr, data) and self._rb(addr, len(data)) == data:
                        return True
                return False
            with self._write_lock:
                pass
            for attempt in range(3):
                    suspended = False
                        if _IS_WINDOWS:
                            _NtSuspendProcess(self.h_process)
                            suspended = True
                        time.sleep(0.005)
                        if self._write_raw(addr, data) and self._rb(addr, len(data)) == data:
                                if suspended:
                                    try:
                                        _NtResumeProcess(self.h_process)
                                    except Exception:
                                        pass
                                return True
                                            if suspended:
                                                try:
                                                    _NtResumeProcess(self.h_process)
                                            time.sleep(0.01 * (attempt + 1))
                        return False
                        except Exception:
                                pass
                                pass
                                except Exception:
                                        pass
                                                try:
                                                    pass
    _EXTRA_PATTERNS = [b'H\x8b\r....H\x85\xc0\x0f\x84....', b'H\x8b\r....H\x85\xc0t.H\x8b\x00', b'H\x8b\r....H\x85\xc9t.H\x8b\x01', b'SH\x83\xec H\x8b\x1d....H\x85\xdb']
    _GS_OFFSETS = (48, 64)
    _ENTRY_READ_SZ = 88
    def _validate_singleton(self, ptr: int) -> bool:
        # irreducible cflow, using cdg fallback
        if not _ptr_valid(ptr):
            return False
        raw = self._rb(ptr + 8, 56)
        if len(raw) < 56:
            return False
            mask = _u64(raw, OFF_MAP_MASK)
            lst = _u64(raw, OFF_MAP_LIST)
            count = _u64(raw, 32)
            if mask == 0 or mask & mask + 1!= 0:
                return False
                    if not _ptr_valid(lst):
                        return False
                        if count < 1000:
                            return False
                            if len(self._rb(lst, 16)) < 16:
                                return False
                                return True
                                except Exception:
                                        return False
                                        pass
    def _get_singleton(self) -> int:
        # irreducible cflow, using cdg fallback
        if self._cached_singleton:
            if self._validate_singleton(self._cached_singleton):
                return self._cached_singleton
            else:
                self._cached_singleton = 0
                self._map_end = self._map_list = self._map_mask = 0
                self._invalidate_cache()
        if self.base:
            cand = self._rb_u64(self.base + self.offsets.singleton_ptr_rva)
            if self._validate_singleton(cand):
                self._cached_singleton = cand
                return cand
                            best_ptr = 0
                            best_count = 0
                            for pat in PATTERNS + self._EXTRA_PATTERNS:
                                try:
                                    hit = pymem.pattern.pattern_scan_module(self.h_process, self.module, pat)
                                    if not hit:
                                        continue
                                    else:
                                        if pat[0] == 72 and pat[1] == 131 and (pat[2] == 236):
                                            rel = self.pm.read_int(hit + 7)
                                            target = hit + 11 + rel
                                        else:
                                            if pat[0] == 83:
                                                rel = self.pm.read_int(hit + 8)
                                                target = hit + 12 + rel
                                            else:
                                                rel = self.pm.read_int(hit + 3)
                                                target = hit + 7 + rel
                                        ptr = self._rb_u64(target)
                                        if not self._validate_singleton(ptr):
                                            continue
                                        else:
                                            raw = self._rb(ptr + 8, 56)
                                            count = _u64(raw, 32)
                                            if count > best_count:
                                                best_count = count
                                                best_ptr = ptr
                                except Exception:
                                    pass
                            if best_ptr:
                                self._cached_singleton = best_ptr
                            return best_ptr
                    except Exception:
                            pass
                            pass
    def _get_map_header(self) -> bool:
        if self._map_mask:
            return True
        else:
            singleton = self._get_singleton()
            if not singleton:
                return False
            else:
                raw = self._rb(singleton + 8, 56)
                if len(raw) < 56:
                    return False
                else:
                    end = _u64(raw, OFF_MAP_END)
                    lst = _u64(raw, OFF_MAP_LIST)
                    mask = _u64(raw, OFF_MAP_MASK)
                    if mask == 0 or lst == 0:
                        return False
                    else:
                        if self._known_map_list and (lst!= self._known_map_list or mask!= self._known_map_mask):
                                self._flag_cache.clear()
                                self._vptr_cache.clear()
                                self._gs_generation.clear()
                                self._map_generation += 1
                        self._map_end = end
                        self._map_list = lst
                        self._map_mask = mask
                        self._known_map_list = lst
                        self._known_map_mask = mask
                        return True
    def _roblox_already_loaded(self) -> bool:
        # irreducible cflow, using cdg fallback
        sg = self._cached_singleton or self._get_singleton()
        if not sg:
            return False
            raw = self._rb(sg + 8, 56)
            mask = _u64(raw, OFF_MAP_MASK)
            lst = _u64(raw, OFF_MAP_LIST)
            return mask >= 4095 and lst!= 0
            except Exception:
                    return False
                    pass
    def _wait_for_ready(self, timeout: float=180.0, log_cb=None) -> bool:
        deadline = time.time() + timeout
        last_log = 0.0
        while time.time() < deadline:
            self._map_mask = 0
            if self._roblox_already_loaded():
                return True
            now = time.time()
            elapsed = int(now - (deadline - timeout))
            if log_cb and now - last_log >= 5.0:
                    log_cb(f'Waiting for Roblox FFlag map… ({elapsed}s elapsed)', 'info')
                    last_log = now
            time.sleep(0.5)
        return False
    def _fnv1a(self, s: str) -> int:
        cached = self._hash_cache.get(s)
        if cached is not None:
            return cached
        else:
            h = FNV_BASIS
            for b in s.encode('utf-8'):
                h = (h ^ b) * FNV_PRIME & 18446744073709551615
            self._hash_cache[s] = h
            return h
    def _parse_node_entry(self, node_addr: int, entry: bytes) -> list[tuple[str, int]]:
        # irreducible cflow, using cdg fallback
        results = []
        s = OFF_ENTRY_STRING
        sz_off = s + OFF_STR_SIZE
        al_off = s + OFF_STR_ALLOC
        if len(entry) < 48:
            return results
        else:
            str_size = _u64(entry, sz_off)
            str_alloc = _u64(entry, al_off)
            if not 2 <= str_size <= 512:
                    return results
            else:
                return results
        if str_alloc > 15:
            heap_ptr = _u64(entry, s)
            if not _ptr_valid(heap_ptr):
                return results
            else:
                raw = self._rb(heap_ptr, str_size)
                name = raw.decode('utf-8', errors='ignore').rstrip('\x00')
        else:
            name = entry[s:s + str_size].decode('utf-8', errors='ignore')
        if not name or len(name) < 2:
            return results
            for gs_off in self._GS_OFFSETS:
                if gs_off + 8 > len(entry):
                    continue
                else:
                    gs = _u64(entry, gs_off)
                    if not _ptr_valid(gs):
                        continue
                    else:
                        results.append((name, gs))
            return results
                except Exception:
                    return results
                        pass
    def _recover_rva(self, bare: str, gs: int) -> None:
        if not self.base or not _ptr_valid(gs):
            return None
        else:
            mod_size = getattr(self.module, 'SizeOfImage', 0)
            if not mod_size:
                mod_size = 268435456
            if not self.base <= gs < self.base + mod_size:
                    return
                else:
                    rva = gs - self.base
                    with self.offsets._lock:
                        if bare not in self.offsets.flag_rvas:
                            self.offsets.flag_rvas[bare] = rva
    def _infer_type_from_gs(self, gs: int) -> str:
        # irreducible cflow, using cdg fallback
        if not _ptr_valid(gs):
            return 'unknown'
        raw = self._rb(gs + GS_TYPE_OFFSET, 4)
        if len(raw) < 4:
            return 'unknown'
            discriminant = struct.unpack_from('<I', raw, 0)[0]
            if discriminant == GS_TYPE_BOOL:
                return 'bool'
                if discriminant == GS_TYPE_INT:
                    return 'int'
                    if discriminant == GS_TYPE_LOG:
                        return 'log'
                        if discriminant == GS_TYPE_STRING:
                            return 'string'
                            return 'unknown'
                            except Exception:
                                    return 'unknown'
                                    pass
    def _enumerate_all_flags(self, log_cb=None) -> int:
        # irreducible cflow, using cdg fallback
        if not self._get_map_header():
            return 0
        else:
            gen = self._map_generation
            added = 0
            nodes_total = 0
            visited = set()
            arr = self._rb(self._map_list, BUCKET_ARRAY_SZ)
            if len(arr) < BUCKET_ARRAY_SZ:
                actual_buckets = len(arr) // BUCKET_STRIDE
                if actual_buckets < 256:
                    if log_cb:
                        log_cb(f'Bucket array too small ({actual_buckets} buckets) — aborting enum', 'warn')
                    return 0
            else:
                actual_buckets = BUCKET_COUNT
            if log_cb:
                log_cb(f'Enumerating {actual_buckets:,} buckets (mask=0x{self._map_mask:X}, end=0x{self._map_end:X})…', 'info')
            for chunk_start in range(0, actual_buckets, ENUM_CHUNK_SZ):
                pass
        chunk_end = min(chunk_start + ENUM_CHUNK_SZ, actual_buckets)
        for bi in range(chunk_start, chunk_end):
            pass
        if nodes_total >= MAX_NODES_TOTAL:
            break
        off = bi * BUCKET_STRIDE
        node_ptr = 0
        for slot in [8, 0]:
            cand = _u64(arr, off + slot)
            if _ptr_valid(cand) and cand!= self._map_end:
                    node_ptr = cand
                    break
        if node_ptr:
            pass
        depth = 0
        while node_ptr and node_ptr!= self._map_end and (depth < MAX_CHAIN_DEPTH) and (nodes_total < MAX_NODES_TOTAL):
            pass
        if node_ptr in visited:
            break
        visited.add(node_ptr)
        depth += 1
        nodes_total += 1
        entry = self._rb(node_ptr, self._ENTRY_READ_SZ)
        if len(entry) < self._ENTRY_READ_SZ:
            break
        fwd = _u64(entry, OFF_ENTRY_FORWARD)
        for name, gs in self._parse_node_entry(node_ptr, entry):
            if name in self._flag_cache:
                continue
            else:
                bare = name
                for prefix, plen in _PREFIX_SORTED:
                    if name.startswith(prefix):
                        bare = name[plen:]
                        break
                self._flag_cache[bare] = gs
                self._gs_generation[bare] = gen
                self._recover_rva(bare, gs)
                added += 1
        if not fwd or fwd == node_ptr:
            continue
        node_ptr = fwd
        if not node_ptr:
            continue
        if node_ptr!= self._map_end and depth < MAX_CHAIN_DEPTH and (not nodes_total < MAX_NODES_TOTAL) and (not timeout < return):
            pass
        if nodes_total >= MAX_NODES_TOTAL:
            pass
        if log_cb:
            log_cb(f'Node cap ({MAX_NODES_TOTAL:,}) reached — stopping early.', 'warn')
        if log_cb:
            log_cb(f'Enumeration complete: {added:,} new flags, {nodes_total:,} nodes visited.', 'ok')
        return added
    def _find_flag(self, name: str) -> int:
        if not self._get_map_header():
            return 0
        else:
            h = self._fnv1a(name)
            bucket_base = self._map_list + (h & self._map_mask) * 16
            bdata = self._rb(bucket_base, 16)
            if len(bdata) < 16:
                return 0
            else:
                node_ptr = 0
                for slot in [8, 0]:
                    cand = _u64(bdata, slot)
                    if _ptr_valid(cand) and cand!= self._map_end:
                            node_ptr = cand
                            break
                if not node_ptr:
                    return 0
                else:
                    depth = 0
                    name_len = len(name)
                    gen = self._map_generation
                    while node_ptr and node_ptr!= self._map_end:
                        if depth >= CHAIN_DEPTH_LIMIT:
                            return 0
                        depth += 1
                        entry = self._rb(node_ptr, self._ENTRY_READ_SZ)
                        if len(entry) < self._ENTRY_READ_SZ:
                            return 0
                        fwd = _u64(entry, OFF_ENTRY_FORWARD)
                        s = OFF_ENTRY_STRING
                        str_size = _u64(entry, s + OFF_STR_SIZE)
                        str_alloc = _u64(entry, s + OFF_STR_ALLOC)
                        if 2 <= str_size <= 256 and str_size == name_len:
                                    try:
                                        if str_alloc > 15:
                                            heap_ptr = _u64(entry, s)
                                            raw = self._rb(heap_ptr, str_size)
                                            entry_name = raw.decode('utf-8', errors='ignore').rstrip('\x00')
                                        else:
                                            entry_name = entry[s:s + str_size].decode('utf-8', errors='ignore')
                                        if entry_name == name:
                                            for gs_off in self._GS_OFFSETS:
                                                gs = _u64(entry, gs_off)
                                                if gs and _ptr_valid(gs):
                                                    else:
                                                        self._flag_cache[name] = gs
                                                        self._gs_generation[name] = gen
                                                        return gs
                                    except Exception:
                                        pass
                        if not fwd or fwd == node_ptr:
                            if False:
                                pass
                            return 0
                        node_ptr = fwd
                    return 0
    def _gs_direct(self, bare: str) -> int:
        if not self.base:
            return 0
        else:
            rva = self.offsets.get_flag_rva(bare)
            if not rva:
                return 0
            else:
                gs = self.base + rva
                return gs if _ptr_valid(gs) else 0
    def _resolve_gs(self, bare: str, method: str='singleton') -> int:
        gs = self._flag_cache.get(bare, 0)
        if gs:
            if self._gs_generation.get(bare, (-1)) == self._map_generation and _ptr_valid(gs):
                return gs
            else:
                del self._flag_cache[bare]
                self._vptr_cache.pop(gs, None)
                self._gs_generation.pop(bare, None)
        return self._find_flag(bare)
    def _resolve_vptr(self, gs: int) -> int:
        if not _ptr_valid(gs):
            return 0
        else:
            vp = self._vptr_cache.get(gs, 0)
            if vp:
                live = _u64(self._rb(gs + OFF_FFLAG_VALUE_PTR, 8), 0)
                if live == vp and _ptr_valid(vp):
                    return vp
                else:
                    del self._vptr_cache[gs]
            struct_data = self._rb(gs, 208)
            if len(struct_data) < OFF_FFLAG_VALUE_PTR + 8:
                return 0
            else:
                vp = _u64(struct_data, OFF_FFLAG_VALUE_PTR)
                if _ptr_valid(vp):
                    self._vptr_cache[gs] = vp
                    return vp
                else:
                    return 0
    def get_int(self, bare: str, method: str='singleton') -> int | None:
        # irreducible cflow, using cdg fallback
        gs = self._resolve_gs(bare, method)
        if not gs:
            return
            vp = self._resolve_vptr(gs)
            if not vp:
                return
                raw = self._rb(vp, 4)
                if len(raw) < 4:
                    return
                    return struct.unpack_from('<i', raw, 0)[0]
                    except Exception:
                            return None
                            pass
    def get_string(self, bare: str, method: str='singleton') -> str | None:
        # irreducible cflow, using cdg fallback
        gs = self._resolve_gs(bare, method)
        if not gs:
            return
            vi = self._resolve_vptr(gs)
            if not vi:
                return
                str_obj = self._rb(vi, 32)
                if len(str_obj) < 24:
                    return
                    length = _u64(str_obj, 8)
                    capacity = _u64(str_obj, 16)
                    if length == 0:
                        return ''
                        if capacity > 15:
                            buf_ptr = _u64(str_obj, 0)
                            if not _ptr_valid(buf_ptr):
                                return
                                raw = self._rb(buf_ptr, length)
                            raw = str_obj[0:length]
                                    return raw.decode('utf-8', errors='ignore')
                                        except Exception:
                                                return None
                                                pass
    def _set_bool(self, bare: str, val: bool, method: str) -> bool:
        gs = self._resolve_gs(bare, method)
        if not _ptr_valid(gs):
            return False
        else:
            vp = self._resolve_vptr(gs)
            if not _ptr_valid(vp):
                return False
            else:
                try:
                    return self._verified_write(vp, b'\x01' if val else b'\x00')
                except Exception:
                    return False
    def _set_int(self, bare: str, val: int, method: str) -> bool:
        gs = self._resolve_gs(bare, method)
        if not _ptr_valid(gs):
            return False
        else:
            vp = self._resolve_vptr(gs)
            if not _ptr_valid(vp):
                return False
            else:
                try:
                    return self._verified_write(vp, val.to_bytes(4, 'little', signed=True))
                except Exception:
                    return False
    def _set_string(self, bare: str, val: str, method: str) -> bool:
        # irreducible cflow, using cdg fallback
        gs = self._resolve_gs(bare, method)
        if not _ptr_valid(gs):
            return False
        else:
            vi = self._resolve_vptr(gs)
            if not _ptr_valid(vi):
                return False
        str_obj = self._rb(vi, 32)
        if len(str_obj) < 32:
            return False
            cap = _u64(str_obj, 16)
            enc = val.encode('utf-8')
            if self._game_transitioning and time.time() < self._transition_deadline:
                    return False
                    if cap > 15:
                        bp = _u64(str_obj, 0)
                        if not _ptr_valid(bp):
                            return False
                            if len(enc) >= cap:
                                return False
                                if self._in_bulk_inject:
                                    if not self._write_raw(bp, enc + b'\x00'):
                                        return False
                                        if not self._write_raw(vi + 8, len(enc).to_bytes(8, 'little')):
                                            return False
                                            if self._rb(bp, len(enc))!= enc:
                                                return False
                                                if self._rb(vi + 8, 8)!= len(enc).to_bytes(8, 'little'):
                                                    return False
                                                    return True
                                    with self._write_lock:
                                        suspended = False
                                            if _IS_WINDOWS:
                                                _NtSuspendProcess(self.h_process)
                                                suspended = True
                                            time.sleep(0.005)
                                            if not self._write_raw(bp, enc + b'\x00'):
                                                if suspended:
                                                    _NtResumeProcess(self.h_process)
                                                if not self._write_raw(vi + 8, len(enc).to_bytes(8, 'little')):
                                                    if suspended:
                                                        _NtResumeProcess(self.h_process)
                                                    ok = self._rb(bp, len(enc)) == enc and self._rb(vi + 8, 8) == len(enc).to_bytes(8, 'little')
                                                    return ok
                                                            _NtResumeProcess(self.h_process)
                        if len(enc) > 15:
                            return False
                            padded = (enc + b'\x00').ljust(16, b'\x00')
                            return self._verified_write(vi, padded)
                                                        except Exception:
                                                                pass
                                                            except Exception:
                                                                    pass
                                                                except Exception:
                                                                        pass
                                                            return False
                                                            pass
    def _write_flag(self, bare: str, val, val_s: str, flag_type: str, method: str) -> bool:
        # irreducible cflow, using cdg fallback
        if flag_type in ('FFlag', 'DFFlag'):
            bval = val if isinstance(val, bool) else val_s.lower() in ('true', '1')
            return self._set_bool(bare, bool(bval), method)
            if flag_type in ['FInt', 'DFInt', 'FLog', 'DFLog']:
                ival = val if isinstance(val, int) else int(float(val_s))
                return self._set_int(bare, ival, method)
                if flag_type in ('FString', 'DFString'):
                    return self._set_string(bare, val_s, method)
                    if isinstance(val, bool):
                        return self._set_bool(bare, val, method)
                        if isinstance(val, int):
                            return self._set_int(bare, val, method)
                            if isinstance(val, float):
                                return self._set_int(bare, int(val), method)
                                if isinstance(val, str):
                                    lv = val_s.lower()
                                    if lv in ['true', 'false']:
                                        return self._set_bool(bare, lv == 'true', method)
                                        return self._set_int(bare, int(val_s), method)
                                    return self._set_string(bare, val_s, method)
                                            except Exception:
                                                return self._set_string(bare, val_s, method)
                        except Exception:
                                return False
                                pass
    def _fallback_write(self, bare: str, val, val_s: str, flag_type: str) -> bool:
        # irreducible cflow, using cdg fallback
        rva = self.offsets.get_flag_rva(bare)
        if not rva or not self.base:
            return False
                gs = self.base + rva
                if not _ptr_valid(gs):
                    return False
                    if len(self._rb(gs, 8)) < 8:
                        return False
                        self._vptr_cache.pop(gs, None)
                        vp = self._resolve_vptr(gs)
                        if not _ptr_valid(vp):
                            self._vptr_cache.pop(gs, None)
                            vp = self._resolve_vptr(gs)
                            if not _ptr_valid(vp):
                                return False
                                def _apply(vp_addr: int) -> bool:
                                    if flag_type in ['FFlag', 'DFFlag']:
                                        bval = val if isinstance(val, bool) else val_s.lower() in ('true', '1')
                                        return self._verified_write(vp_addr, b'\x01' if bval else b'\x00')
                                    else:
                                        if flag_type in ['FInt', 'DFInt', 'FLog', 'DFLog']:
                                            ival = val if isinstance(val, int) else int(float(val_s))
                                            return self._verified_write(vp_addr, ival.to_bytes(4, 'little', signed=True))
                                        else:
                                            if flag_type in ['FString', 'DFString']:
                                                self._flag_cache[bare] = gs
                                                self._gs_generation[bare] = self._map_generation
                                                result = self._set_string(bare, val_s, 'direct')
                                                if not result:
                                                    self._flag_cache.pop(bare, None)
                                                    self._gs_generation.pop(bare, None)
                                                return result
                                            else:
                                                lv = val_s.lower()
                                                if lv in ['true', 'false']:
                                                    bval = lv == 'true'
                                                    return self._verified_write(vp_addr, b'\x01' if bval else b'\x00')
                                                else:
                                                    try:
                                                        ival = int(val_s)
                                                        return self._verified_write(vp_addr, ival.to_bytes(4, 'little', signed=True))
                                                    except Exception:
                                                        self._flag_cache[bare] = gs
                                                        self._gs_generation[bare] = self._map_generation
                                                        result = self._set_string(bare, val_s, 'direct')
                                                        if not result:
                                                            self._flag_cache.pop(bare, None)
                                                            self._gs_generation.pop(bare, None)
                                                        return result
                                if _apply(vp):
                                    return True
                                    self._vptr_cache.pop(gs, None)
                                    vp = self._resolve_vptr(gs)
                                    if not _ptr_valid(vp):
                                        return False
                                        return _apply(vp)
                                        except Exception:
                                                return False
                                                pass
    def inject(self, flags: dict, method: str='singleton', progress_cb=None) -> tuple:
        # irreducible cflow, using cdg fallback
        if not self.pm:
            return (0, len(flags), ['[ERROR] Not attached to Roblox'])
        else:
            ok = fail = 0
            log = []
            total = len(flags)
            if not self._flag_cache:
                self._enumerate_all_flags()
            resolved = []
            for raw_key, val in flags.items():
                bare, flag_type = _parse_flag_key(raw_key)
                val_s = str(val)
                resolved.append((raw_key, bare, val_s, flag_type, val))
            INJECT_CHUNK_SZ = 50
            INTER_CHUNK_SLEEP = 0.02
            global_i = 0
            for chunk_start in range(0, len(resolved), INJECT_CHUNK_SZ):
                pass
        chunk = resolved[chunk_start:chunk_start + INJECT_CHUNK_SZ]
        suspended = False
        if _IS_WINDOWS:
            _NtSuspendProcess(self.h_process)
            suspended = True
        self._in_bulk_inject = True
        for raw_key, bare, val_s, flag_type, val in chunk:
            pass
        success = False
        try:
            success = self._write_flag(bare, val, val_s, flag_type, method)
            if not success:
                old_gs = self._flag_cache.pop(bare, None)
                self._gs_generation.pop(bare, None)
                if old_gs:
                    self._vptr_cache.pop(old_gs, None)
                self._resolve_gs(bare, method)
                success = self._write_flag(bare, val, val_s, flag_type, method)
            if not success:
                success = self._fallback_write(bare, val, val_s, flag_type)
        except Exception:
            success = False
        if success:
            ok += 1
            log.append(f'[OK] {raw_key} = {val_s}')
        else:
            fail += 1
            log.append(f'[FAIL] {raw_key}')
        global_i += 1
        if progress_cb:
            pass
        progress_cb(global_i, total, ok, fail)
        self._in_bulk_inject = False
        if suspended:
            try:
                _NtResumeProcess(self.h_process)
        if chunk_start + INJECT_CHUNK_SZ < len(resolved):
            time.sleep(INTER_CHUNK_SLEEP)
        return (ok, fail, log)
        except Exception:
            pass
        pass
            try:
                pass
    def uninject(self, backup: 'FlagBackupStore', method: str='singleton') -> tuple:
        if not self.pm:
            return (0, 0, ['[ERROR] Not attached'])
        else:
            ok = fail = 0
            log = []
            suspended = False
        try:
            if _IS_WINDOWS:
                _NtSuspendProcess(self.h_process)
                suspended = True
            self._in_bulk_inject = True
            for raw_key, snapshot in backup.snapshots.items():
                bare = snapshot['bare']
                orig_type = snapshot['type']
                orig_value = snapshot['value']
                success = False
                try:
                    if orig_type == 'bool':
                        bv = bool(orig_value) if isinstance(orig_value, bool) else str(orig_value).lower() in ('true', '1')
                        success = self._set_bool(bare, bv, method)
                    else:
                        if orig_type == 'int':
                            success = self._set_int(bare, int(orig_value), method)
                        else:
                            if orig_type == 'string':
                                success = self._set_string(bare, str(orig_value), method)
                except Exception:
                    success = False
                if success:
                    ok += 1
                    log.append(f'[RESTORE] {raw_key} → {orig_value}')
                else:
                    fail += 1
                    log.append(f'[RESTORE FAIL] {raw_key}')
        finally:
            self._in_bulk_inject = False
            if suspended:
                try:
                    _NtResumeProcess(self.h_process)
                except Exception:
                    pass
        return (ok, fail, log)
class FlagBackupStore:
    _TYPE_BYTE_OFFSET = 184
    def __init__(self):
        self.snapshots = {}
        self._lock = threading.Lock()
    def clear(self):
        with self._lock:
            self.snapshots.clear()
    def snapshot_one(self, core: BreadCore, raw_key: str, bare: str, flag_type: str, method: str='singleton') -> bool:
        # irreducible cflow, using cdg fallback
        gs = core._resolve_gs(bare, method)
        if not gs:
            return False
            if flag_type in ['FFlag', 'DFFlag']:
                stored_type = 'bool'
            else:
                if flag_type in ['FInt', 'DFInt', 'FLog', 'DFLog']:
                    stored_type = 'int'
                else:
                    if flag_type in ['FString', 'DFString']:
                        stored_type = 'string'
                    else:
                        struct_data = core._rb(gs, 192)
                        if len(struct_data) >= self._TYPE_BYTE_OFFSET + 4:
                            discriminant = struct.unpack_from('<I', struct_data, self._TYPE_BYTE_OFFSET)[0]
                            stored_type = 'string' if discriminant == 3 else 'int'
                        else:
                            stored_type = 'int'
            if stored_type == 'string':
                val = core.get_string(bare, method)
                if val is None:
                    return False
                val = core.get_int(bare, method)
                if val is None:
                    return False
                    if stored_type == 'bool':
                        val = bool(val)
                    with self._lock:
                        self.snapshots[raw_key] = {'bare': bare, 'type': stored_type, 'value': val}
                                return True
            except Exception:
                    return False
    def snapshot_all(self, core: BreadCore, flags: dict, method: str='singleton') -> int:
        self.clear()
        count = 0
        for raw_key in flags:
            bare, flag_type = _parse_flag_key(raw_key)
            if self.snapshot_one(core, raw_key, bare, flag_type, method):
                count += 1
        return count
class FFlagMonitor:
    pass
    def __init__(self, core: BreadCore, log_cb=None, check_interval: float=1.0):
        self.core = core
        self._log = log_cb or (lambda msg, lvl='info': None)
        self.check_interval = check_interval
        self.desired_flags = {}
        self.monitoring = False
        self._thread = None
        self.reinjected_count = 0
        self._lock = threading.Lock()
    def start(self):
        if self.monitoring:
            return
        else:
            self.monitoring = True
            self._thread = threading.Thread(target=self._loop, daemon=True)
            self._thread.start()
    def stop(self):
        self.monitoring = False
    def set_flags(self, flags: dict, method: str='singleton'):
        desired = {}
        for raw_key, val in flags.items():
            bare, flag_type = _parse_flag_key(raw_key)
            if flag_type in ['FFlag', 'DFFlag']:
                ftype = 'bool'
            else:
                if flag_type in ['FInt', 'DFInt', 'FLog', 'DFLog']:
                    ftype = 'int'
                else:
                    if flag_type in ['FString', 'DFString']:
                        ftype = 'string'
                    else:
                        val_s = str(val).lower()
                        if val_s in ['true', 'false']:
                            ftype = 'bool'
                        else:
                            try:
                                int(val_s)
                                ftype = 'int'
                            except Exception:
                                ftype = 'string'
            desired[raw_key] = {'bare': bare, 'type': ftype, 'desired': str(val), 'method': method}
        with self._lock:
            self.desired_flags = desired
            self.reinjected_count = 0
    def clear(self):
        with self._lock:
            self.desired_flags.clear()
            self.reinjected_count = 0
    def _loop(self):
        # irreducible cflow, using cdg fallback
        time.sleep(2.0)
        while self.monitoring:
            if not self.desired_flags or not self.core.pm:
                time.sleep(1.0)
                    continue
                self._check_and_fix()
                            time.sleep(self.check_interval)
                    except Exception:
                            pass
                            pass
    def _check_and_fix(self):
        with self._lock:
            snapshot = list(self.desired_flags.items())
        for raw_key, info in snapshot:
            bare = info['bare']
            ftype = info['type']
            desired = info['desired']
            method = info['method']
            try:
                has_drifted = False
                if ftype == 'string':
                    current = self.core.get_string(bare, method)
                    if current is None:
                        continue
                    else:
                        has_drifted = current!= desired
                else:
                    if ftype in ['bool', 'int']:
                        val = self.core.get_int(bare, method)
                        if val is None:
                            continue
                        else:
                            if ftype == 'bool':
                                cur_b = bool(val)
                                des_b = desired.lower() in ['true', '1', 'yes']
                                has_drifted = cur_b!= des_b
                            else:
                                try:
                                    has_drifted = val!= int(desired)
                                except Exception:
                                    has_drifted = True
                                else:
                                    pass
                    else:
                        continue
                if has_drifted and self._reinject_one(raw_key, bare, ftype, desired, method):
                        with self._lock:
                            self.reinjected_count += 1
                        self._log(f'Re-injected drifted flag: {raw_key}', 'warn')
            except Exception:
                pass
    def _reinject_one(self, raw_key: str, bare: str, ftype: str, desired: str, method: str) -> bool:
        # irreducible cflow, using cdg fallback
        if ftype == 'bool':
            bv = desired.lower() in ['true', '1', 'yes']
            return self.core._set_bool(bare, bv, method)
            if ftype == 'int':
                return self.core._set_int(bare, int(desired), method)
                if ftype == 'string':
                    return self.core._set_string(bare, desired, method)
                    return False
                except Exception:
                        return False
                        pass
class FileWatcher:
    def __init__(self, interval: float=2.0, log_cb=None):
        self._interval = interval
        self._log = log_cb or (lambda msg, lvl='info': None)
        self._path = None
        self._mtime = None
        self._last_flags = {}
        self._on_change = None
        self._running = False
        self._thread = None
    def start(self, path: str, current_flags: dict, on_change_cb):
        self._path = path
        self._last_flags = dict(current_flags)
        self._on_change = on_change_cb
        try:
            self._mtime = os.stat(path).st_mtime
        except Exception:
            self._mtime = None
        if self._running:
            return
        else:
            self._running = True
            self._thread = threading.Thread(target=self._loop, daemon=True)
            self._thread.start()
    def stop(self):
        self._running = False
        self._path = None
    def update(self, path: str, current_flags: dict):
        self._path = path
        self._last_flags = dict(current_flags)
        try:
            self._mtime = os.stat(path).st_mtime
        except Exception:
            return None
    def _loop(self):
        while self._running:
            try:
                if self._path and os.path.exists(self._path):
                        mtime = os.stat(self._path).st_mtime
                        if self._mtime is not None and mtime!= self._mtime:
                            self._mtime = mtime
                            self._handle_change()
                        else:
                            if self._mtime is None:
                                self._mtime = mtime
            except Exception:
                pass
            time.sleep(self._interval)
    def _handle_change(self):
        # irreducible cflow, using cdg fallback
        with open(self._path, 'r', encoding='utf-8') as f:
            new_flags = json.load(f)
        if not isinstance(new_flags, dict):
            return
            changed = [k for k, v in new_flags.items() if str(v)!= str(self._last_flags.get(k, ''))]
            if not changed:
                return
                self._log(f'File changed — {len(changed)} flag(s) updated', 'info')
                self._last_flags = {k: str(v) for k, v in new_flags.items()}
                if self._on_change:
                    self._on_change({k: str(v) for k, v in new_flags.items()}, changed)
            except Exception as e:
                    self._log(f'File watch read error: {e}', 'err')
def _load_session() -> dict:
    # irreducible cflow, using cdg fallback
    if os.path.exists(_SESSION_PATH):
        with open(_SESSION_PATH, 'r', encoding='utf-8') as f:
            data = json.load(f)
        if isinstance(data, dict) and data:
            return data
        return {}
        except Exception:
                pass
                pass
def _save_session(flags: dict):
    # irreducible cflow, using cdg fallback
    with open(_SESSION_PATH, 'w', encoding='utf-8') as f:
        json.dump(flags, f)
                except Exception:
                        return None
                        pass
def _make_btn(parent, text, cmd, bg=None, fg=None, width=None, height=None, font_size=11):
    """All buttons are golden yellow — the bread aesthetic."""
    btn_bg = bg if bg is not None else C['accent']
    btn_fg = fg if fg is not None else C['btn_text']
    kw = dict(text=text, command=cmd, bg=btn_bg, fg=btn_fg, activebackground='#FFD740', activeforeground=C['btn_text'], relief='flat', bd=0, cursor='hand2', font=('Segoe UI', font_size, 'bold'), padx=12, pady=7)
    if width:
        kw['width'] = width
    if height:
        kw['height'] = height
    return tk.Button(parent, **kw)
class ScrollableFrame(tk.Frame):
    def __init__(self, parent, bg, **kw):
        super().__init__(parent, bg=bg, **kw)
        self.canvas = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0)
        self.vsb = ttk.Scrollbar(self, orient='vertical', command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.vsb.pack(side='right', fill='y')
        self.canvas.pack(side='left', fill='both', expand=True)
        self.inner = tk.Frame(self.canvas, bg=bg)
        self._win_id = self.canvas.create_window((0, 0), window=self.inner, anchor='nw')
        self.inner.bind('<Configure>', self._on_inner_configure)
        self.canvas.bind('<Configure>', self._on_canvas_configure)
        self.canvas.bind_all('<MouseWheel>', self._on_mousewheel)
    def _on_inner_configure(self, _e):
        self.canvas.configure(scrollregion=self.canvas.bbox('all'))
    def _on_canvas_configure(self, e):
        self.canvas.itemconfig(self._win_id, width=e.width)
    def _on_mousewheel(self, e):
        self.canvas.yview_scroll(int((-1) * (e.delta / 120)), 'units')
def _draw_bread_loaf(canvas, cx, cy, w=180, h=75):
    """Draw a simple stylised bread loaf on a tk Canvas."""
    canvas.create_rectangle(cx - w // 2, cy + h // 3, cx + w // 2, cy + h // 2 + 6, fill='#5C3010', outline='#3A1A00', width=2)
    canvas.create_oval(cx - w // 2, cy - h // 2, cx + w // 2, cy + h // 2, fill='#C4844A', outline='#8B5225', width=2)
    canvas.create_oval(cx - w // 3, cy - h // 2 + 6, cx, cy - h // 5, fill='#D4A060', outline='')
    for xoff in [-w // 5, 0, w // 5]:
        canvas.create_line(cx + xoff, cy - h // 4, cx + xoff, cy + h // 4, fill='#8B5225', width=2, capstyle='round')
    import random
    rng = random.Random(42)
    for _ in range(8):
        sx = cx + rng.randint(-w // 3, w // 3)
        sy = cy + rng.randint(-h // 4, h // 8)
        canvas.create_oval(sx - 2, sy - 1, sx + 2, sy + 1, fill='#E8C880', outline='')
class BreadApp(tk.Tk):
    _UI_EVT_LOG = 'log'
    _UI_EVT_STATUS = 'status'
    _UI_EVT_OFFSET_INFO = 'offset_info'
    _UI_EVT_INJECT_DONE = 'inject_done'
    _UI_EVT_UNINJECT_DONE = 'uninject_done'
    _UI_EVT_PROGRESS = 'progress'
    _UI_EVT_MONITOR_STAT = 'monitor_stat'
    _UI_EVT_FILE_WATCH = 'file_watch'
    _UI_EVT_VALIDATE_DONE = 'validate_done'
    _UI_EVT_BATCH_STATUS = 'batch_status'
    def __init__(self, cli_timed: bool=False):
        super().__init__()
        self.title('Bread — FastFlag Injector')
        self.geometry('1260x820')
        self.minsize(940, 640)
        self.configure(bg=C['bg'])
        self.offsets = OffsetStore()
        self.core = BreadCore(self.offsets)
        self.backup = FlagBackupStore()
        self.monitor = FFlagMonitor(self.core, log_cb=self._log)
        self.file_watcher = FileWatcher(log_cb=self._log)
        self.inj_config = InjectionConfig(timed_mode=cli_timed)
        self._batch_injector = None
        self.loaded_flags = {}
        self._ok_flags = {}
        self._inject_busy = False
        self._uninject_busy = False
        self._validate_busy = False
        self._method = 'singleton'
        self._monitor_enabled = True
        self._watching_file = False
        self._last_file_path = ''
        self._session_flags = _load_session()
        self._auto_inject_pending = False
        self._ui_queue = queue.Queue()
        self._auto_inject_var = None
        self._timed_mode_var = None
        self._build_ui()
        self._start_ui_pump()
        threading.Thread(target=self._watcher_loop, daemon=True).start()
        threading.Thread(target=self._bg_fetch_offsets, daemon=True).start()
        if self._session_flags:
            self._do_log(f'Session restored — {len(self._session_flags):,} flag(s) queued for auto-inject on next Roblox attach.', 'accent')
    def _start_ui_pump(self):
        self._drain_queue()
    def _drain_queue(self):
        try:
            while True:
                evt_type, payload = self._ui_queue.get_nowait()
                self._handle_ui_event(evt_type, payload)
        except queue.Empty:
            pass
        self.after(50, self._drain_queue)
    def _post(self, evt_type: str, payload):
        self._ui_queue.put((evt_type, payload))
    def _handle_ui_event(self, evt_type: str, payload):
        if evt_type == self._UI_EVT_LOG:
            msg, level = payload
            if level == '__stats__':
                try:
                    parts = msg.split('__')
                    ok = int(parts[2])
                    fail = int(parts[3])
                    self._stat_labels['ok'].config(text=str(ok), fg=C['success'])
                    self._stat_labels['fail'].config(text=str(fail), fg=C['success'] if fail == 0 else C['error'])
                except Exception:
                    return None
            else:
                self._do_log(msg, level)
        else:
            if evt_type == self._UI_EVT_STATUS:
                text, color = payload
                self.lbl_status.config(text=text, fg=color)
            else:
                if evt_type == self._UI_EVT_OFFSET_INFO:
                    status, singleton, _ = payload
                    color = C['success'] if 'flag' in status.lower() or 'local' in status.lower() or 'ok' in status.lower() else C['warning']
                    self.lbl_off_status.config(text=status, fg=color)
                    self.lbl_singleton.config(text=singleton)
                    if self.loaded_flags:
                        self._filter_table()
                else:
                    if evt_type == self._UI_EVT_INJECT_DONE:
                        self._inject_btn.config(text='⚡ Inject Flags', state='normal', bg=C['accent'])
                        self._inject_busy = False
                        self._progress_var.set(0)
                        self._uninject_btn.config(state='normal', bg=C['accent'])
                    else:
                        if evt_type == self._UI_EVT_UNINJECT_DONE:
                            self._uninject_btn.config(text='↩ Uninject', state='disabled', bg=C['dim'])
                            self._uninject_busy = False
                            self._stat_labels['ok'].config(text='—')
                            self._stat_labels['fail'].config(text='—')
                        else:
                            if evt_type == self._UI_EVT_PROGRESS:
                                done, total = payload
                                pct = done / total * 100 if total else 0
                                self._progress_var.set(pct)
                            else:
                                if evt_type == self._UI_EVT_MONITOR_STAT:
                                    count = payload
                                    self._lbl_reinjected.config(text=f'Re-injected: {count}')
                                else:
                                    if evt_type == self._UI_EVT_VALIDATE_DONE:
                                        ok_count, total = payload
                                        self._validate_btn.config(text='✅ Validate Flags', state='normal', bg=C['accent'])
                                        self._validate_busy = False
                                        self._progress_var.set(0)
                                        self._do_log(f'Validation complete — {ok_count}/{total} flags OK. Click \'📤 Export Valid JSON\' to save.', 'ok')
                                        self._export_btn.config(state='normal' if ok_count > 0 else 'disabled', bg=C['accent'] if ok_count > 0 else C['dim'])
                                    else:
                                        if evt_type == self._UI_EVT_FILE_WATCH:
                                            is_active, fname = payload
                                            color = C['success'] if is_active else C['dim']
                                            text = f'👁 Watching: {fname}' if is_active else '👁 File watch: off'
                                            self._lbl_file_watch.config(text=text, fg=color)
                                        else:
                                            if evt_type == self._UI_EVT_BATCH_STATUS:
                                                batch_idx, total_batches, msg = payload
                                                pct_batch = batch_idx / total_batches * 100 if total_batches else 0
                                                self._progress_var.set(pct_batch)
                                                self._lbl_batch_status.config(text=f'Batch {batch_idx}/{total_batches}  ·  {msg}', fg=C['accent'])
    def _build_ui(self):
        sidebar = tk.Frame(self, bg=C['surface'], width=290)
        sidebar.pack(side='left', fill='y')
        sidebar.pack_propagate(False)
        logo_canvas = tk.Canvas(sidebar, width=290, height=120, bg=C['surface'], highlightthickness=0)
        logo_canvas.pack(fill='x')
        _draw_bread_loaf(logo_canvas, cx=145, cy=65)
        tk.Label(sidebar, text='🍞  BREAD', bg=C['surface'], fg=C['accent'], font=('Georgia', 22, 'bold')).pack(pady=(4, 0))
        tk.Label(sidebar, text='FastFlag Injector  ·  V5', bg=C['surface'], fg=C['dim'], font=('Segoe UI', 10)).pack(pady=(0, 8))
        tk.Frame(sidebar, bg=C['border'], height=1).pack(fill='x', padx=16, pady=4)
        self.lbl_status = tk.Label(sidebar, text='● Waiting for Roblox', bg=C['card'], fg=C['warning'], font=('Segoe UI', 11), wraplength=250, padx=12, pady=10)
        self.lbl_status.pack(fill='x', padx=14, pady=6)
        off_card = tk.Frame(sidebar, bg=C['card'])
        off_card.pack(fill='x', padx=14, pady=4)
        self.lbl_off_status = tk.Label(off_card, text='Offsets: hardcoded (local)', bg=C['card'], fg=C['success'], font=('Segoe UI', 10), wraplength=240, anchor='w')
        self.lbl_off_status.pack(anchor='w', padx=10, pady=(8, 2))
        self.lbl_singleton = tk.Label(off_card, text='', bg=C['card'], fg=C['dim'], font=('Consolas', 10), anchor='w')
        self.lbl_singleton.pack(anchor='w', padx=10, pady=(2, 4))
        _make_btn(off_card, '⟳ Refresh Offsets', lambda pady: threading.Thread(target=self._bg_fetch_offsets, daemon=True).start(), font_size=10).pack(fill='x', padx=8, pady=(0, 8))
        tk.Frame(sidebar, bg=C['border'], height=1).pack(fill='x', padx=16, pady=6)
        _make_btn(sidebar, '📂 Import JSON', self._import_json, font_size=12).pack(fill='x', padx=14, pady=3)
        self._inject_btn = _make_btn(sidebar, '⚡ Inject Flags', self._start_inject, font_size=12)
        self._inject_btn.pack(fill='x', padx=14, pady=3)
        self._uninject_btn = _make_btn(sidebar, '↩ Uninject', self._start_uninject, font_size=11)
        self._uninject_btn.config(state='disabled', bg=C['dim'], fg=C['text'])
        self._uninject_btn.pack(fill='x', padx=14, pady=3)
        _make_btn(sidebar, '✕ Clear Flags', self._clear_flags, font_size=11).pack(fill='x', padx=14, pady=3)
        self._save_btn = _make_btn(sidebar, '💾 Save Flags', self._save_flags, font_size=11)
        self._save_btn.pack(fill='x', padx=14, pady=3)
        self._abort_btn = _make_btn(sidebar, '⛔ Abort Injection', self._abort_inject, font_size=11)
        self._abort_btn.pack(fill='x', padx=14, pady=3)
        tk.Frame(sidebar, bg=C['border'], height=1).pack(fill='x', padx=16, pady=4)
        tk.Label(sidebar, text='VALIDATOR:', bg=C['surface'], fg=C['dim'], font=('Consolas', 10, 'bold')).pack(anchor='w', padx=14, pady=(4, 0))
        self._validate_btn = _make_btn(sidebar, '✅ Validate Flags', self._start_validate, font_size=11)
        self._validate_btn.pack(fill='x', padx=14, pady=3)
        self._export_btn = _make_btn(sidebar, '📤 Export Valid JSON', self._export_valid_flags, font_size=11)
        self._export_btn.config(state='disabled', bg=C['dim'], fg=C['text'])
        self._export_btn.pack(fill='x', padx=14, pady=3)
        tk.Frame(sidebar, bg=C['border'], height=1).pack(fill='x', padx=16, pady=6)
        tk.Label(sidebar, text='METHOD:', bg=C['surface'], fg=C['dim'], font=('Consolas', 10, 'bold')).pack(anchor='w', padx=14)
        m_frame = tk.Frame(sidebar, bg=C['surface'])
        m_frame.pack(fill='x', padx=14, pady=4)
        self._method_btns = {}
        btn = _make_btn(m_frame, 'SINGLETON', lambda: None, font_size=9)
        btn.pack(fill='x')
        self._method_btns['singleton'] = btn
        tk.Frame(sidebar, bg=C['border'], height=1).pack(fill='x', padx=16, pady=6)
        for label_text, var_attr, cmd_name in [('Auto re-inject', '_mon_var', '_toggle_monitor'), ('Auto-inject on boot', '_auto_inject_var', '_toggle_auto_inject'), ('Timed batch (100/5s)', '_timed_mode_var', '_toggle_timed_mode')]:
            row = tk.Frame(sidebar, bg=C['surface'])
            row.pack(fill='x', padx=14, pady=2)
            default = True if var_attr == '_mon_var' else False
            var = tk.BooleanVar(value=default)
            setattr(self, var_attr, var)
            tk.Checkbutton(row, variable=var, text=label_text, bg=C['surface'], fg=C['text'], selectcolor=C['card'], activebackground=C['surface'], font=('Segoe UI', 10), command=getattr(self, cmd_name)).pack(side='left', padx=6)
        self._lbl_batch_status = tk.Label(sidebar, text='', bg=C['surface'], fg=C['dim'], font=('Segoe UI', 9), wraplength=250, anchor='w')
        self._lbl_batch_status.pack(anchor='w', padx=14, pady=1)
        self._lbl_reinjected = tk.Label(sidebar, text='Re-injected: 0', bg=C['surface'], fg=C['dim'], font=('Segoe UI', 10))
        self._lbl_reinjected.pack(anchor='w', padx=14, pady=2)
        self._lbl_file_watch = tk.Label(sidebar, text='👁 File watch: off', bg=C['surface'], fg=C['dim'], font=('Segoe UI', 9), wraplength=250, anchor='w')
        self._lbl_file_watch.pack(anchor='w', padx=14, pady=2)
        tk.Frame(sidebar, bg=C['border'], height=1).pack(fill='x', padx=16, pady=6)
        stats_frame = tk.Frame(sidebar, bg=C['card'])
        stats_frame.pack(fill='x', padx=14, pady=4)
        self._stat_labels = {}
        for row_i, (label, key) in enumerate([('Flags loaded', 'loaded'), ('Last inject OK', 'ok'), ('Last inject FAIL', 'fail')]):
            tk.Label(stats_frame, text=label, bg=C['card'], fg=C['dim'], font=('Segoe UI', 10)).grid(row=row_i, column=0, sticky='w', padx=10, pady=3)
            lbl = tk.Label(stats_frame, text='—', bg=C['card'], fg=C['text'], font=('Consolas', 10, 'bold'))
            lbl.grid(row=row_i, column=1, sticky='e', padx=10)
            stats_frame.columnconfigure(1, weight=1)
            self._stat_labels[key] = lbl
        main_panel = tk.Frame(self, bg=C['bg'])
        main_panel.pack(side='right', fill='both', expand=True)
        top_bar = tk.Frame(main_panel, bg=C['surface'], height=54)
        top_bar.pack(fill='x')
        top_bar.pack_propagate(False)
        tk.Label(top_bar, text='Search flags:', bg=C['surface'], fg=C['dim'], font=('Segoe UI', 10)).pack(side='left', padx=(16, 4), pady=14)
        self._search_var = tk.StringVar()
        self._search_var.trace_add('write', lambda *_: self._filter_table())
        tk.Entry(top_bar, textvariable=self._search_var, bg=C['card'], fg=C['text'], insertbackground=C['accent'], relief='flat', bd=0, font=('Segoe UI', 12), width=32).pack(side='left', pady=12, ipady=4)
        self._lbl_count = tk.Label(top_bar, text='0 flags', bg=C['surface'], fg=C['accent'], font=('Segoe UI', 11, 'bold'))
        self._lbl_count.pack(side='right', padx=16)
        style = ttk.Style()
        style.theme_use('default')
        style.configure('Bread.Horizontal.TProgressbar', troughcolor=C['card'], background=C['accent'], thickness=6)
        self._progress_var = tk.DoubleVar(value=0)
        self._progress_bar = ttk.Progressbar(main_panel, variable=self._progress_var, maximum=100, mode='determinate', style='Bread.Horizontal.TProgressbar')
        self._progress_bar.pack(fill='x')
        hdr = tk.Frame(main_panel, bg=C['border'], height=32)
        hdr.pack(fill='x')
        hdr.pack_propagate(False)
        for col_text, col_width, col_anchor in [('', 28, 'center'), ('FLAG NAME', None, 'w'), ('VALUE', 170, 'w'), ('', 50, 'center')]:
            lbl = tk.Label(hdr, text=col_text, bg=C['border'], fg=C['accent'], font=('Consolas', 10, 'bold'), anchor=col_anchor, padx=6)
            if col_width:
                lbl.pack(side='left')
                lbl.configure(width=col_width // 8)
            else:
                lbl.pack(side='left', expand=True, fill='x')
        self._flag_scroll = ScrollableFrame(main_panel, bg=C['bg'])
        self._flag_scroll.pack(fill='both', expand=True)
        self._flag_rows = []
        log_frame = tk.Frame(main_panel, bg=C['surface'], height=185)
        log_frame.pack(fill='x', side='bottom')
        log_frame.pack_propagate(False)
        log_hdr = tk.Frame(log_frame, bg=C['surface'])
        log_hdr.pack(fill='x')
        tk.Label(log_hdr, text='LOG', bg=C['surface'], fg=C['accent'], font=('Consolas', 10, 'bold')).pack(side='left', padx=12, pady=5)
        _make_btn(log_hdr, 'Clear', self._clear_log, font_size=9).pack(side='right', padx=10, pady=4)
        self._log_box = tk.Text(log_frame, state='disabled', wrap='word', bg=C['card'], fg=C['text'], relief='flat', font=('Consolas', 11), padx=8, pady=6)
        log_sb = ttk.Scrollbar(log_frame, command=self._log_box.yview)
        self._log_box.configure(yscrollcommand=log_sb.set)
        log_sb.pack(side='right', fill='y')
        self._log_box.pack(fill='both', expand=True)
        for tag, color in [('ok', C['success']), ('err', C['error']), ('warn', C['warning']), ('accent', C['accent']), ('info', C['dim'])]:
            self._log_box.tag_config(tag, foreground=color)
        if not _HAS_PYMEM:
            self._do_log('WARNING: pymem not installed — injection disabled. Run: pip install pymem', 'warn')
        if not _IS_WINDOWS:
            self._do_log('WARNING: Not running on Windows — memory ops disabled.', 'warn')
    def _render_table(self, flags: dict):
        for widget in self._flag_rows:
            try:
                widget.destroy()
            except:
                pass
        self._flag_rows.clear()
        inner = self._flag_scroll.inner
        for i, (name, val) in enumerate(flags.items()):
            row_bg = C['card'] if i % 2 == 0 else C['bg']
            row = tk.Frame(inner, bg=row_bg)
            row.pack(fill='x', pady=1, padx=2)
            bare = _strip_prefix(name)
            dot_col = C['success'] if bare in self.core._flag_cache else C['warning']
            tk.Label(row, text='●', bg=row_bg, fg=dot_col, font=('Segoe UI', 10), width=2).pack(side='left', padx=(6, 2), pady=4)
            tk.Label(row, text=name, bg=row_bg, fg=C['text'], font=('Segoe UI', 11), anchor='w').pack(side='left', fill='x', expand=True, padx=4)
            val_var = tk.StringVar(value=str(val))
            entry = tk.Entry(row, textvariable=val_var, width=22, bg=C['surface'], fg=C['text'], insertbackground=C['accent'], relief='flat', bd=1, font=('Consolas', 11))
            entry.pack(side='left', padx=4, pady=4, ipady=2)
            entry.bind('<Return>', lambda _e, n=name, v=val_var: self._update_flag(n, v.get()))
            entry.bind('<FocusOut>', lambda _e, n=name, v=val_var: self._update_flag(n, v.get()))
            _make_btn(row, '✕', lambda n=name, r=row: self._delete_flag(n, r), font_size=10).pack(side='right', padx=6, pady=4)
            self._flag_rows.append(row)
        self._lbl_count.config(text=f'{len(flags)} flags')
        self._stat_labels['loaded'].config(text=str(len(self.loaded_flags)))
    def _filter_table(self):
        q = self._search_var.get().lower()
        subset = {k: v for k, v in self.loaded_flags.items() if not (q in k.lower() or self.loaded_flags)} if q else self.loaded_flags
        self._render_table(subset)
    def _log(self, msg: str, level: str='info'):
        self._post(self._UI_EVT_LOG, (msg, level))
    def _do_log(self, msg: str, level: str='info'):
        ts = datetime.now().strftime('%H:%M:%S')
        tag = level if level in ['ok', 'err', 'warn', 'accent', 'info'] else 'info'
        self._log_box.configure(state='normal')
        self._log_box.insert('end', f'[{ts}] {msg}\n', tag)
        self._log_box.see('end')
        self._log_box.configure(state='disabled')
    def _clear_log(self):
        self._log_box.configure(state='normal')
        self._log_box.delete('1.0', 'end')
        self._log_box.configure(state='disabled')
    def _import_json(self):
        path = filedialog.askopenfilename(filetypes=[('JSON files', '*.json'), ('All files', '*.*')])
        if not path:
            return
        else:
            try:
                self.loaded_flags = load_flags_from_file(path)
                self._render_table(self.loaded_flags)
                self._do_log(f'Loaded {len(self.loaded_flags):,} flags from {Path(path).name}', 'ok')
                self._last_file_path = path
                self.file_watcher.update(path, self.loaded_flags)
                if not self.file_watcher._running:
                    self.file_watcher.start(path, self.loaded_flags, self._on_file_change)
                    self._watching_file = True
                self._post(self._UI_EVT_FILE_WATCH, (True, Path(path).name))
            except Exception as ex:
                messagebox.showerror('Import Error', str(ex))
    def _on_file_change(self, new_flags: dict, changed_keys: list):
        self._do_log(f'File changed — re-injecting {len(changed_keys)} flag(s)…', 'accent')
        self.loaded_flags = new_flags
        self.after(0, lambda /: self._render_table(self.loaded_flags))
        if self.core.pm:
            threading.Thread(target=self._run_inject, args=(copy.copy(new_flags),), daemon=True).start()
    def _start_inject(self):
        if self._inject_busy:
            self._do_log('Already injecting, please wait…', 'warn')
            return
        else:
            if not self.loaded_flags:
                self._do_log('No flags loaded. Import a JSON first.', 'warn')
                return
            else:
                if not self.core.pm:
                    self._do_log('Roblox not attached — launch Roblox first.', 'err')
                    return
                else:
                    if not self.core._roblox_already_loaded():
                        self._do_log('Roblox map not ready — waiting before injecting…', 'warn')
                        flags_copy = copy.copy(self.loaded_flags)
                        def _wait_and_inject():
                            if self.core._wait_for_ready(timeout=120, log_cb=self._log):
                                self._run_inject_sync(flags_copy)
                            else:
                                self._log('Timed out waiting for Roblox FFlag map.', 'err')
                        threading.Thread(target=_wait_and_inject, daemon=True).start()
                        return
                    else:
                        self._inject_busy = True
                        mode_label = 'timed batch' if self.inj_config.timed_mode else 'instant'
                        self._inject_btn.config(text=f'Injecting ({mode_label})…', state='disabled', bg=C['dim'])
                        self._progress_var.set(0)
                        threading.Thread(target=self._run_inject, args=(copy.copy(self.loaded_flags),), daemon=True).start()
    def _run_inject_sync(self, flags: dict):
        self._inject_busy = True
        self.after(0, lambda /: self._inject_btn.config(text='Injecting…', state='disabled', bg=C['dim']))
        self._run_inject(flags)
    def _run_inject(self, flags: dict):
        snapped = self.backup.snapshot_all(self.core, flags, self._method)
        if snapped:
            self._log(f'Backed up {snapped:,} original values.', 'info')
        _total_ok = [0]
        _total_fail = [0]
        _all_lines = []
        def _on_log(msg: str, lvl: str='info'):
            self._log(msg, lvl)
            if msg.startswith('[OK]') or msg.startswith('[FAIL]'):
                _all_lines.append(msg)
        def _on_progress(done: int, total: int, ok: int, fail: int):
            self._post(self._UI_EVT_PROGRESS, (done, total))
        def _on_done(ok: int, fail: int):
            _total_ok[0] = ok
            _total_fail[0] = fail
            total = ok + fail
            self._log(f'Injection complete — {ok:,} OK | {fail:,} FAIL | {total:,} total', 'ok' if fail == 0 else 'warn')
            self._post(self._UI_EVT_LOG, (f'__stats__{ok}__{fail}', '__stats__'))
            ok_flags = {}
            for line in _all_lines:
                if line.startswith('[OK]'):
                    body = line[5:].strip()
                    eq = body.find(' = ')
                    raw_key = body[:eq].strip() if eq!= (-1) else body
                    if raw_key in flags:
                        ok_flags[raw_key] = flags[raw_key]
            self._ok_flags = ok_flags
            if ok > 0 and self._monitor_enabled:
                    self.monitor.set_flags(flags, self._method)
                    if not self.monitor.monitoring:
                        self.monitor.start()
                    self._log('Monitor active — watching for flag drift.', 'info')
            if ok > 0:
                _save_session(flags)
                self._session_flags = flags
                if self._auto_inject_var is not None:
                    self.after(0, lambda /: self._auto_inject_var.set(True))
            self.after(0, lambda /: self._lbl_batch_status.config(text=''))
            self._post(self._UI_EVT_INJECT_DONE, None)
        self._batch_injector = BatchInjector(self.core, self.inj_config, log_cb=_on_log, progress_cb=_on_progress, done_cb=_on_done)
        self._batch_injector.start(flags)
    def _start_uninject(self):
        if self._uninject_busy:
            return
        else:
            if not self.core.pm:
                self._do_log('Roblox not attached.', 'err')
                return
            else:
                if not self.backup.snapshots:
                    self._do_log('No backup available — inject flags first.', 'warn')
                    return
                else:
                    self._uninject_busy = True
                    self._uninject_btn.config(text='Restoring…', state='disabled', bg=C['dim'])
                    threading.Thread(target=self._run_uninject, daemon=True).start()
    def _run_uninject(self):
        try:
            self.monitor.stop()
            self.monitor.clear()
            ok, fail, lines = self.core.uninject(self.backup, self._method)
            for line in lines:
                lvl = 'ok' if line.startswith('[RESTORE]') else 'err'
                self._log(line, lvl)
            self._log(f'Uninject done — {ok:,} restored | {fail:,} failed', 'ok' if fail == 0 else 'warn')
            self.backup.clear()
            _save_session({})
            self._session_flags = {}
            self._auto_inject_pending = False
        finally:
            self._post(self._UI_EVT_UNINJECT_DONE, None)
    def _recover_injected_flags(self, flags: dict):
        if not flags:
            return
        else:
            self._log('Roblox already running — checking flag state…', 'accent')
            reverted = {}
            still_ok = 0
            for raw_key, desired_val in flags.items():
                bare, flag_type = _parse_flag_key(raw_key)
                try:
                    if flag_type in ['FFlag', 'DFFlag']:
                        live = self.core.get_int(bare, self._method)
                        des = 1 if str(desired_val).lower() in ['true', '1'] else 0
                        if live is None or live!= des:
                            reverted[raw_key] = desired_val
                        else:
                            still_ok += 1
                    else:
                        if flag_type in ['FInt', 'DFInt', 'FLog', 'DFLog']:
                            live = self.core.get_int(bare, self._method)
                            if live is None:
                                reverted[raw_key] = desired_val
                            else:
                                try:
                                    if live!= int(str(desired_val)):
                                        reverted[raw_key] = desired_val
                                    else:
                                        still_ok += 1
                                except Exception:
                                    reverted[raw_key] = desired_val
                                else:
                                    pass
                        else:
                            if flag_type in ['FString', 'DFString']:
                                live = self.core.get_string(bare, self._method)
                                if live!= str(desired_val):
                                    reverted[raw_key] = desired_val
                                else:
                                    still_ok += 1
                            else:
                                reverted[raw_key] = desired_val
                except Exception:
                    reverted[raw_key] = desired_val
            if reverted:
                self._log(f'Recovery: {len(reverted)} flag(s) need re-injection, {still_ok} still active.', 'warn')
                self._run_inject(reverted)
            else:
                self._log(f'Recovery: all {still_ok} flag(s) still active — no re-injection needed.', 'ok')
                if self._monitor_enabled:
                    self.monitor.set_flags(flags, self._method)
                    if not self.monitor.monitoring:
                        self.monitor.start()
    def _poll_monitor_stat(self):
        count = self.monitor.reinjected_count
        self._post(self._UI_EVT_MONITOR_STAT, count)
    _WATCHER_POLL_ATTACHED = 1.5
    _WATCHER_POLL_MIN = 0.5
    _WATCHER_POLL_MAX = 8.0
    _WATCHER_BACKOFF_FACTOR = 2.0
    def _watcher_loop(self):
        was_attached = False
        stat_tick = 0
        idle_sleep = self._WATCHER_POLL_MIN
        attach_sleep = self._WATCHER_POLL_MIN
        attach_fail_logged = False
        while True:
            sleep_for = self._WATCHER_POLL_ATTACHED
            try:
                pid = self.core.find_roblox()
                if pid and (not self.core.pm):
                    idle_sleep = self._WATCHER_POLL_MIN
                    if self.core.attach():
                        attach_sleep = self._WATCHER_POLL_MIN
                        attach_fail_logged = False
                        was_attached = True
                        sleep_for = self._WATCHER_POLL_ATTACHED
                        sing = self.core._get_singleton()
                        ver = self.core._detected_version
                        self._post(self._UI_EVT_STATUS, (f'● Roblox  PID {self.core.pid}', C['success']))
                        self._log(f'Attached — PID {self.core.pid} | base 0x{self.core.base:X}', 'ok')
                        if ver:
                            self._log(f'Version: {ver}', 'accent')
                        if sing:
                            self._log(f'Singleton @ 0x{sing:X}', 'accent')
                        if ver:
                            threading.Thread(target=self._bg_fetch_offsets, args=(ver,), daemon=True).start()
                        flags_to_use = copy.copy(self.loaded_flags) if self.loaded_flags else copy.copy(self._session_flags) if self._session_flags else None
                        if flags_to_use and self._auto_inject_pending:
                                already_up = self.core._roblox_already_loaded()
                                if already_up:
                                    threading.Thread(target=self._recover_injected_flags, args=(flags_to_use,), daemon=True).start()
                                else:
                                    def _deferred(f=flags_to_use):
                                        self._log('Waiting for Roblox FFlag map to populate…', 'info')
                                        if self.core._wait_for_ready(timeout=180, log_cb=self._log):
                                            self._log('FFlag map ready — auto-injecting…', 'accent')
                                            self._run_inject_sync(f)
                                        else:
                                            self._log('Timed out waiting for Roblox FFlag map.', 'err')
                                    threading.Thread(target=_deferred, daemon=True).start()
                    else:
                        if not attach_fail_logged:
                            self._log(f'Roblox found (PID {pid}) but attach failed — retrying with back-off…', 'warn')
                            attach_fail_logged = True
                        sleep_for = attach_sleep
                        attach_sleep = min(attach_sleep * self._WATCHER_BACKOFF_FACTOR, self._WATCHER_POLL_MAX)
                else:
                    if pid and self.core.pm:
                        idle_sleep = self._WATCHER_POLL_MIN
                        attach_fail_logged = False
                        sleep_for = self._WATCHER_POLL_ATTACHED
                    else:
                        if not pid and was_attached:
                            self.core.detach()
                            was_attached = False
                            attach_fail_logged = False
                            idle_sleep = self._WATCHER_POLL_MIN
                            attach_sleep = self._WATCHER_POLL_MIN
                            sleep_for = self._WATCHER_POLL_MIN
                            self.monitor.stop()
                            self._post(self._UI_EVT_STATUS, ('● Waiting for Roblox', C['warning']))
                            self._log('Lost Roblox process.', 'err')
                        else:
                            attach_fail_logged = False
                            sleep_for = idle_sleep
                            idle_sleep = min(idle_sleep * self._WATCHER_BACKOFF_FACTOR, self._WATCHER_POLL_MAX)
                stat_tick += 1
                if stat_tick >= 4:
                    stat_tick = 0
                    self._poll_monitor_stat()
            except Exception:
                sleep_for = idle_sleep
                idle_sleep = min(idle_sleep * self._WATCHER_BACKOFF_FACTOR, self._WATCHER_POLL_MAX)
            time.sleep(sleep_for)
    def _bg_fetch_offsets(self, version: str=''):
        ver = version or self.core._detected_version
        ok, msg, count = self.offsets.fetch_and_load(version=ver)
        sing_addr = self.core._cached_singleton if self.core._cached_singleton else self.offsets.singleton_ptr_rva
        if ok:
            status_text = f'Offsets OK · {self.offsets.source}'
            if count:
                status_text += f' · {count:,} RVAs'
        else:
            status_text = 'Offsets: FAILED — using hardcoded'
        singleton_text = f'Singleton: 0x{sing_addr:X}'
        self._post(self._UI_EVT_OFFSET_INFO, (status_text, singleton_text, 0))
        self._log(msg, 'ok' if ok else 'err')
    def _toggle_monitor(self):
        self._monitor_enabled = self._mon_var.get()
        if not self._monitor_enabled:
            self.monitor.stop()
            self._do_log('Monitor disabled.', 'warn')
            return
        else:
            if self.loaded_flags and self.core.pm:
                    self.monitor.set_flags(self.loaded_flags, self._method)
                    self.monitor.start()
            self._do_log('Monitor enabled.', 'ok')
    def _toggle_auto_inject(self):
        enabled = self._auto_inject_var.get()
        if enabled:
            flags = self.loaded_flags or self._session_flags
            if flags:
                _save_session(flags)
                self._session_flags = flags
                self._do_log(f'Auto-inject ON — {len(flags):,} flag(s) saved for next boot.', 'ok')
            else:
                self._auto_inject_var.set(False)
                self._do_log('Auto-inject: no flags loaded. Import and save first.', 'warn')
        else:
            _save_session({})
            self._session_flags = {}
            self._auto_inject_pending = False
            self._do_log('Auto-inject OFF — session cleared.', 'warn')
    def _toggle_timed_mode(self):
        enabled = self._timed_mode_var.get()
        self.inj_config.timed_mode = enabled
        if enabled:
            self._do_log(f'Timed batch mode ON — {self.inj_config.batch_size} flags / batch, {self.inj_config.batch_delay:.1f}s delay.', 'ok')
        else:
            self._do_log('Instant injection mode ON.', 'ok')
    def _abort_inject(self):
        if self._batch_injector and self._batch_injector.running:
            self._batch_injector.abort()
            self._do_log('Abort requested — stopping after current batch.', 'warn')
        else:
            self._do_log('No injection running.', 'info')
    def _start_validate(self):
        if self._validate_busy:
            self._do_log('Validation already running…', 'warn')
            return
        else:
            if not self.loaded_flags:
                self._do_log('No flags loaded — import a JSON first.', 'warn')
                return
            else:
                if not self.core.pm:
                    self._do_log('Roblox not attached — launch Roblox first.', 'err')
                    return
                else:
                    if not self.core._roblox_already_loaded():
                        self._do_log('FFlag map not ready yet — wait for Roblox to finish loading.', 'warn')
                        return
                    else:
                        self._validate_busy = True
                        self._validate_btn.config(text='Validating…', state='disabled', bg=C['dim'])
                        self._progress_var.set(0)
                        threading.Thread(target=self._run_validate, args=(copy.copy(self.loaded_flags),), daemon=True).start()
    def _run_validate(self, flags: dict):
        try:
            def progress_cb(done, total, _ok, _fail):
                self._post(self._UI_EVT_PROGRESS, (done, total))
            _ok, _fail, lines = self.core.inject(flags, self._method, progress_cb=progress_cb)
            ok_flags = {}
            for line in lines:
                if line.startswith('[OK]'):
                    body = line[5:].strip()
                    eq = body.find(' = ')
                    raw_key = body[:eq].strip() if eq!= (-1) else body
                    if raw_key in flags:
                        ok_flags[raw_key] = flags[raw_key]
            self._ok_flags = ok_flags
            for line in lines:
                self._log(line, 'ok' if line.startswith('[OK]') else 'err')
            self._post(self._UI_EVT_VALIDATE_DONE, (len(ok_flags), len(flags)))
        except Exception as e:
            self._log(f'Validation error: {e}', 'err')
            self._post(self._UI_EVT_VALIDATE_DONE, (0, len(flags)))
    def _export_valid_flags(self):
        if not self._ok_flags:
            self._do_log('No validated flags — run Validate first.', 'warn')
            return
        else:
            path = filedialog.asksaveasfilename(defaultextension='.json', filetypes=[('JSON files', '*.json'), ('All files', '*.*')], initialfile='valid_flags.json', title='Export Valid Flags')
            if not path:
                return
            else:
                try:
                    with open(path, 'w', encoding='utf-8') as f:
                        json.dump(self._ok_flags, f, indent=2, ensure_ascii=False)
                    self._do_log(f'Exported {len(self._ok_flags):,} valid flags → {Path(path).name}', 'ok')
                except Exception as e:
                    messagebox.showerror('Export Error', str(ex))
                    self._do_log(f'Export failed: {e}', 'err')
    def _save_flags(self):
        if not self.loaded_flags:
            self._do_log('No flags loaded — import a JSON first.', 'warn')
            return
        else:
            _save_session(self.loaded_flags)
            self._session_flags = copy.copy(self.loaded_flags)
            self._auto_inject_pending = True
            self._auto_inject_var.set(True)
            self._do_log(f'Saved {len(self.loaded_flags):,} flag(s) — will auto-inject on next boot.', 'ok')
    def _set_method(self, method: str):
        self._method = method
        for key, btn in self._method_btns.items():
            btn.config(bg=C['accent'] if key == method else C['card'])
        self._do_log(f'Method → {method.upper()}', 'info')
    def _clear_flags(self):
        self.loaded_flags.clear()
        self._render_table({})
        self._do_log('All flags cleared.', 'warn')
        self.file_watcher.stop()
        self._watching_file = False
        self._post(self._UI_EVT_FILE_WATCH, (False, ''))
    def _update_flag(self, name: str, new_val: str):
        if name in self.loaded_flags and self.loaded_flags[name]!= new_val:
                self.loaded_flags[name] = new_val
                self._do_log(f'Updated {name} = {new_val}', 'info')
    def _delete_flag(self, name: str, row: tk.Frame):
        self.loaded_flags.pop(name, None)
        try:
            row.destroy()
        except:
            pass
        self._flag_rows = [r for r in self._flag_rows if r.winfo_exists()]
        self._lbl_count.config(text=f'{len(self.loaded_flags)} flags')
        self._stat_labels['loaded'].config(text=str(len(self.loaded_flags)))
        self._do_log(f'Deleted: {name}', 'warn')
def _run_batch_cli(args: 'argparse.Namespace') -> None:
    # irreducible cflow, using cdg fallback
    def _print(msg: str, level: str='info') -> None:
        tag = {'ok': 'OK  ', 'err': 'ERR ', 'warn': 'WARN', 'accent': 'INFO', 'info': 'INFO'}.get(level, 'INFO')
        print(f'[{tag}] {msg}', flush=True)
    core = None
    offsets = OffsetStore()
    try:
        flags = load_flags_from_file(args.batch)
    except Exception as e:
        _print(f'Failed to load \'{args.batch}\': {e}', 'err')
        sys.exit(1)
    _print(f'Loaded {len(flags):,} flag(s) from {Path(args.batch).name}')
    _print('Loading offsets…')
    ok_off, msg_off, _ = offsets.fetch_and_load()
    _print(msg_off, 'ok' if ok_off else 'warn')
    core = BreadCore(offsets)
    _print(f'Waiting for Roblox (timeout {args.wait_timeout:.0f}s)…')
    attach_deadline = time.monotonic() + args.wait_timeout
    attach_sleep = 0.5
    attached = False
    while time.monotonic() < attach_deadline:
        if core.attach():
            attached = True
            break
        remaining = attach_deadline - time.monotonic()
        time.sleep(min(attach_sleep, max(0.0, remaining)))
        attach_sleep = min(attach_sleep * 2.0, 4.0)
    if not attached:
        _print('Timed out waiting for Roblox.', 'err')
        sys.exit(1)
    _print(f"Attached — PID {core.pid} | base 0x{core.base:X} | ver {core._detected_version or 'unknown'}", 'ok')
    _print('Waiting for FFlag map…')
    map_ready = core._wait_for_ready(timeout=args.wait_timeout, log_cb=lambda m, _: _print(m))
    if not map_ready:
        _print('FFlag hash-map never reached production size.', 'err')
        sys.exit(1)
    _print('FFlag map ready.', 'ok')
    config = InjectionConfig(timed_mode=args.timed, batch_size=args.batch_size, batch_delay=args.batch_delay, fast_throttle=0.0)
    mode_str = f'timed batch ({args.batch_size} flags / {args.batch_delay:.1f}s)' if args.timed else 'instant'
    _print(f'Starting injection — {len(flags):,} flag(s), mode: {mode_str}')
    done_evt = threading.Event()
    result_ok = [0]
    result_fail = [0]
    def _on_log(msg: str, lvl: str='info') -> None:
        # irreducible cflow, using cdg fallback
        if getattr(args, 'verbose', False) or (not msg.startswith('[OK]') and (not msg.startswith('[FAIL]'))):
                    _print(msg, lvl)
    def _on_progress(done: int, total: int, ok: int, fail: int) -> None:
        pct = done / total * 100 if total else 0
        print(f'\r[PROG] {done:>5}/{total}  {pct:5.1f}%  OK={ok}  FAIL={fail}   ', end='', flush=True)
    def _on_done(ok: int, fail: int) -> None:
        result_ok[0] = ok
        result_fail[0] = fail
        done_evt.set()
    bi = BatchInjector(core, config, log_cb=_on_log, progress_cb=_on_progress, done_cb=_on_done)
    bi.start(flags)
    done_evt.wait(timeout=args.wait_timeout + len(flags) * 0.1 + 120)
    print()
    ok = result_ok[0]
    fail = result_fail[0]
    _print(f'Done — {ok:,} OK | {fail:,} FAIL | {ok + fail:,} total', 'ok' if fail == 0 else 'warn')
    sys.exit(0 if fail == 0 else 1)
                    if core is not None:
                        try:
                            core.detach()
                        except Exception:
                            return
        except KeyboardInterrupt:
            print()
            _print('Interrupted by user.', 'warn')
            sys.exit(130)
                        try:
                            pass
def main() -> None:
    parser = argparse.ArgumentParser(prog='bread', description='Bread — Roblox FastFlag Injector', formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--batch', metavar='FLAGS_JSON', help='Headless batch mode: load flags from FLAGS_JSON, wait for\nRoblox, inject, print summary, exit.  No GUI is opened.\nExit code: 0 = all flags OK, 1 = any FAIL, 130 = interrupted.')
    parser.add_argument('--timed', action='store_true', help='Use timed batch injection instead of instant mode.\nIn GUI mode: opens the app with timed-batch pre-selected.\nIn --batch mode: enables inter-batch sleep (see --batch-delay).')
    parser.add_argument('--batch-size', type=int, default=100, metavar='N', help='Flags per batch in timed mode (default: 100).')
    parser.add_argument('--batch-delay', type=float, default=5.0, metavar='SECS', help='Seconds between batches in timed mode (default: 5.0).')
    parser.add_argument('--wait-timeout', type=float, default=180.0, metavar='SECS', help='Seconds to wait for Roblox / FFlag map in --batch mode\n(default: 180).')
    parser.add_argument('--verbose', action='store_true', help='In --batch mode: print every [OK]/[FAIL] line (may be thousands).')
    args = parser.parse_args()
    if _IS_WINDOWS:
        try:
            is_admin = ctypes.windll.shell32.IsUserAnAdmin()
        except Exception:
            is_admin = False
        if not is_admin:
            ctypes.windll.shell32.ShellExecuteW(None, 'runas', sys.executable, ' '.join((f'\"{a}\"' for a in sys.argv)), None, 1)
            sys.exit(0)
    if args.batch:
        _run_batch_cli(args)
    else:
        app = BreadApp(cli_timed=args.timed)
        app.mainloop()
if __name__ == '__main__':
    main()