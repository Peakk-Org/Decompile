#!/usr/bin/env python3
"""
$Decompile - a dark/red workbench that turns a Windows .exe back into source
code, lets you edit it, and rebuilds it.

  python main.py                      open the GUI
  python main.py tools                show which decompilers are installed
  python main.py install all          download + install every missing tool
  python main.py analyze  app.exe     identify the file (nothing is written)
  python main.py decompile app.exe -o out
  python main.py rebuild out          compile the (edited) source again

Backends (installed on demand into a private folder, nothing system-wide):
  .NET exe        ILSpy (ilspycmd)                  -> C# project
  PyInstaller exe pycdc / decompyle3 / uncompyle6   -> .py files
  native exe      Ghidra (headless)                 -> C pseudocode

The target file is never executed. Only analyse software you own or are
authorised to analyse. Requires Python 3.10+ and no third-party packages.
"""
from __future__ import annotations

import argparse
import ast
import base64
import hashlib
import importlib.util
import json
import marshal
import os
import platform
import re
import shutil
import struct
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
import zlib
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

if sys.version_info < (3, 10):
    sys.exit("$Decompile needs Python 3.10 or newer.")

APP_NAME = "$Decompile"
VERSION = "1.0"
IS_WIN = os.name == "nt"
IS_MAC = sys.platform == "darwin"


def exe(name: str) -> str:
    return name + ".exe" if IS_WIN else name


def _flags() -> int:
    return subprocess.CREATE_NO_WINDOW if IS_WIN else 0


# --------------------------------------------------------------------------- #
# Messaging hooks (the GUI plugs into these; the CLI just prints)
# --------------------------------------------------------------------------- #
_log_sink: Callable[[str, str], None] | None = None
_prog_sink: Callable[[float | None, str], None] | None = None
_last_prog = [0.0]


def set_log_sink(fn):
    global _log_sink
    _log_sink = fn


def set_progress_sink(fn):
    global _prog_sink
    _prog_sink = fn


def _emit(level: str, msg: str) -> None:
    if _log_sink:
        _log_sink(level, msg)
    else:
        tag = {"info": "[*]", "ok": "[+]", "warn": "[!]", "bad": "[x]", "out": "   "}[level]
        print(tag, msg, file=sys.stderr if level == "bad" else sys.stdout, flush=True)


def say(m: str) -> None: _emit("info", m)
def ok(m: str) -> None: _emit("ok", m)
def warn(m: str) -> None: _emit("warn", m)
def bad(m: str) -> None: _emit("bad", m)
def out(m: str) -> None: _emit("out", m)


def progress(frac: float | None, text: str = "") -> None:
    now = time.monotonic()
    if frac is not None and 0 < frac < 1 and now - _last_prog[0] < 0.12:
        return
    _last_prog[0] = now
    if _prog_sink:
        _prog_sink(frac, text)
    elif frac is not None and sys.stdout.isatty():
        print(f"\r    {text} {frac * 100:3.0f}%", end="" if frac < 1 else "\n", flush=True)


class ToolError(Exception):
    """A problem worth showing to the user without a traceback."""


STOP = threading.Event()
_procs: set[subprocess.Popen] = set()


def cancel_all() -> None:
    STOP.set()
    for p in list(_procs):
        try:
            p.kill()
        except OSError:
            pass


def check_stop() -> None:
    if STOP.is_set():
        raise ToolError("Cancelled.")


# --------------------------------------------------------------------------- #
# Folders
# --------------------------------------------------------------------------- #
def is_store_python() -> bool:
    """Microsoft Store Python runs inside an MSIX sandbox that silently redirects %LOCALAPPDATA%: files it writes
    there are invisible to every other program it starts (PowerShell, Zig, Ghidra ...)."""
    if not IS_WIN:
        return False
    for p in (sys.executable, getattr(sys, "base_prefix", ""), getattr(sys, "_base_executable", "")):
        low = str(p or "").lower()
        if "\\windowsapps\\" in low or "pythonsoftwarefoundation" in low:
            return True
    return False


def data_dir() -> Path:
    override = os.environ.get("DOLLAR_DECOMPILE_HOME")
    if override:
        return Path(override).expanduser()
    if IS_WIN:
        in_home = Path.home() / "DollarDecompile"  # outside AppData, so never sandbox-redirected
        in_appdata = Path(os.environ.get("LOCALAPPDATA") or Path.home() / "AppData" / "Local") / "DollarDecompile"
        return in_home if (is_store_python() or (in_home.exists() and not in_appdata.exists())) else in_appdata
    if IS_MAC:
        base = Path.home() / "Library" / "Application Support"
    else:
        base = Path(os.environ.get("XDG_DATA_HOME") or Path.home() / ".local" / "share")
    return base / "DollarDecompile"


TOOLS = data_dir() / "tools"
DOWNLOADS = TOOLS / "downloads"


def dd_tempdir(prefix: str) -> tempfile.TemporaryDirectory:
    """Temp folder INSIDE our data folder (the system temp folder is sandbox-redirected for Store Python)."""
    base = TOOLS.parent / "tmp"
    base.mkdir(parents=True, exist_ok=True)
    return tempfile.TemporaryDirectory(prefix=prefix, dir=str(base))

CONFIG_PATH = TOOLS.parent / "config.json"
_cfg: dict | None = None
_cfg_lock = threading.RLock()


def load_config() -> dict:
    """Small JSON file remembering where the PC scan found tools."""
    global _cfg
    with _cfg_lock:
        if _cfg is None:
            try:
                data = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
                _cfg = data if isinstance(data, dict) else {}
            except (OSError, ValueError):
                _cfg = {}
            if not isinstance(_cfg.get("paths"), dict):
                _cfg["paths"] = {}
        return _cfg


def save_config() -> None:
    with _cfg_lock:
        try:
            CONFIG_PATH.parent.mkdir(parents=True, exist_ok=True)
            tmp = CONFIG_PATH.with_suffix(".tmp")
            tmp.write_text(json.dumps(load_config(), indent=2), encoding="utf-8")
            tmp.replace(CONFIG_PATH)
        except OSError as exc:
            warn(f"Could not save settings: {exc}")


def _registered(key: str) -> str | None:
    """Path remembered by a PC scan, if it still exists."""
    p = load_config()["paths"].get(key)
    return p if isinstance(p, str) and Path(p).is_file() else None


def open_path(p: Path | str) -> None:
    p = str(p)
    try:
        if IS_WIN:
            os.startfile(p)  # type: ignore[attr-defined]
        elif IS_MAC:
            subprocess.Popen(["open", p])
        else:
            subprocess.Popen(["xdg-open", p])
    except OSError as exc:
        warn(f"Could not open {p}: {exc}")


# --------------------------------------------------------------------------- #
# Safe file helpers (inputs may be hostile)
# --------------------------------------------------------------------------- #
MAX_UNPACK = 512 * 1024 * 1024


def safe_join(base: Path, rel: str) -> Path:
    base = base.resolve()
    target = (base / rel.replace("\\", "/").lstrip("/")).resolve()
    if target != base and not target.is_relative_to(base):
        raise ValueError(f"unsafe path: {rel!r}")
    return target


def safe_decompress(raw: bytes) -> bytes:
    d = zlib.decompressobj()
    data = d.decompress(raw, MAX_UNPACK)
    if d.unconsumed_tail:
        raise ValueError("decompressed size exceeds the safety limit")
    return data


def write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def fresh_dir(p: Path) -> Path:
    """Recreate an (empty) directory, but only inside our private tools folder."""
    p = p.resolve()
    if TOOLS.resolve() not in p.parents:
        raise ToolError("refusing to modify a folder outside the tools directory")
    if p.exists():
        shutil.rmtree(p, ignore_errors=True)
    p.mkdir(parents=True)
    return p


# --------------------------------------------------------------------------- #
# Subprocess helpers
# --------------------------------------------------------------------------- #
def run_stream(cmd: list, *, cwd=None, env=None, timeout: int | None = None) -> int:
    """Run a command, streaming its output into the log. Returns the exit code."""
    check_stop()
    argv = [str(c) for c in cmd]
    say("$ " + subprocess.list2cmdline(argv))
    try:
        p = subprocess.Popen(
            argv, cwd=cwd, env=env or tool_env(), stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            encoding="utf-8", errors="replace", creationflags=_flags(),
        )
    except OSError as exc:
        raise ToolError(f"could not start {Path(argv[0]).name}: {exc}") from None
    _procs.add(p)
    timer = threading.Timer(timeout, p.kill) if timeout else None
    if timer:
        timer.start()
    try:
        assert p.stdout is not None
        for line in p.stdout:
            line = line.rstrip()
            if line:
                out(line)
        rc = p.wait()
    finally:
        if timer:
            timer.cancel()
        _procs.discard(p)
    check_stop()
    return rc


def run_capture(cmd: list, timeout: int = 60, env=None, cwd=None) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(c) for c in cmd], capture_output=True, text=True, encoding="utf-8", errors="replace",
        timeout=timeout, env=env or tool_env(), cwd=cwd, stdin=subprocess.DEVNULL, creationflags=_flags(),
    )


# --------------------------------------------------------------------------- #
# Downloading
# --------------------------------------------------------------------------- #
def http_open(url: str, timeout: int = 60):
    req = urllib.request.Request(url, headers={"User-Agent": f"DollarDecompile/{VERSION}"})
    try:
        return urllib.request.urlopen(req, timeout=timeout)
    except urllib.error.HTTPError as exc:
        raise ToolError(f"HTTP {exc.code} while fetching {url}") from None
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        raise ToolError(f"Network error for {url}: {exc}. Check your connection, proxy or firewall.") from None


def download(url: str, dest: Path, *, sha256: str | None = None, label: str = "", hash_note: bool = True) -> Path:
    dest.parent.mkdir(parents=True, exist_ok=True)
    part = dest.with_suffix(dest.suffix + ".part")
    h = hashlib.sha256()
    done = 0
    try:
        with http_open(url) as r, open(part, "wb") as f:
            total = int(r.headers.get("Content-Length") or 0)
            while True:
                check_stop()
                chunk = r.read(1 << 16)
                if not chunk:
                    break
                f.write(chunk)
                h.update(chunk)
                done += len(chunk)
                progress(done / total if total else None,
                         f"{label} {done / 1e6:.0f}" + (f" / {total / 1e6:.0f} MB" if total else " MB"))
    except BaseException:
        part.unlink(missing_ok=True)
        raise
    if sha256:
        if h.hexdigest().lower() != sha256.lower():
            part.unlink(missing_ok=True)
            raise ToolError(f"Checksum mismatch for {dest.name}: the download is corrupt or was tampered with.")
        ok(f"SHA-256 verified for {dest.name}")
    elif hash_note:
        warn(f"No published checksum for {dest.name}; downloaded over HTTPS from {urllib.parse.urlparse(url).netloc}.")
    part.replace(dest)
    progress(1.0, f"{label} done")
    return dest


Asset = tuple[str, str, "str | None"]  # (name, url, sha256)


def github_latest(repo: str) -> tuple[str, list[Asset]]:
    """Latest release of a GitHub repo. Uses the API, falls back to the release
    page when the API is rate-limited (60 requests/hour per IP)."""
    try:
        with http_open(f"https://api.github.com/repos/{repo}/releases/latest", 30) as r:
            data = json.load(r)
        assets = [(a["name"], a["browser_download_url"], (a.get("digest") or "").removeprefix("sha256:") or None)
                  for a in data["assets"]]
        return data["tag_name"], assets
    except (ToolError, ValueError, KeyError):
        pass
    with http_open(f"https://github.com/{repo}/releases/latest", 30) as r:
        tag = r.geturl().rsplit("/tag/", 1)[-1]
    with http_open(f"https://github.com/{repo}/releases/expanded_assets/{tag}", 30) as r:
        html = r.read().decode("utf-8", "replace")
    pat = re.compile(r'href="(/' + re.escape(repo) + r'/releases/download/[^"/]+/([^"]+))"')
    found = list(pat.finditer(html))
    assets, seen = [], set()
    for i, m in enumerate(found):
        name = urllib.parse.unquote(m.group(2))
        if name in seen:
            continue
        seen.add(name)
        end = found[i + 1].start() if i + 1 < len(found) else len(html)
        d = re.search(r"sha256:([0-9a-f]{64})", html[m.end():end])
        assets.append((name, "https://github.com" + m.group(1), d.group(1) if d else None))
    if not assets:
        raise ToolError(f"Could not read the latest release of {repo}.")
    return urllib.parse.unquote(tag), assets


def pick_asset(assets: list[Asset], pattern: str) -> Asset:
    rx = re.compile(pattern)
    for a in assets:
        if rx.search(a[0]):
            return a
    raise ToolError(f"No download matches {pattern!r}; this platform may not be supported.")


def extract_archive(arc: Path, dest: Path, label: str = "Extracting") -> None:
    try:
        _extract_archive(arc, dest, label)
    except ToolError:
        raise
    except Exception as exc:  # noqa: BLE001 - bad zip/tar/xz, unsafe path, disk full ...
        raise ToolError(f"Could not unpack {arc.name}: {exc}") from None


def _extract_archive(arc: Path, dest: Path, label: str) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    name = arc.name.lower()
    if name.endswith(".zip"):
        with zipfile.ZipFile(arc) as z:
            members = z.infolist()
            for i, m in enumerate(members):
                check_stop()
                target = safe_join(dest, m.filename)
                if IS_WIN:  # Ghidra's archive has deep paths; the \\?\ prefix lifts the 260-character limit
                    target = Path("\\\\?\\" + str(target))
                if m.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                    continue
                target.parent.mkdir(parents=True, exist_ok=True)
                with z.open(m) as s, open(target, "wb") as d:
                    shutil.copyfileobj(s, d)
                mode = m.external_attr >> 16
                if mode and not IS_WIN:
                    os.chmod(target, (mode & 0o777) | 0o600)
                progress(i / len(members), f"{label} {i}/{len(members)}")
    elif name.endswith((".tar.gz", ".tgz", ".tar.xz")):
        with tarfile.open(arc) as t:
            members = t.getmembers()
            for i, m in enumerate(members):
                check_stop()
                safe_join(dest, m.name)
                if m.issym() or m.islnk():
                    safe_join(dest, str(Path(m.name).parent / m.linkname) if m.issym() else m.linkname)
                t.extract(m, dest, **({"filter": "data"} if hasattr(tarfile, "data_filter") else {}))
                progress(i / len(members), f"{label} {i}/{len(members)}")
    else:
        raise ToolError(f"Unsupported archive type: {arc.name}")
    progress(1.0, f"{label} done")


def install_asset(asset: Asset, dest: Path, label: str) -> None:
    name, url, sha = asset
    arc = download(url, DOWNLOADS / name, sha256=sha, label=label)
    try:
        extract_archive(arc, fresh_dir(dest), f"Extracting {label}")
    finally:
        arc.unlink(missing_ok=True)


# --------------------------------------------------------------------------- #
# Tool discovery
# --------------------------------------------------------------------------- #
def _first_glob(base: Path, *patterns: str) -> str | None:
    for pat in patterns:
        for p in sorted(base.glob(pat)):
            if p.is_file():
                return str(p)
    return None


def py_exe() -> str:
    """The Python that is running this app (never pythonw.exe: tools need a normal console interpreter)."""
    p = Path(sys.executable or "python")
    if IS_WIN and p.name.lower() == "pythonw.exe" and p.with_name("python.exe").is_file():
        return str(p.with_name("python.exe"))
    return str(p)


def pylib_dir(name: str) -> Path:
    return TOOLS / "pylibs" / name


def pylib_ok(name: str, package: str) -> Path | None:
    """Folder of a private 'pip --target' install, if it is complete and was built for this Python."""
    d = pylib_dir(name)
    try:
        if (d / package / "__init__.py").is_file() and (d / ".pyver").read_text().strip() == f"{sys.version_info[0]}.{sys.version_info[1]}":
            return d
    except OSError:
        pass
    return None


def pylib_entry(lib: Path, script: str) -> tuple[str, str] | None:
    """module, function of a pip console script (read from the package metadata)."""
    for ep in lib.glob("*.dist-info/entry_points.txt"):
        try:
            in_scripts = False
            for line in ep.read_text(encoding="utf-8", errors="replace").splitlines():
                line = line.strip()
                if line.startswith("["):
                    in_scripts = line == "[console_scripts]"
                elif in_scripts and "=" in line:
                    name, target = (x.strip() for x in line.split("=", 1))
                    if name == script and target:
                        mod, _, func = target.split()[0].partition(":")
                        return mod, func
        except OSError:
            continue
    return None


def _with_pythonpath(extra: dict) -> dict:
    env = tool_env()
    if "PYTHONPATH" in extra:
        env["PYTHONPATH"] = extra["PYTHONPATH"] + os.pathsep + env.get("PYTHONPATH", "")
    return env


_java_cache: dict[str, int] = {}
_dotnet_cache: dict[str, int] = {}


def java_major(java: str) -> int:
    if java in _java_cache:
        return _java_cache[java]
    major = 0
    try:
        r = run_capture([java, "-version"], timeout=30, env=os.environ.copy())
        m = re.search(r'version "(\d+)(?:\.(\d+))?', r.stderr + r.stdout)
        if m:
            v = int(m.group(1))
            major = int(m.group(2)) if v == 1 and m.group(2) else v
    except (OSError, subprocess.SubprocessError):
        pass
    if major:  # never cache failures: the tool may be installed later
        _java_cache[java] = major
    return major


def dotnet_sdk_major(dotnet: str) -> int:
    """Highest installed .NET SDK major version (0 = runtime only or not working)."""
    if dotnet in _dotnet_cache:
        return _dotnet_cache[dotnet]
    major = 0
    try:
        r = run_capture([dotnet, "--list-sdks"], timeout=40, env=os.environ.copy())
        major = max((int(m.group(1)) for m in re.finditer(r"^\s*(\d+)\.", r.stdout, re.M)), default=0)
    except (OSError, subprocess.SubprocessError):
        pass
    if major:
        _dotnet_cache[dotnet] = major
    return major


def find_java_home() -> Path | None:
    cands: list[str] = []
    p = _first_glob(TOOLS / "jdk", f"*/bin/{exe('java')}", f"*/Contents/Home/bin/{exe('java')}")
    if p:
        cands.append(p)
    reg = _registered("jdk")
    if reg:
        cands.append(reg)
    if os.environ.get("JAVA_HOME"):
        cands.append(str(Path(os.environ["JAVA_HOME"]) / "bin" / exe("java")))
    w = shutil.which("java")
    if w:
        cands.append(os.path.realpath(w))
    for c in cands:  # Ghidra needs a full JDK (javac present), not just a JRE
        home = Path(c).parent.parent
        if Path(c).is_file() and (home / "bin" / exe("javac")).is_file() and java_major(c) >= 21:
            return home
    return None


def find_java() -> str | None:
    home = find_java_home()
    return str(home / "bin" / exe("java")) if home else None


def find_ghidra() -> str | None:
    script = "analyzeHeadless.bat" if IS_WIN else "analyzeHeadless"
    hit = _first_glob(TOOLS / "ghidra", f"*/support/{script}") or _registered("ghidra")
    if hit:
        return hit
    base = os.environ.get("GHIDRA_INSTALL_DIR") or os.environ.get("GHIDRA_HOME")
    if base and (Path(base) / "support" / script).is_file():
        return str(Path(base) / "support" / script)
    return shutil.which("analyzeHeadless")


def find_dotnet() -> str | None:
    cands = []
    if (TOOLS / "dotnet" / exe("dotnet")).is_file():
        cands.append(str(TOOLS / "dotnet" / exe("dotnet")))
    reg = _registered("dotnet")
    if reg:
        cands.append(reg)
    w = shutil.which("dotnet")
    if w:
        cands.append(w)
    for c in cands:
        if dotnet_sdk_major(c) >= 8:
            return c
    return None


def find_ilspy() -> str | None:
    return _first_glob(TOOLS / "ilspycmd", exe("ilspycmd")) or _registered("ilspycmd") or shutil.which("ilspycmd")


def find_upx() -> str | None:
    return _first_glob(TOOLS / "upx", f"*/{exe('upx')}", exe("upx")) or _registered("upx") or shutil.which("upx")


def find_pycdc() -> str | None:
    return _first_glob(TOOLS / "pycdc", exe("pycdc")) or _registered("pycdc") or shutil.which("pycdc")


def find_uncompyle6() -> str | None:
    d = pylib_ok("dec6", "uncompyle6")
    return str(d / "uncompyle6") if d else (_registered("uncompyle6") or shutil.which("uncompyle6"))


def find_decompyle3() -> str | None:
    d = pylib_ok("dec3", "decompyle3")
    return str(d / "decompyle3") if d else (_registered("decompyle3") or shutil.which("decompyle3"))


def find_pyinstaller() -> str | None:
    d = pylib_ok("build", "PyInstaller")
    return str(d / "PyInstaller") if d else (_registered("pyinstaller") or shutil.which("pyinstaller"))


def find_zig() -> str | None:
    d = pylib_ok("zig", "ziglang")
    if d and (d / "ziglang" / exe("zig")).is_file():
        return str(d / "ziglang" / exe("zig"))
    return _registered("zig") or shutil.which("zig")


def tool_cmd(key: str) -> tuple[list[str], dict] | None:
    """(argv prefix, extra env) that runs a Python-based tool, wherever it lives."""
    path = tool_path(key)
    if not path:
        return None
    p = Path(path)
    if p.is_dir() and key in ("uncompyle6", "decompyle3"):  # our private pip --target folder
        ep = pylib_entry(p.parent, key)
        if not ep:
            return None
        code = f"import sys; from {ep[0]} import {ep[1]} as _m; sys.exit(_m())"
        return [py_exe(), "-c", code], {"PYTHONPATH": str(p.parent)}
    return [path], {}


def pyinstaller_cmd() -> tuple[list[str], dict] | None:
    """How to start PyInstaller: our private copy, or whichever one the PC scan found."""
    d = pylib_ok("build", "PyInstaller")
    if d:
        return [py_exe(), "-m", "PyInstaller"], {"PYTHONPATH": str(d)}
    script = find_pyinstaller()
    return ([script], {}) if script else None


def build_python() -> str | None:
    """The Python that owns an EXTERNAL PyInstaller (scan-found / on PATH), to pip-install a program's dependencies."""
    script = find_pyinstaller()
    if script and not Path(script).is_dir():
        if not IS_WIN:  # pip's scripts start with '#!/path/to/python': that is the owning interpreter
            try:
                with open(script, "rb") as f:
                    first = f.readline(512).decode("utf-8", "replace").strip()
                if first.startswith("#!"):
                    parts = first[2:].split()
                    if parts and Path(parts[0]).name == "env" and len(parts) > 1:
                        found = shutil.which(parts[1])
                        if found:
                            return found
                    elif parts and Path(parts[0]).is_file():
                        return parts[0]
            except OSError:
                pass
        base = Path(script).parent
        for d in (base, base.parent):
            for n in (("python.exe",) if IS_WIN else ("python3", "python")):
                if (d / n).is_file():
                    return str(d / n)
    return None


def tool_env() -> dict:
    env = os.environ.copy()
    paths = []
    home = find_java_home()
    if home:
        env["JAVA_HOME"] = str(home)
        paths.append(str(home / "bin"))
    dn = TOOLS / "dotnet"
    if (dn / exe("dotnet")).is_file():
        dotnet_root: Path | None = dn
    else:
        reg = _registered("dotnet")
        dotnet_root = Path(reg).parent if reg else None
    if dotnet_root:
        env["DOTNET_ROOT"] = str(dotnet_root)
        paths.append(str(dotnet_root))
    env["DOTNET_CLI_TELEMETRY_OPTOUT"] = "1"
    env["DOTNET_NOLOGO"] = "1"
    env["DOTNET_ROLL_FORWARD"] = "Major"
    env["ZIG_GLOBAL_CACHE_DIR"] = str(TOOLS / "zig-cache")
    env["ZIG_LOCAL_CACHE_DIR"] = str(TOOLS / "zig-cache" / "local")
    env["PATH"] = os.pathsep.join(paths + [env.get("PATH", "")])
    return env


# --------------------------------------------------------------------------- #
# Tool installers
# --------------------------------------------------------------------------- #
def _plat() -> tuple[str, str]:
    arch = "aarch64" if platform.machine().lower() in ("arm64", "aarch64") else "x64"
    return arch, ("windows" if IS_WIN else "mac" if IS_MAC else "linux")


def ensure_pip(py: str) -> None:
    if run_capture([py, "-m", "pip", "--version"], timeout=90, env=os.environ.copy()).returncode == 0:
        return
    say("pip is missing - installing it with ensurepip...")
    run_stream([py, "-m", "ensurepip", "--upgrade", "--user"], timeout=600, env=os.environ.copy())
    if run_capture([py, "-m", "pip", "--version"], timeout=90, env=os.environ.copy()).returncode != 0:
        raise ToolError(f"pip is not available for {py}. Run:  \"{py}\" -m ensurepip --upgrade")


def pip_install_with(py: str, *pkgs: str) -> None:
    """pip install into whatever environment owns *py* (used for external Pythons)."""
    if any(p.startswith("-") for p in pkgs):
        raise ToolError("Package names cannot start with '-'.")
    progress(None, f"pip install {' '.join(pkgs)}")
    rc = run_stream([py, "-m", "pip", "install", "--disable-pip-version-check", *pkgs], timeout=3600)
    if rc != 0:
        raise ToolError(f"pip install {' '.join(pkgs)} failed (see log above).")


def pip_install_to(name: str, *pkgs: str) -> None:
    """Install packages into our private folder (pip --target). No virtual environment is involved,
    so it works with every Python (python.org, Microsoft Store, conda ...)."""
    if any(p.startswith("-") for p in pkgs):
        raise ToolError("Package names cannot start with '-'.")
    py = py_exe()
    ensure_pip(py)
    d = pylib_dir(name)
    d.mkdir(parents=True, exist_ok=True)
    progress(None, f"pip install {' '.join(pkgs)}")
    cmd = [py, "-m", "pip", "install", "--disable-pip-version-check", "--upgrade", "--no-warn-script-location",
           "--target", str(d), *pkgs]
    if run_stream(cmd, timeout=3600) != 0:
        raise ToolError(f"pip install {' '.join(pkgs)} failed (see log above).")
    (d / ".pyver").write_text(f"{sys.version_info[0]}.{sys.version_info[1]}", encoding="utf-8")


def install_jdk() -> None:
    tag, assets = github_latest("adoptium/temurin21-binaries")
    arch, osn = _plat()
    pat = rf"^OpenJDK21U-jdk_{{}}_{osn}_hotspot_.*\.(zip|tar\.gz)$"
    try:
        asset = pick_asset(assets, pat.format(arch))
    except ToolError:
        asset = pick_asset(assets, pat.format("x64"))
    say(f"Downloading Temurin JDK 21 ({tag}) - needed by Ghidra...")
    install_asset(asset, TOOLS / "jdk", "JDK")


def install_ghidra() -> None:
    tag, assets = github_latest("NationalSecurityAgency/ghidra")
    asset = pick_asset(assets, r"^ghidra_.*_PUBLIC_.*\.zip$")
    say(f"Downloading Ghidra ({tag}) - about 400 MB...")
    install_asset(asset, TOOLS / "ghidra", "Ghidra")


def install_dotnet() -> None:
    DOWNLOADS.mkdir(parents=True, exist_ok=True)
    dest = fresh_dir(TOOLS / "dotnet")
    if IS_WIN:
        script = download("https://dot.net/v1/dotnet-install.ps1", DOWNLOADS / "dotnet-install.ps1",
                          label="dotnet-install", hash_note=False)
        cmd = ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", script,
               "-InstallDir", dest, "-Channel", "LTS", "-NoPath"]
    else:
        script = download("https://dot.net/v1/dotnet-install.sh", DOWNLOADS / "dotnet-install.sh",
                          label="dotnet-install", hash_note=False)
        cmd = ["bash", script, "--install-dir", dest, "--channel", "LTS", "--no-path"]
    say("Installing the .NET SDK with Microsoft's official dotnet-install script...")
    progress(None, "Installing .NET SDK")
    if run_stream(cmd, timeout=3600) != 0:
        raise ToolError(".NET SDK install failed (see log above).")


def install_ilspy() -> None:
    dn = find_dotnet()
    if not dn:
        raise ToolError(".NET SDK is not available.")
    dest = TOOLS / "ilspycmd"
    dest.mkdir(parents=True, exist_ok=True)
    progress(None, "Installing ilspycmd")
    if run_stream([dn, "tool", "install", "ilspycmd", "--tool-path", dest], timeout=1800) != 0:
        if run_stream([dn, "tool", "update", "ilspycmd", "--tool-path", dest], timeout=1800) != 0:
            raise ToolError("Could not install ilspycmd from NuGet (see log above).")


def install_upx() -> None:
    tag, assets = github_latest("upx/upx")
    arch = "arm64" if platform.machine().lower() in ("arm64", "aarch64") else "amd64"
    pat = r"win64\.zip$" if IS_WIN else rf"{arch}_linux\.tar\.xz$"
    if IS_MAC:
        raise ToolError("UPX has no official macOS build; install it with `brew install upx`.")
    say(f"Downloading UPX ({tag})...")
    install_asset(pick_asset(assets, pat), TOOLS / "upx", "UPX")


def install_zig() -> None:
    pip_install_to("zig", "ziglang")
    z = find_zig()
    if not z:
        raise ToolError("ziglang was installed but zig was not found inside it.")
    r = run_capture([z, "version"], timeout=60)
    if r.returncode != 0 or not r.stdout.strip():
        hint = "\nMicrosoft Store Python hides AppData from other programs: use a folder outside AppData." if is_store_python() else ""
        raise ToolError("Zig was installed but cannot start: " + ((r.stderr or r.stdout).strip()[:300] or "no output") + hint)


def install_uncompyle6() -> None:
    pip_install_to("dec6", "uncompyle6")


def install_decompyle3() -> None:
    pip_install_to("dec3", "decompyle3")


def install_pyinstaller() -> None:
    pip_install_to("build", "pyinstaller")


def find_vcredist() -> str | None:
    if not IS_WIN:
        return None
    sysdir = Path(os.environ.get("SystemRoot") or r"C:\Windows") / "System32"
    ok_ = (sysdir / "vcruntime140.dll").is_file() and (sysdir / "msvcp140.dll").is_file()
    return str(sysdir / "vcruntime140.dll") if ok_ else None


def install_vcredist() -> None:
    inst = download("https://aka.ms/vs/17/release/vc_redist.x64.exe", DOWNLOADS / "vc_redist.x64.exe",
                    label="Visual C++ Redistributable", hash_note=False)
    say("Starting Microsoft's installer - Windows will ask for permission (UAC)...")
    q = str(inst).replace("'", "''")
    script = (f"$p = Start-Process -FilePath '{q}' -ArgumentList '/install','/passive','/norestart' "
              "-Verb RunAs -Wait -PassThru; exit $p.ExitCode")
    rc = run_stream(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", script], timeout=1800)
    if rc not in (0, 1638, 3010):  # 1638 = newer already installed, 3010 = installed, reboot suggested
        raise ToolError(f"The Visual C++ installer did not finish (exit {rc}). Did you decline the permission prompt?")


PYCDC_SOURCES = ["pycdc.cpp", "ASTree.cpp", "ASTNode.cpp", "bytecode.cpp", "data.cpp", "pyc_code.cpp",
                 "pyc_module.cpp", "pyc_numeric.cpp", "pyc_object.cpp", "pyc_sequence.cpp", "pyc_string.cpp"]


def install_pycdc() -> None:
    zig = find_zig()
    if not zig:
        raise ToolError("The Zig compiler is not available.")
    env = tool_env()
    with dd_tempdir("dd_pycdc_") as tmp_s:
        tmp = Path(tmp_s)
        src_zip = download("https://codeload.github.com/zrax/pycdc/zip/refs/heads/master", tmp / "src.zip",
                           label="pycdc source")
        extract_archive(src_zip, tmp / "src", "Extracting pycdc source")
        root = next(p for p in (tmp / "src").iterdir() if p.is_dir())
        sources = PYCDC_SOURCES + sorted(f"bytes/{p.name}" for p in (root / "bytes").glob("python_*.cpp"))
        objs = tmp / "obj"
        objs.mkdir()
        say(f"Compiling pycdc from source with Zig ({len(sources)} files, a few minutes)...")

        def compile_one(rel: str) -> str:
            check_stop()
            o = objs / (rel.replace("/", "_") + ".o")
            r = run_capture([zig, "c++", "-std=c++11", "-O2", "-w", f"-I{root}", "-c", root / rel, "-o", o],
                            timeout=1800, env=env, cwd=root)
            if r.returncode != 0:
                raise ToolError(f"Compiling {rel} failed:\n{r.stderr[-1500:]}")
            return str(o)

        done = []
        with ThreadPoolExecutor(max_workers=max(1, os.cpu_count() or 2)) as pool:
            for i, o in enumerate(pool.map(compile_one, sources), 1):
                done.append(o)
                progress(i / len(sources), f"Compiling pycdc {i}/{len(sources)}")
        dest = TOOLS / "pycdc"
        dest.mkdir(parents=True, exist_ok=True)
        progress(None, "Linking pycdc")
        r = run_capture([zig, "c++", *done, "-o", dest / exe("pycdc")], timeout=900, env=env)
        if r.returncode != 0:
            raise ToolError(f"Linking pycdc failed:\n{r.stderr[-1500:]}")


@dataclass(frozen=True)
class ToolDef:
    key: str
    name: str
    purpose: str
    size: str
    find: Callable[[], str | None]
    install: Callable[[], None]
    deps: tuple[str, ...] = ()


REG: dict[str, ToolDef] = {t.key: t for t in [
    ToolDef("dotnet", ".NET SDK", "Runs ILSpy and rebuilds C# projects", "~250 MB", find_dotnet, install_dotnet),
    ToolDef("ilspycmd", "ILSpy (ilspycmd)", ".NET exe  ->  C# project", "~30 MB", find_ilspy, install_ilspy, ("dotnet",)),
    ToolDef("zig", "Zig C/C++ compiler", "Builds pycdc, rebuilds C source", "~80 MB", find_zig, install_zig),
    ToolDef("pycdc", "pycdc (Decompyle++)", "Python 3.9+ exe  ->  .py", "builds in ~3 min", find_pycdc, install_pycdc, ("zig",)),
    ToolDef("decompyle3", "decompyle3", "Python 3.7-3.8 exe  ->  .py", "~10 MB", find_decompyle3, install_decompyle3),
    ToolDef("uncompyle6", "uncompyle6", "Python 3.8 and older  ->  .py", "~10 MB", find_uncompyle6, install_uncompyle6),
    ToolDef("pyinstaller", "PyInstaller", "Rebuilds edited Python source into an exe", "~30 MB", find_pyinstaller, install_pyinstaller),
    ToolDef("jdk", "Java JDK 21", "Required by Ghidra", "~200 MB", find_java, install_jdk),
    ToolDef("ghidra", "Ghidra", "Native exe  ->  C pseudocode", "~450 MB", find_ghidra, install_ghidra, ("jdk",)),
    ToolDef("upx", "UPX", "Unpacks UPX-packed exes first", "~2 MB", find_upx, install_upx),
]}


def remove_legacy_venvs() -> None:
    """Housekeeping: delete the virtual environments of old versions and stale temp folders."""
    try:
        legacy = TOOLS / "venvs"
        if legacy.is_dir() and TOOLS.resolve() in legacy.resolve().parents:
            shutil.rmtree(legacy, ignore_errors=True)
        tmp = TOOLS.parent / "tmp"
        if tmp.is_dir():
            for d in tmp.iterdir():
                if time.time() - d.stat().st_mtime > 6 * 3600:
                    shutil.rmtree(d, ignore_errors=True)
    except OSError:
        pass


if IS_WIN:
    REG["vcredist"] = ToolDef("vcredist", "Visual C++ Redistributable", "Required by Ghidra on Windows", "~25 MB",
                              find_vcredist, install_vcredist)
    REG["ghidra"] = replace(REG["ghidra"], deps=("jdk", "vcredist"))


def tool_path(key: str) -> str | None:
    return REG[key].find()


def is_installed(key: str) -> bool:
    return tool_path(key) is not None


def install_tool(key: str) -> None:
    t = REG[key]
    for dep in t.deps:
        if not is_installed(dep):
            install_tool(dep)
    if is_installed(key):
        ok(f"{t.name} is already installed.")
        return
    say(f"Installing {t.name}...")
    t.install()
    if not is_installed(key):
        raise ToolError(f"{t.name} was installed but could not be found afterwards.")
    ok(f"{t.name} installed.")


def missing_tools(keys: list[str]) -> list[str]:
    return [k for k in keys if not is_installed(k)]


# --------------------------------------------------------------------------- #
# File identification
# --------------------------------------------------------------------------- #
MACHINES = {0x14C: "x86 (32-bit)", 0x8664: "x86-64", 0x1C0: "ARM", 0x1C4: "ARMv7 Thumb-2", 0xAA64: "ARM64"}


@dataclass
class FileInfo:
    path: str
    size: int
    sha256: str
    is_pe: bool = False
    is_dll: bool = False
    arch: str = "unknown"
    compiled: str = ""
    sections: list[str] = field(default_factory=list)
    kind: str = "native"  # native | dotnet | pyinstaller
    packer: str = ""
    python_version: str = ""
    notes: list[str] = field(default_factory=list)


def sha256_of(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_pe(path: Path, fi: FileInfo) -> bool:
    """Fill PE details into *fi*. Returns True if the file has a .NET (CLR) header."""
    with open(path, "rb") as f:
        dos = f.read(64)
        if len(dos) < 64 or dos[:2] != b"MZ":
            return False
        (e_lfanew,) = struct.unpack_from("<I", dos, 0x3C)
        f.seek(e_lfanew)
        if f.read(4) != b"PE\0\0":
            return False
        coff = f.read(20)
        if len(coff) < 20:
            return False
        machine, nsec, stamp, _, _, opt_size, chars = struct.unpack("<HHIIIHH", coff)
        opt = f.read(opt_size)
        sect_raw = f.read(40 * min(nsec, 96))
    fi.is_pe = True
    fi.is_dll = bool(chars & 0x2000)
    fi.arch = MACHINES.get(machine, f"unknown (0x{machine:04X})")
    try:
        fi.compiled = datetime.fromtimestamp(stamp, timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    except (OverflowError, OSError, ValueError):
        pass
    for i in range(len(sect_raw) // 40):
        name = sect_raw[i * 40: i * 40 + 8].rstrip(b"\0").decode("latin-1")
        fi.sections.append(name)
        if name.upper().startswith("UPX"):
            fi.packer = "UPX"
    if len(opt) >= 2:
        (magic,) = struct.unpack_from("<H", opt, 0)
        dir_off = 96 if magic == 0x10B else 112 if magic == 0x20B else 0
        if dir_off and len(opt) >= dir_off + 15 * 8:
            (n_dirs,) = struct.unpack_from("<I", opt, dir_off - 4)
            if n_dirs > 14:
                clr_rva, clr_size = struct.unpack_from("<II", opt, dir_off + 14 * 8)
                return clr_rva != 0 and clr_size != 0
    return False


def analyze(path: Path) -> FileInfo:
    if not path.is_file():
        raise ToolError(f"Not a file: {path}")
    fi = FileInfo(path=str(path), size=path.stat().st_size, sha256=sha256_of(path))
    is_dotnet = parse_pe(path, fi)
    if not fi.is_pe:
        fi.notes.append("No valid PE header found; treating it as a generic native binary.")
    pyi = PyInstallerArchive(path)
    if is_dotnet:
        fi.kind = "dotnet"
        fi.notes.append("Managed .NET assembly: near-original C# can usually be recovered.")
    elif pyi.find():
        fi.kind = "pyinstaller"
        fi.python_version = f"{pyi.pymaj}.{pyi.pymin}"
        fi.notes.append(f"PyInstaller bundle (Python {fi.python_version}): .py files can usually be recovered.")
        if (pyi.pymaj, pyi.pymin) >= (3, 14):
            fi.notes.append("Python 3.14 bytecode is not supported by pycdc yet; expect failures.")
    else:
        fi.notes.append("Native machine code: only approximate C pseudocode is possible "
                        "(names, comments and structure are lost).")
    if fi.packer:
        fi.notes.append(f"{fi.packer}-packed: it will be unpacked first when UPX is installed.")
    return fi


def required_tools(fi: FileInfo) -> list[str]:
    if fi.kind == "dotnet":
        return ["dotnet", "ilspycmd"]
    if fi.kind == "pyinstaller":
        maj, mn = (int(x) for x in fi.python_version.split("."))
        return [py_tools_for(maj, mn)[0]]
    return ["jdk", "ghidra"] + (["vcredist"] if "vcredist" in REG else [])


def py_tools_for(major: int, minor: int) -> list[str]:
    if (major, minor) >= (3, 9):
        return ["pycdc"]
    if (major, minor) >= (3, 7):
        return ["decompyle3", "uncompyle6"]
    return ["uncompyle6"]


# --------------------------------------------------------------------------- #
# PyInstaller archive reader
# --------------------------------------------------------------------------- #
PYI_MAGIC = b"MEI\x0c\x0b\x0a\x0b\x0e"
_TOC_HDR = struct.Struct("!IIIIBc")


@dataclass
class TocEntry:
    pos: int
    csize: int
    usize: int
    cflag: int
    ctype: str
    name: str


@dataclass
class PycItem:
    name: str
    path: Path
    rel: str
    kind: str  # entry | runtime | module


@dataclass
class ExtractResult:
    items: list[PycItem] = field(default_factory=list)
    files: int = 0
    warnings: list[str] = field(default_factory=list)


def pyc_header(magic: bytes, major: int, minor: int) -> bytes:
    size = 16 if (major, minor) >= (3, 7) else 12 if (major, minor) >= (3, 3) else 8
    return magic + b"\0" * (size - 4)


class PyInstallerArchive:
    def __init__(self, path: Path):
        self.path = path
        self.size = path.stat().st_size
        self.cookie_pos = -1
        self.overlay_pos = self.toc_pos = self.toc_len = 0
        self.pymaj = self.pymin = 0
        self.entries: list[TocEntry] = []

    def find(self) -> bool:
        window = min(self.size, 8 * 1024 * 1024)
        try:
            with open(self.path, "rb") as f:
                f.seek(self.size - window)
                tail = f.read(window)
                idx = tail.rfind(PYI_MAGIC)
                if idx < 0:
                    return False
                self.cookie_pos = self.size - window + idx
                f.seek(self.cookie_pos)
                raw = f.read(88)
        except OSError:
            return False
        try:
            if b"python" in raw[24:88].lower():
                _, pkg_len, toc_pos, toc_len, pyver, _ = struct.unpack("!8sIIii64s", raw[:88])
                cookie_size = 88
            else:
                _, pkg_len, toc_pos, toc_len, pyver = struct.unpack("!8siiii", raw[:24])
                cookie_size = 24
        except struct.error:
            return False
        self.overlay_pos = self.size - (pkg_len + (self.size - self.cookie_pos - cookie_size))
        if (not 0 <= self.overlay_pos < self.size or toc_len <= 0 or toc_pos < 0
                or self.overlay_pos + toc_pos + toc_len > self.size):
            return False
        self.toc_pos, self.toc_len = toc_pos, toc_len
        self.pymaj, self.pymin = divmod(pyver, 100) if pyver >= 100 else divmod(pyver, 10)
        return True

    def read_toc(self) -> list[TocEntry]:
        with open(self.path, "rb") as f:
            f.seek(self.overlay_pos + self.toc_pos)
            toc = f.read(self.toc_len)
        entries, off = [], 0
        while off < len(toc):
            if off + _TOC_HDR.size > len(toc):
                raise ToolError("Corrupt PyInstaller table of contents.")
            esize, pos, csize, usize, cflag, ctype = _TOC_HDR.unpack_from(toc, off)
            if esize < _TOC_HDR.size or off + esize > len(toc):
                raise ToolError("Corrupt PyInstaller table of contents.")
            name = toc[off + _TOC_HDR.size: off + esize].split(b"\0", 1)[0].decode("utf-8", "replace")
            entries.append(TocEntry(pos, csize, usize, cflag, ctype.decode("latin-1"), name or f"unnamed_{len(entries)}"))
            off += esize
        self.entries = entries
        return entries

    def bundled_packages(self) -> set[str]:
        """Top-level folders of bundled binaries/data files = third-party packages."""
        tops = set()
        for e in self.entries:
            if e.ctype in ("b", "x"):
                n = e.name.replace("\\", "/")
                if "/" in n:
                    tops.add(n.split("/")[0])
        return tops

    def _read(self, f, e: TocEntry) -> bytes:
        start = self.overlay_pos + e.pos
        if start < 0 or start + e.csize > self.size:
            raise ValueError("entry points outside the archive")
        f.seek(start)
        data = f.read(e.csize)
        return safe_decompress(data) if e.cflag == 1 else data

    def _pyc_magic(self, f, res: ExtractResult) -> bytes:
        for e in self.entries:
            if e.ctype in ("z", "Z"):
                try:
                    data = self._read(f, e)
                except (ValueError, zlib.error):
                    continue
                if data[:4] == b"PYZ\0":
                    return data[4:8]
        res.warnings.append("PYZ header not found; using this Python's magic number (decompilers may reject it)")
        return importlib.util.MAGIC_NUMBER

    def extract(self, outdir: Path) -> ExtractResult:
        res = ExtractResult()
        outdir.mkdir(parents=True, exist_ok=True)
        with open(self.path, "rb") as f:
            header = pyc_header(self._pyc_magic(f, res), self.pymaj, self.pymin)
            for i, e in enumerate(self.entries):
                check_stop()
                progress(i / max(1, len(self.entries)), f"Extracting {i}/{len(self.entries)}")
                if e.ctype in ("d", "o"):
                    continue
                try:
                    self._extract_entry(f, e, outdir, header, res)
                except (ValueError, OSError, zlib.error, struct.error) as exc:
                    res.warnings.append(f"{e.name}: {exc}")
        return res

    def _extract_entry(self, f, e: TocEntry, outdir: Path, header: bytes, res: ExtractResult) -> None:
        data = self._read(f, e)
        if e.ctype == "s":
            path = safe_join(outdir, e.name + ".pyc")
            write_bytes(path, header + data)
            kind = "runtime" if e.name.startswith(("pyiboot", "pyi_rth")) else "entry"
            res.items.append(PycItem(e.name, path, e.name + ".pyc", kind))
        elif e.ctype in ("m", "M"):
            write_bytes(safe_join(outdir, e.name + ".pyc"), data if data[2:4] == b"\r\n" else header + data)
            res.files += 1
        elif e.ctype in ("z", "Z"):
            self._extract_pyz(data, outdir / f"{Path(e.name).name}_extracted", header, res)
        else:
            write_bytes(safe_join(outdir, e.name), data)
            res.files += 1

    def _extract_pyz(self, data: bytes, dest: Path, header: bytes, res: ExtractResult) -> None:
        if data[:4] != b"PYZ\0":
            res.warnings.append("a PYZ archive has a bad header and was skipped")
            return
        (toc_off,) = struct.unpack("!i", data[8:12])
        try:
            # marshal is not hardened against hostile input: analyse unknown samples in a VM.
            toc = marshal.loads(data[toc_off:])
        except Exception as exc:  # noqa: BLE001
            res.warnings.append(f"cannot read PYZ table of contents: {exc}")
            return
        undecodable = 0
        for name, (typ, pos, length) in (toc.items() if isinstance(toc, dict) else toc):
            if isinstance(name, bytes):
                name = name.decode("utf-8", "replace")
            try:
                code = safe_decompress(data[pos: pos + length])
            except (zlib.error, ValueError):
                undecodable += 1
                continue
            if typ == 2:
                continue
            parts = [p for p in name.split(".") if p]
            if not parts:
                continue
            rel = "/".join(parts) + ("/__init__.pyc" if typ in (1, 3) else ".pyc")
            try:
                path = safe_join(dest, rel)
                write_bytes(path, header + code)
            except (ValueError, OSError) as exc:
                res.warnings.append(f"{name}: {exc}")
                continue
            res.items.append(PycItem(name, path, rel, "module"))
        if undecodable:
            res.warnings.append(f"{undecodable} PYZ modules could not be decompressed (encrypted archive?)")


# --------------------------------------------------------------------------- #
# Decompile pipelines
# --------------------------------------------------------------------------- #
_STDLIB = set(getattr(sys, "stdlib_module_names", ()))
_PYI_INTERNAL = ("pyimod", "_pyi", "pyiboot", "PyInstaller")
KNOWN_THIRD_PARTY = frozenset((
    "requests urllib3 certifi idna charset_normalizer chardet six numpy pandas scipy matplotlib PIL yaml colorama "
    "tqdm psutil cryptography bs4 soupsieve lxml pygame PyQt5 PyQt6 PySide2 PySide6 customtkinter darkdetect "
    "pyperclip win32api win32con win32com pythoncom pywintypes pkg_resources setuptools _distutils_hack wheel pip "
    "attr attrs typing_extensions websocket websockets aiohttp discord cv2 sklearn tensorflow torch keyboard mouse "
    "pyautogui pynput selenium jinja2 markupsafe click flask werkzeug packaging dateutil pytz tzdata pydantic rich "
    "pygments cffi pycparser nacl paramiko bcrypt OpenSSL zmq google grpc pefile altgraph win32 pywin").split())


def is_app_module(name: str, third: set[str]) -> bool:
    top = name.split(".")[0]
    return (top not in _STDLIB and not top.startswith(_PYI_INTERNAL)
            and top not in KNOWN_THIRD_PARTY and top not in third)


def tidy_python(src: str) -> tuple[str, bool]:
    """Remove the bogus module-level `return None` pycdc emits. Returns (source, parses_ok)."""
    for _ in range(25):
        try:
            compile(src, "<decompiled>", "exec", dont_inherit=True)
            return src, True
        except (SyntaxError, ValueError) as e:
            lines = src.splitlines()
            i = (getattr(e, "lineno", None) or 0) - 1
            if "outside function" in (getattr(e, "msg", "") or "") and 0 <= i < len(lines) and lines[i].strip() in ("return None", "return"):
                lines[i] = re.match(r"\s*", lines[i]).group() + "pass"  # type: ignore[union-attr]
                src = "\n".join(lines) + "\n"
                continue
            return src, False
    return src, False


_TRACE_RX = re.compile(r"^(?:Reduce \S+ invalid by check|\s*(?:L\.\s*\d+:\s*)?(?:[\d-]+\s+)?\S+\s+::=\s.*\(\d+\))\s*$")


def strip_parser_trace(text: str) -> str:
    """decompyle3 3.9.x always prints its internal grammar trace to stdout; it must not end up in the source."""
    lines = text.splitlines()
    kept = [ln for ln in lines if not _TRACE_RX.match(ln)]
    return "\n".join(kept) + "\n" if len(kept) != len(lines) else text


def decompile_pyc(pyc: Path, dst: Path, tools: list[str]) -> str:
    """Returns ok | partial | failed."""
    for key in tools:
        cmd = tool_cmd(key)
        if not cmd:
            continue
        try:
            r = run_capture([*cmd[0], pyc], timeout=240, env=_with_pythonpath(cmd[1]))
        except (subprocess.SubprocessError, OSError):
            continue
        if r.returncode != 0 or not r.stdout.strip():
            continue
        text, parses = tidy_python(strip_parser_trace(r.stdout))
        warned = any(m in text + r.stderr for m in ("Decompyle incomplete", "Unsupported opcode", "Parse error"))
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(f"# Decompiled from {pyc.name} with {key}\n{text}", encoding="utf-8")
        return "ok" if parses and not warned else "partial"
    return "failed"


def _need(keys: list[str]) -> None:
    miss = missing_tools(keys)
    if miss:
        names = ", ".join(REG[k].name for k in miss)
        raise ToolError(f"Missing tool(s): {names}. Install them from the Tools tab (or `main.py install {miss[0]}`).")


def run_pyinstaller(exe_path: Path, out_dir: Path, src: Path, fi: FileInfo, scope: str, jobs: int) -> dict:
    arc = PyInstallerArchive(exe_path)
    if not arc.find():
        raise ToolError("No PyInstaller archive found in this file.")
    arc.read_toc()
    say(f"PyInstaller archive: {len(arc.entries)} entries, Python {arc.pymaj}.{arc.pymin}")
    tools = py_tools_for(arc.pymaj, arc.pymin)
    _need(tools[:1] if not any(is_installed(t) for t in tools) else [])
    res = arc.extract(out_dir / "extracted")
    for w in res.warnings:
        warn(w)
    ok(f"Extracted {len(res.items) + res.files} files.")
    third = arc.bundled_packages()
    wanted = [it for it in res.items if scope == "all" or it.kind == "entry"
              or (scope == "app" and it.kind == "module" and is_app_module(it.name, third))]
    entries = [it for it in wanted if it.kind == "entry"]
    say(f"Decompiling {len(wanted)} file(s) ({len(entries)} entry script(s)); scope: {scope}")
    stats = {"ok": 0, "partial": 0, "failed": 0}
    failed: list[str] = []

    def work(it: PycItem):
        check_stop()
        return it, decompile_pyc(it.path, src / Path(it.rel).with_suffix(".py"), tools)

    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        for i, (it, status) in enumerate(pool.map(work, wanted), 1):
            stats[status] += 1
            if status == "failed":
                failed.append(it.name)
            progress(i / len(wanted), f"Decompiling {i}/{len(wanted)}")
    ok(f"Decompiled {stats['ok']} parsed OK, {stats['partial']} need review, {stats['failed']} failed.")
    if (arc.pymaj, arc.pymin) >= (3, 11) and tool_path("pycdc"):
        warn(f"pycdc's support for Python {arc.pymaj}.{arc.pymin} is incomplete: it can silently DROP statements "
             "(for example `x += 1`) while still producing valid-looking code. Review every file against how the "
             "program really behaves. The original .pyc files are kept in the 'extracted' folder.")
    elif stats["partial"] or stats["failed"]:
        warn("Decompilers can silently drop or mangle statements, especially on Python 3.12+ code. "
             "Read every recovered file against the original behaviour before trusting it.")
    if failed:
        warn("Failed: " + ", ".join(failed[:10]))
    return {"stats": stats, "entries": [Path(it.rel).with_suffix(".py").as_posix() for it in entries],
            "third_party": sorted(third), "extracted": len(res.items) + res.files}


def run_dotnet(exe_path: Path, src: Path) -> dict:
    _need(["dotnet", "ilspycmd"])
    src.mkdir(parents=True, exist_ok=True)
    progress(None, "ILSpy is decompiling...")
    rc = run_stream([tool_path("ilspycmd"), "-p", "-o", src, exe_path.resolve()], timeout=3600)
    if rc != 0:
        raise ToolError(f"ilspycmd exited with code {rc}.")
    n = sum(1 for _ in src.rglob("*.cs"))
    csproj = sorted(src.rglob("*.csproj"), key=lambda p: len(p.parts))
    ok(f"Recovered {n} C# files.")
    return {"stats": {"cs_files": n}, "csproj": csproj[0].relative_to(src).as_posix() if csproj else ""}


GHIDRA_TYPES_H = """\
/* ghidra_types.h - maps Ghidra's pseudo-types onto C so the output has a chance to compile. */
#pragma once
#include <stdint.h>
#include <stdbool.h>
typedef unsigned char undefined, undefined1, byte, uchar;
typedef unsigned short undefined2, word, ushort;
typedef unsigned int undefined4, dword, uint;
typedef unsigned long long undefined8, qword, ulonglong;
typedef long long longlong;
#ifdef _WIN32
typedef unsigned int ulong;
#else
typedef unsigned long ulong;
#endif
typedef void code(void);
"""

GHIDRA_SCRIPT = r'''// ExportDecompiled.java - headless Ghidra script used by $Decompile
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;

public class ExportDecompiled extends GhidraScript {
    @Override
    protected void run() throws Exception {
        String[] args = getScriptArgs();
        if (args.length < 1) { printerr("usage: ExportDecompiled.java <output_dir>"); return; }
        File outDir = new File(args[0]);
        File funcDir = new File(outDir, "functions");
        funcDir.mkdirs();
        DecompInterface ifc = new DecompInterface();
        if (!ifc.openProgram(currentProgram)) {
            printerr("Could not open program in decompiler: " + ifc.getLastMessage());
            return;
        }
        int done = 0, failed = 0;
        try (PrintWriter all = new PrintWriter(new FileWriter(new File(outDir, "all_functions.c")))) {
            all.println("// Decompiled by Ghidra via $Decompile");
            all.println("// Program: " + currentProgram.getName());
            all.println();
            FunctionIterator it = currentProgram.getFunctionManager().getFunctions(true);
            while (it.hasNext() && !monitor.isCancelled()) {
                Function f = it.next();
                DecompileResults res = ifc.decompileFunction(f, 60, monitor);
                if (res == null || !res.decompileCompleted() || res.getDecompiledFunction() == null) { failed++; continue; }
                String code = res.getDecompiledFunction().getC();
                String safe = f.getName().replaceAll("[^A-Za-z0-9_.-]", "_");
                if (safe.length() > 80) safe = safe.substring(0, 80);
                String addr = f.getEntryPoint().toString().replaceAll("[^A-Za-z0-9]", "_");
                try (PrintWriter one = new PrintWriter(new FileWriter(new File(funcDir, safe + "_" + addr + ".c")))) {
                    one.print(code);
                }
                all.println("// ---- " + f.getName() + " @ " + f.getEntryPoint() + " ----");
                all.println(code);
                done++;
            }
        }
        ifc.dispose();
        println("$Decompile: decompiled " + done + " functions (" + failed + " failed)");
    }
}
'''


def run_ghidra(exe_path: Path, src: Path, timeout: int = 3600) -> dict:
    _need(["jdk", "ghidra"])
    src.mkdir(parents=True, exist_ok=True)
    say("Ghidra auto-analyses the file first; large programs can take several minutes.")
    progress(None, "Ghidra is analysing...")
    with dd_tempdir("dd_ghidra_") as tmp_s:
        tmp = Path(tmp_s)
        (tmp / "scripts").mkdir()
        (tmp / "proj").mkdir()
        (tmp / "scripts" / "ExportDecompiled.java").write_text(GHIDRA_SCRIPT, encoding="utf-8")
        cmd = [tool_path("ghidra"), tmp / "proj", "dd", "-import", exe_path.resolve(),
               "-scriptPath", tmp / "scripts", "-postScript", "ExportDecompiled.java", src.resolve(),
               "-analysisTimeoutPerFile", timeout, "-deleteProject"]
        rc = run_stream(cmd, timeout=timeout + 900)
    combined = src / "all_functions.c"
    if not combined.exists():
        raise ToolError(f"Ghidra finished (exit {rc}) without output; see the log above.")
    (src / "ghidra_types.h").write_text(GHIDRA_TYPES_H, encoding="utf-8")
    combined.write_text('#include "ghidra_types.h"\n' + combined.read_text(encoding="utf-8", errors="replace"),
                        encoding="utf-8")
    n = sum(1 for _ in (src / "functions").glob("*.c"))
    ok(f"Decompiled {n} functions into all_functions.c.")
    return {"stats": {"functions": n}}


def print_info(fi: FileInfo) -> None:
    say(f"File    : {fi.path}")
    say(f"Size    : {fi.size:,} bytes   SHA-256: {fi.sha256}")
    if fi.is_pe:
        say(f"PE      : {fi.arch}{' DLL' if fi.is_dll else ''}, compiled {fi.compiled or 'n/a'}")
    say(f"Type    : {fi.kind}" + (f" (Python {fi.python_version})" if fi.python_version else ""))
    for n in fi.notes:
        say(n)


def decompile(exe_path: Path, out_dir: Path, scope: str = "entry", force: bool = False, jobs: int | None = None) -> dict:
    STOP.clear()
    fi = analyze(exe_path)
    print_info(fi)
    if out_dir.exists():
        existing = {p.name for p in out_dir.iterdir()}
        if "report.json" in existing:
            raise ToolError(f"{out_dir} already holds a decompiled project. Choose a new folder (nothing is ever deleted).")
        if existing - {"source", "extracted", "_unpacked", "rebuilt", ".build"} and not force:
            raise ToolError(f"{out_dir} is not empty. Choose an empty folder (nothing is ever deleted).")
    out_dir.mkdir(parents=True, exist_ok=True)

    target = exe_path
    if fi.packer == "UPX":
        if is_installed("upx"):
            target = out_dir / "_unpacked" / exe_path.name
            target.parent.mkdir(exist_ok=True)
            shutil.copy2(exe_path, target)
            if run_stream([tool_path("upx"), "-d", target]) == 0:
                ok("Unpacked UPX layer.")
                fi = analyze(target)
            else:
                warn("UPX could not unpack it; continuing with the packed file.")
                target = exe_path
        else:
            warn("File is UPX-packed. Install UPX from the Tools tab for much better results.")

    src = out_dir / "source"
    jobs = jobs or min(8, os.cpu_count() or 2)
    if fi.kind == "dotnet":
        extra = run_dotnet(target, src)
    elif fi.kind == "pyinstaller":
        extra = run_pyinstaller(target, out_dir, src, fi, scope, jobs)
    else:
        extra = run_ghidra(target, src)
    report = {"tool": f"{APP_NAME} {VERSION}", "created": datetime.now(timezone.utc).isoformat(timespec="seconds"),
              "kind": fi.kind, "python_version": fi.python_version, "input": asdict(fi), **extra}
    (out_dir / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    progress(1.0, "Done")
    ok(f"Done. Source is in {src}")
    return report


# --------------------------------------------------------------------------- #
# Projects + rebuild
# --------------------------------------------------------------------------- #
def load_project(path: Path) -> dict:
    """Accepts an output folder (has report.json) or its source/ subfolder."""
    path = path.resolve()
    for root in (path, path.parent):
        rp = root / "report.json"
        if rp.is_file() and (root / "source").is_dir():
            try:
                data = json.loads(rp.read_text(encoding="utf-8"))
            except (OSError, ValueError) as exc:
                raise ToolError(f"{rp} is unreadable: {exc}") from None
            if not isinstance(data, dict) or data.get("kind") not in ("pyinstaller", "dotnet", "native"):
                raise ToolError(f"{rp} is not a valid $Decompile report.")
            data["root"], data["source"] = str(root), str(root / "source")
            return data
    raise ToolError(f"{path} is not a $Decompile output folder (report.json not found).")


def required_for_rebuild(kind: str) -> list[str]:
    return {"pyinstaller": ["pyinstaller"], "dotnet": ["dotnet"]}.get(kind, ["zig"])


def check_python_tree(src: Path) -> list[tuple[Path, int, str]]:
    errs = []
    for p in sorted(src.rglob("*.py")):
        try:
            compile(p.read_text(encoding="utf-8", errors="replace"), str(p), "exec", dont_inherit=True)
        except SyntaxError as e:
            errs.append((p, e.lineno or 1, e.msg or "syntax error"))
    return errs


def top_imports(src: Path) -> set[str]:
    mods: set[str] = set()
    local = {p.stem for p in src.glob("*.py")} | {p.name for p in src.iterdir() if p.is_dir()}
    for p in src.rglob("*.py"):
        try:
            tree = ast.parse(p.read_text(encoding="utf-8", errors="replace"))
        except SyntaxError:
            continue
        for n in ast.walk(tree):
            if isinstance(n, ast.Import):
                mods |= {a.name.split(".")[0] for a in n.names}
            elif isinstance(n, ast.ImportFrom) and n.module and n.level == 0:
                mods.add(n.module.split(".")[0])
    return {m for m in mods if m not in _STDLIB and m not in local}


def rebuild(project: Path, entry: str | None = None, windowed: bool = False, pip_packages: list[str] | None = None) -> Path:
    STOP.clear()
    proj = load_project(project)
    root, src, kind = Path(proj["root"]), Path(proj["source"]), proj["kind"]
    outdir = root / "rebuilt"
    outdir.mkdir(exist_ok=True)
    _need(required_for_rebuild(kind))

    if kind == "pyinstaller":
        errs = check_python_tree(src)
        if errs:
            for p, line, msg in errs[:15]:
                bad(f"{p.relative_to(src)}:{line}: {msg}")
            raise ToolError(f"{len(errs)} file(s) have syntax errors. Fix them in the editor, then rebuild.")
        entries = proj.get("entries") or [p.name for p in src.glob("*.py")]
        entry = entry or (entries[0] if entries else None)
        if not entry or not (src / entry).is_file():
            raise ToolError("Pick the entry script (the file that starts the program).")
        if pip_packages:
            if pylib_ok("build", "PyInstaller"):
                pip_install_to("build", *pip_packages)  # same private folder PyInstaller runs from
            else:
                pip_py = build_python()
                try:
                    if not pip_py:
                        raise ToolError("owner of PyInstaller not found")
                    pip_install_with(pip_py, *pip_packages)
                except ToolError:
                    if any(p.startswith("-") for p in pip_packages):
                        raise
                    warn("Could not install into that Python (system-managed?). Using $Decompile's private copy instead.")
                    pip_install_to("build", "pyinstaller", *pip_packages)
        ext = sorted(top_imports(src))
        if ext:
            say("Third-party imports found: " + ", ".join(ext) +
                ". If the rebuilt exe misses them, add them under 'Extra pip packages'.")
        name = Path(entry).stem
        launch = pyinstaller_cmd()
        if not launch:
            raise ToolError("PyInstaller is not installed. Install it from the Tools tab.")
        argv, pyi_env = launch
        cmd = [*argv, "--noconfirm", "--clean", "--onefile",
               "--noconsole" if windowed else "--console", "--name", name, "--distpath", outdir,
               "--workpath", root / ".build" / "work", "--specpath", root / ".build", "--paths", src, src / entry]
        say("Note: the rebuilt exe embeds the Python of this PC, not necessarily the original version.")
        progress(None, "PyInstaller is building...")
        if run_stream(cmd, cwd=src, env=_with_pythonpath(pyi_env), timeout=3600) != 0:
            raise ToolError("PyInstaller failed; see the log above.")
        result = outdir / exe(name)

    elif kind == "dotnet":
        csproj = proj.get("csproj")
        proj_file = src / csproj if csproj and (src / csproj).is_file() else next(iter(sorted(src.rglob("*.csproj"))), None)
        if not proj_file:
            raise ToolError("No .csproj found in the source folder.")
        progress(None, "dotnet build...")
        if run_stream([tool_path("dotnet"), "build", proj_file, "-c", "Release", "-o", outdir, "--nologo"], cwd=src, timeout=3600) != 0:
            raise ToolError("dotnet build failed; fix the errors shown above and rebuild.")
        built = sorted(outdir.glob("*.exe")) or sorted(outdir.glob("*.dll"))
        result = built[0] if built else outdir

    else:  # native C pseudocode
        cfiles = sorted(p.name for p in src.glob("*.c"))
        if not cfiles:
            raise ToolError("No .c files in the source folder.")
        result = outdir / exe("rebuilt")
        warn("Native rebuild is best-effort: decompiled C is pseudocode and usually needs manual fixes first.")
        progress(None, "Compiling C...")
        if run_stream([tool_path("zig"), "cc", "-std=gnu11", "-w", "-o", result, *cfiles], cwd=src, timeout=3600) != 0:
            raise ToolError("The C compiler reported errors (shown above). Fix them in the editor and try again.")
    progress(1.0, "Done")
    ok(f"Rebuilt: {result}")
    return result


# --------------------------------------------------------------------------- #
# PC scan: find tools that are already installed anywhere and remember where
# --------------------------------------------------------------------------- #
@dataclass
class ScanResult:
    found: dict[str, list[str]] = field(default_factory=dict)
    registered: dict[str, str] = field(default_factory=dict)
    folders: int = 0
    seconds: float = 0.0
    stopped: bool = False
    deep: bool = False
    lines: list[tuple[str, str, str]] = field(default_factory=list)  # (tool, detail, ok|warn)


def _target_names() -> dict[str, str]:
    e = ".exe" if IS_WIN else ""
    return {("analyzeheadless.bat" if IS_WIN else "analyzeheadless"): "ghidra", f"javac{e}": "jdk",
            f"dotnet{e}": "dotnet", f"ilspycmd{e}": "ilspycmd", f"upx{e}": "upx", f"pycdc{e}": "pycdc",
            f"uncompyle6{e}": "uncompyle6", f"decompyle3{e}": "decompyle3", f"pyinstaller{e}": "pyinstaller",
            f"zig{e}": "zig"}


_PRUNE_NAMES = frozenset({
    "node_modules", ".git", ".svn", ".hg", "__pycache__", "site-packages", ".cache", ".npm", ".gradle", ".m2",
    "$recycle.bin", "system volume information", "windowsapps", "winsxs", "$windows.~bt", "$windows.~ws",
    "$winreagent", "msocache", "perflogs", "steamapps", "crashdumps", "d3dscache", ".vscode", ".idea"})


def _fixed_drives() -> list[str]:
    """Windows: local hard drives only (no network shares, CD/DVD or USB-floppy)."""
    try:
        import ctypes
        k32 = ctypes.windll.kernel32  # type: ignore[attr-defined]
        mask = k32.GetLogicalDrives()
        return [f"{chr(65 + i)}:\\" for i in range(26) if mask & (1 << i) and k32.GetDriveTypeW(f"{chr(65 + i)}:\\") == 3]
    except Exception:  # noqa: BLE001
        return [(os.environ.get("SystemDrive") or "C:") + "\\"]


def _abs_prunes() -> set[str]:
    out = {os.path.normcase(str(TOOLS))}
    if IS_WIN:
        for d in _fixed_drives():
            out |= {os.path.normcase(os.path.join(d, n)) for n in ("Windows", "Windows.old", "Recovery", "ProgramData\\Microsoft",
                                                                      "ProgramData\\Package Cache")}
        local = os.environ.get("LOCALAPPDATA")
        if local:
            out |= {os.path.normcase(os.path.join(local, *n.split("\\"))) for n in
                    ("Temp", "Packages", "Microsoft\\Windows", "Microsoft\\Edge", "Google", "Mozilla")}
    elif not IS_MAC:
        out |= {"/proc", "/sys", "/dev", "/run", "/boot", "/lost+found", "/var/lib/docker", "/var/cache", "/var/log", "/tmp"}
    return out


def python_script_dirs() -> list[str]:
    """Scripts/bin folders of the Pythons on this PC (where pip puts pyinstaller, uncompyle6 ...)."""
    import site
    import sysconfig
    dirs: set[str] = set()
    try:
        dirs.add(sysconfig.get_path("scripts"))
        dirs.add(sysconfig.get_path("scripts", sysconfig.get_preferred_scheme("user")))
        dirs.add(str(Path(site.getuserbase()) / ("Scripts" if IS_WIN else "bin")))
    except Exception:  # noqa: BLE001
        pass
    if IS_WIN:
        try:
            r = run_capture(["py", "-0p"], timeout=15, env=os.environ.copy())
            for m in re.finditer(r"([A-Za-z]:\\[^\r\n]*?python[w]?\.exe)", r.stdout, re.I):
                dirs.add(str(Path(m.group(1)).parent / "Scripts"))
        except (OSError, subprocess.SubprocessError):
            pass
        appdata = os.environ.get("APPDATA")
        if appdata and (Path(appdata) / "Python").is_dir():
            dirs.update(str(p / "Scripts") for p in (Path(appdata) / "Python").glob("Python*"))
    return sorted(d for d in dirs if d)


def _scan_roots(deep: bool) -> list[tuple[str, int]]:
    """(folder, how many levels deep to look). Quick = the usual install places; deep = every drive."""
    env, home = os.environ, Path.home()
    roots: list[tuple[str, int]] = [(d, 0) for d in env.get("PATH", "").split(os.pathsep) if d]
    roots += [(d, 0) for d in python_script_dirs()]
    if deep:
        if IS_WIN:
            roots += [(d, 9) for d in _fixed_drives()]
        elif IS_MAC:
            roots += [(d, 9) for d in ("/Applications", "/Library", "/usr/local", "/opt", str(home))]
        else:
            roots.append(("/", 9))
        return roots
    if IS_WIN:
        for k in ("ProgramFiles", "ProgramFiles(x86)", "ProgramW6432", "ProgramData"):
            if env.get(k):
                roots.append((env[k], 4))
        local, app = env.get("LOCALAPPDATA"), env.get("APPDATA")
        if local:
            roots += [(os.path.join(local, "Programs"), 4), (os.path.join(local, "Microsoft", "WinGet"), 5)]
        if app:
            roots.append((os.path.join(app, "Python"), 3))
        roots += [(str(home / n), 4) for n in ("scoop", ".dotnet", "Desktop", "Downloads", "Documents", "tools", "ghidra")]
        roots += [(d, 3) for d in _fixed_drives()]
    elif IS_MAC:
        roots += [(d, 4) for d in ("/Applications", "/Library/Java/JavaVirtualMachines", "/usr/local", "/opt", str(home))]
    else:
        roots += [(d, 4) for d in ("/usr/lib/jvm", "/usr/local", "/opt", "/usr/share", "/usr/lib/dotnet", "/snap", str(home))]
    return roots


def _scan_chunk(chunk: list, targets: dict[str, str], abs_prune: set[str], deadline: float, halt: threading.Event):
    """List a batch of folders (runs in a worker thread). Returns (subfolders, hits, folders_done)."""
    subdirs: list[tuple[str, int, int]] = []
    hits: list[tuple[str, str]] = []
    done = 0
    for d, depth, md in chunk:
        if halt.is_set() or STOP.is_set() or time.monotonic() > deadline:
            break
        try:
            with os.scandir(d) as it:
                for e in it:
                    try:
                        if e.is_dir(follow_symlinks=False):
                            if depth < md and e.name.lower() not in _PRUNE_NAMES:
                                if IS_WIN and getattr(e.stat(follow_symlinks=False), "st_file_attributes", 0) & 0x400:
                                    continue  # junction / reparse point: avoids loops like 'Application Data'
                                if os.path.normcase(e.path) not in abs_prune:
                                    subdirs.append((e.path, depth + 1, md))
                        else:
                            k = targets.get(e.name.lower())
                            if k and e.is_file() and (IS_WIN or os.access(e.path, os.X_OK)):
                                hits.append((k, e.path))
                    except OSError:
                        continue
        except OSError:
            continue  # no permission / vanished folder
        done += 1
    return subdirs, hits, done


def _walk(roots: list[tuple[str, int]], targets: dict[str, str], abs_prune: set[str], deadline: float,
          resolve: Callable[[str, str], bool], stats: dict) -> None:
    """Parallel breadth-first search (shallow places first). Stops as soon as every wanted tool is resolved.
    `resolve(key, path)` checks a hit and returns True when it is a working copy."""
    remaining = set(targets.values())
    seen: dict[str, int] = {}
    level: list[tuple[str, int, int]] = []
    for r, md in roots:
        k = os.path.normcase(r) if r else ""
        if k and os.path.isdir(r) and seen.get(k, -1) < md:
            seen[k] = md
            level.append((r, 0, md))
    workers = max(8, min(32, (os.cpu_count() or 2) * 4))
    halt, last_tick = threading.Event(), 0.0
    with ThreadPoolExecutor(max_workers=workers) as pool:
        while level and remaining:
            if STOP.is_set() or time.monotonic() > deadline:
                stats["stopped"], stats["reason"] = True, ("stopped" if STOP.is_set() else "time limit")
                break
            size = max(1, min(48, len(level) // (workers * 2) + 1))
            chunks = [level[i:i + size] for i in range(0, len(level), size)]
            nxt: list[tuple[str, int, int]] = []
            for subdirs, hits, done in pool.map(lambda c: _scan_chunk(c, targets, abs_prune, deadline, halt), chunks):
                stats["folders"] += done
                for k, path in hits:
                    if k in remaining and resolve(k, path):
                        remaining.discard(k)
                if not remaining:
                    break
                for d, depth, md in subdirs:
                    key, left = os.path.normcase(d), md - depth
                    if seen.get(key, -1) < left:
                        seen[key] = left
                        nxt.append((d, depth, md))
                now = time.monotonic()
                if now - last_tick > 0.2:
                    last_tick = now
                    progress(None, f"Scanning... {stats['folders']:,} folders")
            level = nxt
        halt.set()


def _file_contains(path: Path, needle: bytes, limit: int = 64 * 1024 * 1024) -> bool:
    try:
        with open(path, "rb") as f:
            seen, tail = 0, b""
            while seen < limit:
                chunk = f.read(1 << 20)
                if not chunk:
                    return False
                if needle in tail + chunk:
                    return True
                tail, seen = chunk[-len(needle):], seen + len(chunk)
    except OSError:
        pass
    return False


def _validate(key: str, path: str) -> tuple[str, tuple] | None:
    """Is this candidate a working copy? Returns (path to remember, rank) - higher rank wins."""
    p = Path(path)
    try:
        if key == "ghidra":
            props = p.parent.parent / "Ghidra" / "application.properties"
            if p.parent.name != "support" or not props.is_file():
                return None
            m = re.search(r"application\.version=([\d.]+)", props.read_text(encoding="utf-8", errors="replace"))
            ver = tuple(int(x) for x in m.group(1).split(".")) if m else (0,)
            return (str(p), ver) if ver >= (11, 0) else None  # 10.x and older need an old JDK
        if key == "jdk":  # candidate is javac (must exist); remember the java next to it
            if not p.is_file():
                return None
            java = p.parent / exe("java")
            major = java_major(str(java)) if java.is_file() else 0
            return (str(java), (major,)) if major >= 21 else None
        if key == "dotnet":
            major = dotnet_sdk_major(str(p))
            return (str(p), (major,)) if major >= 8 else None
        if key == "zig":
            r = run_capture([p, "version"], timeout=20, env=os.environ.copy())
            return (str(p), (1,)) if r.returncode == 0 and re.match(r"\d+\.\d+", r.stdout.strip()) else None
        if key == "pycdc":  # must really be Decompyle++, not any file called pycdc
            return (str(p), (0,)) if _file_contains(p, b"Decompyle++") else None
        if key == "upx":
            r = run_capture([p, "--version"], timeout=20, env=os.environ.copy())
            return (str(p), (0,)) if r.returncode == 0 and r.stdout.lower().startswith("upx") else None
        if key in ("uncompyle6", "decompyle3", "pyinstaller"):
            r = run_capture([p, "--version"], timeout=40, env=os.environ.copy())
            return (str(p), (0,)) if r.returncode == 0 and re.search(r"\d+\.\d+", r.stdout + r.stderr) else None
        return (str(p), (0,)) if p.is_file() else None  # ilspycmd: needs .NET to run, so just check it exists
    except (OSError, subprocess.SubprocessError, ValueError):
        return None


def scan_pc(deep: bool = False, budget: int | None = None) -> ScanResult:
    """Find already-installed tools and remember their real locations so $Decompile uses them.
    Only tools that are still missing are searched for, and the search stops as soon as they are found."""
    t0 = time.monotonic()
    res = ScanResult(deep=deep)
    stats: dict = {"folders": 0, "stopped": False, "reason": ""}
    deadline = t0 + (budget or (1800 if deep else 120))
    cfg, tried = load_config(), set()
    missing = [k for k in REG if not is_installed(k)]

    def resolve(key: str, path: str) -> bool:
        res.found.setdefault(key, []).append(path)
        real = os.path.normcase(os.path.realpath(path))
        if real in tried:
            return False
        tried.add(real)
        v = _validate(key, path)
        if not v:
            return False
        cfg["paths"][key] = res.registered[key] = v[0]
        return True

    if not missing:
        ok("Every tool is already available - nothing to search for.")
    for phase_deep in (False, True) if deep else (False,):
        if not missing or stats["stopped"]:
            break
        say("Scanning every local drive for what is still missing (file names only; nothing leaves your PC)..."
            if phase_deep else "Quick scan of the usual install folders (file names only; nothing leaves your PC)...")
        names = {n: k for n, k in _target_names().items() if k in missing}
        _walk(_scan_roots(phase_deep), names, _abs_prunes(), deadline, resolve, stats)
        missing = [k for k in missing if k not in res.registered]
    res.folders, res.stopped = stats["folders"], stats["stopped"]
    res.seconds = time.monotonic() - t0
    if res.registered:
        save_config()
    cfg["last_scan"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    if deep and not res.stopped:
        cfg["deep_scan_done"] = True
    save_config()
    for key, t in REG.items():
        path = t.find()
        if key in res.registered:
            ok(f"{t.name}: found on this PC and registered -> {res.registered[key]}")
            res.lines.append((t.name, f"Found on this PC: {res.registered[key]}", "ok"))
        elif path:
            say(f"{t.name}: available -> {path}")
            res.lines.append((t.name, f"Available: {path}", "ok"))
        else:
            warn(f"{t.name}: not found on this PC (install it from the Tools tab)")
            res.lines.append((t.name, "Not found on this PC", "warn"))
    (warn if res.stopped else ok)(
        f"Scan {'ended early (' + stats['reason'] + ')' if res.stopped else 'finished'}: {res.folders:,} folders in "
        f"{res.seconds:.1f}s, {len(res.registered)} tool(s) registered.")
    progress(1.0, "Scan done")
    return res


_ver_cache: dict[tuple[str, str], str] = {}


def vcredist_version() -> str:
    try:
        import winreg  # Windows only
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\VisualStudio\14.0\VC\Runtimes\x64") as k:
            return str(winreg.QueryValueEx(k, "Version")[0]).lstrip("v")
    except (ImportError, OSError):
        return ""


def tool_version(key: str, path: str) -> str:
    """Best-effort version string for display (cached; may start the tool, so call it from a worker thread)."""
    ck = (key, path)
    if ck in _ver_cache:
        return _ver_cache[ck]
    v, p = "", Path(path)
    num = re.compile(r"\d+(?:\.\d+)+")
    try:
        if key == "ghidra":
            m = re.search(r"application\.version=([\d.]+)",
                          (p.parent.parent / "Ghidra" / "application.properties").read_text(encoding="utf-8", errors="replace"))
            v = m.group(1) if m else ""
        elif key == "jdk":
            r = run_capture([path, "-version"], timeout=30, env=os.environ.copy())
            m = re.search(r'version "([\d._+]+)', r.stderr + r.stdout)
            v = m.group(1) if m else ""
        elif key == "dotnet":
            r = run_capture([path, "--list-sdks"], timeout=40, env=os.environ.copy())
            vers = re.findall(r"^\s*(\d+(?:\.\d+)+)", r.stdout, re.M)
            v = max(vers, key=lambda x: tuple(int(i) for i in x.split("."))) if vers else ""
        elif key in ("zig", "upx", "ilspycmd"):
            r = run_capture([path, "version" if key == "zig" else "--version"], timeout=30, env=tool_env())
            m = num.search(r.stdout + r.stderr)
            v = m.group(0) if m else ""
        elif key in ("uncompyle6", "decompyle3", "pyinstaller"):
            if p.is_dir():
                for di in p.parent.glob("*.dist-info"):
                    m = re.match(rf"(?i){re.escape(key)}-([\d.]+)\.dist-info$", di.name)
                    if m:
                        v = m.group(1)
                        break
            else:
                r = run_capture([path, "--version"], timeout=60, env=os.environ.copy())
                m = num.search(r.stdout + r.stderr)
                v = m.group(0) if m else ""
        elif key == "pycdc":
            v = "built " + datetime.fromtimestamp(p.stat().st_mtime).strftime("%Y-%m-%d")
        elif key == "vcredist":
            v = vcredist_version()
    except (OSError, subprocess.SubprocessError, ValueError):
        v = ""
    if v:
        _ver_cache[ck] = v
    return v


LOCATE_HINT = {"ghidra": "support/analyzeHeadless(.bat) inside the Ghidra folder", "jdk": "bin/java(.exe) of a JDK 21+",
               "dotnet": "dotnet(.exe) of a .NET 8+ SDK", "ilspycmd": "ilspycmd(.exe)", "zig": "zig(.exe)", "upx": "upx(.exe)",
               "pycdc": "pycdc(.exe)", "uncompyle6": "uncompyle6(.exe) (in a Scripts folder)",
               "decompyle3": "decompyle3(.exe) (in a Scripts folder)", "pyinstaller": "pyinstaller(.exe) (in a Scripts folder)"}


def register_manual(key: str, path: str) -> str:
    """Register a tool the user located by hand. Returns the path that was registered."""
    if key not in LOCATE_HINT:
        raise ToolError(f"{key} cannot be located manually.")
    p = Path(path)
    if not p.is_file():
        raise ToolError("That file does not exist.")
    cand = str(p.with_name(exe("javac"))) if key == "jdk" and p.name.lower() in ("java", "java.exe") else path
    v = _validate(key, cand)
    if not v:
        raise ToolError(f"That does not look like a working {REG[key].name}. Choose: {LOCATE_HINT[key]}")
    load_config()["paths"][key] = v[0]
    save_config()
    return v[0]


def get_setting(name: str, default):
    st = load_config().get("settings")
    return st.get(name, default) if isinstance(st, dict) else default


def set_setting(name: str, value) -> None:
    cfg = load_config()
    if not isinstance(cfg.get("settings"), dict):
        cfg["settings"] = {}
    cfg["settings"][name] = value
    save_config()


def forget_registered_paths() -> None:
    load_config()["paths"] = {}
    save_config()


def tool_origin(key: str, path: str) -> str:
    """Where a tool lives: '$Decompile' (our private folder), 'PC scan' or 'system'."""
    try:
        if TOOLS.resolve() in Path(path).resolve().parents:
            return "$Decompile"
        reg = load_config()["paths"].get(key)
        if reg and os.path.normcase(os.path.realpath(reg)) == os.path.normcase(os.path.realpath(path)):
            return "PC scan"
    except OSError:
        pass
    return "system"


# --------------------------------------------------------------------------- #
# Command line (the GUI is the main way in; this is handy for scripting)
# --------------------------------------------------------------------------- #
def _cli(argv: list[str]) -> int:
    p = argparse.ArgumentParser(prog="main.py", description=f"{APP_NAME} {VERSION}")
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("tools", help="show which tools are installed")
    sc = sub.add_parser("scan", help="find tools already installed on this PC and remember where they are")
    sc.add_argument("--deep", action="store_true", help="walk every local drive (slow) instead of the usual folders")
    i = sub.add_parser("install", help="download + install a tool ('all' = every missing one)")
    i.add_argument("key", help="all | " + " | ".join(REG))
    a = sub.add_parser("analyze")
    a.add_argument("file")
    d = sub.add_parser("decompile")
    d.add_argument("file")
    d.add_argument("-o", "--output")
    d.add_argument("--scope", choices=("entry", "app", "all"), default="entry")
    r = sub.add_parser("rebuild")
    r.add_argument("project")
    r.add_argument("--entry")
    r.add_argument("--windowed", action="store_true")
    r.add_argument("--pip", nargs="*", default=[])
    args = p.parse_args(argv)
    remove_legacy_venvs()
    try:
        if args.cmd == "tools":
            for k, t in REG.items():
                path = t.find()
                where = f"[{tool_origin(k, path)}] {path}" if path else f"not installed ({t.size})"
                print(f"{'[+]' if path else '[ ]'} {t.name:<22} {t.purpose:<44} {where}")
        elif args.cmd == "scan":
            scan_pc(args.deep)
        elif args.cmd == "install":
            for k in (list(REG) if args.key == "all" else [args.key]):
                if k not in REG:
                    raise ToolError(f"unknown tool {k!r}")
                if args.key != "all" or not is_installed(k):
                    install_tool(k)
        elif args.cmd == "analyze":
            fi = analyze(Path(args.file).expanduser())
            print_info(fi)
            miss = missing_tools(required_tools(fi))
            say("Missing tools for this file: " + (", ".join(miss) if miss else "none"))
        elif args.cmd == "decompile":
            exe_path = Path(args.file).expanduser()
            decompile(exe_path, Path(args.output or f"{exe_path.stem}_src").expanduser(), args.scope)
        elif args.cmd == "rebuild":
            rebuild(Path(args.project).expanduser(), args.entry, args.windowed, args.pip)
        return 0
    except ToolError as exc:
        bad(str(exc))
        return 1
    except KeyboardInterrupt:
        return 130
    except Exception as exc:  # noqa: BLE001 - never show a raw traceback for an unexpected failure
        bad(f"Unexpected error: {type(exc).__name__}: {exc}")
        return 1


# --------------------------------------------------------------------------- #
# Artwork (PNG / ICO as base64). Generated once so main.py stays a single file.
# --------------------------------------------------------------------------- #
NAV_B64 = {
    'home': (
        "iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAEB0lEQVR42tVXT2gcVRj/fW9m19jGorGbvLezNNBSSWdnJv8Q"
        "KkU23j0URE8B8WQ91qsH6UGPuQk2eNRLgyB4lBCLAcXqxSxVipLdbLObzWYXa0obN/Pe52F30klMNrtJLDgwMLz35vt93ze/"
        "3++9Af5vFwOCAeupgt6KAd56WuALyNkAUFT+ZGkoO9Wq/k3rP25vC7QwlH19XQWPGulRLkr/7dgcnTQm7YBKb7qeHjX1dMAV"
        "5fMjZ4yL0r8edYO7BKcuSETfIme9htthUfrXB4Q1YxFQ0+F7RKj2k/VlHxE1dPhxZi3/AQMCABPAx2EutQPhvvQ+euSMcS0d"
        "mKi9ALCivKsbKvgrdCZ4VXkzMcaLI8slel5V3iehM851FWwWZPaN6Jv+hMkEAKxIL7euggZnJrgs/c+jTvYMHr2Qd91kWXpf"
        "cGaCa+mgtiK9HABEgHHC/THoBVUVlDgzwWXlf72qJk/1JLdIGvmU219W3jxnJrmqgpXfhwJvL+he8GXljawrf4kzk7ym/IXf"
        "1Etnu5JbFCCfcmVVBj9vOeNcVf6de6nshbiGO+l7OeXKNeX/2H536e7ZERWPvY8btbJaVt5ITQX5B+lR3lBBs6j8Vw+q9KDE"
        "i6nshYoKNh+kR7mmgnsF6bp7KxcRe9/CnC6o7JVToPkzwspuGvN3UoiExZAMiE30dyGPQWaAhLCG+4j6N41pnhHWxWfJ+qag"
        "slcIczrSuVhAziaAS9KbHqDE4oBlp6smnCXwYh8IBqgSYKYwyF0aAwPa9AsBAn9XNeHNF4SdHqDEYkl60wTwAnL2Dt0FkU4S"
        "NWuh/uxcZeldBoWtSY6bDLXcKWcvtO/oOW5GTMTEAIP0ucrStQ0Tzj5D1BREet9sy/LScNs0aFV689vOOEcS6mYjiNasSC+3"
        "7YzzfenNM0AfAqIsLw3H19pxl6K1X4sMCALMKsjsDuty3nWTL/4prgoj+kIyGgBsFpYRZqv+vPkKd91wd9vJEMCx2BRZqR3/"
        "Np2chnDDlBreO9JOftoUjCRaJG/CIAkbYaN5jXDjZidTIsD8q+I2uOkELpicJljX9PYdwcgDgCF4KSvxsmByDiGd2bfVXV0C"
        "W0myLMF6Lr32y0yLF8H7SbIuQ4RbvYSye9yU28w1p5+4WP307rkTAtbMO1tcZUcyxFO4bVpjPj/Jq7WuwCwOb95hmbF4TIAh"
        "wBChCQBEaHYas1k8PnLFDBgNNmzhfMkZqwOAMXpom9kYYKjkjF08aIyNPq/BhvcQquPRZ0fHyvt+UCQuNziE3eN+HsJggGys"
        "m+0fnEr+lb1S2rfiuej0QJh9yPq5kCFC1r0hE5mH0IYJs/GYvcU4ypH0uL8oJ/Gbc6zjLfUOiMOOt/8Av/jOY4n3eA4AAAAA"
        "SUVORK5CYII="
    ),
    'scan': (
        "iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAD6UlEQVR42uVXTWwbVRD+5r11fkoK5KfJvl1D1AhBcHbXTg1c"
        "OLjihDhxwFXggji0Uk9U4sKhVSs4wA04oUo9cahQAiduCFF6Q9CoUmhSEFVIHceO3SQKKUnsOPuGw3qLCbZjF1kceJIPfm9m"
        "vvlm5s28Bf5vi1oVZEAAKRH+/w7ASVzXBOiOeDYNSG7iIAMicKq9ZTRnmZaEGR8A1sxEjMEnKtCjRKQlYZGFnKXszTsHZf9V"
        "qBkQBOic6aQigt4l0MuDIgJQVYU1in7Fl6Av7xM+PJ6bu9kOODVjmjWdC0eEfK9fSOT9vaLP+JaABWKSTIgLwktKdj267ldK"
        "26zPja7eutwu87+BAkDGdM/79gkuKM9fNd3zmWhs4KBscWhc5Uzv400rzjt2gu+a7ptBXQQ22gZdUfEXN6y43lDxUkY5r9ae"
        "M1JG8MMD41nTO7tlJ7houX8Ujk0+xQC1VXCh8LLpfMPRJGdM50KwH+uqV9kXAcFIRqo6Vzia5KzpXqklcWiO/yqmiWe7hTFf"
        "Yr0mNB03C3O7AJgAbuZsTsWiXTB+rYDLW+gaG8/PrnFQinX1asIRNgfxwoAwiBlfq8LcNpBuqFz1XF8CYOcXMiXWPw4J4+gj"
        "uuIFp+mG4a53EAURBHA7CG/x0O52EinBAEngdoQEg3w76G6Ndf8BzBSyY9Fm7+VQRxAd2kbrGV8Ca2hCggCewTAfzvi6DwD7"
        "JOJl1rQPygT7w9xycd0ddsd6Jf3ig7cr0h97IruwGeay8RWc0TnlPNNL8tau1pvdfb1jQ3d+2GqpuAjQ00jL0eJPi2Xmr0zZ"
        "9Rjty0sBYFLWu5fT1btMADPTB/3CkCD+LABNy2ZFecBQWjJA+RHPWVPe7qYV56zpna2JCl1DyuCqXLifV87723aCV5VbzFrP"
        "D1bPxUN1ryUVO71jJ3jLinNeuZeLlvf0QdmCPRHPK/eLHTvBOdMtbypvZ1m5ZwDgRrWxPNSQyIw4bx2R4pNBETma9/e0z/he"
        "AD+DWDLI6SZKDokIVvb3NiRhwAgmF+/Cf+PJ3PznN5CMPIfZSltjcRqQpwD/N+WM95F4RzO/1i+MxyMURLDEGve1X2DgqkH+"
        "RzuaXukR4lPNYEGgw8Cp1YdAzkwc6wFie7Qf9UHcR3LJ75HzA4uzvz8YFtbEVDfkVc3MgohaYY7mT5vGDZ+RlhcBEeY0Y01M"
        "3bM8XVCuf8/ydMaamGol580cIEZaXkPKqFfZtcYbgTNSRseerY3AV5T7eu006zj4WgBeWQ/Az9U2no6Dr1txLtuTvGI6uTBt"
        "Hf1aCHO6rNy3S/bkXH7EOdVxxgdfKP/JChnWMv0Tdm7VB8/yVGkAAAAASUVORK5CYII="
    ),
    'tools': (
        "iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAADOklEQVR42tWXzW9MYRTGn/O+r5miLcW0c/uhJRNJx3wQiYWF"
        "EoJILCf8A/4BupBYkEissOpGNxYikrESiaWPjQhpCDo+QorWzHSqrY/qaO/ccyxub02rHaadEu/y3pvzO8/Jc855L/CPDlUq"
        "kLixvHhCgCxp5gIoQULPfn4bHUZKCKNFQjUBDgCMtsZXK5sb8gXYz3Nr3u/G3UIRQyoGFiQ04ZrzzopuWwl0OsBOB6gnga0V"
        "9QFI5uzC+chQakwAml16Wmh5CeB+K3p0OairWmkfAOSFoUHwE0GDkHMmXxYM72gZSI1OwabhplxockppOhg7sIKoGwBG2Rlw"
        "hLuJcJ9FajTRoRXQhwG6nBtY/rXFVcyLcq4AJKGQvz8YefmtaQtng9HnH6zw+tnfpoOb2yvoYNe9mYb47pHGuHxsjPG7+uhe"
        "AHiFkF8ALUjoJKAB4BSgKgTuMK6aWKfdvJX7rchbCYd9UwD6tc3m95BZWAq80sCAgC+USk3OY1QhQMRN6peBUlYp7vxshrcT"
        "IkSgtr5AOJgEtBTFSrr9LW/qNq4igIsSWFg7edlnG2JtrORxndK1o+xcaMo8PV70HgTwYCBczUY/qCLqGxO53tzou4SeHsdz"
        "tyrf2CBr8EmfgjycEBEf0bGMFTnzqTm8ZkodjzRFYqzNzSpS7TWkD4LlA/X02ECCylbsLQECOBOMXPErdXhchAhALWn1WZws"
        "CZ6BpJqEttZo7dcAhtk+2ZLpPetNurLAxdB0MHq1TpsjI1xgAaABxQDqlYEhN9y4MPLM2Unh043ZZxdnQ/8IPDfUtgXAWmWW"
        "jTiFWw7kRBXMflHSSsITCurRJ8aN0OCTnDdey1oSc0GH2S7ALa/5LtybN2Zfa/+jdKlFUtZa/B00L5waLzh7Ngylst5guQNg"
        "13SEu06pywAtHjq/qlJH/Qso5piv5O3NpYTOUFx0WaOlhs4AX0NCEcBpK9K1zoXaSwWdLrV3J/oY2l47MZbPGSKyRaRWa3+e"
        "nYpDpxV722Pt69ZvQnIvoI0voI3/Ozu9w7a9t9LQudyMdHBLIGfFzw1Z8fMvrE3rvHvWX//VkAr+bZQcIC6oQ//J9Pkvzw9g"
        "XtY4TUjuuQAAAABJRU5ErkJggg=="
    ),
    'code': (
        "iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAADt0lEQVR42u1WTW8bVRQ9bxynCVVXoZn3ZpwEEFIqz3tjT+wi"
        "IUAuYkslPhQpi0ogIRYsukhE16grJIgEv4Bsq7BA7NhVEYiqqNlA261rzxgwNgm4ThPH47ksxmNPEidx1CAUibeyPDPn3HPv"
        "Pfdd4P9zwkMAI4D9pwH8K8CrQCIOHv2uTcxeKF5M8/C/+cRpq9EGpjiXS1a4vLMh7EZpUr0AALdRGBkGUzte6XyCAUFZT7/k"
        "GZcmIvUMoFINzzLGcgEwqrFgusyty69jzV99WuX3kEsCgMvltbbpUIWrHwGACqEqb1K9sWM65HF5xxNybdd0yOXyWvzbEyu+"
        "h1wyj/V2WbcWxpm20gFAoO8BALWaBgAsQZfPaQlowF0GfKcxYJxpK2XdWshjvX0c+aFKy7q1UBe2v2M65AprOao3AQkAqHD5"
        "bZDKkaer9wGgzOWXO6ZDdWH7Zd1aGEb5kKTzvc6mmcKYx2Vl08iQa1qZT7rZc4W1fGLyo0hvozDSHRYaAHiG7fxlZMjj0i3O"
        "FMbiHX0i8siDR5GG70Xg6kNKzZHH1Tdxnx9FfsDnkYqibi3UDTvYNR1yhTpAGldV4XKFpnLk6daNeEB7ydXyrulQ3bCDYo+8"
        "29BRFN6kfLlm2P6mkelUhLo5iBQ91WCekL9smw65unVlv5o4eUWom5tGplMz7E5J2K9G7/amTAfs/DnGEj6R3yFUAeAKmowB"
        "FAdkAD3SMzPPIJjd6PgNStLP4dOvg1h0RGgyAOgQqgGjYIxpI9sUnB+Y6hJXi00jS00jSyUul2IpZPE0l4V8y0/NkcvVDwMu"
        "iJ7aEpdLfTy1OHD8RqkqcbnUMLLUMLLkdcn7Hd2tHZef0VQuqOjy88Pq63Hr47+NLD3eI+KQUdoHVouPjSxtmVlyRQQ+n+hZ"
        "Sci1TmqOXG69uzewENgVannbDIN3e0qPuTz66bQ+qAnbb+2dWswzLk14XDWqQrUf6fbz/WkWkYY2qgnb97h6byjS/cojT7fC"
        "i+CLbpe+9iS028PIu6sxpa0D3h2SdPAUy7R2TYc8Q934ldsf0VSeKlx9BQD30+nRsKbq0ydmlurCbg0zKg+9nfJYbxNyyenq"
        "g1tbCK4ntQQQ0NUA9AqIiEA/AYD1cDy0G6Or41oCW6Dr09UHt6h7uz3FyhOm8Xch3/Z0+80/hL3RCDs1361vWJZU+sUqt9+J"
        "f3MKq08I9Jueee5PI9N0ubx7P50eHbTgnfrSFzVJ8WKa1yZmL+wniXf22Vlhz8QCf2bPP6nP+hfblSQFAAAAAElFTkSuQmCC"
    ),
    'gear': (
        "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"
        "Pc5p8z/5aPsX9fkzB8EVxD8AAAAASUVORK5CYII="
    ),
    'sliders': (
        "iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAEFElEQVR42u1WTWicZRB+Zt7v+za7SbY12jT7R5UmSJNsii6t"
        "P7TEW9F6alj14MGTB0GQeukt9aoHzwVF0ItkDYJgwYMkooI0FSEmFGMwtpukm582icn+ffu973jYTbJJdjfBUCniwMDyzbvz"
        "vPPOPDMD/C81RAAWJJUA9G8B0m4wAfgBRVYGG6wCSEd6Ti+G4udvhhKB3ecOqoO7Ltzw6eZCiQDD/dRPPOAjQs6Y6QL0G5G7"
        "kz8eNsgdwFOReLRdIbu2BjSrvC44Te9FLN8746WcXjKenHdarCVdmtW2/UzrBmdXsIIjxLIfyLpu5oJVCJy699v8FrAgqQgp"
        "ne7ofelRZX29Yjxv06jAlgL0xdU/1Q13A9+2nTQJO8DrYsAQTwAiQBrVSMUuR9my72vvYiwzcV2QVBaQkjKIzOSMuc6gZi3C"
        "AFCC6fOzaj1j+z1AuJ0toyEskJ8AuBDQfuEKQRRI8sbkFGSm/DUlDXOc7ugbeEzxFwRCEQZBsjDrFb6MZSYvHTbHvJM6SVWp"
        "WB5BvxXLjA8vet6r6+L94BoZX9ClD5iaXq/i9dbZm0jYW34SCXvTtq0N+sBuw2B9zlKt/0jb2eBQd7dTy9e+oBXebd80kbBH"
        "0G8JwBPd3c7uSAXgTHvv8YVQ/PPlcF9mOdQ3faej910AGEG/NQSoat81wUdOnGj6J/lKd/R+L9GE3AnF5V74tJjo05IOxd9s"
        "5HuLTnOhvnNNRMMF0X+IoHSgJkAQA/I3E5+Z9op6YPU2P+8EzLVgFOti8iTySzkvpPzMnVntvRZbmByp0GnHgzODntIkig7Q"
        "xwGIAEwAXBgsGo/uG82eiLGAFkN4rlLBGoKsVcX5Hf6/CoUC5/xhe3l1TdrqQrZhTTQBABuPfH6yNXmjEeV0j5fycoQVPa4c"
        "pD33asAtfJjVftXKjhlzSt6FhfFszeps1IUayWw4/qQP+MgCnxWRQk7MJ5HMxGUCTJ1OVnsM1tIhQNWbaJu/V2M9J2eOdXfU"
        "89eAj0kexeKe9L6ADSL8XLp9vPeVgKK3IRTUwDca9tWpuy1upHNOdU1HNOE7DwCmOjt9XdMRPbrDR7sAKbMZMR2cMj2Xjiln"
        "WCqFdNj2SZWqNPMdPaccst4vwqwYiGGUE8QAmfItLxwl1X5lI2PGSjn+OBg1YWVbeZGUQHKb5+v1ZR/4EVf0lXBm8pYAbAFJ"
        "AlLQoCeamV/2gWo+Q1EM8iJ6rJS3brhZLBoPMeUgyJzk/akHG4Qlba4BuAUkaQfG7+GeWJAdX6HoymabKRm2bDaey3Q5ajtv"
        "/VrK68WqpcAIv+gzXqEIwFdjShYANPkc+su4xa75yfSBVp9quRN91m/r7GcPYg3C3lFW1moq7V38tofGfvpwr7oPzXL/n5G/"
        "Abj2G220zdf4AAAAAElFTkSuQmCC"
    ),
    'doc': (
        "iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAD5klEQVR42sWXz29UVRTHP+fe+6YDFChFYDrVqgkSQ9poJEFi"
        "TEb2LCRRlm5MMMaV/gPgzpjAzqWujY0Sl8SYOm40CPEHxahpIjSdoS1QfkP73rvnuOgMHcq0wxQiZ/feO/d+53vP+X7vGaFN"
        "GAhUPF3ED8B+qjlPIgzcw+aG5UwF7MLQyJZiLu9m6JxT0pUWR0yciK7Dbb0lcVbq57403vbCaOwKePF4q3lY4PD2QvJJakrB"
        "dSYxb0oPjqnScFmmR48blSAdjj20PTKxYqqaX9bstBjjhjjBtDVHQRyYghi8mYj0bXT+2FRpGJmudgRvCywiWcH5IDGOlqf/"
        "ON6J8dTAyGtBXH+KsdmHYxceArw9sCENXhvGqITnIJyH+zb4h1uyi14DEOaS1DQqfO6x97b7pCN4WJ2L6H6quVHh+QcXy2I/"
        "Qs2GY9H5sKW+64Na+c8xZ/6LftfKHCdwX6nc45GRmGJ5rfzXR07JbqqeSc3SPueP1UsjHwrocqmFR9StyCJuT79LgsCneGFe"
        "lRzjtipO5PjFHS+dkJnfz7cyD4+GiwNMsPdvxHjojsWo4EzwDjDjoBe3SV0sdlnjDh3Q+PWDF8+dBE4u/14bGNlbENl8R0Jc"
        "E/AZbolRCU1PbsYbjefBnTWfZJkAZElitYnBRSC7Epr6WBPwHg5E4WNdMWGCfPkLgBrD1pWBtLoTwOy20fV1P/KOiCwoOr+k"
        "81a3E92E67/m9PQztbM/H+mgmA6MzQNEHw4OFHo+Q2NDviuEc1xP704Czx4Fq6+SvCqwQxpN4X+8lC2MRmxBjbTVPO65LBbX"
        "O98P8v1yg1lLjQ2gPP3rBeBQtx1fW/tRN9GPuMnS168UfchizNL2N5pYnw8baznnd03/dslA6msF1kaNa+VvDgy6wrfXNRJc"
        "WGkooIhjg6SngFePghx+BMYGoDn/zvn8l4j1xUWbXLJMw8CiiegNjaLwHcBRYM2MHaIAQ7NnzwJ7n0CN9yRTO+ZfX+dCkprO"
        "R1PnxWlBXDG1uFCeHq82c78Cfwi6nbkerPEYlTA5NNcbUjmx1SebMyIOQTESPPU8Xr+8c+/Q1ol490xj3Ri9jWpc6U7HJk39"
        "udv7qeZMcrVeevmF1OLALNliBmLbASFcfGri1I12+9RkJAfMROzhGCvF1GJE9K16afhFQ5wS78yoZe6eN8AMGQ5J6qXhojbu"
        "yOYQCKBGKcck5GmyKnDz5lGxWgHx23yyr4Dbt4Ql7Rt/BX/KTZmJ+UIW7WqrSlbaifHduwt91+Rgor4nRbWr/zIt5eoVn9wk"
        "/v10ffyne9PK/xzS8cXShFvxjwNxlKq1k9d/bgjKdfrcgMgAAAAASUVORK5CYII="
    ),
    'info': (
        "iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAEK0lEQVR42tVXvU8cVxD/zXt7EBwsQxTu3sIRJFtKsXvvzuKQ"
        "7O5cULhNQRfiJo1LlNqy8weksBs3kXWKqGxZ+ROIOxcQOeagiGTDwn3AEcUg8xHu7r1JsbdmOexAcBySJ20zb2Z+M/Pma4H/"
        "w2GAHgKSUXDiX0gDfQhAwZiQx/NNSAbESXTSSZQRHhkAqKWyHyccZJoMnyy7AMCCagnCQrOFkrv+fKdT5m8Dt0NHBNjyYPbz"
        "boublviL80KO9JAMbwCAGXts8NqaQDD9uC9wP119/mvbcyaATwwcvRcBvKYy30gSdz6Vid7fbQt/WPsLg2cBBG32EQKNfSRE"
        "7hPh4DfT3DZs76i10ndxPccCR54C4IqrfxiUiS83rcG+5e8l8f1kbf7ntxlbd/WoYbrZLejrPiFRNc3podr8V5Gud3n+xpAo"
        "iQLlT3N6lNddXamq7PXOaCwNeGppwFNxGgBUVfb6uqsrnB7lQPnT0Zv/ZT5FoKtKT9n0KNddXV5WngcAs8gnwvIBBamcv+7q"
        "6rqrq0Eq5zNAjIIzi3wCAJaV59VdXbbpUV5Veiqu+x0lAwoG/Et1V29vDeaaQVKPA0AJXhcAzKDghIb5k5zOM6fzvKr8yfhd"
        "xBsk9fjWYK5Zd/V2MOBfCo17S6lFgmWl7/JwnpeV/yDyNB5mBqg04PVW3Eyx4maKpQGvN6JHfAee+w94OM9lpe/GMY5kccXN"
        "n6uoTHlzMNdaSWoddqrjG0fneRg2ElpJar05mGtVVKZccfPnOvPh4G1T2Su7Q5e5rPSzI0wdRpaVvlFW+sYJ+J7tDl3m1VT2"
        "ShxLAMBPqBMACGF0D0mWhKchvSAPK7stCOCqq/N9Uhb7pCxWXZ0ngBm3D71fJCsJT3tIshBGH8ICgGtvakkoEBEzVuP0g/Mt"
        "AMAIbr62ptlgtsLI/vBu8ZDXkSwzVkFExELF6eI0Q6Mbzp4BBAGCiVun0dEOdds6smtgZiIMx+mdp8FG0DFtN5IlwjCYmcmu"
        "xentUCcZAKyV83tsyDCuhvQn5rSjNJI1jKt7bMhaOR/Haof6kQ2TKzH/yrQqvUJkVpJaR6VxmnICgJWk1r1CZF6ZVkWIxPwh"
        "rGh6zKDgDNXmdhn0+IJ0pBV2igC+iJdH8iAhjGGAOWz8R5r/RbwUBLAVduqCdCSDHg/V5nZnUHCiYSFiobEMkDH23karsdMv"
        "nMkgqcfHMNeM2mD0nqbV1Z8gciSIrEVXHLQEr2sMc80gqcf7hTO50WrsGGPvMUDX8MSiM6sJsMCEGNlYeLHPuHVeSKdHoris"
        "PC+DxUbYBgvEAFlht2B5d8+aXcu0FDaLOs0in8hgsbGsPK9HonheSGefcWtkY+EFMCFCjPcci0Eq5wepnH/asXhmi8D7rD4r"
        "bfbP/pHV50yXvX9jvT2zhf6//QvzIc6fj5BcPMfIUfIAAAAASUVORK5CYII="
    ),
}
WHITE_B64 = {
    'scan': (
        "iVBORw0KGgoAAAANSUhEUgAAABYAAAAWCAYAAADEtGw7AAACQUlEQVR42rWVz2sTURDHZ5rUQGPBIlgQBP8Bb0UULx70Vqt/"
        "gR76D/RPyNWbB/8HIeDJg4f2UrGieMlFKkKhtVnXNLv7fu/bTdSvB3frWpMmpjgwLOzM+7w382bmEf0n4XEGAExENSJCoVzo"
        "d2bGTLsBqE2wz80M7Xa7FzPnNnLnXnit3+XWPs+9Xw+CYIGIqN1u1/4Z6pJkbeC9AQCn1L4V4n0q5RcAGOb5oYrjm1OfvAK9"
        "BwDDLNt2Uq5UfbwQt4fefxh4n7t+f2UiHAADYEi5lHuvvDE7J2zHi8NOp5lZu59qvQdgvrhkHgeuExEZITYAwCTJteL//Am/"
        "c0RE6uhoFQBckqydetnHaRDipRHioFJuoyMDGl7r1ArxtHqwqpQh/qpL5mUmCsaFx8zEzGDm/NtwqOaYl8eld676BdEhE11l"
        "ZrRarb8aCAAB4DAMm/ONxhKIPk+qiDoRkRViHQB0HN8qc1oJnwE0iIhUFD0EABNFdybluFy44K0Ncuc+hp1Oc5Sv6/cvD7z/"
        "6qTcnqZLj+tRRdGNQZblgyzbc1o/6PV654mIhBAXUqUeZdYmAOC13unv7i5O1Silg4yi6wPvPwGAkzJ3QvSclD+KTnxlkuQt"
        "AKRab6Fo8Ynwcga02+1a5tx9b+0Tr/Wz3LnH3pi7BWQxVWqrgG9ODT/NobQhCBZSrTdngTOAGoB6RWunwYPfcJ75hRgF98a8"
        "juP4ykzzehQ8DMOm0/oNAKhifpxZSrgx5lJm7eqZ0jDmffxDfgLHuzqyWf3jiQAAAABJRU5ErkJggg=="
    ),
    'refresh': (
        "iVBORw0KGgoAAAANSUhEUgAAABQAAAAUCAYAAACNiR0NAAACCElEQVR42s1UPW8TQRSct+fEOseOE1mCCgkKChoKGhoaWor8"
        "kZT8ALumRUpECaVFgUCipURCFkWElIKKIlKkJHt3vo/dO3tvKHIXWRc7MVR5zWp334xm37x9wF2J+PT0/snJSQcASMp/kdRA"
        "xvG9IsumcRi+r869OkfdBCbpXZFcroqkipybOedaQj6v0ssa11pFJiIE4Oqzxj6Itf6jlNol6YmIW0lYk52dnfV63e5bl+ff"
        "t3Z23pFsW2sfSFEIADUvywTAI0RRH4BeEHHtmYrn59tmOv1BkmkYfgCAJAzHJFnmOZMgmM+yjM5amiB4WGHVsqd6ABBrfViR"
        "vSHZJimx1vt07mMaBF9mxrAw5jQOgtccj72lLl8VPwx3bZLkWRQdNe/qyKLol01TXatavF+UqQDAOPekvbW1SeBzVYINESFJ"
        "RbI9HA4Vy/JTu9PZjYPgRZNHrduDIlICKEejEaEuYS3PmzfzFglLAPA97zhP00KAvcq1OSeTDU4mGwDmIkIB9vI0LXzyuNmH"
        "t5oCkUWZqIxirPVh85cAgCwxRnBx0TWbm9/8Xu+ZmU6PWJZfAUCUeuVvbz81cfzTL4qXGAwSALzWf8vc1lr3bZIc2DS1rMKm"
        "qbVJcqC17q8aCnLL10MURQPf9x8DgDHmd7/fv2jmrD1ZmvWpa3bTuJI1R1bdDeU/qbqT8RdFdov1ORo8iwAAAABJRU5ErkJg"
        "gg=="
    ),
    'folder': (
        "iVBORw0KGgoAAAANSUhEUgAAABQAAAAUCAYAAACNiR0NAAABuklEQVR42rVUPW8TQRR8s97EH3gl5CJS6CiQqNy4TMOf8H+g"
        "g4o/EX4HhU/poHYDgsKmo3ETISHk6BRfDh+XM77dSeG7aB1d7NgKT1rt6d5qdt/MvCfyyIHygyQqDwDcGfU+sCKn9npqdH7+"
        "lKQJw9CEYWhImslkUt92YWXMo+gtyVkSRTaNY6ZxzOv5nMss+zWfTrsF6OFwONQkK9dgMKjdcvj36ur7Qb3+cpll70VEOREl"
        "Inmj2XxtnZs2Wq3uTqKkcRxYa09Mp/PMT/65uDgxR0efF0ny1eb5TwI1kG4NQSnXaLeX13EctDudj7ooJ1PAAUktIjIej9Hr"
        "9QDgS3x5+e6JMW9snj/HXYEAEdIqpY4BvBCRFaAASkgCyL2Xk6QCcCoip5vKTKLoW2mvjZYA4DbZplQfgEaBpbeSDDi/AfwI"
        "gkCJyBqn+qHer/rZ7/d5N6ceu5eVr1hp0tFodK+B/SUi5Y61khXgnLW5p/JunTab/dNau1tAm+f1pjHHSRR9gIhaOWj7lOHK"
        "ifaw1eou0vSHL8onUaoL4JWQNQAPbzPAaq1/L4Az+W+x98yrwIDPh5D7j/6C8xtvEAbnRK0GcwAAAABJRU5ErkJggg=="
    ),
    'download': (
        "iVBORw0KGgoAAAANSUhEUgAAABQAAAAUCAYAAACNiR0NAAABzUlEQVR42r2UP2/TUBTFz7WdxthyWtcsTPz5IkzsfAzEQmeW"
        "7GXvt4CJCSTiraoIC+oXoJKXqrKv7bzWCakPA3H1FDV1FCGu9Janq5/Pufc8A/+zSAoAlGWZlGWZ2HebyumDkfQ98rvbtmck"
        "/T7oRqCIEADSNF2CvBaR56rqd/e7WnYAYJbn34zqgldXoz6F3kN2LbkDAPadkMR9ar2H7HYKAdD+mIi0W83wbhGqsV5cHIrI"
        "ra22NMYVEWZZ9piq8X1ubODdVg1w/ihJfswuL5+ICAVwSbpF295kWRYk+/tnhjzvtm6PwwZ2tpYgP+0FwTMvDL+oakzAiMjv"
        "OI6DOIo+DsPwhYh8TtN0uYJt3vx4PHYAoM7zdyR5U1Wns6L4aVTNrChOSdKoHlt2pTcu0+l0AAB1URytoDSqC5Ks8/wDAEwm"
        "E6/v1axHx7OhJGmq6ngn2DrUqL65rqr3XZS2gq0aXZLe2tmzegYkPf5V2B3Xyuu/LyHpiEhrVN/6UfSqqescgAv2/ANEAODW"
        "j6LDpq6/hgcHJyQdzwr0S8dxXgejUde8zZABEZBcADgBILJ6myTpNU3zFPM559tkC8AQIIZD8X3/l4gsd9p8X/0Bt4tTAfvp"
        "9QcAAAAASUVORK5CYII="
    ),
    'chevron': (
        "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAABKUlEQVR42q2UMU7DQBBFZ4OVgoJjIApKeuSCK9DQIE4ADa1r"
        "qKioOAGXcE6QjpKOJJK9ya5jex0bkUcRGyERITvOtKN9+jv/z4hsKeAA8GRfBQx6PUyN8TNjrht1XTkKUCIimbXvAGkcX9Uw"
        "T0RUZ0XO2svP1aoESLW+FREJw3A3mNX6oiqKJUA2n983yhrVbWGeiMgyis7LotAA6WLxWPdUV2WeiMh8NjstnfsAcEnyTBh6"
        "wGAnZUkUHVd5PgbIjHna5ua/ORmNRhvgcBh/rdeFiIhS6rBrpjZzmkxOKufeAIokedVaH7X+WgOx0+nZz3ysffnVV63tN3Hs"
        "l84ta8ceml4QBINWEEDVgcwBUmPuumboz4okWt/0SnVqjJ9pvfPS7u+M9Dls3/jnHifkXSktAAAAAElFTkSuQmCC"
    ),
}
MISC_B64 = {
    'heart': (
        "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACDklEQVR42p2Uv2oUURSHv3NmZldDChPSpJWADxCsAm5ikUI3"
        "EQNTKExAVrfwHcJE9BUEEbbZBC22C8ZisxiwFR/AJm+QKFhIMnfusZiZdc2uuniruWfu/d1zvvMHJiwDMZBp7ZMF4ji4vLc4"
        "DkYFLu//LLjcjixuzY/Z49a8LbejSXekenlo2dx+hugDzK6h+gXvdgHQcBfvbyDyDfNvOeimIyKmAKSpCBjNpEt9ZgdYAhbQ"
        "YAWTI0yO0GAFWACWqM/s0Ey6AkaaCpQMpNfLbXN7jbD2gYvzDAgQEQyPEJTAcgTFzICcWj3CXdyWg+6xxXGgnMwVXnnWEPEI"
        "gogCUooYYOV38a844/GsAXAyp8rsohUMOMXKUMc5jmfITFFOAZhdNGUVX7o+wGUZiJZe/K1KFJdlGAMAVvG/Cmy9NUc9+0QY"
        "Xidz+ZDNuExOGAbk7oTz6Cb9zlcArchLv3OG9/fI/RmBBpj5CeF4VBXz34H70u+cVRn/rVql18vtzsNbRPU+5iO8pwRfhVQI"
        "Obcuh3uD6k6BuCLa6+XWSEN5/+YjziVooIjaCK+cKApw7pEc7g2skYaVCJOyYcvtSD6/zqyZPKVWf0l24cCM2pWI8x878m7/"
        "RXVmql4DsLvJc9t6bLb1xGwjeQVgjTScqmGHXd9IQwDbSPZtY/t4OAmmFbk8e4pJEF8da+7/Xf8S+QlQHeyNIVJZ7QAAAABJ"
        "RU5ErkJggg=="
    ),
    'bigcheck': (
        "iVBORw0KGgoAAAANSUhEUgAAACgAAAAoCAYAAACM/rhtAAAItElEQVR42t2Ze2wc1RXGv3Pnzr7wIxAlbqABgisEfqwd1gJS"
        "RNeuUNV/KkTa2ZIUkJpKSRWpRaVU2HHT8QhwUpVCVSRarAakoqLgQVQIVbQVkr2C8pK3OLvOkkhAIGljkTSp7di7sztz7+kf"
        "u2vWkAcJoVV6pZFm5d1zfnPu3O989xo4v4Oq13kNeG6DQZZriSMr2mjl0Ty7lqtB4DP+7XMfbAuLR42zrZ/FowbYFp9fBRlk"
        "YVS4lFIAEJ/+xUXG7NyNDNwEUAcr/UUAjdVvnyBD/APgKQL+ppqbXs+u+slCDdRF6lNX9NMBjloGUm4FLD/QIQy5CYxbSYqr"
        "jIYIYAqAAXA1J1Elsq+h5j1woN8D4XmtgieybTumPh7zMwFaPGq4lFJfev0HTQ0XLxtixvdlYyQKQVBzHjjQBwDOgfE+A8eq"
        "QZeDcCVAnSTFGqMpAmhGcMIrEuG38/+eGXrnxkfnarHPGTA5Zst0nxN0ZPvXybD5hIiFrwEzdKF0nEF/ECSeFQ2YyFzmFE72"
        "+8Q/7ZieR49m/S0Cf0fEwpeACLpQ2heU/E1T8Z2v1XKcNWCSbZkmJ4jnBm4XYfNJETYjqlgOiPA4a/HQnmud9+tfgeSKNkJv"
        "9fM4kD6a5/op7HrbvpKEvpcZW4xoSOqS7+mS/91s547dtVyfGrBW+vhk/7dFLPS0CEmhSv5h9vX3sh0P/nmxukfzjNNJCIPg"
        "WiK5oo1qVYpPDX6dTLHLCJuX6nKgdaG8Mdu985lTTfcnAK1Ry3BTruqa2nY9mcbLImSGtOfv9ReKt+7teejdJNsyPQQNx9Fn"
        "pRe2LRLfmDYyPSN+e26w1ZTieREx23XZL7Ovbt7TMfxmLfepAZkJGKK2I4iZR/1JozHSqgv+h7pUWJft/uWBxMRmM9Mz4n8W"
        "DcUQAMfRndn+qwzTfFXEzBZ1wnvXX2F251eiAAwxiBZnZIlwWnAFyNHyw+B+oznWqjw/UL5/x3mDI0fHb5uPJiY2m7n4zveU"
        "r+9Qnh8YzbFW+WFwP8jRFtwlTKI+gEspFc/3X00SWwFAe8HvcvGdL31WuOSYLUGO7nrrvjuMpqZ3/NjKV9pzg625+IMvcVnt"
        "AgCS2BrP91/tUkrVd5zFm+R49V6LrbI5FgrmvFkZCt0P2xaZxCp1zpUbtYx0nxO0//2+LoqFdnEp+EKopel6Cb4LzGTGzOFg"
        "zpuVzbEQtNi6hGURkEHpPidITNgxaKyHIQDNT711rXM42QsBOssFUbcwYLn6mjf6l5vR0B9BZDLYD47NF0nSXwAg0+ochOan"
        "KjmxPjFhx9J9TgCurA8BAJZrCQAIwvoGI2quVrNFJlPsBoNW9ubPzYUwKNkLATBCDfJpETPXsK/KQhpSFYNvTl774KsJjEgw"
        "iEyxW80W2Yiaq4OwvqGeSQDAkRVtBABM+majKQJd8g/OTIsMCOySe07VS8I20n1O0DX101+Zy6JfUye8otEcDati+e5c1/CL"
        "SbZlhrYEIPDMtMjokn/QaIqASd9czyQAIN3bzpUez51kGiAhJj/oczyMWgZQ83hMS64ztUhygnh22yajOfLD4PiCZyyLRdXx"
        "wq5sfMejdZ2DMWoZH/Q5HgkxSaYBIu6sZ6q+jKlKlTRWs2YwcAAAktWnqDoUXnKdAtLi0UrlcgM3iag5oua9stEYiag575Wr"
        "O7u3WGwZaQwtLrpaDgYOsGZAY3U9kwBAtVbFoEYwg1gcAwD0Vl90BsUnB9d079s+1rXvZ+Ptb96zGkRsVSqMj0vVNRPbVsGU"
        "LrQmMoRUJf9wCTrlUkq5aFsixLX+TSyOgbnCUGkhDIDO6HCTQxAgMCS2yUsu6jUuMpOyKfZMYsKOuSn3I81iJgvt1DZlh8JR"
        "8awIy1VQOoAQCgV127624WmLLeNsFUEA4NqSJvAJEIFJL6+5Eowvrsr9YEYwU/SMSGidatB/SkzYMZCjwbZIjg8ZLqWUycFv"
        "ZHP0y3q+5InGaIiLpS171g6/mRyzpUsnMajV+Ex6OYgqDDWjAXC1gqOiinuIBIGANUDFMqX7HAXbFtkO+XD5XyfuFiEZUQtl"
        "X0RDvRXIzTG4eUr3OUHnnoEfGcuim/yZhaK8OBYJZgqP7InvfDLJp/Z86aMVGSNgDQkCBA7VM4mKcu+l6izl2FdgrbuvGLMj"
        "i37OcTSGgGz78K912d8gwtJU815ZREO9QUPLi5ZlIT41+FXZEHlYzRVLsjEa9We9v2Y7h+9JjtkyDUed0o+mXHXFmB1hrbvZ"
        "V2CmXD2TAICVtadg8bKa8yDC5uXLVukEGGRxRTDhODrBj5vZzh271XxpgwibIb3glY2I+ZX9e/ekAfyeg0CTaYRVsfxOeT7Y"
        "CGZKj+OUftFiS4BBy1bphAibl6s5D8Ti5XomAQCuVRFjWRJvqKJ/yGiOEvv6dhD4yPhHUpOhLX5iYrOZ7a5AUsgMqYVSYITl"
        "TSToMtbMYBR1qbx+3w07j1luSpzONx4ZbyMQmH19u9EcJVX0D8mSeKOeSdSWdHLMlpkepwCB56A0IOjOtW/bl6bHoevdRaZn"
        "ZAmkCJtS+yoAszKiIUN5/l25rp/nkmO2dE+3a2NbpMeh175tXwpBd1Zy4rlMj1OouB/wEjeT7kXlSYV+LJgtlGVTpDkol7fD"
        "cXQiM71E75ZAFksbyBBEISmCmeJArmvHs2faCAFAIjNtwHF0UC5vl02R5mC2UIbQjy1hOenuH0A8O/jIdYce4K792/3ObP8t"
        "AJCY2GyebHsAAPHJgY54fqBj0ZieYdRidWb7b+nav92/7tADHM8OPlLPcP4sf9Upf+L+NHCZnhE/PvnjNSIce+2sLD+I2HLz"
        "lG9x5gFs1J5fFhGzRYRjL7RP3Nua6Rnxk2xL2HVVqgr1GeFsWyTZlpmeEb994t5WEY69ICJmi/b8MoCN+RZn3nLztKQNXpDb"
        "zgti435BHH1cEIdHF8Tx2//6APP/6Aj4gjlE/y//G+I/jBWc7Omh1hgAAAAASUVORK5CYII="
    ),
    'gear_red': (
        "iVBORw0KGgoAAAANSUhEUgAAABYAAAAWCAYAAADEtGw7AAADWUlEQVR42rWVPW8cVRSGn3PvzI5XTgJCQhiFApRuRZMPihRO"
        "kQKt2bWlRF4K7LVkg0zlX5BIo5GSX+AOEZDYpPGiEHltvAVKk5Ik7rZDUBBhhIQgjrU7Mzv3UIzXnsgykEg53f0473nv+Xgv"
        "/IcpCIDWmktaay4V9/7NzHMgYWi00bAahma0FlCtz52j5N+i5N/S2ifnBbR4p+gzMq+4kChyxSD0ejkzY95AUbJhRsnExTtF"
        "nyOMD6LX5iZ1drmj9eZFiSLH7kQe2IlBEBBLJj4APTyJIqf15kWdXe5obW6yiJXTP2Bmb1Iaq2Pkrk41L0h3NdYwNJjsV7Is"
        "QSRF00TD0Eg7SnSqeQEjd3Mfe7OIlQNXKqogCNfZe/oEYycI/Ac6PX9ZoshhxhSli2oXO+4kipxOz18m8B9g7AR7T58gXFcQ"
        "KhWFQnVH+dKZ5lkwPxKULf1nq4i8TVCeRXW/EAJx/1tUf6N8YoW4n4H7QNZb28Wc563UaFgqFaXX86TdTrTW/AjRKtb7mFLw"
        "FoP+JkonB2aasXKNJP6dbLiGSlc2W99ro1GiUhnS64m029mxPan15po2PletLywePVtYzM+aa8f1fs64PncOsTFGfIaZgr9L"
        "2f+JQb8rG60prS1cwTNfAzB0i7L5zXdab24xVq7ST89AehLPCk5TNAtk485j0en5T7GlLxkOM0QsqKJsEgQ14niZ8+99xfYv"
        "f4M82udznrPvvsajn5cIgi+I402EGoigmuF5liz57HBAPM8iAmmqvKgpiu8JqvZg2A5T4b+OMYIb/oFvn2H+ZypceoY0O4Hx"
        "3sQ5RdO/ZOPO41dcvEYjf8LuhCfd1fil2q26EnByZwgg7Xb2ygbkUISiSHVm4RJiOxhjSZMBwj3ptBoMswpJsk6SrDPMKtJp"
        "NRDukSYDjLGI7ejMwiWiSI+IkOS1vcH4qdO4bIc4nZTO7fsahoZszyBSRajiBqJhaKRz+z5xOonLdhg/dRrlhoAeEaFcHrNr"
        "JIMNnF6VrdZDbYQliSKH+CVUfawt4ew7EkVOqyuBbLUe4vRq7pNdK2Id+8WMniRR5PTK/PsMzTbWs7j0Q1lv/TDSl+OE3jsC"
        "1uvJyOHgu0lcQKm0L/ruzxGzgzsFnxcYqpf7TP8BQz0G7Q2a+f8AAAAASUVORK5CYII="
    ),
}
STATUS_B64 = {
    'ok': (
        "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAAC+ElEQVR42q2UTWicVRSGn/fe75vJJJk2yUyCSIXWkgqmJBVF"
        "i6jF/+4k0RHqypWFVlFQonRhEUHq30KQgktBQTKiiBvBIraK0I20waZaLbUiGjJmmjR1JvP93OMijTZBXfVdHjjP4Zx731es"
        "ykxIBnDj8eeuKfZ1P2TB7jCzYQBJP8rp685C65OZ296YXd+jNYWpmt+x/YZJ83rSFaJrMSCElUHOgSAk2W/K7e0T3/3wGo/W"
        "89VeYSYQoyef7Vax9HHU331/vtAmpHmOhMxWhklmZrjY+6ivRHqh9bl12uPTY2+2wFBtquap1ThzavqzqL90X9b8MwFiJLFO"
        "AjAMSP1AdyG70D6ybWR0N/U6fqY+Y/HDw5PRYO8T2R+XEpwK/wUJQEKujODVSpPCYHm4ce6X1hf3vPOVRk8cHMKnp1zBD1ia"
        "A3L8iwS0LeOtao3F0OZg89NQKnQRkqxpeTzicOmE7+2qWpIbyDmEZy0rwrEQ2uzfeBcPlm9mc1xBOBeS3HxvVxWXTkTm2IWZ"
        "mYSApbCMARtcFwEjwtEMLcZ7xniqfzffts6wv/EBkRwCzMzMscsJthKCHKhjGY+Vb2XvxjtZDG1ieS7aMjcVN/FydYLZbJ7J"
        "+Y+4GJaJcJiZCEGCrdHqBczAIR7fsJMtxetILePw4jE2xxVerz5CURH7Gh/yczpPnyuREdaub3AWp1skTCaebtQ5VB3nQGWc"
        "zAI7u7ZwfXETLzXqHFv+iYrr+RtikuGcGZx1ChxFUjCjIM/p5Hf2zr3H953zvFgd54HeHby/8CXvLh1n4AoIgMxAkgJH1zx/"
        "SHNivLtkHQZ9mcODe5jNF3mmUSeWXznuP+YMij0hyZvk8YgAxqYPPB8NlQ9lc0sJTgWH6FhGQRGBgAEed/lTX1awJBoqF7K5"
        "pRdOjr7yqq9N1Xzl7nu/aZz/9fZooHs4tJMkYC6WV8AQwl0JMTMgjSo9hazZOrJt+9i+kRHc/5pW0koyrDOt7yuRrTft1YuR"
        "qxRsfwHQ35347gMGCQAAAABJRU5ErkJggg=="
    ),
    'warn': (
        "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACNUlEQVR42q2UzUuUURTGf899P4YZxzIUC4kCnRZtWrkM3Bi0"
        "KEQhqUVCQbsWLYb+iBBq0TIIbGegRC2C2kj9BdXOFIKIEiE/ZkZ9P+5p8U5oOtrGBy5c7r3POfc59z5HtGGGJAzg1/PzZ051"
        "xWPec9nMLgBIWnSOj7+byavTd7793M/R3oXZGwTXxoceBoHux5EbwMDMUQTyIEhS/yPP7emb+aVHky/J/3JlVgTjxaXKTrQ1"
        "X+p2V9KGJ8ksB4OsUeyH3QYQhwqiqmNn078rpeVxbn9qAchmCQC20trb8olgtLmeJaBIQlgGF+6BeVh8Bi7GzAws7ToZxlsb"
        "+fty9PUqgNMkeXO7Vi/3hKPN9SyRFEsSeAjKULsLFx9A3AOWogJxcz1Lyj3haHO7VtckuducGeyXs3rayL2ksF16UAjJGqx9"
        "gXyb/ZAUpo3cy1l9c2aw3znHRKUS9CWpGeD2HS8CytEBLknNKpWgzzkmnJlGsOIJO0McCcPMNOKQhsybUAeGebC0kNo5hwqu"
        "htzhmTxEVSgPgKLD5O3qxGxJTnZQnhXkdAPWPkPWAAX/3s6wgmtLoWQLiJudcpBvw4dbRZ0sB1c6KFNIsgXnPXOtVr4aRxLg"
        "dwvc/kfDT2D4cTHH7y2+jyOp1cpXvWfOdU8tr5jXdFQNnJll7U8CPoVSL5wbK0apt1iT2ia3LKoGzrymu6eWV46wiITfgbPX"
        "i/zfX4MrHWqR/5iWPaatHm3aY2sjx9XY/gAbWkuZrAy63wAAAABJRU5ErkJggg=="
    ),
    'bad': (
        "iVBORw0KGgoAAAANSUhEUgAAABIAAAASCAYAAABWzo5XAAACaklEQVR42q2UsWtUQRDGf/P2vX33cqY7DrFJcehfIFxhQAgR"
        "g6ASIWARFALpVAgEtZeA2kSIVgFRsTtQVJCEiCDEIn+DpLARCdeF5O7tvn1jsRdQ6xtYFnZ3vplv55sRRqYgAgqgV26fJpPr"
        "qE6jehYAkR+I7OL1g3x+/ft/H/n7QBcWDMPiPklyh8SciRHqGEmSuNfhF3X9nMbgqfR64cRXdATGpcUJCvMe27hE5SCEMMpP"
        "RkiKAMYYUgtuuMMgzLPz9jjeLiwYAIbFFrYxixs6yjIjywRjQHWEIxACeK/kucc2LG74hcZgDiCRXi8wLFbJiwhSBVuf64g2"
        "J8BXEUAEfIU2J6jPdYQqWNzQkRezDItV6fVCovOLbWCVytWUZVp3phhsrOHuLcUMVOMKAXdvicHGGnVnCsoypXI1sKrzi+0E"
        "LzdIsxYhKFmWyEGfdHeP6kKXcmUZSgelo1xZprrQJd3dQw76kGUJIShp1sLLjRThIqAoYAxyeET+6Bmysoybm0GcB8DPzWC3"
        "vmLXN8EYyFKoYzUQLqYgHbQWUEGJD1ITHZzHX5kBwH7cxr54Bbk9EUusqNYC0kkYk6Wg+0hyPuokVocQcCNq9uM2AO7aZbDZ"
        "v9QURRKFaj9F+QbcRIAQ0Mkm7u4S1XSXbOtrpAOozfBzM+ipJnbjJXJ0DEkSu0P5lpDpOyrfxxjB+1rbLarpLun3PfL1zfgn"
        "uSVf3yT9vkc13UXbLfC+xhih8n0yfRd77eqtB+TFY8pBFGRnCjnoI4dHkQJEQU420XaLZP8npMaRF5Zy8FA+vXkythYZX9OO"
        "bYyMa7D9AeXzZZUSJ5TAAAAAAElFTkSuQmCC"
    ),
}
BADGE_B64 = {
    'net': (
        "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"
        "gg=="
    ),
    'py': (
        "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"
    ),
    'ghidra': (
        "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"
    ),
    'build': (
        "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"
    ),
    'upx': (
        "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"
    ),
    'vc': (
        "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"
    ),
}
LOGO_B64 = {
    16: (
        "iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAC0UlEQVR42j3SS2hcdRTH8e/5//93pjOTmUkm6SSkmKpUEF3U"
        "lU8wERQpblwJIq4CunDb4sYHCC4UtSLStYhCl4KRggruikiFCl2koiCNWONMzLzuPO69/3O6mNGzOhwOHw4/jgD82DrTeHPS"
        "f/2QbFuNkkfIMDzgEAww5iVCftKFq7vSeu+l0a9d+bK5tfJ+Nti7ZfnjhRkOGGJs4CkwUlMUKIsQF1AQ4S6S6y+75jnfc/7t"
        "m5a9mJvlHqRvaq/6hj0VKraXp3a/S+xul9htKywgVhKxAitGYqeOJTbcP6Y7hZmCeQfuo7DqLq6edj9r5l5Lmu6L6qYbm7qz"
        "JO4+guvG3KUx+uMi0yONTwYBr+DqOP08afPM+iYHrRoXhsc80WpzsXMLB3x4ok2aeL7SlENRcYmX34YjHxwwQXlOajzdXKNb"
        "r9Do9Hm4vU5nlLLtKuwur9JoLHF9MuKTk1v85XJ2/7hJP0acgDiDc6GGaWTJlNpak1mMMM047QKj6YwiRh6qLXP57z955MY1"
        "vusdURYhRDPqCGulEpPVOtUkoHkkHYyYZhlRIBjsd4/4lJQfJgMiykpIMMBvhMorPYubB1ZYNx1LJcKJXElHKaKGitBygc+y"
        "AZdnPWrOEwWmmNTF/xsAVGApGo/OhI3OgJ4pJe8pRGgi/BSnXNEx6z6QYv//A0BQwUoIX+uYB0KZ7UqDGcb+ZMxMlRuifJD3"
        "mWIokMMckAXggZ4pO6HKu9U2XSu4lk8YFhlXbMIv5MTF8hQjwygWmDHPxwTRC+UVvi9Szk86WFRq4jhEqS4WZ0CGMcOIAgoK"
        "qN8KlQeXnDzWtVi8Me26kSqFCEOMgJABM4xsARRAJhQewpYrfyOXave2L8Wjb/ctO1tBcIAA/r+UFhcoEGXeOxFOEfZfYPVZ"
        "Afi4ds/6ng3fuq35jkEic0REF4ADA7P5PF+RcPV5W37n/PT3gzvfb3EKKbKcKgAAAABJRU5ErkJggg=="
    ),
    20: (
        "iVBORw0KGgoAAAANSUhEUgAAABQAAAAUCAYAAACNiR0NAAAD/0lEQVR42l2UTY9URRSGn1NVt7une7pnHGYGkM8QiRoVx4lK"
        "Is5CEyMsTHDFwsRE0Rj1D2BYgEsTTJSFG4kfBBWNUXTjhpUCMcpyJChgZASShvns7pnb996qOi66gYmVnLxVyclbb1VyHjkE"
        "5l2IH9S3bT8dO/tno58ANQAGUJDI3SWgq446Im56l5Q/Pbh8bRowAvB6dd2ec7F7/AbFqFdFACfCikYcQoIgPXPCKj/t963F"
        "tR63lTdOLDdPynv1Dds/LzrnL2veKIG3iLHAvAambJUawq8hJSqoQAUhAFEg9kxjhrotkhT7zD07bZIMHLgYs2cFfIK4qEiH"
        "KK/YhnxYGpPjvi0z0csuOyC7XU0uxEwKVBwiRkQA45CQijqPVsxC9Ds8qg5MpkpFhKNulGPDWzhbFRaLnKPlMU7VNtLWQFsj"
        "L9s6gyosRE+uShqjLAavLcIjDtQYRAqibjUJn5XGmShV6T6wmbHLV/ixvon7R8f5ojnDD3mbva7GATPEM8PDfJMuMp2nDFTL"
        "1K2TTpqJE8AKtKLykhvkicFhZseGSOaWeLKV49aPM7fYpoJwsraBpxsjZAbKWYcvtz0EFcefRZe3r14ijUFcBFGFOsJTrspK"
        "Ykl8wKlitt6LrqRolrOnVCfEiLWGeilhylpC7vk2W+TgzGWuFBk7kxrGKqQa2WHKPGpKhCKnUXbU6lVMlpPOLRFUmStybuUZ"
        "s+0OEgIlazly6xqvXvqDJR8YcQlBwVkMCqzDktcq1NeOIjGiWU5eeFa8J4QAIiCCyXK+bt7go9Dius9Zn5RIVVmOCgZcQZSa"
        "CL+ElH2LV5loN9k7spbJ+hDttEsIARFBAQtkAie6SzQpqImhrYrSGwYAZ0A9MGoM+8MAU7GMv9litrmEKFhrEKAA1ojhK9/h"
        "HzwNsXSI9OzuzqMJ/ZsXNHIgzPO9pow7R7Wc4JylANoaqQI/hZRjvs2ACDlKhDt1O6JDQBUCMIjhwXKFauJoiOFf7fL3Soo3"
        "ws8SOeZbIL3eAqUA/P9MnYAaEeaj5/DAGnaXG7RDwem8BXmgiee7mHJdAxURYt8s76vvJ9U+iZwAyxr1PlvitdIQZ/IOh7tz"
        "XPIZj0mZvyhQoCxCDngUD2QoOXoHFIBGwIyKuxBBXkwG9f18geeXr/Ob74IIv5OT0XviMkqK0u1r1jcOPeqoQaQuclHeqW18"
        "+FRon5/Hl5sx+GExxvVhlwDSZ+Ft/sV+qlUI0y5qN0miL7jalD1TtG4+Vx6+fEvDHhEqHiSAROmpX1XF7b0gQZAIIiJmvbh8"
        "0lTe+mS5eUr6pI+HhjZPnsvTNxfUT4hgFQQFATH9hLH/8VF6qkpsiJ2etNWPj3RmzgL2P0uKDo9ulKuPAAAAAElFTkSuQmCC"
    ),
    24: (
        "iVBORw0KGgoAAAANSUhEUgAAABgAAAAYCAYAAADgdz34AAAFTUlEQVR42m2VXahcVxXHf2vvPWfmzMy9M5Obm5uGJinlVqVE"
        "IX4UfGjFDxREaaB9aCnYB2lpQcSKou1LX2x98SEoilT8AAOCaS3WD2rIi6TWPIjaYtuATSW9mqT3Zu7k3pk5c772Xj6cMzdT"
        "ccHinM0+a63zX+u/1hIqEUC/0z56/C+anhgS3hsIYuo7waAABP6PVFcY6Rt78ZhpvvDk+NKfWXBsHBLu7aw99UqYPbalPi7n"
        "NoBDKFBQcMLCzY33+dMirGCLYy5+5rkjd35VXj9dWAG9t7P21J988sSG5g1FQ20THOiOeh1gtIvoVIM2FA2KelUVUK01gBYo"
        "23i7pf6Ol65fPvhmOf2NfKt95IOndOf8WyEzMcYoiAEssB08d7o2X2kMeDzb4rp6JhroiSUWYaQBAXyNTKuU6Az1h6Xh7rG9"
        "T5tXJbtnqL4RYURBHBBUmYTAI9GAP0SHGFJy0ecYhROuy/fiA3QwGMABTRUcYKog0kJkhOc1svvNKJTrBRVcB0w1sIzhx/FB"
        "TkYr5AcGnComfMLG/Ki1xqn2zVzwORsh57A4vub67ISSNIQ5AnJVGXvPVP26mxfbAqkGPmJb/LC1xro3lOuH2Wo3ePjtNp/r"
        "rbDcW+Klzas8k42IEb4gHR6ULoN9HX4xvsabecrQKIebLbrWorniKhpWkb3CN6IVbifi2s0DOu0WKxc3OBEvU6z2GW+P+XuZ"
        "8mDU4+NRl48uDdhIE26xytlb38/bZYa2W1zxBV/f+Cd5KHHcgMUtpsExGkwOreBKT7m9S5mkuKM3IdfHzGYzHmj16ahgWxE2"
        "brI/MlyeTVGEI6v7OTva4qG33mCjzPlYoyNOFbEIqQY+7FocdA12NocsH1ih0W7Sec9RQpKSZDnWWkpV3ikLXOq5qdOiL5a7"
        "uvuYzjK+fPUiz+8OKVD61hEAZ+pOsQifd12MKp3+EnHTQVlSpAWTzW3yvKDUQFkXs8w8o50xUbfNRpHx3dFlnhsPWXKOHCXX"
        "ujlBCCjLYvAorPbpLneg9OA9CBSRZZYkIMK8XipCOp3x5O5VzoaELATWGg0S1T021bRXpJ4yX8o2+f6VKR94J+Izg1U+uX+N"
        "dDwly/Lqa2FvIsUI/yDnj2VCbISGsXvOF2VOU0rgbmlzfxHTx9DbmjAczqAowBgw8i7DSIRniymhRuVR5u4Xg5j54DHAy5py"
        "TjK61rGM4FTBWowYGlSOSpQehp+VY877lLZUPxeAgLxrAApoVWOpcjZR5elixG/DlLUoott0LDccGYH/hJzLvqCh8HM/5ifF"
        "Lk2RPee+RhFqHFrz34mgqlUGdoPnoajPI/E+UqAvltIpf0unFN5zVeB3OuMFn9AxgkcpgQKlRPFzJAtj3c2DZcCSMXyzta9y"
        "TODFYsqFPOV93nBOCl7UGUlQuiIUdd1KlALqcxVkoQbqAlWjjbTkgajPrbbFq2XCt9NtzhRT7pImZ4ALWrCEIRYhBULtrNgL"
        "UJ29VCi0XoauZ+yl4JWBWB6OepxMhzydDpmqsiqGv1b7jDZCusCSUOd8jqKs61DnX62IxmoumeOm9XwXq4fE8UQ61MfSTXKB"
        "rgiz2hAgQUlrzfYU8hqBlyr3ApqjOsDKunWnxQB3t9d+cC5MH70WijAQq1qRCqMVfaWm8aKEBSTzooYqoHbF2jtM+/Tvk0fv"
        "swrmjds+e+b87pWDHj6UiJpqQCAqNzTwPyo3VKnUInJAnDluWr/8aWf1i93k2XxvtBjg8c6RT71Cet9E/W1Vd1SdI/WUCHNk"
        "1aInVMtEAVWEjtp/3W6bvzo5+fevy6of5L+tc8UTz2nwBgAAAABJRU5ErkJggg=="
    ),
    32: (
        "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAIPElEQVR42nWXWYxmRRXHf6eq7rd3T2+z9izADPsqYMCRIDwQ"
        "IURNkHnQmBgkqI8+SUBDD6CROPLACz4QBDQGExglkABGfRBFGQQxAQIMI8tIM8NML/N1f9tdqo4P9349t3vgJpWqW7fu+Z/9"
        "nBKKZwbM3RAihAdGdl75Zoh3d0nXC6iCDAeAFv8M3+XkFlJ6NxA8xjZVF86SxoEfdLf+Xfhrln8iDM+zB+wT4H8xsn33AZ/c"
        "826Ir1oUX01V8wMl4sNZOfXRz/hmgXVikzOk+u9Lbe2emeUPnxsKLMPF7c3pb72g/YffCINKrIqFsFYyg6AoiSo1kVOAdLV2"
        "yvsSwFgRzpMqX5TmDx/ofbRvBowA3D+y48r92fILB0I/qiOZBadrpI4Q+hqIEM42Fd4JMY6cCVvo0wMi+VrXMFFoxncIcolp"
        "mBtt46Z7Ox/9wSh77Iu+f9/rGkcNxEsJfPhjBWgHz4QYflvfzDmmQqxKFaGG0FclQ6khiOYEbIn5knZsC8Nboa8v+/i+4+we"
        "sRMj3Sv+Enozn2gmEWIK50EABxiFRQ1c55r8rjnNJrHcNZinKUKG0lHl87bGLZV1vOoHUGgjFHQotFLSqGT5Ymqplrxm3ia9"
        "qq3B2eLMkOsKQqK5ve+qTfF4fTM7U+GptENbPYkqO0zEvtp6nmtu5WjI6GjAIUxh2CIWI7kQw/AZ0nYQ2ur1MMmXTC8wlaII"
        "6PCQRVgMnm3ieLI5zZ1ujMRAb+cWnkqWmRbHHdVJ9lc3873qOC9lA55Mltkijj6Bu9wE10mduSzFAg4hQohEcJKjxKgkQTc6"
        "IaisCZlEAze5FvvqG9ighmPq2XjlZbzRXuRqrfCd5iTTUZXuaIPOfJuHkxOAckwzrpc6N1BjSyWiU4/4c+cEc5rRU80DH2XU"
        "RYwaS0C905KvWGCgynmmwq8am0m9p+2EsTN3kqUZWw59zO31SVLr6GzbQOPYCfany/wz63GRqXK2rfL9+gRxgLPU8tDUJj4Y"
        "HfDmcpuDkdKODOe3RomDZ9/HH5J5FVfKXliERAPXuAYuKEvOsO7s08gWl1DvodOjU41obNtEfGSObqfHmI14pLGFM03E+moV"
        "GW2ixvDg/CxH5//Hvaefw2lbJrkRA5UKL8wf49b3D3EsTbmgUhUXch8p4lSpinCtraPW0Dr3dHoHP6A6vZHk+AKIMHL6VsLi"
        "EjbLSCPH1eoQEXrB07FCUwMmU745OkUalKzdwY018JFw73tv89OPP8Aaw5hz+BBwJ7McJEE5wzguNlX6VvDvvE+lVqUxOYbv"
        "9nCXnovpDxiEQIwgqvSAEAKZ95CkjDQbqAbGxRbJwPL7o0f4TX+R5xfnGHcRqShBc+M7DbkPWIQunsttjSkTMT+IGR1t0do4"
        "AXML2KlxsqVllmaPkyVpHu+qpCHgNRAUsl6fZq1KvV4rIl54Y9Dhjk8+5FjIWB9FDFTz6pbnBnHDpKOaM3FzNIr1nsZYK5c8"
        "TjFGoNMl6/SxlYg4y0iSFK9aroAgwvHFNtU45mXreScd8PjyHCnKlHP0SueHjxtmq4AyJpa3spiLJ8eZXj+Vc+UsZClBA9Qq"
        "9OOY/iAGkVWEKGrBOjE8s7TATLpARYTIGCoixKqnVFUAp3n+QQCP8qNkjl8v9DhjeZYdrsKF9RY3Tm9nVIVuPyYjV5cYkzO4"
        "Jod0CTwd+kxalxcwAjEghZuvZdrl5SPPwwG4xFTZnCibkoQdBDb3hFiOM9/p4/txDm5PBc+AMTE867scDAktY4jRAlLRT+0g"
        "8lS90kh4YFoce6MxLpQqHQJ9DXQ/WSAzgrUGJQcfkjPFf1WEJQ08kXWpiBCKE3pqb7Dq3WWlDw74U+jxSjLg23aEPaZJC0Ol"
        "GoEqiVeMKIaT9k9QKgge5e5kgcMhoy5CUsgcVmZWmCo/ZlgzQ9FItIom4yfZAi9rzKbIMRJZxioRzcJl++qZDxn/zWJO+IyA"
        "MpMu8KrGNETyOC98aghcblL0pNbVSMmaQ067qnzDjfLV+ggS5a1FhjJRrTBHxptpn8M+l7FmDDPpAq+EmFEMaUliXxqhRL9c"
        "/Zwp3hUQEZaD5wpX47HWZjJVBhpoiiHCMusTjmQZY2JZJPCodplNPcfU05Lc6YbAGVqA6woDQ3BdHQWrG88YuK0yhqAkBMbE"
        "8baPeTRpE9LAV6hxgIQ/ap+PyKghVEo2HwJmq5g4aY41JggugNUiTjsEzncVro8aWARF2DuY47G4TVcDt5oWD9LhXxpTRahj"
        "CEBSBFpAVgCzEiNlLZSlD4h1VZXFYToeaOC2yjrGTcQzyRJ7B/O85RMmxDIhlv3ap4/SKmJgsCbUFF0BWwuuJdtr3uKrFVl0"
        "u6Ty0rjYMBtSc4Gtca1t8N3eUR5J2tRUGBdLAJZRbNEhJwUZUzCiJfWGktNlK1Fw8pIh+b4ZFSvbNHpRdNeu6teOLP3j+Wz5"
        "c1fYWjih3r7uYyYk7/pV82Rjiooppa657DurGSjH/klwLa5rA1R22+aRu83WS4wcOhRfrPUfX2Tr8resy7sh9ZPi8CjZMD9I"
        "LlVK3v+nKCmsjGRlrasdr/i31HOEDiHsMlW53NRmru7857jdA/aXafvgTdFkz4t8eU4zM8gb1QCimucJVcnnUAz/KWtf3pd8"
        "VlCPapL7hDnL1MwXpHn/g93Z+24Gu+pyemdr+9df8/2975Fc0FZPxmdcTpVTqtpaJyvvG4R1WLab6P3LTONnP+8cfqgonn6F"
        "zpAJ5bzWPa3+De/q4JpUdT2Eoe+Ur+My7KRWmDNoKF3Nh2ZXxERiFraqe/EWs+HZczqvzg3BAf4PTJ51eaT00V4AAAAASUVO"
        "RK5CYII="
    ),
    40: (
        "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"
        "AAAASUVORK5CYII="
    ),
    48: (
        "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"
    ),
    64: (
        "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"
        "SUVORK5CYII="
    ),
    96: (
        "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"
    ),
    128: (
        "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"
        "vLMo6lAb4P8FtDAzOCJQYYcAAAAASUVORK5CYII="
    ),
}
ICO_B64 = (
    "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"
)


# =========================================================================== #
# GUI  (tkinter - ships with Python, nothing to install)
# =========================================================================== #
import platform
import queue

try:
    import tkinter as tk
    from tkinter import filedialog, font as tkfont, ttk
except ImportError:  # pragma: no cover
    tk = None

C = {
    "bg": "#070304", "side": "#0a0405", "panel": "#0f0709", "card": "#120a0c", "card2": "#190d11",
    "editor": "#0b0506", "border": "#31121a", "border_hi": "#5e1522", "text": "#f4efef", "muted": "#a79a9e",
    "dim": "#6e6165", "red": "#e5192d", "red_hi": "#ff3b4e", "red_lo": "#5e0d19", "red_bg": "#3b0b14",
    "ok": "#2fd47b", "ok_bg": "#0d2418", "warn": "#f5a524", "warn_bg": "#2a1c07", "bad": "#ff4d5e",
}
PAGES = (("home", "Home", "home"), ("scan", "Scan PC", "scan"), ("tools", "Tools", "tools"),
         ("decompile", "Decompile", "code"), ("rebuild", "Rebuild", "gear"), ("settings", "Settings", "sliders"),
         ("logs", "Logs", "doc"), ("about", "About", "info"))
KIND_TEXT = {
    "pyinstaller": "Rebuild as a Windows exe with PyInstaller",
    "dotnet": "Rebuild with `dotnet build` (Release)",
    "native": "Rebuild with the Zig C compiler (best-effort: decompiled C is pseudocode)",
}
SCOPES = {
    "Main script only (recommended)": "entry",
    "Main script + the program's own modules": "app",
    "Everything, including libraries": "all",
}
MAX_EDIT_BYTES = 8 * 1024 * 1024
SHORT = {"dotnet": "SDK", "ilspycmd": "ILSpy", "pycdc": "pycdc", "decompyle3": "decompyle3", "uncompyle6": "uncompyle6",
         "jdk": "JDK", "ghidra": "Ghidra", "zig": "Zig", "pyinstaller": "PyInstaller", "upx": "UPX", "vcredist": "VC++"}
# (id, title, subtitle, components, badge)
HOME_ROWS = [
    ("net", ".NET / ILSpy", "Decompile .NET executables (C#)", ["dotnet", "ilspycmd"], "net"),
    ("py", "Python / decompilers", "pycdc / decompyle3 / uncompyle6", ["pycdc", "decompyle3", "uncompyle6"], "py"),
    ("ghidra", "Ghidra", "Decompile native executables (C)", ["jdk", "ghidra"], "ghidra"),
    ("build", "Build tools", "Zig compiler / PyInstaller (rebuild)", ["zig", "pyinstaller"], "build"),
    ("upx", "UPX", "Unpack UPX-packed executables", ["upx"], "upx"),
]
LOG_FILE = TOOLS.parent / "logs" / "dollardecompile.log"


def install_plan(keys: list[str]) -> list[str]:
    plan: list[str] = []

    def visit(k: str) -> None:
        if k in plan or is_installed(k):
            return
        for d in REG[k].deps:
            visit(d)
        plan.append(k)

    for k in keys:
        visit(k)
    return plan


def shorten(text: str, n: int) -> str:
    return text if len(text) <= n else text[: n // 2 - 1] + "..." + text[-(n - n // 2 - 2):]


def fmt_time(iso: str) -> str:
    try:
        return datetime.fromisoformat(iso).astimezone().strftime("%d %b %Y  %H:%M")
    except (ValueError, OSError):
        return "never"


class Btn(tk.Label if tk else object):  # type: ignore[misc]
    """Flat label-button that looks the same on every OS."""
    STYLES = {"primary": ("red", "#ffffff", "red_hi", None), "outline": ("panel", "text", "card2", "border_hi"),
              "ghost": ("card", "muted", "card2", None), "dark": ("card2", "text", "red_bg", None)}

    def __init__(self, parent, text, command, kind="primary", font=None, padx=18, pady=8, image=None):
        bg, fg, hover, edge = self.STYLES[kind]
        self._bg, self._fg, self._hover = C[bg], C.get(fg, fg), C[hover]
        self._dis_bg = C["red_lo"] if kind == "primary" else self._bg
        kw = {"image": image, "compound": "left"} if image is not None else {}
        super().__init__(parent, text=text, bg=self._bg, fg=self._fg, font=font, padx=padx, pady=pady, cursor="hand2",
                         highlightthickness=1 if edge else 0, highlightbackground=C[edge] if edge else self._bg, **kw)
        self.command, self.enabled = command, True
        self.bind("<Enter>", lambda e: self.enabled and self.config(bg=self._hover))
        self.bind("<Leave>", lambda e: self.config(bg=self._bg if self.enabled else self._dis_bg))
        self.bind("<ButtonRelease-1>", self._click)

    def _click(self, e) -> None:
        if self.enabled and 0 <= e.x < self.winfo_width() and 0 <= e.y < self.winfo_height():
            self.command()

    def set_enabled(self, on: bool) -> None:
        self.enabled = on
        try:
            self.config(fg=self._fg if on else C["dim"], bg=self._bg if on else self._dis_bg, cursor="hand2" if on else "arrow")
        except tk.TclError:  # the button was destroyed by a page refresh
            pass


class ScrollFrame(tk.Frame if tk else object):  # type: ignore[misc]
    """A frame that scrolls vertically when its content is taller than the window."""

    def __init__(self, parent, bg):
        super().__init__(parent, bg=bg)
        self.canvas = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0)
        self.vsb = ttk.Scrollbar(self, orient="vertical", style="Dark.Vertical.TScrollbar", command=self.canvas.yview)
        self.inner = tk.Frame(self.canvas, bg=bg)
        self.win = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.inner.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", lambda e: self.canvas.itemconfigure(self.win, width=e.width))

    def scroll(self, direction: int) -> None:
        if self.inner.winfo_reqheight() > self.canvas.winfo_height():
            self.canvas.yview_scroll(direction, "units")


class Hero(tk.Canvas if tk else object):  # type: ignore[misc]
    """The banner at the top of the Home page."""

    def __init__(self, parent, app):
        super().__init__(parent, height=150, bg=C["panel"], highlightthickness=1, highlightbackground=C["border_hi"])
        self.app = app
        self.bind("<Configure>", lambda e: self.draw())

    def draw(self) -> None:
        self.delete("all")
        w, h, a = self.winfo_width(), 150, self.app
        for i, col in enumerate(("#1c0a10", "#200b12", "#27101a")):  # mountains on the right
            k = i * 0.04
            pts = [w * (0.52 + k), h, w * (0.62 + k), h * (0.50 - i * .05), w * (0.69 + k), h * 0.64, w * (0.80 + k), h * (0.18 + i * .06),
                   w * (0.90 + k), h * 0.62, w, h * 0.46, w, h]
            self.create_polygon(pts, fill=col, outline=C["red_lo"] if i == 2 else "")
        for r, col in ((92, "#150709"), (74, "#1d080d"), (58, "#2a0a12"), (44, "#3b0b14")):  # glow behind the logo
            self.create_oval(100 - r, 75 - r, 100 + r, 75 + r, fill=col, outline="")
        self.create_image(100, 75, image=a.logo(128))
        x = 210
        self.create_text(x, 56, text="$", anchor="w", fill=C["red"], font=a.f_hero)
        self.create_text(x + a.f_hero.measure("$") + 2, 56, text="Decompile", anchor="w", fill=C["text"], font=a.f_hero)
        self.create_text(x + 2, 108, anchor="w", fill=C["muted"], font=a.f_ui,
                         text="Smart Decompiler   \u2022   Auto Scan   \u2022   Real Paths   \u2022   Safe Extraction")
        if w > 980:
            self.create_text(w - 40, 62, anchor="e", fill=C["muted"], font=a.f_quote, justify="right",
                             text="\u201cNot just a tool,\nit\u2019s your reverse engineering\ncompanion.\u201d")
            self.create_text(w - 40, 122, anchor="e", fill=C["dim"], font=a.f_small, text="\u2013 Peakk")


class App(tk.Tk if tk else object):  # type: ignore[misc]
    def __init__(self):
        if IS_WIN:
            try:
                import ctypes
                ctypes.windll.shcore.SetProcessDpiAwareness(1)
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("DollarDecompile.App")
            except Exception:  # noqa: BLE001
                pass
        super().__init__()
        self.title(APP_NAME)
        self.geometry("1320x860")
        self.minsize(1280, 700)
        self.configure(bg=C["bg"])
        remove_legacy_venvs()
        self.q: queue.Queue = queue.Queue()
        self.busy = False
        self.actions: list[Btn] = []
        self.project: dict | None = None
        self.cur_file: Path | None = None
        self.cur_enc = "utf-8"
        self.dirty = False
        self._lines = 0
        self._pb_indeterminate = False
        self._auto_out = ""
        self.statuses: dict | None = None
        self.last_scan: ScanResult | None = None
        self.activity: deque = deque(maxlen=40)
        self.log_views: list = []
        self.scrollers: dict[str, ScrollFrame] = {}
        self.current_page = "home"
        self.last_build: Path | None = None
        self._imgs: dict = {}
        self._logf = self._open_log_file()
        set_log_sink(lambda lvl, m: self.q.put(("log", lvl, m)))
        set_progress_sink(lambda f, t: self.q.put(("prog", f, t)))
        self._fonts()
        self._icon()
        self._ttk_style()
        self._build()
        self.show("home")
        self.bind_all("<Control-s>", lambda e: self.save_file())
        self.bind_all("<MouseWheel>", self._wheel)
        self.bind_all("<Button-4>", self._wheel)
        self.bind_all("<Button-5>", self._wheel)
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.after(60, self.pump)
        self.after(150, self._dark_titlebar)
        if is_store_python():
            say(f"Microsoft Store Python detected: data is kept in {TOOLS.parent} (outside the Store sandbox).")
        say("Ready. Pick an .exe on the Decompile page - missing decompilers are downloaded for you.")
        self.refresh_tools()
        if get_setting("auto_scan", True):
            self.after(700, self.auto_scan)

    # ------------------------------------------------------------------ images / fonts / style
    def pic(self, group: str, name):
        key = (group, name)
        if key not in self._imgs:
            data = {"nav": NAV_B64, "white": WHITE_B64, "misc": MISC_B64, "status": STATUS_B64, "badge": BADGE_B64,
                    "logo": LOGO_B64}[group][name]
            self._imgs[key] = tk.PhotoImage(data=data)
        return self._imgs[key]

    def logo(self, size: int):
        return self.pic("logo", size)

    def _icon(self) -> None:
        """Your icon.ico: window + taskbar icon (the .ico is embedded in this file)."""
        try:
            ico = TOOLS.parent / "icon.ico"
            ico.parent.mkdir(parents=True, exist_ok=True)
            ico.write_bytes(base64.b64decode(ICO_B64))
            if IS_WIN:
                self.iconbitmap(default=str(ico))
                return
        except (OSError, tk.TclError):
            pass
        try:
            self.iconphoto(True, *(self.logo(n) for n in (64, 48, 32, 16)))
        except tk.TclError:
            pass

    def _dark_titlebar(self) -> None:
        if not IS_WIN:
            return
        try:
            import ctypes
            self.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(self.winfo_id()) or self.winfo_id()
            dwm = ctypes.windll.dwmapi

            def rgb(h: str) -> int:
                return int(h[1:3], 16) | (int(h[3:5], 16) << 8) | (int(h[5:7], 16) << 16)
            for attr in (20, 19):  # dark title bar (new / old attribute id)
                dwm.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(ctypes.c_int(1)), 4)
            for attr, col in ((35, C["bg"]), (34, C["red_lo"]), (36, C["text"])):  # Windows 11: caption, border, text
                dwm.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(ctypes.c_int(rgb(col))), 4)
        except Exception:  # noqa: BLE001 - purely cosmetic
            pass

    def _fonts(self) -> None:
        fams = set(tkfont.families())
        pick = lambda *n, d: next((x for x in n if x in fams), d)  # noqa: E731
        ui = pick("Segoe UI", "SF Pro Text", "Helvetica Neue", "DejaVu Sans", d="TkDefaultFont")
        mono = pick("Cascadia Mono", "Consolas", "Menlo", "DejaVu Sans Mono", "Courier New", d="TkFixedFont")
        self.f_ui = tkfont.Font(family=ui, size=10)
        self.f_bold = tkfont.Font(family=ui, size=10, weight="bold")
        self.f_h1 = tkfont.Font(family=ui, size=17, weight="bold")
        self.f_h2 = tkfont.Font(family=ui, size=12, weight="bold")
        self.f_small = tkfont.Font(family=ui, size=9)
        self.f_tiny = tkfont.Font(family=ui, size=8, weight="bold")
        self.f_mono = tkfont.Font(family=mono, size=10)
        self.f_logo = tkfont.Font(family=ui, size=22, weight="bold")
        self.f_hero = tkfont.Font(family=ui, size=36, weight="bold")
        self.f_quote = tkfont.Font(family=ui, size=11, slant="italic")
        self.f_nav = tkfont.Font(family=ui, size=11)

    def _ttk_style(self) -> None:
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure("Red.Horizontal.TProgressbar", troughcolor=C["card2"], background=C["red"], bordercolor=C["card2"],
                     lightcolor=C["red"], darkcolor=C["red"], thickness=8)
        for o in ("Vertical", "Horizontal"):
            st.configure(f"Dark.{o}.TScrollbar", background=C["card2"], troughcolor=C["bg"], bordercolor=C["bg"],
                         arrowcolor=C["muted"], lightcolor=C["card2"], darkcolor=C["card2"], gripcount=0)
            st.map(f"Dark.{o}.TScrollbar", background=[("active", C["red_lo"]), ("pressed", C["red"])])
        st.configure("Dark.Treeview", background=C["card"], fieldbackground=C["card"], foreground=C["text"], borderwidth=0,
                     rowheight=24, font=self.f_ui)
        st.map("Dark.Treeview", background=[("selected", C["red_lo"])], foreground=[("selected", "#ffffff")])
        st.layout("Dark.Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
        st.configure("Dark.TCombobox", fieldbackground=C["card2"], background=C["card2"], foreground=C["text"],
                     arrowcolor=C["red"], bordercolor=C["border"], lightcolor=C["card2"], darkcolor=C["card2"],
                     selectbackground=C["card2"], selectforeground=C["text"], padding=6)
        st.map("Dark.TCombobox", fieldbackground=[("readonly", C["card2"])], foreground=[("readonly", C["text"])],
               selectbackground=[("readonly", C["card2"])], selectforeground=[("readonly", C["text"])])
        for opt, val in (("background", C["card2"]), ("foreground", C["text"]), ("selectBackground", C["red_lo"]),
                         ("selectForeground", "#ffffff")):
            self.option_add(f"*TCombobox*Listbox.{opt}", val)
        self.option_add("*TCombobox*Listbox.font", self.f_ui)

    # ------------------------------------------------------------------ small widget helpers
    def lbl(self, parent, text="", kind="text", **kw):
        fonts = {"text": (self.f_ui, C["text"]), "muted": (self.f_small, C["muted"]), "h1": (self.f_h1, C["text"]),
                 "h2": (self.f_h2, C["text"]), "bold": (self.f_bold, C["text"]), "key": (self.f_tiny, C["dim"])}
        font, fg = fonts[kind]
        font = kw.pop("font", font)
        bg = kw.pop("bg", parent.cget("bg"))
        return tk.Label(parent, text=text, font=font, fg=kw.pop("fg", fg), bg=bg, **kw)

    def entry(self, parent, var):
        return tk.Entry(parent, textvariable=var, font=self.f_ui, bg=C["card2"], fg=C["text"], insertbackground=C["red"],
                        relief="flat", highlightthickness=1, highlightbackground=C["border"], highlightcolor=C["red"],
                        selectbackground=C["red_lo"], selectforeground="#ffffff")

    def card(self, parent, bg=None):
        return tk.Frame(parent, bg=bg or C["card"], highlightthickness=1, highlightbackground=C["border"])

    def btn(self, parent, text, cmd, kind="primary", action=False, icon=None, **kw):
        b = Btn(parent, text, cmd, kind, font=self.f_bold, image=icon, **kw)
        if action:
            self.actions.append(b)
            if self.busy:
                b.set_enabled(False)
        return b

    def check(self, parent, text, var, command=None):
        return tk.Checkbutton(parent, text=text, variable=var, command=command, font=self.f_ui, fg=C["text"],
                              bg=parent.cget("bg"), activebackground=parent.cget("bg"), activeforeground=C["text"],
                              selectcolor=C["card2"], highlightthickness=0, bd=0)

    def scrollbar(self, parent, orient, target):
        return ttk.Scrollbar(parent, orient=orient, style=f"Dark.{orient.capitalize()}.TScrollbar", command=target)

    def pill(self, parent, text: str, fg: str, tint: str):
        f = self.f_tiny
        w, h = f.measure(text) + 26, f.metrics("linespace") + 10
        cv = tk.Canvas(parent, width=w, height=h, bg=parent.cget("bg"), highlightthickness=0)
        r = h // 2
        cv.create_polygon([r, 0, w - r, 0, w, 0, w, r, w, h, w - r, h, r, h, 0, h, 0, r, 0, 0], smooth=True, fill=tint, outline=fg)
        cv.create_text(w // 2, h // 2, text=text, fill=fg, font=f)
        return cv

    def make_log(self, parent, height: int):
        wrap = tk.Frame(parent, bg=C["editor"], highlightthickness=1, highlightbackground=C["border"])
        t = tk.Text(wrap, bg=C["editor"], fg=C["text"], font=self.f_mono, relief="flat", wrap="word", state="disabled",
                    padx=10, pady=6, height=height, selectbackground=C["red_lo"], highlightthickness=0, insertbackground=C["red"])
        sb = self.scrollbar(wrap, "vertical", t.yview)
        t.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        t.pack(side="left", fill="both", expand=True)
        for tag, col in (("info", C["text"]), ("ok", C["ok"]), ("warn", C["warn"]), ("bad", C["red_hi"]), ("out", C["muted"])):
            t.tag_configure(tag, foreground=col)
        self.log_views.append(t)
        return wrap

    def page_title(self, parent, title: str, sub: str = "", wrap: int = 900):
        row = tk.Frame(parent, bg=C["bg"])
        self.lbl(row, title, "h1").pack(anchor="w")
        if sub:
            self.lbl(row, sub, "muted", justify="left", wraplength=wrap).pack(anchor="w", pady=(2, 0))
        return row

    # ------------------------------------------------------------------ layout
    def _build(self) -> None:
        head = tk.Frame(self, bg=C["bg"])
        head.pack(fill="x", padx=18, pady=(10, 8))
        tk.Label(head, image=self.logo(48), bg=C["bg"]).pack(side="left", padx=(0, 14))
        tb = tk.Frame(head, bg=C["bg"])
        tb.pack(side="left")
        row = tk.Frame(tb, bg=C["bg"])
        row.pack(anchor="w")
        tk.Label(row, text="$", font=self.f_logo, fg=C["red"], bg=C["bg"]).pack(side="left")
        tk.Label(row, text="Decompile", font=self.f_logo, fg=C["text"], bg=C["bg"]).pack(side="left")
        tk.Label(tb, text="R E V E R S E   \u2022   E D I T   \u2022   R E B U I L D", font=self.f_tiny, fg=C["red"],
                 bg=C["bg"]).pack(anchor="w")
        self.pill(head, f"v{VERSION}", C["red"], C["bg"]).pack(side="right", padx=(0, 4))
        tk.Label(head, text="Turn  Executables  Into  Possibilities", font=self.f_quote, fg=C["muted"],
                 bg=C["bg"]).pack(side="right", padx=40)
        tk.Frame(self, bg=C["red"], height=2).pack(fill="x")

        foot = tk.Frame(self, bg=C["side"])
        foot.pack(fill="x", side="bottom")
        tk.Frame(foot, bg=C["border"], height=1).pack(fill="x")
        fr = tk.Frame(foot, bg=C["side"])
        fr.pack(fill="x", padx=14, pady=5)
        tk.Label(fr, image=self.logo(20), bg=C["side"]).pack(side="left")
        tk.Label(fr, text=APP_NAME, font=self.f_bold, fg=C["text"], bg=C["side"]).pack(side="left", padx=(6, 6))
        tk.Label(fr, text=f"v{VERSION}", font=self.f_small, fg=C["muted"], bg=C["side"]).pack(side="left")
        tk.Label(fr, text="Built for Developers", font=self.f_small, fg=C["red_hi"], bg=C["side"]).pack(side="right")
        tk.Label(fr, image=self.pic("misc", "heart"), bg=C["side"]).pack(side="right", padx=(0, 6))
        mid = tk.Frame(fr, bg=C["side"])
        mid.pack(expand=True)
        self.f_idle = tk.Frame(mid, bg=C["side"])
        self.f_idle.pack()
        self.dot = tk.Label(self.f_idle, text="\u25cf", font=self.f_small, fg=C["muted"], bg=C["side"])
        self.dot.pack(side="left", padx=(0, 6))
        self.status = tk.Label(self.f_idle, text="Starting...", font=self.f_small, fg=C["text"], bg=C["side"])
        self.status.pack(side="left")
        self.f_busy = tk.Frame(mid, bg=C["side"])
        self.busy_lbl = tk.Label(self.f_busy, text="", font=self.f_small, fg=C["text"], bg=C["side"], width=26, anchor="e")
        self.busy_lbl.pack(side="left")
        self.pb = ttk.Progressbar(self.f_busy, style="Red.Horizontal.TProgressbar", length=260, maximum=100)
        self.pb.pack(side="left", padx=10)
        self.prog_lbl = tk.Label(self.f_busy, text="", font=self.f_small, fg=C["muted"], bg=C["side"], width=26, anchor="w")
        self.prog_lbl.pack(side="left")
        self.stop_btn = self.btn(self.f_busy, "Stop", self.on_stop, "dark", padx=12, pady=2)
        self.stop_btn.pack(side="left", padx=(8, 0))

        body = tk.Frame(self, bg=C["bg"])
        body.pack(fill="both", expand=True)
        side = tk.Frame(body, bg=C["side"], width=196)
        side.pack(side="left", fill="y")
        side.pack_propagate(False)
        tk.Frame(body, bg=C["border"], width=1).pack(side="left", fill="y")
        self.nav: dict[str, tuple] = {}
        for i, (key, text, icon) in enumerate(PAGES):
            row = tk.Frame(side, bg=C["side"], cursor="hand2")
            row.pack(fill="x", padx=10, pady=(16 if i == 0 else 3, 0))
            bar = tk.Frame(row, bg=C["side"], width=3)
            bar.pack(side="left", fill="y")
            lab = tk.Label(row, text="  " + text, image=self.pic("nav", icon), compound="left", font=self.f_nav,
                           fg=C["muted"], bg=C["side"], anchor="w", padx=10, pady=10)
            lab.pack(side="left", fill="x", expand=True)
            for w in (row, lab, bar):
                w.bind("<Button-1>", lambda e, k=key: self.show(k))
            self.nav[key] = (row, bar, lab)
        holder = tk.Frame(body, bg=C["bg"])
        holder.pack(side="left", fill="both", expand=True)
        holder.grid_rowconfigure(0, weight=1)
        holder.grid_columnconfigure(0, weight=1)
        self.pages = {"home": self._page_home(holder), "scan": self._page_scan(holder), "tools": self._page_tools(holder),
                      "decompile": self._page_decompile(holder), "rebuild": self._page_rebuild(holder),
                      "settings": self._page_settings(holder), "logs": self._page_logs(holder), "about": self._page_about(holder)}
        for p in self.pages.values():
            p.grid(row=0, column=0, sticky="nsew")

    def show(self, key: str) -> None:
        self.pages[key].tkraise()
        self.current_page = key
        for k, (row, bar, lab) in self.nav.items():
            on = k == key
            for w in (row, lab):
                w.config(bg=C["red_bg"] if on else C["side"])
            bar.config(bg=C["red"] if on else C["side"])
            lab.config(fg=C["text"] if on else C["muted"])

    def _wheel(self, e) -> None:
        sf = self.scrollers.get(self.current_page)
        if sf:
            sf.scroll(-1 if (getattr(e, "num", 0) == 4 or getattr(e, "delta", 0) > 0) else 1)

    def _scroll_page(self, parent, key: str):
        sf = ScrollFrame(parent, C["bg"])
        self.scrollers[key] = sf
        wrap = tk.Frame(sf.inner, bg=C["bg"])
        wrap.pack(fill="both", expand=True, padx=18, pady=16)
        return sf, wrap

    # ------------------------------------------------------------------ HOME
    def _page_home(self, parent):
        sf, wrap = self._scroll_page(parent, "home")
        self.hero = Hero(wrap, self)
        self.hero.pack(fill="x")
        bar = self.card(wrap)
        bar.pack(fill="x", pady=(12, 0))
        bi = tk.Frame(bar, bg=C["card"])
        bi.pack(fill="x", padx=16, pady=14)
        self.home_scan_btn = self.btn(bi, "  Scan PC for Tools", lambda: self.scan(False), "primary", action=True,
                                      icon=self.pic("white", "scan"), padx=16, pady=11)
        self.home_scan_btn.pack(side="left")
        self.scan_icon = tk.Label(bi, image=self.pic("misc", "bigcheck"), bg=C["card"])
        self.scan_icon.pack(side="left", padx=(16, 10))
        tx = tk.Frame(bi, bg=C["card"])
        tx.pack(side="left")
        self.scan_head = tk.Label(tx, text="No scan yet", font=self.f_bold, fg=C["muted"], bg=C["card"])
        self.scan_head.pack(anchor="w")
        self.scan_sub = tk.Label(tx, text="Run a scan to find tools you already have.", font=self.f_small, fg=C["muted"], bg=C["card"])
        self.scan_sub.pack(anchor="w")
        self.btn(bi, "  Scan Again", lambda: self.scan(True, budget=300), "outline", action=True, icon=self.pic("white", "refresh"),
                 padx=16, pady=8).pack(side="right")
        self.last_scan_lbl = tk.Label(bi, text="", font=self.f_small, fg=C["muted"], bg=C["card"])
        self.last_scan_lbl.pack(side="right", padx=12)

        cols = tk.Frame(wrap, bg=C["bg"])
        cols.pack(fill="both", expand=True, pady=(12, 0))
        cols.grid_columnconfigure(0, weight=3)
        cols.grid_columnconfigure(1, weight=1, minsize=280)
        left, right = tk.Frame(cols, bg=C["bg"]), tk.Frame(cols, bg=C["bg"])
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        right.grid(row=0, column=1, sticky="nsew")

        self.tools_card = self.card(left)
        self.tools_card.pack(fill="x")
        self.home_table = tk.Frame(self.tools_card, bg=C["card"])
        self.home_table.pack(fill="x", padx=16, pady=14)

        bk = self.card(left)
        bk.pack(fill="x", pady=(12, 0))
        bki = tk.Frame(bk, bg=C["card"])
        bki.pack(fill="x", padx=16, pady=14)
        tk.Label(bki, image=self.pic("nav", "code"), bg=C["card"]).grid(row=0, column=0, rowspan=2, padx=(0, 12))
        self.lbl(bki, "Decompilation Backends", "h2", bg=C["card"]).grid(row=0, column=1, sticky="w")
        self.lbl(bki, "Pick a file on the Decompile page and $Decompile chooses the right one.", "muted", bg=C["card"]).grid(row=1, column=1, sticky="w")
        cards = tk.Frame(bki, bg=C["card"])
        cards.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(12, 0))
        bki.grid_columnconfigure(1, weight=1)
        for i, (badge, t1, t2) in enumerate((("net", ".NET  \u2192  C# Project", "Uses ILSpy (ilspycmd)"),
                                             ("py", "Python  \u2192  .py Files", "Uses pycdc / decompyle3 / uncompyle6"),
                                             ("ghidra", "Native  \u2192  C Pseudocode", "Uses Ghidra (headless)"))):
            cards.grid_columnconfigure(i, weight=1, uniform="bk")
            self._backend_card(cards, badge, t1, t2).grid(row=0, column=i, sticky="ew", padx=(0 if i == 0 else 8, 0))

        self.results_card = self.card(right)
        self.results_card.pack(fill="x")
        self.results_body = tk.Frame(self.results_card, bg=C["card"])
        self.results_body.pack(fill="x", padx=16, pady=14)
        self.activity_card = self.card(right)
        self.activity_card.pack(fill="x", pady=(12, 0))
        self.activity_body = tk.Frame(self.activity_card, bg=C["card"])
        self.activity_body.pack(fill="x", padx=16, pady=14)
        return sf

    def _backend_card(self, parent, badge: str, t1: str, t2: str):
        f = tk.Frame(parent, bg=C["card2"], highlightthickness=1, highlightbackground=C["border"], cursor="hand2")
        inner = tk.Frame(f, bg=C["card2"], cursor="hand2")
        inner.pack(fill="x", padx=10, pady=10)
        parts = [f, inner]
        parts.append(tk.Label(inner, image=self.pic("badge", badge), bg=C["card2"], cursor="hand2"))
        parts[-1].pack(side="left")
        tx = tk.Frame(inner, bg=C["card2"], cursor="hand2")
        tx.pack(side="left", padx=10)
        parts.append(tx)
        for t, font, col in ((t1, self.f_bold, C["text"]), (t2, self.f_small, C["muted"])):
            parts.append(tk.Label(tx, text=t, font=font, fg=col, bg=C["card2"], anchor="w", cursor="hand2"))
            parts[-1].pack(anchor="w")
        parts.append(tk.Label(inner, image=self.pic("white", "chevron"), bg=C["card2"], cursor="hand2"))
        parts[-1].pack(side="right")
        for w in parts:
            w.bind("<Button-1>", lambda e: self.show("decompile"))
            w.bind("<Enter>", lambda e, f=f: f.config(highlightbackground=C["red"]))
            w.bind("<Leave>", lambda e, f=f: f.config(highlightbackground=C["border"]))
        return f

    def row_info(self, comps: list[str]):
        st = self.statuses or {}
        have = [k for k in comps if st.get(k)]
        state = "ok" if len(have) == len(comps) else ("warn" if have else "bad")
        return state, have, [k for k in comps if k not in have]

    def render_home(self) -> None:
        st = self.statuses
        for w in self.home_table.winfo_children():
            w.destroy()
        t = self.home_table
        missing_all = [k for k in REG if st is not None and not st.get(k)]
        head = tk.Frame(t, bg=C["card"])
        head.grid(row=0, column=0, columnspan=5, sticky="ew", pady=(0, 8))
        tk.Label(head, image=self.pic("nav", "tools"), bg=C["card"]).pack(side="left", padx=(0, 10))
        self.lbl(head, "Detected & Installed Tools", "h2", bg=C["card"]).pack(side="left")
        if st is None:
            self.pill(head, "Checking...", C["muted"], C["card"]).pack(side="left", padx=12)
        elif missing_all:
            self.pill(head, f"{len(missing_all)} Missing", C["warn"], C["warn_bg"]).pack(side="left", padx=12)
        else:
            self.pill(head, "All Ready", C["ok"], C["ok_bg"]).pack(side="left", padx=12)
        for c, (txt, minw) in enumerate((("Tool / Backend", 205), ("Status", 112), ("Version", 120), ("Installation Path", 150), ("", 78))):
            t.grid_columnconfigure(c, weight=1 if c in (0, 3) else 0, minsize=minw)
            if txt:
                self.lbl(t, txt, "muted", bg=C["card"]).grid(row=1, column=c, sticky="w", pady=(0, 6))
        r = 2
        rows = list(HOME_ROWS)
        if "vcredist" in REG:
            rows.append(("vc", "Microsoft Visual C++ Redistributable", "Required by Ghidra on Windows", ["vcredist"], "vc"))
        rows.append(("pysys", "Python (System)", "Required for the application", [], "py"))
        for rid, title, sub, comps, badge in rows:
            tk.Frame(t, bg=C["border"], height=1).grid(row=r, column=0, columnspan=5, sticky="ew")
            r += 1
            state, have, miss = ("ok", [], []) if rid == "pysys" else self.row_info(comps)
            if st is None and rid != "pysys":
                state = "wait"
            f = tk.Frame(t, bg=C["card"])
            f.grid(row=r, column=0, sticky="w", pady=7)
            tk.Label(f, image=self.pic("badge", badge), bg=C["card"]).pack(side="left", padx=(0, 10))
            tf = tk.Frame(f, bg=C["card"])
            tf.pack(side="left")
            self.lbl(tf, title, "bold", bg=C["card"], wraplength=150, justify="left").pack(anchor="w")
            self.lbl(tf, sub, "muted", bg=C["card"], wraplength=150, justify="left").pack(anchor="w")
            sf_ = tk.Frame(t, bg=C["card"])
            sf_.grid(row=r, column=1, sticky="w")
            if state == "wait":
                self.lbl(sf_, "Checking...", "muted", bg=C["card"]).pack()
            else:
                tk.Label(sf_, image=self.pic("status", state), bg=C["card"]).pack(side="left", padx=(0, 6))
                word = {"ok": "Installed", "warn": f"{len(have)} of {len(comps)} installed", "bad": "Not installed"}[state]
                tk.Label(sf_, text=word, font=self.f_small, fg={"ok": C["ok"], "warn": C["warn"], "bad": C["bad"]}[state],
                         bg=C["card"]).pack(side="left")
            ver_lines, path = [], ""
            if rid == "pysys":
                ver_lines, path = [platform.python_version()], os.path.dirname(py_exe())
            else:
                for k in have:
                    p, _o, v = (st or {}).get(k) or ("", "", "")
                    if not path:
                        path = (p if Path(p).is_dir() else os.path.dirname(p)) or p
                    ver_lines.append((f"{SHORT[k]} {v}" if len(comps) > 1 else v) if v else (SHORT[k] if len(comps) > 1 else ""))
            self.lbl(t, "\n".join(x for x in ver_lines if x) or "-", "muted", bg=C["card"], justify="left", anchor="nw").grid(row=r, column=2, sticky="w")
            self.lbl(t, shorten(path, 46) if path else "-", "muted", bg=C["card"], wraplength=140, justify="left").grid(row=r, column=3, sticky="w", padx=(0, 8))
            if state in ("bad", "warn"):
                self.btn(t, "Install", lambda m=miss: self.install_many(m), "primary", action=True, padx=14, pady=4).grid(row=r, column=4, sticky="e")
            elif state == "ok" and path:
                self.btn(t, " Open", lambda p=path: open_path(p), "outline", icon=self.pic("white", "folder"), padx=12, pady=4).grid(row=r, column=4, sticky="e")
            r += 1
        self.render_results()
        self.render_scan_bar()
        self.update_footer()

    def render_scan_bar(self) -> None:
        st = self.statuses
        iso = load_config().get("last_scan", "")
        self.last_scan_lbl.config(text=f"Last scan: {fmt_time(iso)}" if iso else "")
        if st is None:
            head, sub, col = "Checking tools...", "Looking for installed tools.", C["muted"]
        else:
            miss = [k for k in REG if not st.get(k)]
            if not iso:
                head, sub, col = "No scan yet", "Run a scan to find tools you already have.", C["muted"]
            elif miss:
                head, sub, col = f"Scan completed - {len(miss)} tool(s) missing", "Install them from the Tools page.", C["warn"]
            else:
                head, sub, col = "Full system scan completed", "All required tools are installed and configured.", C["ok"]
        self.scan_head.config(text=head, fg=col)
        self.scan_sub.config(text=sub)

    def render_results(self) -> None:
        for w in self.results_body.winfo_children():
            w.destroy()
        b, st = self.results_body, self.statuses
        head = tk.Frame(b, bg=C["card"])
        head.pack(fill="x", pady=(0, 8))
        tk.Label(head, image=self.pic("white", "scan"), bg=C["card"]).pack(side="left", padx=(0, 10))
        self.lbl(head, "Scan Results", "h2", bg=C["card"]).pack(side="left")
        items: list[tuple[str, str, str]] = []
        if st is not None:
            rows = HOME_ROWS + ([("vc", "Visual C++ Redistributable", "", ["vcredist"], "vc")] if "vcredist" in REG else [])
            for _rid, title, _sub, comps, _b in rows:
                state, have, miss = self.row_info(comps)
                names = ", ".join(SHORT[k] for k in have)
                if state == "ok":
                    items.append((f"Checking {title}", f"Found {names}", "ok"))
                elif state == "warn":
                    items.append((f"Checking {title}", f"Found {names}; missing {', '.join(SHORT[k] for k in miss)}", "warn"))
                else:
                    items.append((f"Checking {title}", "Not found - install it from Tools", "bad"))
            if self.last_scan:
                s = self.last_scan
                items.append(("Scanning drives", f"{'Stopped early' if s.stopped else 'Completed'} in {s.seconds:.1f}s "
                              f"({s.folders:,} folders)", "warn" if s.stopped else "ok"))
        for title, detail, lvl in items:
            f = tk.Frame(b, bg=C["card"])
            f.pack(fill="x", pady=4)
            tk.Label(f, image=self.pic("status", lvl), bg=C["card"]).pack(side="left", anchor="n", padx=(0, 10), pady=2)
            tf = tk.Frame(f, bg=C["card"])
            tf.pack(side="left", fill="x")
            self.lbl(tf, title, "text", bg=C["card"], justify="left", wraplength=190).pack(anchor="w")
            self.lbl(tf, detail, "muted", bg=C["card"], justify="left", wraplength=190).pack(anchor="w")
        if st is not None:
            miss = [k for k in REG if not st.get(k)]
            ready = not miss
            box = tk.Frame(b, bg=C["ok_bg"] if ready else C["warn_bg"], highlightthickness=1,
                           highlightbackground=C["ok"] if ready else C["warn"])
            box.pack(fill="x", pady=(10, 0))
            bi = tk.Frame(box, bg=box.cget("bg"))
            bi.pack(fill="x", padx=12, pady=10)
            tk.Label(bi, image=self.pic("status", "ok" if ready else "warn"), bg=box.cget("bg")).pack(side="left", anchor="n", padx=(0, 10))
            tf = tk.Frame(bi, bg=box.cget("bg"))
            tf.pack(side="left")
            tk.Label(tf, text="Everything is ready!" if ready else f"{len(miss)} tool(s) still missing", font=self.f_bold,
                     fg=C["ok"] if ready else C["warn"], bg=box.cget("bg")).pack(anchor="w")
            tk.Label(tf, text="All tools are installed and configured with their real paths." if ready else "Open the Tools page to install them.",
                     font=self.f_small, fg=C["muted"], bg=box.cget("bg"), wraplength=170, justify="left").pack(anchor="w")
        self.render_activity()

    def render_activity(self) -> None:
        for w in self.activity_body.winfo_children():
            w.destroy()
        head = tk.Frame(self.activity_body, bg=C["card"])
        head.pack(fill="x", pady=(0, 6))
        tk.Label(head, image=self.pic("nav", "doc"), bg=C["card"]).pack(side="left", padx=(0, 10))
        self.lbl(head, "Recent Activity", "h2", bg=C["card"]).pack(side="left")
        items = list(self.activity)[-5:][::-1]
        if not items:
            self.lbl(self.activity_body, "Nothing yet.", "muted", bg=C["card"]).pack(anchor="w")
        for tm, text, lvl in items:
            f = tk.Frame(self.activity_body, bg=C["card"])
            f.pack(fill="x", pady=2)
            tk.Label(f, image=self.pic("status", lvl), bg=C["card"]).pack(side="left", padx=(0, 8))
            tk.Label(f, text=shorten(text, 36), font=self.f_small, fg=C["text"], bg=C["card"]).pack(side="left")
            tk.Label(f, text=tm, font=self.f_small, fg=C["dim"], bg=C["card"]).pack(side="right")

    def update_footer(self) -> None:
        st = self.statuses
        if st is None:
            self.dot.config(fg=C["muted"])
            self.status.config(text="Checking tools...")
            return
        miss = [k for k in REG if not st.get(k)]
        self.dot.config(fg=C["warn"] if miss else C["ok"])
        self.status.config(text=(f"{len(miss)} tool(s) missing" if miss else "System Ready") + f"   |   Python {platform.python_version()}   |   "
                           + ("Install missing tools on the Tools page" if miss else "All Tools Installed"))

    # ------------------------------------------------------------------ SCAN PC
    def _page_scan(self, parent):
        sf, wrap = self._scroll_page(parent, "scan")
        self.page_title(wrap, "Scan PC", "$Decompile looks for tools you already have and uses them where they are. Only file names "
                              "are read; nothing leaves your PC. Tools that are already available are not searched for.").pack(fill="x")
        card = self.card(wrap)
        card.pack(fill="x", pady=(14, 0))
        ci = tk.Frame(card, bg=C["card"])
        ci.pack(fill="x", padx=18, pady=16)
        self.limit_var = tk.StringVar(value="5 minutes")
        row = tk.Frame(ci, bg=C["card"])
        row.pack(fill="x")
        self.btn(row, "  Quick scan", lambda: self.scan(False), "primary", action=True, icon=self.pic("white", "scan"), padx=20, pady=10).pack(side="left")
        self.btn(row, "Scan whole PC", lambda: self.scan(True, budget=self._limit()), "outline", action=True, padx=18, pady=10).pack(side="left", padx=10)
        self.lbl(row, "Time limit for the whole-PC scan", "muted", bg=C["card"]).pack(side="left", padx=(18, 8))
        ttk.Combobox(row, textvariable=self.limit_var, values=["1 minute", "5 minutes", "30 minutes"], state="readonly", width=12,
                     style="Dark.TCombobox", font=self.f_ui).pack(side="left")
        self.lbl(ci, "Quick scan checks the usual install folders (seconds). The whole-PC scan walks every local drive, shallowest folders "
                     "first, and stops as soon as everything is found.", "muted", bg=C["card"], justify="left", wraplength=860).pack(anchor="w", pady=(12, 0))
        res = self.card(wrap)
        res.pack(fill="x", pady=(14, 0))
        self.scan_res_body = tk.Frame(res, bg=C["card"])
        self.scan_res_body.pack(fill="x", padx=18, pady=16)
        loc = self.card(wrap)
        loc.pack(fill="x", pady=(14, 0))
        li = tk.Frame(loc, bg=C["card"])
        li.pack(fill="x", padx=18, pady=16)
        self.lbl(li, "Locate a tool yourself", "h2", bg=C["card"]).pack(anchor="w")
        self.lbl(li, "Scan did not find it? Point $Decompile at the program and it will be checked and remembered.", "muted", bg=C["card"]).pack(anchor="w", pady=(2, 10))
        lr = tk.Frame(li, bg=C["card"])
        lr.pack(fill="x")
        self.loc_var = tk.StringVar()
        self.loc_cb = ttk.Combobox(lr, textvariable=self.loc_var, state="readonly", width=30, style="Dark.TCombobox", font=self.f_ui,
                                   values=[REG[k].name for k in LOCATE_HINT if k in REG])
        self.loc_cb.pack(side="left")
        self.loc_cb.current(0)
        self.btn(lr, "Browse...", self.locate_selected, "outline", action=True, padx=16, pady=6).pack(side="left", padx=10)
        self.loc_hint = self.lbl(lr, "", "muted", bg=C["card"])
        self.loc_hint.pack(side="left", padx=6)
        self.loc_cb.bind("<<ComboboxSelected>>", lambda e: self._loc_hint())
        self._loc_hint()
        self.render_scan_page()
        return sf

    def _limit(self) -> int:
        return {"1 minute": 60, "5 minutes": 300, "30 minutes": 1800}.get(self.limit_var.get(), 300)

    def _loc_key(self) -> str:
        names = {REG[k].name: k for k in LOCATE_HINT if k in REG}
        return names[self.loc_var.get()]

    def _loc_hint(self) -> None:
        self.loc_hint.config(text="Choose: " + LOCATE_HINT[self._loc_key()])

    def locate_selected(self) -> None:
        key = self._loc_key()
        p = filedialog.askopenfilename(title=f"Locate {REG[key].name}: {LOCATE_HINT[key]}")
        if p:
            self.run_job(f"Registering {REG[key].name}", lambda: register_manual(key, p), lambda r: ok(f"{REG[key].name} registered -> {r}"))

    def render_scan_page(self) -> None:
        for w in self.scan_res_body.winfo_children():
            w.destroy()
        b = self.scan_res_body
        self.lbl(b, "Results of the last scan", "h2", bg=C["card"]).pack(anchor="w", pady=(0, 8))
        s = self.last_scan
        if not s:
            self.lbl(b, "No scan has run in this session yet.", "muted", bg=C["card"]).pack(anchor="w")
            return
        self.lbl(b, f"{'Stopped early' if s.stopped else 'Finished'} in {s.seconds:.1f}s - {s.folders:,} folders looked at, "
                    f"{len(s.registered)} tool(s) newly registered.", "muted", bg=C["card"]).pack(anchor="w", pady=(0, 8))
        for name, detail, lvl in s.lines:
            f = tk.Frame(b, bg=C["card"])
            f.pack(fill="x", pady=3)
            tk.Label(f, image=self.pic("status", "ok" if lvl == "ok" else "warn"), bg=C["card"]).pack(side="left", padx=(0, 10))
            self.lbl(f, name, "bold", bg=C["card"], width=26, anchor="w").pack(side="left")
            self.lbl(f, shorten(detail, 90), "muted", bg=C["card"]).pack(side="left")

    # ------------------------------------------------------------------ TOOLS
    def _page_tools(self, parent):
        sf, wrap = self._scroll_page(parent, "tools")
        top = tk.Frame(wrap, bg=C["bg"])
        top.pack(fill="x")
        # buttons first: a widget packed earlier with expand would otherwise squeeze them off the row
        self.btn(top, "Open tools folder", lambda: (TOOLS.mkdir(parents=True, exist_ok=True), open_path(TOOLS)), "ghost", padx=12, pady=6).pack(side="right")
        self.btn(top, "Re-check", self.refresh_tools, "outline", padx=14, pady=6).pack(side="right", padx=8)
        self.btn(top, "Install all missing", self.install_all, "primary", action=True, padx=16, pady=6).pack(side="right")
        self.page_title(top, "Tools", "Everything downloads from the official project pages (GitHub, PyPI, Microsoft) into "
                                      "a private folder, or is used where you already have it.", wrap=560).pack(side="left", fill="x", expand=True)
        card = self.card(wrap)
        card.pack(fill="x", pady=(14, 0))
        self.tools_table = tk.Frame(card, bg=C["card"])
        self.tools_table.pack(fill="x", padx=14, pady=10)
        self.render_tools_page()
        return sf

    def render_tools_page(self) -> None:
        t = self.tools_table
        for w in t.winfo_children():
            w.destroy()
        st = self.statuses or {}
        for c, w in enumerate((0, 0, 1, 0, 0)):
            t.grid_columnconfigure(c, weight=w)
        for i, (key, tool) in enumerate(REG.items()):
            if i:
                tk.Frame(t, bg=C["border"], height=1).grid(row=2 * i - 1, column=0, columnspan=5, sticky="ew")
            r = 2 * i
            hit = st.get(key)
            tk.Label(t, image=self.pic("status", "ok" if hit else "bad"), bg=C["card"]).grid(row=r, column=0, padx=(4, 10), pady=8)
            f = tk.Frame(t, bg=C["card"])
            f.grid(row=r, column=1, sticky="w", padx=(0, 16))
            self.lbl(f, tool.name, "bold", bg=C["card"]).pack(anchor="w")
            self.lbl(f, tool.purpose, "muted", bg=C["card"]).pack(anchor="w")
            if hit:
                p, origin, v = hit
                self.lbl(t, (f"{v}   " if v else "") + f"[{origin}]  {shorten(p, 70)}", "muted", bg=C["card"], anchor="w").grid(row=r, column=2, sticky="w")
            else:
                self.lbl(t, "not installed", "muted", bg=C["card"], fg=C["bad"], anchor="w").grid(row=r, column=2, sticky="w")
                bf = tk.Frame(t, bg=C["card"])
                bf.grid(row=r, column=3, columnspan=2, sticky="e", padx=4)
                if key in LOCATE_HINT:
                    self.btn(bf, "Locate...", lambda k=key: self._locate(k), "ghost", action=True, padx=10, pady=4).pack(side="left", padx=(0, 6))
                self.btn(bf, f"Install  ({tool.size})", lambda k=key: self.install_one(k), "primary", action=True, padx=12, pady=4).pack(side="left")

    def _locate(self, key: str) -> None:
        self.loc_var.set(REG[key].name)
        self._loc_hint()
        self.locate_selected()

    # ------------------------------------------------------------------ DECOMPILE
    def _page_decompile(self, parent):
        page = tk.Frame(parent, bg=C["bg"])
        wrap = tk.Frame(page, bg=C["bg"])
        wrap.pack(fill="both", expand=True, padx=22, pady=16)
        self.page_title(wrap, "Decompile a program", "$Decompile detects how the exe was built and uses the right decompiler. "
                                                     "Missing ones are downloaded for you.").pack(fill="x")
        card = self.card(wrap)
        card.pack(fill="x", pady=(12, 0))
        inner = tk.Frame(card, bg=C["card"])
        inner.pack(fill="x", padx=18, pady=14)
        inner.grid_columnconfigure(0, weight=1)
        self.exe_var, self.out_var = tk.StringVar(), tk.StringVar()
        scope_default = next((k for k, v in SCOPES.items() if v == get_setting("scope", "entry")), next(iter(SCOPES)))
        self.scope_var = tk.StringVar(value=scope_default)
        self.exe_var.trace_add("write", lambda *a: self._auto_output())
        self.lbl(inner, "PROGRAM (.exe)", "key", bg=C["card"]).grid(row=0, column=0, sticky="w")
        self.entry(inner, self.exe_var).grid(row=1, column=0, sticky="ew", ipady=6, pady=(3, 10))
        self.btn(inner, "Browse", self.browse_exe, "outline", padx=16, pady=6).grid(row=1, column=1, padx=(8, 0), pady=(3, 10))
        self.lbl(inner, "OUTPUT FOLDER", "key", bg=C["card"]).grid(row=2, column=0, sticky="w")
        self.entry(inner, self.out_var).grid(row=3, column=0, sticky="ew", ipady=6, pady=(3, 10))
        self.btn(inner, "Browse", self.browse_out, "outline", padx=16, pady=6).grid(row=3, column=1, padx=(8, 0), pady=(3, 10))
        self.lbl(inner, "IF IT IS A PYTHON PROGRAM, RECOVER", "key", bg=C["card"]).grid(row=4, column=0, sticky="w")
        ttk.Combobox(inner, textvariable=self.scope_var, values=list(SCOPES), state="readonly", style="Dark.TCombobox",
                     font=self.f_ui).grid(row=5, column=0, sticky="ew", pady=(3, 12))
        row = tk.Frame(inner, bg=C["card"])
        row.grid(row=6, column=0, columnspan=2, sticky="w")
        self.btn(row, "Analyze", self.on_analyze, "outline", action=True, padx=20, pady=8).pack(side="left")
        self.btn(row, "Decompile", self.on_decompile, "primary", action=True, padx=24, pady=8).pack(side="left", padx=10)
        info = self.card(wrap)
        info.pack(fill="x", pady=(12, 0))
        ii = tk.Frame(info, bg=C["card"])
        ii.pack(fill="x", padx=18, pady=12)
        ii.grid_columnconfigure(1, weight=1)
        self.info_vars: dict[str, tk.StringVar] = {}
        for i, k in enumerate(("Detected", "Details", "Size", "SHA-256", "Needs")):
            self.lbl(ii, k.upper(), "key", bg=C["card"]).grid(row=i, column=0, sticky="w", pady=2, padx=(0, 16))
            v = tk.StringVar(value="-")
            self.info_vars[k] = v
            tk.Label(ii, textvariable=v, font=self.f_ui if k != "SHA-256" else self.f_mono, fg=C["text"], bg=C["card"], anchor="w",
                     justify="left", wraplength=800).grid(row=i, column=1, sticky="w", pady=2)
        self.note_lbl = tk.Label(ii, text="", font=self.f_small, fg=C["warn"], bg=C["card"], anchor="w", justify="left", wraplength=860)
        self.note_lbl.grid(row=5, column=0, columnspan=2, sticky="w", pady=(6, 0))
        self.make_log(wrap, 7).pack(fill="both", expand=True, pady=(12, 0))
        return page

    def _auto_output(self) -> None:
        p = self.exe_var.get().strip().strip('"')
        if p and (not self.out_var.get() or self.out_var.get() == self._auto_out):
            self._auto_out = str(Path(p).with_name(Path(p).stem + "_src"))
            self.out_var.set(self._auto_out)

    def browse_exe(self) -> None:
        p = filedialog.askopenfilename(title="Choose a program", filetypes=[("Programs", "*.exe *.dll"), ("All files", "*.*")])
        if p:
            self.exe_var.set(p)

    def browse_out(self) -> None:
        p = filedialog.askdirectory(title="Choose the output folder")
        if p:
            self.out_var.set(p)

    def show_info(self, fi: FileInfo, missing: list[str] | None = None) -> None:
        kinds = {"dotnet": ".NET assembly (C#/VB)", "pyinstaller": "Python program (PyInstaller)",
                 "native": "Native program (C / C++ / Delphi / Rust ...)"}
        v = self.info_vars
        v["Detected"].set(kinds[fi.kind])
        v["Details"].set((f"{fi.arch}{' DLL' if fi.is_dll else ''}" if fi.is_pe else "not a PE file")
                         + (f", Python {fi.python_version}" if fi.python_version else "")
                         + (f", compiled {fi.compiled}" if fi.compiled else "") + (f", packed with {fi.packer}" if fi.packer else ""))
        v["Size"].set(f"{fi.size:,} bytes")
        v["SHA-256"].set(fi.sha256)
        v["Needs"].set(", ".join(REG[k].name + ("" if (k not in (missing or [])) else "  (not installed)") for k in required_tools(fi)))
        self.note_lbl.config(text="\n".join(fi.notes))

    def _exe_path(self) -> Path | None:
        s = self.exe_var.get().strip().strip('"')
        if not s or not Path(s).expanduser().is_file():
            self.message("Choose a program first", "Pick an existing .exe with the Browse button.")
            return None
        return Path(s).expanduser()

    def on_analyze(self) -> None:
        p = self._exe_path()
        if p:
            self.run_job("Analyzing", lambda: (analyze(p), missing_tools_all()), lambda r: self.show_info(r[0], r[1]))

    def on_decompile(self) -> None:
        p = self._exe_path()
        if not p:
            return
        out_dir = Path(self.out_var.get().strip().strip('"') or p.with_name(p.stem + "_src")).expanduser()
        scope = SCOPES.get(self.scope_var.get(), "entry")
        jobs = int(get_setting("jobs", 0)) or None

        def analyze_job():
            fi = analyze(p)
            return fi, required_tools(fi), missing_tools_all()

        def decided(r):
            fi, keys, missing = r
            self.show_info(fi, missing)
            self.with_tools(keys, "Decompiling", lambda: decompile(p, out_dir, scope, jobs=jobs), lambda rep: self.after_decompile(out_dir))

        self.run_job("Analyzing", analyze_job, decided)

    def after_decompile(self, out_dir: Path) -> None:
        self.open_project(out_dir)
        self.show("rebuild")

    # ------------------------------------------------------------------ REBUILD (editor)
    def _page_rebuild(self, parent):
        page = tk.Frame(parent, bg=C["bg"])
        top = tk.Frame(page, bg=C["bg"])
        top.pack(fill="x", padx=22, pady=(16, 6))
        self.page_title(top, "Rebuild", "Edit the recovered source, then build it again.").pack(side="left")
        self.btn(top, "Open project...", self.browse_project, "outline", padx=14, pady=5).pack(side="right")
        self.btn(top, "Show folder", lambda: self.project and open_path(self.project["root"]), "ghost", padx=12, pady=5).pack(side="right", padx=6)
        self.proj_lbl = self.lbl(page, "No project open. Decompile a program first, or open an existing output folder.", "muted")
        self.proj_lbl.pack(anchor="w", padx=22)
        # bottom parts are packed first so the expanding editor can never squeeze them off-screen
        self.make_log(page, 5).pack(side="bottom", fill="x", padx=22, pady=(0, 12))
        rb = self.card(page)
        rb.pack(side="bottom", fill="x", padx=22, pady=(8, 8))
        ri = tk.Frame(rb, bg=C["card"])
        ri.pack(fill="x", padx=16, pady=10)
        self.kind_lbl = self.lbl(ri, "Open a project to rebuild it.", "bold", bg=C["card"])
        self.kind_lbl.pack(anchor="w")
        self.entry_var, self.win_var, self.pip_var = tk.StringVar(), tk.BooleanVar(value=False), tk.StringVar()
        self.py_opts = tk.Frame(ri, bg=C["card"])
        self.py_opts.pack(anchor="w", pady=(8, 0))
        self.lbl(self.py_opts, "Entry script", "key", bg=C["card"]).pack(side="left")
        self.entry_cb = ttk.Combobox(self.py_opts, textvariable=self.entry_var, state="readonly", width=24, style="Dark.TCombobox", font=self.f_ui)
        self.entry_cb.pack(side="left", padx=(6, 16))
        self.check(self.py_opts, "Hide console window", self.win_var).pack(side="left", padx=(0, 16))
        self.lbl(self.py_opts, "Extra pip packages", "key", bg=C["card"]).pack(side="left")
        self.entry(self.py_opts, self.pip_var).pack(side="left", padx=6, ipady=3)
        brow = tk.Frame(ri, bg=C["card"])
        brow.pack(anchor="w", pady=(10, 0))
        self.btn(brow, "Rebuild", self.on_rebuild, "primary", action=True, padx=26, pady=8).pack(side="left")
        self.show_out_btn = self.btn(brow, "Show rebuilt file", self._show_rebuilt, "outline", padx=16, pady=8)

        split = tk.PanedWindow(page, orient="horizontal", bg=C["bg"], sashwidth=5, bd=0)
        split.pack(fill="both", expand=True, padx=22, pady=8)
        left = tk.Frame(split, bg=C["card"], highlightthickness=1, highlightbackground=C["border"])
        self.tree = ttk.Treeview(left, show="tree", style="Dark.Treeview", selectmode="browse")
        tsb = self.scrollbar(left, "vertical", self.tree.yview)
        self.tree.configure(yscrollcommand=tsb.set)
        tsb.pack(side="right", fill="y")
        self.tree.pack(fill="both", expand=True)
        self.tree.bind("<<TreeviewOpen>>", self.on_tree_open)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree_paths: dict[str, Path | None] = {}
        split.add(left, minsize=180, width=250)
        right = tk.Frame(split, bg=C["bg"])
        bar = tk.Frame(right, bg=C["card"])
        bar.pack(fill="x")
        self.file_lbl = self.lbl(bar, "No file open", "bold", bg=C["card"])
        self.file_lbl.pack(side="left", padx=12, pady=7)
        self.btn(bar, "Save  (Ctrl+S)", self.save_file, "dark", padx=12, pady=4).pack(side="right", padx=8, pady=4)
        self.btn(bar, "Open externally", lambda: self.cur_file and open_path(self.cur_file), "ghost", padx=12, pady=4).pack(side="right")
        ed = tk.Frame(right, bg=C["editor"], highlightthickness=1, highlightbackground=C["border"])
        ed.pack(fill="both", expand=True)
        self.gutter = tk.Text(ed, width=6, bg=C["card"], fg=C["dim"], font=self.f_mono, relief="flat", bd=0, padx=6, pady=6,
                              state="disabled", takefocus=0, wrap="none", cursor="arrow", highlightthickness=0, selectbackground=C["card"])
        self.gutter.tag_configure("r", justify="right")
        self.text = tk.Text(ed, bg=C["editor"], fg=C["text"], font=self.f_mono, relief="flat", wrap="none", undo=True, maxundo=-1,
                            insertbackground=C["red"], selectbackground=C["red_lo"], selectforeground="#ffffff", padx=8, pady=6,
                            highlightthickness=0, tabs=(self.f_mono.measure("    "),))
        self.text.tag_configure("err", background="#4a0e18")
        vsb = self.scrollbar(ed, "vertical", self._yview)
        hsb = self.scrollbar(ed, "horizontal", self.text.xview)
        self.text.configure(yscrollcommand=lambda a, b: (vsb.set(a, b), self.gutter.yview_moveto(a)), xscrollcommand=hsb.set)
        hsb.pack(side="bottom", fill="x")
        vsb.pack(side="right", fill="y")
        self.gutter.pack(side="left", fill="y")
        self.text.pack(side="left", fill="both", expand=True)
        self.text.bind("<<Modified>>", self._on_modified)
        self.text.bind("<KeyRelease>", lambda e: self._gutter())
        self.syntax_lbl = self.lbl(right, "", "muted")
        self.syntax_lbl.pack(anchor="w", pady=(4, 0))
        split.add(right, minsize=400)
        return page

    def _yview(self, *a) -> None:
        self.text.yview(*a)
        self.gutter.yview(*a)

    def _gutter(self) -> None:
        n = int(self.text.index("end-1c").split(".")[0])
        if n == self._lines:
            return
        self._lines = n
        self.gutter.config(state="normal")
        self.gutter.delete("1.0", "end")
        self.gutter.insert("1.0", "\n".join(str(i) for i in range(1, n + 1)), "r")
        self.gutter.config(state="disabled")
        self.gutter.yview_moveto(self.text.yview()[0])

    def _on_modified(self, _e=None) -> None:
        if self.text.edit_modified():
            if self.cur_file and not self.dirty:
                self.dirty = True
                self.file_lbl.config(text=f"{self.cur_file.name}  *")
            self.text.edit_modified(False)
            self._gutter()

    def browse_project(self) -> None:
        p = filedialog.askdirectory(title="Choose a $Decompile output folder (contains report.json)")
        if p:
            self.open_project(Path(p))

    def open_project(self, root: Path) -> None:
        try:
            proj = load_project(root)
        except ToolError as exc:
            bad(str(exc))
            self.message("Not a project", str(exc))
            return
        if self.dirty and not self.confirm("Unsaved changes", "Discard the unsaved changes in the editor?", "Discard"):
            return
        self.project, self.dirty, self.cur_file = proj, False, None
        self.last_build = None
        self.show_out_btn.pack_forget()
        self.proj_lbl.config(text=proj["root"])
        self.kind_lbl.config(text=KIND_TEXT.get(proj["kind"], KIND_TEXT["native"]))
        entries = proj.get("entries") or []
        self.entry_cb.config(values=entries)
        self.entry_var.set(entries[0] if entries else "")
        if proj["kind"] == "pyinstaller":
            self.py_opts.pack(anchor="w", pady=(8, 0))
        else:
            self.py_opts.pack_forget()
        self.fill_tree()
        self._set_text("", None)
        src = Path(proj["source"])
        first = (src / entries[0]) if entries and (src / entries[0]).is_file() else next(iter(sorted(src.glob("*.c")) + sorted(src.glob("*.cs"))), None)
        if first:
            self.open_file(first)

    def fill_tree(self) -> None:
        self.tree.delete(*self.tree.get_children())
        self.tree_paths = {}
        self._add_dir("", Path(self.project["source"]))  # type: ignore[index]

    def _add_dir(self, parent: str, path: Path) -> None:
        try:
            items = sorted(path.iterdir(), key=lambda p: (not p.is_dir(), p.name.lower()))
        except OSError:
            return
        for p in items[:3000]:
            iid = self.tree.insert(parent, "end", text=("  " + p.name))
            self.tree_paths[iid] = p
            if p.is_dir():
                self.tree_paths[self.tree.insert(iid, "end", text="")] = None  # placeholder so the folder can expand

    def on_tree_open(self, _e) -> None:
        iid = self.tree.focus()
        kids = self.tree.get_children(iid)
        path = self.tree_paths.get(iid)
        if path and len(kids) == 1 and self.tree_paths.get(kids[0], 1) is None:
            self.tree_paths.pop(kids[0], None)
            self.tree.delete(kids[0])
            self._add_dir(iid, path)

    def on_tree_select(self, _e) -> None:
        iid = self.tree.focus()
        p = self.tree_paths.get(iid) if iid else None
        if p and p.is_file() and p != self.cur_file:
            self.open_file(p)

    def _set_text(self, content: str, path: Path | None) -> None:
        self.text.delete("1.0", "end")
        self.text.insert("1.0", content)
        self.text.edit_reset()
        self.text.edit_modified(False)
        self.dirty = False
        self.cur_file = path
        self.file_lbl.config(text=path.name if path else "No file open")
        self.text.tag_remove("err", "1.0", "end")
        self.syntax_lbl.config(text="")
        self._lines = -1
        self._gutter()

    def open_file(self, path: Path) -> None:
        if self.dirty and self.cur_file and self.confirm("Unsaved changes", f"Save changes to {self.cur_file.name} first?", "Save"):
            self.save_file()
        try:
            if path.stat().st_size > MAX_EDIT_BYTES:
                self._set_text("", None)
                self.syntax_lbl.config(text=f"{path.name} is too large for the built-in editor - use 'Open externally'.")
                self.cur_file = path
                return
            raw = path.read_bytes()
        except OSError as exc:
            bad(f"Cannot open {path}: {exc}")
            return
        if b"\0" in raw[:4096]:
            self._set_text("", None)
            self.syntax_lbl.config(text=f"{path.name} is a binary file.")
            return
        try:
            self.cur_enc, content = "utf-8", raw.decode("utf-8")
        except UnicodeDecodeError:
            self.cur_enc, content = "latin-1", raw.decode("latin-1")
        self._set_text(content.replace("\r\n", "\n"), path)
        if path.suffix == ".py":
            self.check_syntax(quiet=True)

    def save_file(self) -> bool:
        if not self.cur_file or self.current_page != "rebuild":
            return False
        data = self.text.get("1.0", "end-1c")
        if os.linesep != "\n":
            data = data.replace("\n", os.linesep)
        try:
            try:
                payload = data.encode(self.cur_enc)
            except UnicodeEncodeError:  # typed characters the old encoding cannot hold
                self.cur_enc = "utf-8"
                payload = data.encode("utf-8")
            tmp = self.cur_file.with_name(self.cur_file.name + ".dd-tmp")
            tmp.write_bytes(payload)
            tmp.replace(self.cur_file)
        except OSError as exc:
            bad(f"Could not save: {exc}")
            return False
        self.dirty = False
        self.text.edit_modified(False)  # a stale <<Modified>> event must not mark the saved file dirty again
        self.file_lbl.config(text=self.cur_file.name)
        ok(f"Saved {self.cur_file.name}")
        if self.cur_file.suffix == ".py":
            self.check_syntax()
        return True

    def check_syntax(self, quiet: bool = False) -> bool:
        self.text.tag_remove("err", "1.0", "end")
        try:
            compile(self.text.get("1.0", "end-1c"), str(self.cur_file or "<editor>"), "exec", dont_inherit=True)
        except SyntaxError as e:
            line = e.lineno or 1
            self.text.tag_add("err", f"{line}.0", f"{line}.end+1c")
            self.text.see(f"{line}.0")
            self.syntax_lbl.config(text=f"Syntax error, line {line}: {e.msg}", fg=C["red_hi"])
            return False
        self.syntax_lbl.config(text="" if quiet else "Syntax OK", fg=C["ok"])
        return True

    def on_rebuild(self) -> None:
        if not self.project:
            self.message("No project", "Decompile a program first (or open an output folder).")
            return
        if self.dirty:
            self.save_file()
        root, kind = self.project["root"], self.project["kind"]
        entry, windowed = self.entry_var.get() or None, self.win_var.get()
        pkgs = self.pip_var.get().split()
        self.last_build = None

        def done(path):
            self.last_build = Path(path)
            self.show_out_btn.pack(side="left", padx=10)

        self.with_tools(required_for_rebuild(kind), "Rebuilding", lambda: rebuild(Path(root), entry, windowed, pkgs), done)

    def _show_rebuilt(self) -> None:
        if self.last_build:
            open_path(self.last_build if self.last_build.is_dir() else self.last_build.parent)

    # ------------------------------------------------------------------ SETTINGS / LOGS / ABOUT
    def _page_settings(self, parent):
        sf, wrap = self._scroll_page(parent, "settings")
        self.page_title(wrap, "Settings", "Changes are saved immediately.").pack(fill="x")
        card = self.card(wrap)
        card.pack(fill="x", pady=(14, 0))
        ci = tk.Frame(card, bg=C["card"])
        ci.pack(fill="x", padx=18, pady=16)
        self.auto_var = tk.BooleanVar(value=bool(get_setting("auto_scan", True)))
        self.check(ci, "Look for installed tools every time $Decompile starts (recommended)", self.auto_var,
                   lambda: set_setting("auto_scan", bool(self.auto_var.get()))).pack(anchor="w", pady=4)
        self.btn(ci, "Run the whole-PC scan again at the next start", self._reset_deep, "outline", padx=14, pady=6).pack(anchor="w", pady=(8, 14))
        self.lbl(ci, "Python programs: what to recover by default", "key", bg=C["card"]).pack(anchor="w")
        default_scope = next((k for k, v in SCOPES.items() if v == get_setting("scope", "entry")), next(iter(SCOPES)))
        self.set_scope = tk.StringVar(value=default_scope)
        cb = ttk.Combobox(ci, textvariable=self.set_scope, values=list(SCOPES), state="readonly", width=44, style="Dark.TCombobox", font=self.f_ui)
        cb.pack(anchor="w", pady=(3, 12))
        cb.bind("<<ComboboxSelected>>", lambda e: (set_setting("scope", SCOPES[self.set_scope.get()]), self.scope_var.set(self.set_scope.get())))
        self.lbl(ci, "Parallel decompile jobs (0 = automatic)", "key", bg=C["card"]).pack(anchor="w")
        self.jobs_var = tk.IntVar(value=int(get_setting("jobs", 0)))
        tk.Spinbox(ci, from_=0, to=32, textvariable=self.jobs_var, width=6, font=self.f_ui, bg=C["card2"], fg=C["text"], buttonbackground=C["card2"],
                   relief="flat", highlightthickness=1, highlightbackground=C["border"], insertbackground=C["red"],
                   command=lambda: set_setting("jobs", int(self.jobs_var.get() or 0))).pack(anchor="w", pady=(3, 0))
        data = self.card(wrap)
        data.pack(fill="x", pady=(14, 0))
        di = tk.Frame(data, bg=C["card"])
        di.pack(fill="x", padx=18, pady=16)
        self.lbl(di, "Data folder", "h2", bg=C["card"]).pack(anchor="w")
        self.lbl(di, str(TOOLS.parent), "muted", bg=C["card"]).pack(anchor="w", pady=(2, 2))
        if is_store_python():
            self.lbl(di, "Microsoft Store Python detected: this folder is outside AppData on purpose, because the Store sandbox hides "
                         "AppData from the programs $Decompile starts.", "muted", bg=C["card"], fg=C["warn"], wraplength=860, justify="left").pack(anchor="w", pady=(0, 6))
        row = tk.Frame(di, bg=C["card"])
        row.pack(anchor="w", pady=(6, 0))
        self.btn(row, "Open data folder", lambda: (TOOLS.parent.mkdir(parents=True, exist_ok=True), open_path(TOOLS.parent)), "outline", padx=14, pady=6).pack(side="left")
        self.btn(row, "Forget remembered tool locations", self._forget, "outline", padx=14, pady=6).pack(side="left", padx=8)
        self.btn(row, "Delete downloaded installers", self._clear_downloads, "outline", padx=14, pady=6).pack(side="left")
        return sf

    def _reset_deep(self) -> None:
        cfg = load_config()
        cfg["deep_scan_done"] = cfg["deep_scan_offered"] = False
        save_config()
        ok("The whole-PC scan will run again at the next start.")

    def _forget(self) -> None:
        if self.confirm("Forget tool locations", "Tools found by a scan will be forgotten and searched for again at the next scan.\nTools "
                        "installed by $Decompile itself are not touched.", "Forget"):
            forget_registered_paths()
            self.refresh_tools()

    def _clear_downloads(self) -> None:
        shutil.rmtree(DOWNLOADS, ignore_errors=True)
        ok("Downloaded installers deleted.")

    def _page_logs(self, parent):
        page = tk.Frame(parent, bg=C["bg"])
        wrap = tk.Frame(page, bg=C["bg"])
        wrap.pack(fill="both", expand=True, padx=22, pady=16)
        top = tk.Frame(wrap, bg=C["bg"])
        top.pack(fill="x")
        self.page_title(top, "Logs", f"Also saved to {LOG_FILE}").pack(side="left")
        self.btn(top, "Open log file", lambda: LOG_FILE.exists() and open_path(LOG_FILE), "ghost", padx=12, pady=5).pack(side="right")
        self.btn(top, "Clear", self._clear_log, "outline", padx=14, pady=5).pack(side="right", padx=8)
        self.make_log(wrap, 20).pack(fill="both", expand=True, pady=(12, 0))
        return page

    def _page_about(self, parent):
        sf, wrap = self._scroll_page(parent, "about")
        card = self.card(wrap)
        card.pack(fill="x")
        ci = tk.Frame(card, bg=C["card"])
        ci.pack(fill="x", padx=22, pady=20)
        tk.Label(ci, image=self.logo(96), bg=C["card"]).pack(side="left", padx=(0, 22))
        tf = tk.Frame(ci, bg=C["card"])
        tf.pack(side="left")
        row = tk.Frame(tf, bg=C["card"])
        row.pack(anchor="w")
        tk.Label(row, text="$", font=self.f_hero, fg=C["red"], bg=C["card"]).pack(side="left")
        tk.Label(row, text="Decompile", font=self.f_hero, fg=C["text"], bg=C["card"]).pack(side="left")
        self.lbl(tf, f"Version {VERSION}   -   Turn executables into possibilities", "muted", bg=C["card"]).pack(anchor="w")
        self.lbl(tf, "Detects how a Windows program was built, picks the right decompiler (ILSpy, pycdc / decompyle3 / uncompyle6, "
                     "Ghidra), downloads what is missing, lets you edit the result and builds it again. The program you analyse is never "
                     "executed. Only analyse software you own or are authorised to analyse.", "muted", bg=C["card"], justify="left",
                 wraplength=700).pack(anchor="w", pady=(8, 0))
        sysc = self.card(wrap)
        sysc.pack(fill="x", pady=(14, 0))
        si = tk.Frame(sysc, bg=C["card"])
        si.pack(fill="x", padx=22, pady=16)
        self.lbl(si, "This computer", "h2", bg=C["card"]).pack(anchor="w", pady=(0, 6))
        self.about_text = self.lbl(si, "", "muted", bg=C["card"], justify="left", wraplength=900, font=self.f_mono)
        self.about_text.pack(anchor="w")
        row = tk.Frame(si, bg=C["card"])
        row.pack(anchor="w", pady=(12, 0))
        self.btn(row, "Copy diagnostics", self._copy_diag, "outline", padx=14, pady=6).pack(side="left")
        self.btn(row, "Open data folder", lambda: (TOOLS.parent.mkdir(parents=True, exist_ok=True), open_path(TOOLS.parent)), "outline", padx=14, pady=6).pack(side="left", padx=8)
        self.refresh_about()
        return sf

    def diagnostics(self) -> str:
        lines = [f"{APP_NAME} {VERSION}", f"OS: {platform.platform()}", f"Python: {platform.python_version()} ({py_exe()})",
                 f"Microsoft Store Python: {is_store_python()}", f"Tk: {tk.TkVersion}", f"Data folder: {TOOLS.parent}"]
        for k, t in REG.items():
            hit = (self.statuses or {}).get(k)
            lines.append(f"{t.name}: " + (f"{hit[2] or 'installed'}  [{hit[1]}]  {hit[0]}" if hit else "not installed"))
        return "\n".join(lines)

    def refresh_about(self) -> None:
        self.about_text.config(text=self.diagnostics())

    def _copy_diag(self) -> None:
        self.clipboard_clear()
        self.clipboard_append(self.diagnostics())
        ok("Diagnostics copied to the clipboard.")

    # ------------------------------------------------------------------ scanning / tools
    def auto_scan(self) -> None:
        """At every start: look for tools already on this PC. The very first start also searches every drive (max 1 minute)."""
        cfg = load_config()
        deep = not cfg.get("deep_scan_done") and not cfg.get("deep_scan_offered")
        if deep:
            cfg["deep_scan_offered"] = True
            save_config()
            say("First start: looking for tools you already have (usual folders first, then every drive, max 1 minute). Press Stop to skip.")
        self.scan(deep, budget=60 if deep else None)

    def scan(self, deep: bool, budget: int | None = None) -> None:
        self.run_job("Scanning this PC", lambda: scan_pc(deep, budget), self._after_scan)

    def _after_scan(self, res: ScanResult) -> None:
        self.last_scan = res
        self.render_scan_page()
        self.render_home()

    def refresh_tools(self) -> None:
        def look():
            out_ = {}
            for k, t in REG.items():
                p = t.find()
                out_[k] = (p, tool_origin(k, p), tool_version(k, p)) if p else None
            return out_
        self.bg(look, self.render_tools)

    def render_tools(self, status: dict | None) -> None:
        if status is None:
            return
        self.statuses = status
        self.render_home()
        self.render_tools_page()
        self.refresh_about()

    def install_many(self, keys: list[str]) -> None:
        plan = install_plan(keys)
        if not plan:
            return
        if self.confirm("Install tools", "\n".join(f"  -  {REG[k].name}  ({REG[k].size})" for k in plan) + "\n\nDownload and install now?", "Install"):
            self.run_job("Installing tools", lambda: [install_tool(k) for k in plan])

    def install_one(self, key: str) -> None:
        self.install_many([key])

    def install_all(self) -> None:
        plan = [k for k in REG if not is_installed(k)]
        if not plan:
            self.message("All set", "Every tool is already installed.")
            return
        self.install_many(plan)

    # ------------------------------------------------------------------ job plumbing
    def bg(self, fn, cb) -> None:
        def run():
            try:
                r = fn()
            except Exception:  # noqa: BLE001
                r = None
            self.q.put(("call", lambda: cb(r)))
        threading.Thread(target=run, daemon=True).start()

    def run_job(self, title: str, work, on_ok=None) -> None:
        if self.busy:
            warn("Another task is still running - wait for it or press Stop.")
            return
        STOP.clear()
        self.set_busy(True, title)

        def runner():
            res, err = None, None
            try:
                res = work()
            except ToolError as exc:
                err = str(exc)
            except Exception as exc:  # noqa: BLE001
                import traceback
                err = f"{type(exc).__name__}: {exc}"
                _emit("out", traceback.format_exc())
            self.q.put(("call", lambda: self._job_done(title, res, err, on_ok)))

        threading.Thread(target=runner, daemon=True).start()

    def _job_done(self, title, res, err, on_ok) -> None:
        self.set_busy(False)
        self.refresh_tools()
        if err:
            bad(err)
            self.dot.config(fg=C["bad"])
            self.status.config(text=f"{title}: failed - see the Logs page")
            return
        if on_ok:
            on_ok(res)

    def with_tools(self, keys, title, work, on_ok=None) -> None:
        """Make sure tools are installed (asking first), then run work()."""
        def check():
            return install_plan(list(keys))

        def decided(plan):
            if plan:
                listing = "\n".join(f"  -  {REG[k].name}   ({REG[k].size})" for k in plan)
                if not self.confirm("Download required tools", "These tools are needed and not installed yet:\n\n" + listing +
                                    "\n\nDownload and install them now?", "Install"):
                    return

            def full():
                for k in plan:
                    install_tool(k)
                return work()
            self.run_job(title, full, on_ok)

        self.run_job("Checking tools", check, decided)

    def set_busy(self, on: bool, title: str = "") -> None:
        self.busy = on
        self.actions = [b for b in self.actions if b.winfo_exists()]  # drop buttons destroyed by page refreshes
        for b in self.actions:
            b.set_enabled(not on)
        if on:
            self.f_idle.pack_forget()
            self.busy_lbl.config(text=title + "...")
            self.f_busy.pack()
        else:
            self.pb.stop()
            self.pb.config(mode="determinate", value=0)
            self._pb_indeterminate = False
            self.prog_lbl.config(text="")
            self.f_busy.pack_forget()
            self.f_idle.pack()
            self.update_footer()

    def on_stop(self) -> None:
        warn("Stopping...")
        cancel_all()

    # ------------------------------------------------------------------ queue + log
    def _open_log_file(self):
        try:
            LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
            if LOG_FILE.exists() and LOG_FILE.stat().st_size > 2 * 1024 * 1024:
                LOG_FILE.replace(LOG_FILE.with_suffix(".old"))
            return open(LOG_FILE, "a", encoding="utf-8", buffering=1)
        except OSError:
            return None

    def pump(self) -> None:
        try:
            for _ in range(400):
                try:
                    item = self.q.get_nowait()
                except queue.Empty:
                    break
                try:
                    if item[0] == "log":
                        self.append_log(item[1], item[2])
                    elif item[0] == "prog":
                        self.set_progress(item[1], item[2])
                    elif item[0] == "call":
                        item[1]()
                except Exception:  # noqa: BLE001 - keep the UI alive, show what went wrong
                    import traceback
                    try:
                        self.append_log("bad", "Internal error (the app keeps running):\n" + traceback.format_exc())
                    except Exception:  # noqa: BLE001
                        pass
        finally:
            self.after(50, self.pump)

    def append_log(self, level: str, msg: str) -> None:
        prefix = {"info": "[*] ", "ok": "[+] ", "warn": "[!] ", "bad": "[x] ", "out": "    "}[level]
        stamp = datetime.now().strftime("%H:%M")
        if self._logf:
            try:
                self._logf.write(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} {prefix}{msg}\n")
            except (OSError, ValueError):
                self._logf = None
        if level in ("ok", "warn", "bad") and len(msg) < 220:
            self.activity.append((stamp, msg, "ok" if level == "ok" else "warn" if level == "warn" else "bad"))
            if self.current_page == "home":
                self.after_idle(self.render_activity)
        for t in self.log_views:
            at_end = t.yview()[1] > 0.98
            t.config(state="normal")
            t.insert("end", prefix + msg + "\n", level)
            if int(t.index("end-1c").split(".")[0]) > 4000:
                t.delete("1.0", "500.0")
            t.config(state="disabled")
            if at_end:
                t.see("end")

    def _clear_log(self) -> None:
        for t in self.log_views:
            t.config(state="normal")
            t.delete("1.0", "end")
            t.config(state="disabled")

    def set_progress(self, frac, text: str) -> None:
        self.prog_lbl.config(text=text[:34])
        if frac is None:
            if not self._pb_indeterminate:
                self.pb.config(mode="indeterminate")
                self.pb.start(14)
                self._pb_indeterminate = True
        else:
            if self._pb_indeterminate:
                self.pb.stop()
                self.pb.config(mode="determinate")
                self._pb_indeterminate = False
            self.pb.config(value=max(0.0, min(1.0, frac)) * 100)

    # ------------------------------------------------------------------ dialogs
    def _dialog(self, title: str, message: str):
        d = tk.Toplevel(self)
        d.title(title)
        d.configure(bg=C["bg"])
        d.transient(self)
        d.resizable(False, False)
        tk.Frame(d, bg=C["red"], height=3).pack(fill="x")
        tk.Label(d, text=title, font=self.f_bold, fg=C["text"], bg=C["bg"]).pack(anchor="w", padx=22, pady=(16, 4))
        tk.Label(d, text=message, font=self.f_ui, fg=C["muted"], bg=C["bg"], justify="left", wraplength=480).pack(anchor="w", padx=22, pady=(0, 14))
        return d

    def _show_dialog(self, d, dy: int) -> None:
        d.update_idletasks()
        x = self.winfo_rootx() + (self.winfo_width() - d.winfo_width()) // 2
        y = self.winfo_rooty() + (self.winfo_height() - d.winfo_height()) // 3 + dy
        d.geometry(f"+{max(0, x)}+{max(0, y)}")
        try:
            d.wait_visibility()
            d.grab_set()
        except tk.TclError:
            pass

    def confirm(self, title: str, message: str, yes: str = "OK") -> bool:
        result = {"v": False}
        d = self._dialog(title, message)
        row = tk.Frame(d, bg=C["bg"])
        row.pack(anchor="e", padx=22, pady=(0, 16))

        def close(v):
            result["v"] = v
            d.destroy()
        Btn(row, "Cancel", lambda: close(False), "outline", font=self.f_bold).pack(side="left", padx=(0, 8))
        Btn(row, yes, lambda: close(True), "primary", font=self.f_bold).pack(side="left")
        d.protocol("WM_DELETE_WINDOW", lambda: close(False))
        self._show_dialog(d, 0)
        self.wait_window(d)
        return result["v"]

    def message(self, title: str, text: str) -> None:
        d = self._dialog(title, text)
        Btn(d, "OK", d.destroy, "primary", font=self.f_bold).pack(anchor="e", padx=22, pady=(0, 16))
        self._show_dialog(d, 60)

    def on_close(self) -> None:
        if self.busy and not self.confirm("Task running", "A task is still running. Stop it and quit?", "Quit"):
            return
        cancel_all()
        if self._logf:
            try:
                self._logf.close()
            except OSError:
                pass
        self.destroy()


def missing_tools_all() -> list[str]:
    return [k for k in REG if not is_installed(k)]


def main() -> int:
    if len(sys.argv) > 1:
        return _cli(sys.argv[1:])
    if tk is None:
        print("Tkinter is not available in this Python. Install it (Windows: re-run the Python installer and tick "
              "'tcl/tk'; Debian/Ubuntu: sudo apt install python3-tk) or use the command line: python main.py --help")
        return 1
    App().mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
