"""
pq_verify.ct_div -- secret operands of the library's integer divisions, at
run time (PQV013).

Memcheck tracks which bits are secret (undefined) but reports only branches
and addresses that depend on them; a hardware division whose operand is
secret goes unreported, though its latency depends on that operand on many
processors (KyberSlash). This reads the operands' shadow bits at each
division instead: the constant-time driver runs under memcheck with its
gdbserver on, gdb attached through vgdb puts a breakpoint on every integer
division instruction in the library, and at each one, while the driver has
secrets marked, reads Valgrind's first shadow register set (V bits; a set bit
is secret) for the dividend and the divisor -- or, for a divisor in memory,
the V bits of those bytes (`monitor get_vbits`).

What makes a silent run mean something:
  * a self-test in the same run: right after the secrets are marked, the
    driver divides once by a secret dividend and once by a public one, and
    exactly the first must be reported, or the check cannot verify;
  * divisions are counted only while secrets are live (the driver calls
    pqv_ct_armed/pqv_ct_disarmed around the operation), so setup code -- the
    key pair, the ciphertext decaps is given -- cannot use up a site's
    budget of checks before the secret operation reaches it;
  * any error reading a shadow register, an operand form not understood, or
    a run that did not end normally is CANNOT VERIFY, never "no secret
    division".

Scope: x86-64 only (shadow register names and operand forms are
architecture-specific); other architectures are reported as not checked,
with the division listing as before. gdb and vgdb must be installed; without
them the divisions are listed, not checked, as before this check existed.
Each site is checked on at most `max_checks` executions while secrets are
live (1,024 by default), and the report says when a site reached that.
Precision is memcheck's: its propagation of V bits is exact for most
integer operations and conservative for some, so a reported secret operand
is one memcheck could not prove public.
"""
import json
import os
import re
import shutil
import signal
import subprocess
import tempfile

X86_64 = 62
MAX_CHECKS = 1024
SELFTEST_FN = "pqv_ct_div"
# Valgrind options for the run: the gdbserver, its shadow registers, and the
# register updates that keep them exact at every instruction (the
# constant-time runs use the same; see ct_audit's module docstring).
VALGRIND = ("--tool=memcheck", "--vgdb=yes", "--vgdb-error=0",
            "--vgdb-shadow-registers=yes", "--error-limit=no", "--leak-check=no",
            "--vex-iropt-register-updates=allregs-at-each-insn")

_INSN = re.compile(r"^\s*([0-9a-f]+):\s+(i?div[bwlq]?)\s+(\S[^#]*?)\s*(?:#.*)?$")
_FN = re.compile(r"^([0-9a-f]+) <(.+)>:$")


class Unavailable(RuntimeError):
    """The check cannot run here (no gdb or vgdb, not x86-64)."""


def available():
    """None if the check can run, else why not."""
    for tool, what in (("gdb", "gdb"), ("vgdb", "vgdb, Valgrind's gdbserver bridge"),
                       ("valgrind", "Valgrind")):
        if not shutil.which(tool):
            return f"{what} is not installed"
    return None


def sites(disassembly):
    """[{fn, fn_start, offset, mnemonic, operands}] for every integer
    division instruction in `objdump -d --no-show-raw-insn` output of an
    x86-64 object. `offset` is the instruction's link-time address."""
    out, fn, start = [], "?", 0
    for line in disassembly.splitlines():
        m = _FN.match(line)
        if m:
            start, fn = int(m.group(1), 16), m.group(2)
            continue
        m = _INSN.match(line)
        if m:
            out.append({"fn": fn, "fn_start": start, "offset": int(m.group(1), 16),
                        "mnemonic": m.group(2), "operands": m.group(3).strip()})
    return out


# The gdb side. It runs inside gdb's Python; cfg names the sites, the output
# file and the budget. Every outcome it cannot vouch for is written down as an
# error, and the Python side turns any error into CANNOT VERIFY.
GDB_SCRIPT = r'''
import gdb, json, re

cfg = json.load(open(gdb.convenience_variable("pqv_cfg").string()))
out = {"selftest": [], "sites": {}, "errors": [], "armed": 0, "exit_code": None,
       "connected": False}
state = {"armed": False}


def save():
    with open(cfg["out"], "w") as fh:
        json.dump(out, fh)


REG = {}
for p, (b, w, d) in {"rax": ("al", "ax", "eax"), "rbx": ("bl", "bx", "ebx"),
                     "rcx": ("cl", "cx", "ecx"), "rdx": ("dl", "dx", "edx"),
                     "rsi": ("sil", "si", "esi"), "rdi": ("dil", "di", "edi"),
                     "rbp": ("bpl", "bp", "ebp"), "rsp": ("spl", "sp", "esp")}.items():
    REG.update({b: (p, 8), w: (p, 16), d: (p, 32), p: (p, 64)})
for i in range(8, 16):
    REG.update({f"r{i}b": (f"r{i}", 8), f"r{i}w": (f"r{i}", 16),
                f"r{i}d": (f"r{i}", 32), f"r{i}": (f"r{i}", 64)})
WIDTH = {"b": 8, "w": 16, "l": 32, "q": 64}
MEM = re.compile(r"^(-?(?:0x[0-9a-f]+|\d+))?\((%[a-z0-9]+)?(?:,(%[a-z0-9]+)(?:,([1248]))?)?\)$")


def shadow(parent, width):
    v = gdb.parse_and_eval(f"${parent}s1")
    if v.type.code == gdb.TYPE_CODE_VOID:
        raise RuntimeError(f"no shadow register ${parent}s1")
    return int(v) & ((1 << width) - 1)


def reg(name):
    return int(gdb.parse_and_eval("$" + name)) & ((1 << 64) - 1)


def memory_vbits(operand, nbytes, pc):
    m = MEM.match(operand)
    if not m:
        raise RuntimeError(f"operand form not handled: {operand!r}")
    disp = int(m.group(1), 0) if m.group(1) else 0
    base, index, scale = m.group(2), m.group(3), int(m.group(4) or 1)
    if base == "%rip":
        length = gdb.selected_frame().architecture().disassemble(pc)[0]["length"]
        addr = pc + length + disp
    else:
        addr = disp + (reg(base[1:]) if base else 0) + (reg(index[1:]) * scale if index else 0)
    addr &= (1 << 64) - 1
    text = gdb.execute(f"monitor get_vbits {addr:#x} {nbytes}", to_string=True)
    bits = re.sub(r"\s", "", text)
    if not re.fullmatch(r"[0-9a-f]+", bits):
        raise RuntimeError(f"get_vbits {addr:#x} {nbytes}: {text.strip()!r}")
    return int(bits, 16)


def secret_operands(mnemonic, operands, pc):
    """Which operands of this division carry secret bits."""
    if operands.startswith("%"):
        name = operands[1:]
        if name not in REG:
            raise RuntimeError(f"register not handled: {operands!r}")
        parent, width = REG[name]
        divisor = shadow(parent, width)
    else:
        suffix = mnemonic[-1]
        if suffix not in WIDTH:
            raise RuntimeError(f"no operand size for {mnemonic} {operands}")
        width = WIDTH[suffix]
        divisor = memory_vbits(operands, width // 8, pc)
    found = ["divisor"] if divisor else []
    if width == 8:
        if shadow("rax", 16):
            found.append("dividend")
    elif shadow("rax", width) or shadow("rdx", width):
        found.append("dividend")
    return found


class Flag(gdb.Breakpoint):
    def __init__(self, fn, value):
        super().__init__(fn, internal=True)
        self.value = value

    def stop(self):
        state["armed"] = self.value
        if self.value:
            out["armed"] += 1
        return False


class Division(gdb.Breakpoint):
    def __init__(self, key, addr, site, selftest=False):
        super().__init__(f"*{addr:#x}", internal=True)
        self.key, self.site, self.selftest = key, site, selftest
        if not selftest:
            out["sites"][key] = {"fn": site["fn"], "offset": site["offset"],
                                 "checked": 0, "secret": 0, "what": [], "capped": False}

    def stop(self):
        if not state["armed"]:
            return False
        try:
            pc = int(gdb.selected_frame().pc())
            what = secret_operands(self.site["mnemonic"], self.site["operands"], pc)
        except Exception as exc:                       # fail closed
            out["errors"].append(f"{self.key}: {type(exc).__name__}: {exc}")
            self.enabled = False
            return False
        if self.selftest:
            out["selftest"].append(bool(what))
            return False
        r = out["sites"][self.key]
        r["checked"] += 1
        if what:
            r["secret"] += 1
            r["what"] = sorted(set(r["what"]) | set(what))
        if r["checked"] >= cfg["max_checks"]:
            r["capped"] = True
            self.enabled = False
        return False


def exited(event):
    out["exit_code"] = getattr(event, "exit_code", None)


try:
    gdb.execute("set pagination off")
    gdb.execute("set confirm off")
    gdb.execute("set remote noack-packet off")       # gdb 15 with vgdb 3.22 needs it
    gdb.execute(f"target remote | vgdb --wait=10 --pid={cfg['pid']}")
    out["connected"] = True
    # Valgrind's gdbserver stops at every memcheck error once gdb is attached;
    # the errors are ct_audit's business, so let them pass.
    gdb.execute("monitor v.set vgdb-error 999999999", to_string=True)
    gdb.events.exited.connect(exited)
    gdb.Breakpoint("pqv_ct_loaded", internal=True)
    gdb.execute("continue")
    try:
        bias = int(gdb.parse_and_eval("load_bias"))
    except gdb.error:
        bias = int(gdb.parse_and_eval("$rdi"))
    for bp in list(gdb.breakpoints()):
        bp.delete()
    start = int(gdb.parse_and_eval(f"&{cfg['selftest']['fn']}").cast(gdb.lookup_type("long")))
    Division("selftest", start + cfg["selftest"]["rel"], cfg["selftest"], selftest=True)
    for s in cfg["sites"]:
        Division(f"{s['fn']}+{s['offset'] - s['fn_start']:#x}", bias + s["offset"], s)
    Flag("pqv_ct_armed", True)
    Flag("pqv_ct_disarmed", False)
    for _ in range(64):                              # until the driver exits
        if out["exit_code"] is not None:
            break
        gdb.execute("continue")
except Exception as exc:
    out["errors"].append(f"gdb: {type(exc).__name__}: {exc}")
save()
'''


def _kill_group(proc):
    if proc is not None and proc.poll() is None:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except OSError:
            proc.kill()
        proc.wait()


def run(exe, args, lib_sites, selftest, timeout=600, max_checks=MAX_CHECKS):
    """One driver run under memcheck with gdb on its divisions. `selftest` is
    the driver's own division ({fn, rel, mnemonic, operands}). Returns the
    gdb side's record; a run gdb could not attach to is retried once (the
    vgdb handshake is occasionally refused)."""
    why = available()
    if why:
        raise Unavailable(why)
    work = tempfile.mkdtemp(prefix="pqv-div-")
    try:
        script = os.path.join(work, "div.py")
        with open(script, "w") as fh:
            fh.write(GDB_SCRIPT)
        result = None
        for attempt in (1, 2):
            out = os.path.join(work, f"out{attempt}.json")
            cfg = os.path.join(work, f"cfg{attempt}.json")
            vg = None
            try:
                with open(os.path.join(work, f"valgrind{attempt}.log"), "w") as log:
                    vg = subprocess.Popen(["valgrind", *VALGRIND, exe, *args],
                                          stdout=subprocess.DEVNULL, stderr=log,
                                          start_new_session=True)
                with open(cfg, "w") as fh:
                    json.dump({"pid": vg.pid, "sites": lib_sites, "selftest": selftest,
                               "out": out, "max_checks": max_checks}, fh)
                try:
                    subprocess.run([shutil.which("gdb"), "-batch", "-nx",
                                    "-iex", "set auto-load off",
                                    "-ex", f'set $pqv_cfg = "{cfg}"',
                                    "-ex", f"file {exe}", "-ex", f"source {script}"],
                                   stdin=subprocess.DEVNULL, capture_output=True,
                                   timeout=timeout, start_new_session=True)
                except subprocess.TimeoutExpired:
                    return {"errors": [f"the run did not finish within {timeout:g} s"],
                            "selftest": [], "sites": {}}
            finally:
                _kill_group(vg)
            try:
                with open(out) as fh:
                    result = json.load(fh)
            except (OSError, ValueError):
                result = {"errors": ["gdb wrote no result"], "selftest": [], "sites": {},
                          "connected": False}
            if result.get("connected") or attempt == 2:
                return result
        return result
    finally:
        shutil.rmtree(work, ignore_errors=True)


def judge(result):
    """(secret_sites, why_not): the sites whose operands carried secret bits
    while secrets were live, and why the run cannot vouch for silence (None
    when it can). Pure, so the rules are testable without a debugger."""
    if result.get("errors"):
        return [], "the secret-division check failed: " + "; ".join(result["errors"][:3])
    if result.get("exit_code") not in (0,):
        return [], f"the driver did not exit normally under the check ({result.get('exit_code')})"
    if result.get("selftest") != [True, False]:
        return [], ("the secret-division check's self-test was not reported as it must "
                    f"be (a secret and a public division read as {result.get('selftest')})")
    secret = [dict(s, site=k) for k, s in sorted(result.get("sites", {}).items())
              if s.get("secret")]
    return secret, None


def selftest_site(exe_disassembly):
    """The driver's own division, relative to its function's start."""
    for s in sites(exe_disassembly):
        if s["fn"] == SELFTEST_FN:
            return {"fn": SELFTEST_FN, "rel": s["offset"] - s["fn_start"],
                    "mnemonic": s["mnemonic"], "operands": s["operands"]}
    raise Unavailable("the driver's self-test division was not found in its code")
