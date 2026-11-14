"""
pq_verify.ct_fndsa -- FN-DSA (Falcon) signing under Valgrind memcheck.

Signing runs with the secret key and the signer's randomness marked secret,
and memcheck reports every branch and memory address that depends on them.
Falcon's signer branches on secret-derived values by design, and from
outside a compiled library nothing can be declared public mid-call, so each
branch memcheck reports is matched against a table of the sites the signer
takes by design (SITES): the function it is in, inlined or not, and the
source line its report names, read from the file the library's debug
information points to. There is no function-level exemption. GCC 13 inlines
fpr_floor into the sampler and compiles its branch-free select into a jump
on the centre, and an exemption for "the sampler" would have passed that.

    a branch at a listed site        listed with its reason, not judged
    any other branch                 a finding
    a secret memory address          a finding, wherever it is
    a branch with no source line,    CANNOT VERIFY: it cannot be matched
      or whose source is unreadable
    a secret operand memcheck needs  CANNOT VERIFY: a vector shift's count,
      public that is neither a         for one, which is not a branch
      branch nor an address

What is marked secret: the secret key after its header byte (the header
names the set), and every draw from the signer's randomness but the 40-byte
nonce, which the signature carries in clear. The driver takes the place of
the library's randombytes (PQClean, exported from the driver) or installs
itself through liboqs's custom-RNG hook. A signing call that draws nothing
secret through it is refused, never passed: the base sampler reads only the
PRNG, and unmarked randomness would hide a leak there.

Not checked, reported as not applicable: key generation, which draws (f, g)
and rejects them until the NTRU equation can be solved, branching on the
candidates by design. Verification handles public data only.

The self-test and memcheck's options are pq_verify.ct_audit's: a branch
and a discarded secret-indexed read, both of which must be reported.
"""
import ctypes
import os
import re
import shutil
import subprocess
import tempfile
import xml.etree.ElementTree as ET

from .ct_audit import (DISCARDED_READ_C, SELFTEST_KINDS, SELFTEST_MISSED, Unavailable,
                       _parse, _run_or_refuse, available, division_fields)

NONCE = 40
SIGNATURES = 4

DRIVER_C = r"""
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <valgrind/memcheck.h>

typedef int (*sg_t)(uint8_t *, size_t *, const uint8_t *, size_t, const uint8_t *);
typedef void (*oqs_rng_t)(void (*)(uint8_t *, size_t));
#define SECRET(p, n) VALGRIND_MAKE_MEM_UNDEFINED((p), (n))
#define PUBLIC(p, n) VALGRIND_MAKE_MEM_DEFINED((p), (n))
#define NONCE 40

static uint64_t st = 0x9E3779B97F4A7C15ULL;
static int marking;
static long secret_draws;
static volatile int sink;
@DISCARDED_READ@

static void fill(uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) {
        st ^= st << 13; st ^= st >> 7; st ^= st << 17;
        p[i] = (uint8_t)st;
    }
}

/* The signer's randomness. Exported, so that it takes the place of a
   library's own randombytes, and installed through liboqs's custom-RNG hook.
   The 40-byte draw is the nonce, which the signature carries in clear; every
   other draw while signing is secret. */
int randombytes(uint8_t *out, size_t n) {
    fill(out, n);
    if (marking && n != NONCE) {
        SECRET(out, n);
        secret_draws++;
    }
    return 0;
}
int PQCLEAN_randombytes(uint8_t *out, size_t n) { return randombytes(out, n); }
static void oqs_rng(uint8_t *out, size_t n) { randombytes(out, n); }

static uint8_t *slurp(const char *path, size_t n) {
    uint8_t *b = malloc(n);
    FILE *f = fopen(path, "rb");
    if (!b || !f || fread(b, 1, n, f) != n) { fprintf(stderr, "read %s\n", path); exit(3); }
    fclose(f);
    return b;
}

/* selftest
   sign LIB SIGN SK_BYTES SIG_CAPACITY SK_FILE COUNT */
int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "selftest")) {
        uint8_t s[1];
        s[0] = (uint8_t)(uintptr_t)argv;
        SECRET(s, 1);
        if (s[0] & 1) sink = 1;               /* a branch: must be reported */
        discarded_read(s);                    /* a discarded secret-indexed read:
                                                 must be reported too */
        return 0;
    }
    if (argc != 8 || strcmp(argv[1], "sign")) { fprintf(stderr, "usage\n"); return 2; }
    void *h = dlopen(argv[2], RTLD_NOW | RTLD_LOCAL);
    if (!h) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 3; }
    sg_t sg = (sg_t)dlsym(h, argv[3]);
    if (!sg) { fprintf(stderr, "dlsym %s\n", argv[3]); return 3; }
    oqs_rng_t custom = (oqs_rng_t)dlsym(h, "OQS_randombytes_custom_algorithm");
    if (custom) custom(oqs_rng);
    size_t sk_n = strtoul(argv[4], 0, 10), cap = strtoul(argv[5], 0, 10);
    int count = atoi(argv[7]);
    uint8_t *sk = slurp(argv[6], sk_n), *sig = malloc(cap), m[33];
    if (!sig || sk_n < 2) return 4;
    for (int i = 0; i < count; i++) {
        size_t siglen = cap;
        long before = secret_draws;
        fill(m, sizeof m);
        SECRET(sk + 1, sk_n - 1);             /* the header byte names the set */
        marking = 1;
        int rc = sg(sig, &siglen, m, sizeof m, sk);
        marking = 0;
        PUBLIC(&rc, sizeof rc); PUBLIC(&siglen, sizeof siglen);
        PUBLIC(sig, cap); PUBLIC(sk, sk_n);
        if (rc) { fprintf(stderr, "signing failed (returned %d)\n", rc); return 4; }
        if (secret_draws == before) {
            fprintf(stderr, "signing drew no randomness through the driver but the nonce\n");
            return 5;
        }
    }
    printf("signed %d\n", count);
    return 0;
}
"""
DRIVER_C = DRIVER_C.replace("@DISCARDED_READ@", DISCARDED_READ_C)

# The sites PQClean's Falcon signer branches at on secret-derived values by
# design (crypto_sign/falcon-*/clean and avx2 at 0586a82, and liboqs 0.16.0's
# copies, src/sig/falcon/pqclean_*): (function, source line) -> why. Both are
# compared without PQClean's namespace prefix (PQCLEAN_FALCON512_CLEAN_ and
# the like) and with runs of whitespace collapsed. For the clean code,
# liboqs's own Valgrind suppressions (tests/constant_time/sig/passes/
# falcon_sign) excuse the same sites for the same reasons.
_KEY = ("every valid key takes it the same way; only a malformed key leaves early")
_REJECT = ("the sampler's rejection: Falcon scales its acceptance probability (ccs) so "
           "that the number of tries does not depend on the centre or on sigma")
SITES = {
    ("trim_i8_decode", "if (w == -mask2) {"):
        "decoding the secret key, refusing the coefficient -2^(bits-1): " + _KEY,
    ("complete_private", "if (t2[u] == 0) {"):
        "recomputing G, refusing an f that is not invertible: " + _KEY,
    ("complete_private", "if (gi < -127 || gi > +127) {"):
        "recomputing G, refusing a G out of range: " + _KEY,
    ("BerExp", "} while (!w && i > 0);"):
        "BerExp's lazy comparison: one more random byte is compared with probability "
        "1/256, whatever the secret",
    ("sampler", "if (BerExp(&spc->p, x, ccs)) {"): _REJECT,
    # clang folds the sampler's test into BerExp's result and names this line
    ("BerExp", "return (int)(w >> 31);"): _REJECT,
    ("do_sign_dyn", "if (is_short_half(sqn, s2tmp, logn)) {"):
        "the norm bound: an accepted signature's norm follows from the signature and "
        "the public key; a candidate over the bound is discarded",
    ("comp_encode", "if (x[u] < -2047 || x[u] > +2047) {"):
        "encoding s2, which the signature carries",
    ("comp_encode", "if (t < 0) {"): "encoding s2, which the signature carries",
    ("comp_encode", "while (acc_len >= 8) {"): "encoding s2, which the signature carries",
    ("comp_encode", "if (acc_len > 0) {"): "encoding s2, which the signature carries",
}
POLICY = ("the sites of PQClean's Falcon signer, clean and AVX2, reviewed at 0586a82 "
          "and in liboqs 0.16.0")

_NS = re.compile(r"PQCLEAN_FALCON(?:PADDED)?\d+_[A-Z0-9]+_")
_CLONE = re.compile(r"\.(?:constprop|isra|part|cold|lto_priv)(?:\.\d+)*$")
_POINTER = ctypes.sizeof(ctypes.c_void_p)
KIND_LABELS = {"branch": "branch on a secret",
               "address": "secret used as a memory address",
               "operand": "secret used where memcheck needs a public value"}


def _name(fn):
    """A function name without PQClean's namespace or GCC's clone suffix."""
    return _CLONE.sub("", _NS.sub("", fn or "??"))


def normalise(text):
    """A source line as SITES holds it: no namespace, whitespace collapsed."""
    return " ".join(_NS.sub("", text).split())


def _frames(err):
    st = err.find("stack")
    out = []
    for f in (st.findall("frame") if st is not None else []):
        try:
            line = int(f.findtext("line") or 0)
        except ValueError:
            line = 0
        out.append({"fn": f.findtext("fn") or "??", "obj": f.findtext("obj") or "",
                    "dir": f.findtext("dir") or "", "file": f.findtext("file") or "",
                    "line": line})
    return out


def parse(path):
    """[(kind, frames, count)]: kind 'branch', 'address' (a value of the
    pointer's size, which memcheck checks for an address or a jump target) or
    'operand' (any other size: a vector shift's count, for one)."""
    root = ET.parse(path).getroot()
    counts = {}
    for pair in root.iter("pair"):
        u = pair.findtext("unique")
        if u is not None:
            try:
                counts[u] = int(pair.findtext("count") or 1)
            except ValueError:
                counts[u] = 1
    out = []
    for err in root.iter("error"):
        kind = err.findtext("kind")
        if kind == "UninitCondition":
            k = "branch"
        elif kind == "UninitValue":
            m = re.search(r"of size (\d+)", err.findtext("what") or "")
            k = "address" if not m or int(m.group(1)) == _POINTER else "operand"
        else:
            continue
        out.append((k, _frames(err), counts.get(err.findtext("unique"), 1)))
    return out


def _source_line(frame, cache):
    """(normalised text of the frame's source line, None) or (None, why not)."""
    if not frame["file"] or frame["line"] <= 0:
        return None, ("no source line for it in the library's debug information (built "
                      "without -g, or the compiler gave this instruction none)")
    path = os.path.join(frame["dir"], frame["file"]) if frame["dir"] else frame["file"]
    if path not in cache:
        try:
            with open(path, encoding="utf-8", errors="replace") as fh:
                cache[path] = fh.read().splitlines()
        except OSError:
            cache[path] = None
    lines = cache[path]
    if lines is None:
        return None, f"its source, {path}, is not readable"
    if frame["line"] > len(lines):
        return None, f"{path} has no line {frame['line']}"
    return normalise(lines[frame["line"] - 1]), None


def judge(errors, lib):
    """Sort memcheck's reports: ({site: count} intended, findings, unjudged),
    each site (kind, function, file:line or None) with its reason."""
    real = os.path.realpath(lib)
    intended, findings, unjudged, cache = {}, {}, {}, {}

    def add(bucket, key, n, why):
        c, _ = bucket.get(key, (0, why))
        bucket[key] = (c + n, why)

    for kind, frames, n in errors:
        mine = [f for f in frames if f["obj"] and os.path.realpath(f["obj"]) == real]
        site = mine[0] if mine else (frames[0] if frames else None)
        fn = _name(site["fn"]) if site else "??"
        where = (f"{os.path.basename(site['file'])}:{site['line']}"
                 if site and site["file"] and site["line"] > 0 else None)
        key = (kind, fn, where)
        if kind == "address":
            add(findings, key, n, "a secret memory address is never by design")
        elif kind == "operand":
            add(unjudged, key, n, "memcheck needs this operand public, and it is neither a "
                                  "branch nor an address, so it is not judged")
        elif not mine:
            add(unjudged, key, n, "not in the library's own code")
        else:
            text, why_not = _source_line(site, cache)
            if text is None:
                add(unjudged, key, n, why_not)
            elif (fn, text) in SITES:
                add(intended, key, n, SITES[(fn, text)])
            else:
                add(findings, key, n, "not a site the signer takes by design")
    return intended, findings, unjudged


def _listing(bucket):
    return [{"kind": KIND_LABELS[k], "function": fn, "where": where, "count": n, "why": why}
            for (k, fn, where), (n, why) in sorted(bucket.items(),
                                                   key=lambda kv: (kv[0][1], kv[0][2] or ""))]


def describe(site):
    """One report line for a listed site."""
    at = f" ({site['where']})" if site["where"] else ""
    return f"{site['kind']} in {site['function']}{at}, {site['count']:,} time(s)"


def run_fndsa(lib, param_set, sign_symbol, sk, sig_capacity, signatures=SIGNATURES,
              timeout=900):
    """Sign `signatures` messages under memcheck with `sk` (a key pair the
    library made, outside Valgrind) and judge the reports. -> {'stages':
    {'sign': (p, 1)} or {'cannot-verify': (0, 1)}, 'leaks', 'unjudged',
    'intended', 'not_applicable', 'signatures', 'policy', 'divisions',
    'divisions_not_listed', 'selftest', 'tool'} -- or raises Unavailable."""
    why = available()
    if why:
        raise Unavailable(why)
    work = tempfile.mkdtemp(prefix="pqv-ct-fndsa-")
    try:
        src = os.path.join(work, "pqv_ct_fndsa.c")
        exe = os.path.join(work, "pqv_ct_fndsa")
        with open(src, "w") as fh:
            fh.write(DRIVER_C)
        cc = shutil.which("cc") or shutil.which("gcc")
        p = subprocess.run([cc, "-O1", "-g", "-rdynamic", "-o", exe, src, "-ldl"],
                           capture_output=True, text=True)
        if p.returncode:
            raise Unavailable(f"the driver did not build: {p.stderr.strip()[-300:]}")
        skf = os.path.join(work, "sk")
        with open(skf, "wb") as fh:
            fh.write(sk)
        st = _parse(_run_or_refuse(exe, ["selftest"], work, "selftest", timeout))
        if not SELFTEST_KINDS <= {kind for kind, _ in st}:
            raise Unavailable(SELFTEST_MISSED)
        xml = _run_or_refuse(exe, ["sign", lib, sign_symbol, str(len(sk)),
                                   str(sig_capacity), skf, str(signatures)],
                             work, "sign", timeout)
        intended, findings, unjudged = judge(parse(xml), lib)
        if findings:
            stages = {"sign": (0, 1)}
        elif unjudged:
            stages = {"cannot-verify": (0, 1)}
        else:
            stages = {"sign": (1, 1)}
        return {"stages": stages, "leaks": _listing(findings), "unjudged": _listing(unjudged),
                "intended": _listing(intended), "signatures": signatures,
                "policy": POLICY, "selftest": True, "set": param_set,
                "not_applicable": {
                    "keyGen": "key generation draws (f, g) and rejects them until the "
                              "NTRU equation can be solved, branching on the candidates "
                              "by design"},
                **division_fields(lib),
                "tool": subprocess.run(["valgrind", "--version"], capture_output=True,
                                       text=True).stdout.strip()}
    finally:
        shutil.rmtree(work, ignore_errors=True)
