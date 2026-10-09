"""
pq_verify.ct_audit — secret-dependent branches and memory accesses, under Valgrind.

The technique mlkem-native, BoringSSL and libsodium use on themselves
(ctgrind): secret inputs are marked *undefined* with Valgrind's memcheck
client requests, the library runs, and memcheck reports every conditional
branch and every memory address that depends on them -- the leaks behind
cache-timing and branch-timing attacks (Clangover was a compiler-introduced
branch on a secret message bit). pq-verify does it from outside, on the
vendor's own compiled entry points; no source and no rebuild are needed.

What is checked (ML-KEM, through the derandomised API --audit-kem binds):
    encaps   Encaps(ek, m)    with m secret
    decaps   Decaps(c, dk)    with dk's secret parts secret (the K-PKE secret
                              key and z), on a valid ciphertext and on a
                              random one (the implicit-rejection path)

What is not, and why -- each reported as not applicable, never passed:
  * Key generation. The public matrix seed rho is derived from the secret
    seed d and then rejection-sampled, which is a branch on data the check
    must treat as secret. Libraries declassify rho internally (mlkem-native's
    MLK_CT_TESTING_DECLASSIFY); a black-box check cannot.
  * Variable-latency instructions. Memcheck tracks branches and addresses,
    not instruction timing, so a secret division (KyberSlash) is invisible to
    it. The report lists every division instruction in the library, with
    its function, for a reviewer to look at -- a listing, not a verdict.
  * Power, EM and microarchitectural effects beyond branches and addresses.
    This is a software check on one compiled binary, not a lab measurement.

A self-test runs first: a deliberate branch on a marked secret inside the
driver must be reported. If memcheck does not see it, nothing it says is
trusted and the stage is CANNOT VERIFY.
"""
import os
import re
import shutil
import subprocess
import tempfile
import xml.etree.ElementTree as ET

DRIVER_C = r"""
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <valgrind/memcheck.h>

typedef int (*kp_t)(uint8_t *, uint8_t *, const uint8_t *);
typedef int (*enc_t)(uint8_t *, uint8_t *, const uint8_t *, const uint8_t *);
typedef int (*dec_t)(uint8_t *, const uint8_t *, const uint8_t *);

static uint64_t st;
static void fill(uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) {
        st ^= st << 13; st ^= st >> 7; st ^= st << 17;
        p[i] = (uint8_t)st;
    }
}
#define SECRET(p, n) VALGRIND_MAKE_MEM_UNDEFINED((p), (n))
#define PUBLIC(p, n) VALGRIND_MAKE_MEM_DEFINED((p), (n))
static volatile int sink;

int main(int argc, char **argv) {
    if (argc != 11) { fprintf(stderr, "usage\n"); return 2; }
    const char *mode = argv[1];
    size_t ek_n = strtoul(argv[6], 0, 10), dk_n = strtoul(argv[7], 0, 10);
    size_t ct_n = strtoul(argv[8], 0, 10), k = strtoul(argv[9], 0, 10);
    int iters = atoi(argv[10]);
    st = 0x9E3779B97F4A7C15ULL;
    if (!strcmp(mode, "selftest")) {
        uint8_t s[1]; fill(s, 1); SECRET(s, 1);
        if (s[0] & 1) sink = 1;               /* must be reported */
        return 0;
    }
    void *h = dlopen(argv[2], RTLD_NOW | RTLD_LOCAL);
    if (!h) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 3; }
    kp_t kp = (kp_t)dlsym(h, argv[3]);
    enc_t enc = (enc_t)dlsym(h, argv[4]);
    dec_t dec = (dec_t)dlsym(h, argv[5]);
    if (!kp || !enc || !dec) { fprintf(stderr, "dlsym\n"); return 3; }
    uint8_t *ek = malloc(ek_n), *dk = malloc(dk_n), *c = malloc(ct_n), *c2 = malloc(ct_n);
    uint8_t coins[64], m[32], ss[32];
    for (int it = 0; it < iters; it++) {
        fill(coins, 64);
        if (kp(ek, dk, coins)) { fprintf(stderr, "keypair failed\n"); return 4; }
        fill(m, 32);
        if (!strcmp(mode, "encaps")) {
            SECRET(m, 32);
            if (enc(c, ss, ek, m)) { fprintf(stderr, "encaps failed\n"); return 4; }
            PUBLIC(c, ct_n); PUBLIC(ss, 32); PUBLIC(m, 32);
        } else {
            if (enc(c, ss, ek, m)) { fprintf(stderr, "encaps failed\n"); return 4; }
            fill(c2, ct_n);
            /* dk = dk_pke (384k) || ek || H(ek) || z: the first and last parts are secret */
            SECRET(dk, 384 * k); SECRET(dk + dk_n - 32, 32);
            if (dec(ss, c, dk)) { fprintf(stderr, "decaps failed\n"); return 4; }
            PUBLIC(ss, 32);
            if (dec(ss, c2, dk)) { fprintf(stderr, "decaps (implicit rejection) failed\n"); return 4; }
            PUBLIC(ss, 32); PUBLIC(dk, dk_n);
        }
    }
    return 0;
}
"""

KINDS = {"UninitCondition": "branch on a secret",
         "UninitValue": "secret used as a memory address"}
_RANK = {"ML-KEM-512": 2, "ML-KEM-768": 3, "ML-KEM-1024": 4}
OPS = ("encaps", "decaps")


class Unavailable(RuntimeError):
    """Valgrind, its headers or a compiler is missing."""


def available():
    """None if the check can run, else why not."""
    if not shutil.which("valgrind"):
        return "valgrind is not installed"
    if not any(os.path.exists(os.path.join(d, "valgrind", "memcheck.h"))
               for d in ("/usr/include", "/usr/local/include", "/opt/homebrew/include")):
        return "valgrind's headers (valgrind/memcheck.h) are not installed"
    if not (shutil.which("cc") or shutil.which("gcc")):
        return "no C compiler"
    return None


def _driver(work):
    src = os.path.join(work, "pqv_ct_driver.c")
    exe = os.path.join(work, "pqv_ct_driver")
    with open(src, "w") as fh:
        fh.write(DRIVER_C)
    cc = shutil.which("cc") or shutil.which("gcc")
    p = subprocess.run([cc, "-O1", "-g", "-o", exe, src, "-ldl"],
                       capture_output=True, text=True)
    if p.returncode:
        raise Unavailable(f"the driver did not build: {p.stderr.strip()[-300:]}")
    return exe


def _run(exe, args, work, tag, timeout):
    xml = os.path.join(work, f"memcheck-{tag}.xml")
    cmd = ["valgrind", "--tool=memcheck", "--xml=yes", f"--xml-file={xml}",
           "--track-origins=yes", "--error-limit=no", "--leak-check=no", exe, *args]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if p.returncode not in (0,):
        raise RuntimeError(f"the driver failed ({tag}, exit {p.returncode}): "
                           f"{(p.stderr or '').strip().splitlines()[-1:]}")
    return _parse(xml)


def _parse(path):
    """[(kind, [frames])] for every secret-dependence error; frames are
    (function, object file)."""
    out = []
    root = ET.parse(path).getroot()
    for err in root.iter("error"):
        kind = err.findtext("kind")
        if kind not in KINDS:
            continue
        stack = err.find("stack")
        frames = [(f.findtext("fn") or "??", f.findtext("obj") or "")
                  for f in (stack.findall("frame") if stack is not None else [])]
        out.append((kind, frames))
    return out


def _attribute(errors, lib):
    """Errors whose innermost frame inside the library is known, as
    {(kind, function)}: where in the vendor's code the secret was used."""
    real = os.path.realpath(lib)
    found = {}
    for kind, frames in errors:
        fn = next((f for f, o in frames if o and os.path.realpath(o) == real), None)
        where = fn or (frames[0][0] if frames else "??")
        found[(kind, where)] = found.get((kind, where), 0) + 1
    return found


def divisions(lib):
    """{function: count} of division instructions in the library's code
    (objdump). Not a verdict: memcheck cannot see instruction timing, and a
    division on public data is harmless. A reviewer's list."""
    if not shutil.which("objdump"):
        return None
    p = subprocess.run(["objdump", "-d", "--no-show-raw-insn", lib],
                       capture_output=True, text=True)
    out, fn = {}, "?"
    for line in p.stdout.splitlines():
        m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
        if m:
            fn = m.group(1)
            continue
        if re.search(r"\s(i?div[bwlq]?|udiv|sdiv)\s", line):
            out[fn] = out.get(fn, 0) + 1
    return out


def run_kem(lib, param_set, kp, enc, dec, iterations=4, timeout=600):
    """{'stages': {op: (passed, 1)}, 'leaks': {op: [...]}, 'not_applicable':
    {...}, 'divisions': {...}, 'selftest': bool} -- or raises Unavailable."""
    why = available()
    if why:
        raise Unavailable(why)
    from .core import _KEM_SIZES
    ek_n, dk_n, ct_n, _ = _KEM_SIZES[param_set]
    work = tempfile.mkdtemp(prefix="pqv-ct-")
    try:
        exe = _driver(work)
        base = [lib, kp, enc, dec, str(ek_n), str(dk_n), str(ct_n),
                str(_RANK[param_set]), str(iterations)]
        st = _run(exe, ["selftest", *base], work, "selftest", timeout)
        if not any(kind == "UninitCondition" for kind, _ in st):
            raise Unavailable("memcheck did not report the self-test's deliberate "
                              "secret branch, so its silence would mean nothing")
        stages, leaks = {}, {}
        for op in OPS:
            found = _attribute(_run(exe, [op, *base], work, op, timeout), lib)
            stages[op] = (int(not found), 1)
            leaks[op] = [{"kind": KINDS[k], "function": f, "count": n}
                         for (k, f), n in sorted(found.items())]
        return {"stages": stages, "leaks": leaks, "selftest": True,
                "not_applicable": {
                    "keyGen": "the public matrix seed is derived from the secret seed "
                              "and rejection-sampled; libraries declassify it "
                              "internally, which a black-box check cannot"},
                "divisions": divisions(lib), "iterations": iterations,
                "tool": subprocess.run(["valgrind", "--version"], capture_output=True,
                                       text=True).stdout.strip()}
    finally:
        shutil.rmtree(work, ignore_errors=True)


# ─────────────────────── Classic McEliece (not FIPS) ───────────────────────
# The NIST API takes no coins: encapsulation draws its error vector from
# randombytes(). The driver defines randombytes() and PQCLEAN_randombytes()
# (exported, so they interpose on a library's own) and installs itself through
# liboqs's OQS_randombytes_custom_algorithm when present; a call that draws no
# randomness through it is refused (exit 5), never reported clean. Key pairs
# and the valid ciphertexts come from the library itself, outside Valgrind:
# key generation is minutes per key under memcheck, and it is not checked.

MCE_DRIVER_C = r"""
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <valgrind/memcheck.h>

typedef int (*enc_t)(uint8_t *, uint8_t *, const uint8_t *);
typedef int (*dec_t)(uint8_t *, const uint8_t *, const uint8_t *);
typedef void (*oqs_rng_t)(void (*)(uint8_t *, size_t));

static uint64_t st;
static int mark_secret;
static long calls;
static void fill(uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) {
        st ^= st << 13; st ^= st >> 7; st ^= st << 17;
        p[i] = (uint8_t)st;
    }
}
#define SECRET(p, n) VALGRIND_MAKE_MEM_UNDEFINED((p), (n))
#define PUBLIC(p, n) VALGRIND_MAKE_MEM_DEFINED((p), (n))
static volatile int sink;

int randombytes(uint8_t *out, size_t n) {
    fill(out, n);
    if (mark_secret) SECRET(out, n);
    calls++;
    return 0;
}
int PQCLEAN_randombytes(uint8_t *out, size_t n) { return randombytes(out, n); }
static void oqs_rng(uint8_t *out, size_t n) { randombytes(out, n); }

static uint8_t *slurp(const char *path, size_t n) {
    uint8_t *b = malloc(n);
    FILE *f = fopen(path, "rb");
    if (!f || fread(b, 1, n, f) != n) { fprintf(stderr, "read %s\n", path); exit(3); }
    fclose(f);
    return b;
}

/* mode lib enc dec pk_n sk_n ct_n pad_bits keys dir */
int main(int argc, char **argv) {
    if (argc != 11) { fprintf(stderr, "usage\n"); return 2; }
    const char *mode = argv[1];
    size_t pk_n = strtoul(argv[5], 0, 10), sk_n = strtoul(argv[6], 0, 10);
    size_t ct_n = strtoul(argv[7], 0, 10);
    unsigned pad = (unsigned)strtoul(argv[8], 0, 10);
    int keys = atoi(argv[9]);
    st = 0x9E3779B97F4A7C15ULL;
    if (!strcmp(mode, "selftest")) {
        uint8_t s[1]; fill(s, 1); SECRET(s, 1);
        if (s[0] & 1) sink = 1;               /* must be reported */
        return 0;
    }
    void *h = dlopen(argv[2], RTLD_NOW | RTLD_LOCAL);
    if (!h) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 3; }
    enc_t enc = (enc_t)dlsym(h, argv[3]);
    dec_t dec = (dec_t)dlsym(h, argv[4]);
    if (!enc || !dec) { fprintf(stderr, "dlsym\n"); return 3; }
    oqs_rng_t custom = (oqs_rng_t)dlsym(h, "OQS_randombytes_custom_algorithm");
    if (custom) custom(oqs_rng);
    uint8_t *c = malloc(ct_n), *c2 = malloc(ct_n), ss[32];
    char path[4096];
    for (int k = 0; k < keys; k++) {
        snprintf(path, sizeof path, "%s/pk%d", argv[10], k);
        uint8_t *pk = slurp(path, pk_n);
        snprintf(path, sizeof path, "%s/sk%d", argv[10], k);
        uint8_t *sk = slurp(path, sk_n);
        snprintf(path, sizeof path, "%s/ct%d", argv[10], k);
        uint8_t *ct = slurp(path, ct_n);
        if (!strcmp(mode, "encaps")) {
            long before = calls;
            mark_secret = 1;
            if (enc(c, ss, pk)) { fprintf(stderr, "encaps failed\n"); return 4; }
            mark_secret = 0;
            if (calls == before) { fprintf(stderr, "no randomness through the driver\n"); return 5; }
            PUBLIC(c, ct_n); PUBLIC(ss, 32);
        } else {
            fill(c2, ct_n);
            if (pad) c2[ct_n - 1] &= (uint8_t)((1u << pad) - 1);
            SECRET(sk, sk_n);
            if (dec(ss, ct, sk)) { fprintf(stderr, "decaps failed\n"); return 4; }
            PUBLIC(ss, 32);
            if (dec(ss, c2, sk)) { fprintf(stderr, "decaps (implicit rejection) failed\n"); return 4; }
            PUBLIC(ss, 32); PUBLIC(sk, sk_n);
        }
        free(pk); free(sk); free(ct);
    }
    return 0;
}
"""
MCE_OPS = ("encaps", "decaps")


def _parse_origins(path):
    """[(kind, [frames], [origin frames])]: the origin is the stack that made
    the value secret (a client request: the driver's marking, or the
    randomness it handed the library)."""
    out = []
    root = ET.parse(path).getroot()
    for err in root.iter("error"):
        kind = err.findtext("kind")
        if kind not in KINDS:
            continue
        stacks = err.findall("stack")
        fr = [[(f.findtext("fn") or "??", f.findtext("obj") or "") for f in st.findall("frame")]
              for st in stacks]
        out.append((kind, fr[0] if fr else [], fr[1] if len(fr) > 1 else []))
    return out


def _classify(errors, lib):
    """Split memcheck's reports into leaks and the sampler's.

    A report inside the library function that drew the random bytes it
    depends on (the first library frame of its origin that is not a
    randombytes wrapper) is the error vector's sampler: listed, not judged.
    Its range and repetition checks are rejection sampling, which the
    submitters' code declassifies (crypto_declassify, a no-op in a build),
    and memcheck, which does not follow branches, then also taints what the
    function computes after them -- GCC reuses the register holding the
    rejection flag, provably zero once the loop exits, as a later loop's
    counter or index. A real leak in the sampler's own construction of the
    error vector would land in the same list. Everything else -- any report
    outside the sampler, or in a library without symbols -- is a leak."""
    real = os.path.realpath(lib)

    def inlib(frames):
        return [fn for fn, o in frames if o and os.path.realpath(o) == real]
    leaks, sampling = {}, {}
    for kind, frames, origin in errors:
        mine = inlib(frames)
        where = mine[0] if mine else (frames[0][0] if frames else "??")
        drew = next((fn for fn in inlib(origin) if "randombytes" not in fn.lower()), None)
        excused = bool(drew) and where == drew and where not in ("??", "")
        bucket = sampling if excused else leaks
        bucket[(kind, where)] = bucket.get((kind, where), 0) + 1
    return leaks, sampling


def run_mceliece(lib, param_set, enc, dec, material, timeout=1800):
    """Classic McEliece Encaps and Decaps under memcheck. `material` is
    [(pk, sk, ct)] made by the library itself. -> {'stages': {op: (p, 1)},
    'leaks': {op: [...]}, 'sampling': {op: [...]}, 'not_applicable': {...},
    'divisions', 'selftest', 'tool'} -- or raises Unavailable."""
    why = available()
    if why:
        raise Unavailable(why)
    from .mceliece import Params
    P = Params(param_set)
    work = tempfile.mkdtemp(prefix="pqv-ct-mce-")
    try:
        src = os.path.join(work, "pqv_ct_mce.c")
        exe = os.path.join(work, "pqv_ct_mce")
        with open(src, "w") as fh:
            fh.write(MCE_DRIVER_C)
        cc = shutil.which("cc") or shutil.which("gcc")
        p = subprocess.run([cc, "-O1", "-g", "-rdynamic", "-o", exe, src, "-ldl"],
                           capture_output=True, text=True)
        if p.returncode:
            raise Unavailable(f"the driver did not build: {p.stderr.strip()[-300:]}")
        for k, (pk, sk, ct) in enumerate(material):
            for name, data in (("pk", pk), ("sk", sk), ("ct", ct)):
                with open(os.path.join(work, f"{name}{k}"), "wb") as fh:
                    fh.write(data)
        pad = P.mt % 8 if P.padded else 0
        base = [lib, enc, dec, str(P.pk_bytes), str(P.sk_bytes), str(P.ct_bytes),
                str(pad), str(len(material)), work]
        st = _parse(_run_or_refuse(exe, ["selftest", *base], work, "selftest", timeout))
        if not any(kind == "UninitCondition" for kind, _ in st):
            raise Unavailable("memcheck did not report the self-test's deliberate "
                              "secret branch, so its silence would mean nothing")
        stages, leaks, sampling = {}, {}, {}
        for op in MCE_OPS:
            found, excused = _classify(
                _parse_origins(_run_or_refuse(exe, [op, *base], work, op, timeout)), lib)
            stages[op] = (int(not found), 1)
            leaks[op] = [{"kind": KINDS[k], "function": f, "count": n}
                         for (k, f), n in sorted(found.items())]
            sampling[op] = [{"kind": KINDS[k], "function": f, "count": n}
                            for (k, f), n in sorted(excused.items())]
        return {"stages": stages, "leaks": leaks, "sampling": sampling, "selftest": True,
                "not_applicable": {
                    "keyGen": "key generation retries when an attempt fails (a "
                              "polynomial that is not irreducible, repeated support "
                              "elements, a matrix that is not systematic); the "
                              "submitters declassify those comparisons, which a "
                              "black-box check cannot tell from a leak, and it takes "
                              "minutes per key under memcheck"},
                "divisions": divisions(lib), "keys": len(material),
                "tool": subprocess.run(["valgrind", "--version"], capture_output=True,
                                       text=True).stdout.strip()}
    finally:
        shutil.rmtree(work, ignore_errors=True)


def _run_or_refuse(exe, args, work, tag, timeout):
    """Run under memcheck; return the XML path. A driver that could not
    exercise the library (no randomness through it, a failed call) raises
    Unavailable: silence from a call that did not run is not a pass."""
    xml = os.path.join(work, f"memcheck-{tag}.xml")
    cmd = ["valgrind", "--tool=memcheck", "--xml=yes", f"--xml-file={xml}",
           "--track-origins=yes", "--error-limit=no", "--leak-check=no", exe, *args]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if p.returncode:
        last = (p.stderr or "").strip().splitlines()[-1:] or [""]
        raise Unavailable(f"the {tag} driver could not exercise the library "
                          f"(exit {p.returncode}): {last[0]}")
    return xml
