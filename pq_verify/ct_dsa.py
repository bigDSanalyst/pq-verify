"""
pq_verify.ct_dsa -- ML-DSA constant time, judged against the implementation's
own declarations of what is public. CONSTANT-TIME.md is the specification.

Sign branches on secret-derived values by design: its rejection loop decides
from them whether to discard an attempt, and each attempt's challenge hash is
public before the decision. A check that drives a compiled library from
outside can only mark values public after a call returns, so it cannot tell
those intended branches from a leak. This check therefore needs the library
built with its declassification annotations enabled and pq-verify's shim in
front of them (pq_verify/harness/ct): memcheck then sees every secret-
dependent branch and address inside the library, and the shim logs every
declassification with its call site, which the policy judges.

    hooked build     the library exports pqv_ct_mark: memcheck plus policy
    anything else    CANNOT VERIFY, with the reason; never a pass

The policy is a table of known sites for one implementation at one pinned
commit (mldsa-native at 159509d): each site's length, its place in the
attempt, and its value wherever the public key and signature determine it.
Any memcheck report is a finding, wherever it is: there is no function-level
exemption.
"""
import hashlib
import os
import shutil
import subprocess
import tempfile

from .ct_audit import (DISCARDED_READ_C, KINDS, MEMCHECK, SELFTEST_KINDS, SELFTEST_MISSED,
                       Unavailable, _attribute, _parse, available, divisions)
from .symbols import exported_functions

HARNESS_CT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "harness", "ct")
SHIM_C = os.path.join(HARNESS_CT, "pqv_ct_shim.c")

Q = 8380417
# FIPS 204 sizes and parameters. ctilde = lambda/4 bytes; w1 = one packed w1
# polynomial; g1, g2 = gamma1, gamma2.
SETS = {
    "ML-DSA-44": dict(k=4, l=4, pk=1312, sk=2560, sig=2420, ctilde=32, w1=192,
                      tau=39, g1=1 << 17, g2=(Q - 1) // 88),
    "ML-DSA-65": dict(k=6, l=5, pk=1952, sk=4032, sig=3309, ctilde=48, w1=128,
                      tau=49, g1=1 << 19, g2=(Q - 1) // 32),
    "ML-DSA-87": dict(k=8, l=7, pk=2592, sk=4896, sig=4627, ctilde=64, w1=128,
                      tau=60, g1=1 << 19, g2=(Q - 1) // 32),
}
PRE = b"\x00\x00"           # pure ML-DSA, empty context: M' = 0 || 0 || M
FLAGS = {"&z_invalid", "&w0_invalid", "&h_invalid"}
FLAG_VALUES = {0, 0xFFFFFFFF}

# The site table: mldsa-native at 159509d, portable C backend. Each entry is
# the source's own declaration (sign.c, poly_kl.c); CONSTANT-TIME.md,
# section 3, gives the source's justification for each.
POLICIES = {
    "mldsa-native": {
        "commit": "159509d78063316bf090bbcd0aa50af5bb03cf70",
        "keyGen": {("keypair_internal", "rho"), ("keypair_internal", "pk"),
                   ("mld_rej_eta_c", "&t_valid")},
        "sign": {("signature_internal", "rho"),
                 ("mld_attempt_signature_generation", "challenge_bytes"),
                 ("mld_compute_pack_z", "&z_invalid"),
                 ("mld_attempt_signature_generation", "&w0_invalid"),
                 ("mld_attempt_signature_generation", "&h_invalid"),
                 ("mld_attempt_signature_generation", "w0"),
                 ("mld_attempt_signature_generation", "w1_packed"),
                 ("mld_attempt_signature_generation", "sig")},
    },
}

DRIVER_C = r"""
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <valgrind/memcheck.h>

typedef int (*kp_t)(uint8_t *, uint8_t *, const uint8_t *);
typedef int (*sg_t)(uint8_t *, const uint8_t *, size_t, const uint8_t *, size_t,
                    const uint8_t *, const uint8_t *, int);
typedef void (*note_t)(const char *);
#define SECRET(p, n) VALGRIND_MAKE_MEM_UNDEFINED((p), (n))
#define PUBLIC(p, n) VALGRIND_MAKE_MEM_DEFINED((p), (n))
static volatile int sink;
@DISCARDED_READ@

static long unhex(const char *s, uint8_t *out, size_t max) {
    size_t n = strlen(s);
    while (n && (s[n - 1] == '\n' || s[n - 1] == '\r')) n--;
    if (n % 2 || n / 2 > max) return -1;
    for (size_t i = 0; i < n / 2; i++) {
        unsigned v;
        if (sscanf(s + 2 * i, "%2x", &v) != 1) return -1;
        out[i] = (uint8_t)v;
    }
    return (long)(n / 2);
}
static void puthex(FILE *f, const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) fprintf(f, "%02x", p[i]);
}

int main(int argc, char **argv) {
    /* selftest
       keygen LIB KP SG PKN SKN SIGN SEED OUT
       sign   LIB KP SG PKN SKN SIGN SEED OUT MSGS */
    if (argc == 2 && !strcmp(argv[1], "selftest")) {
        uint8_t s[1];
        s[0] = (uint8_t)(uintptr_t)argv;
        SECRET(s, 1);
        if (s[0] & 1) sink = 1;               /* a branch: must be reported */
        discarded_read(s);                    /* a discarded secret-indexed read:
                                                 must be reported too */
        return 0;
    }
    if (argc < 10) { fprintf(stderr, "usage\n"); return 2; }
    const char *mode = argv[1];
    void *h = dlopen(argv[2], RTLD_NOW | RTLD_LOCAL);
    if (!h) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 3; }
    kp_t kp = (kp_t)dlsym(h, argv[3]);
    sg_t sg = (sg_t)dlsym(h, argv[4]);
    note_t note = (note_t)dlsym(h, "pqv_ct_note");
    if (!kp || !sg || !note) { fprintf(stderr, "dlsym\n"); return 3; }
    size_t pk_n = strtoul(argv[5], 0, 10), sk_n = strtoul(argv[6], 0, 10);
    size_t sig_n = strtoul(argv[7], 0, 10);
    uint8_t seed[32], rnd[32], m[1024], pre[2] = {0, 0};
    if (unhex(argv[8], seed, 32) != 32) { fprintf(stderr, "seed\n"); return 2; }
    FILE *out = fopen(argv[9], "w");
    uint8_t *pk = malloc(pk_n), *sk = malloc(sk_n), *sig = malloc(sig_n);
    if (!out || !pk || !sk || !sig) return 4;
    if (!strcmp(mode, "keygen")) {
        SECRET(seed, 32);
        note("keygen begin");
        int rc = kp(pk, sk, seed);
        note("keygen end");
        PUBLIC(pk, pk_n); PUBLIC(sk, sk_n);
        fprintf(out, "rc %d\npk ", rc); puthex(out, pk, pk_n); fprintf(out, "\n");
        return 0;
    }
    if (strcmp(mode, "sign") || argc != 11) { fprintf(stderr, "usage\n"); return 2; }
    FILE *msgs = fopen(argv[10], "r");
    if (!msgs) return 4;
    note("setup begin");                      /* an unmarked key: no reports */
    if (kp(pk, sk, seed)) { fprintf(stderr, "keypair failed\n"); return 4; }
    note("setup end");
    char line[4096];
    int i = 0;
    while (fgets(line, sizeof line, msgs)) {
        long mlen = unhex(line, m, sizeof m);
        if (mlen < 0) { fprintf(stderr, "message %d\n", i); return 2; }
        memset(rnd, 0, sizeof rnd);
        SECRET(sk + 32, 32);                  /* K */
        SECRET(sk + 128, sk_n - 128);         /* s1, s2, t0 */
        SECRET(rnd, 32);
        char b[64];
        snprintf(b, sizeof b, "call %d begin", i); note(b);
        int rc = sg(sig, m, (size_t)mlen, pre, 2, rnd, sk, 0);
        snprintf(b, sizeof b, "call %d end", i); note(b);
        PUBLIC(sig, sig_n); PUBLIC(sk, sk_n); PUBLIC(rnd, 32);
        fprintf(out, "sig %d %d ", i, rc); puthex(out, sig, sig_n); fprintf(out, "\n");
        i++;
    }
    fprintf(out, "pk "); puthex(out, pk, pk_n);
    fprintf(out, "\nsk "); puthex(out, sk, sk_n); fprintf(out, "\n");
    fclose(out);
    return 0;
}
"""

DRIVER_C = DRIVER_C.replace("@DISCARDED_READ@", DISCARDED_READ_C)


class NotHooked(Exception):
    """The library was not built with pq-verify's shim and its annotations, or
    no policy covers it: CANNOT VERIFY."""


def shim_include():
    """The directory to put first on a library's include path."""
    return HARNESS_CT


def shim_source():
    """The shim's C file, to link into the library."""
    return SHIM_C


def hooked(lib):
    """True if the library carries pq-verify's shim."""
    return "pqv_ct_mark" in exported_functions(lib)


def policy_for(lib, exported=None):
    """The site table's name for this library, or None."""
    exported = exported_functions(lib) if exported is None else exported
    if any(e.startswith("PQCP_MLDSA_NATIVE") for e in exported):
        return "mldsa-native"
    return None


# --- FIPS 204 arithmetic, for the one comparison that needs it: w0 on the
# accepting attempt, from the public key and the signature alone.

_ZETAS = [pow(1753, int(f"{i:08b}"[::-1], 2), Q) for i in range(256)]


def _ntt(f):
    """FIPS 204, Algorithm 41."""
    w, m, n = [x % Q for x in f], 0, 128
    while n >= 1:
        for start in range(0, 256, 2 * n):
            m += 1
            z = _ZETAS[m]
            for j in range(start, start + n):
                t = z * w[j + n] % Q
                w[j + n] = (w[j] - t) % Q
                w[j] = (w[j] + t) % Q
        n //= 2
    return w


def _intt(w):
    """FIPS 204, Algorithm 42."""
    f, m, n = list(w), 256, 1
    while n < 256:
        for start in range(0, 256, 2 * n):
            m -= 1
            z = Q - _ZETAS[m]
            for j in range(start, start + n):
                t = f[j]
                f[j] = (t + f[j + n]) % Q
                f[j + n] = z * (t - f[j + n]) % Q
        n *= 2
    return [8347681 * x % Q for x in f]


def _unpack(data, bits, count=256):
    """SimpleBitUnpack: little-endian fields of `bits` bits."""
    x, mask = int.from_bytes(data, "little"), (1 << bits) - 1
    return [(x >> (bits * i)) & mask for i in range(count)]


def _rej_ntt_poly(seed):
    """FIPS 204, Algorithm 30 (RejNTTPoly)."""
    n = 840
    while True:
        buf, out = hashlib.shake_128(seed).digest(n), []
        for i in range(0, n - 2, 3):
            v = buf[i] | buf[i + 1] << 8 | (buf[i + 2] & 0x7F) << 16
            if v < Q:
                out.append(v)
                if len(out) == 256:
                    return out
        n *= 2


def _sample_in_ball(ctilde, tau):
    """FIPS 204, Algorithm 29 (SampleInBall)."""
    n = 8 + 256
    while True:
        buf = hashlib.shake_256(ctilde).digest(n)
        signs, pos, c = int.from_bytes(buf[:8], "little"), 8, [0] * 256
        for i in range(256 - tau, 256):
            while pos < n and buf[pos] > i:
                pos += 1
            if pos == n:
                break
            j = buf[pos]
            pos += 1
            c[i], c[j] = c[j], 1 - 2 * (signs >> (i + tau - 256) & 1)
        else:
            return c
        n *= 2


def w0_public(pk, sig, w1_packed, P):
    """[k][256] w0 - c*s2 + c*t0 mod q, the value mldsa-native declassifies as
    w0, as anyone can compute it from the public key and the signature:
    Az - c*t1*2^d - 2*gamma2*w1 (Az - c*t1*2^d = Ay - c*s2 + c*t0)."""
    k, ell, ct = P["k"], P["l"], P["ctilde"]
    zbits = 18 if P["g1"] == 1 << 17 else 20
    zlen, wlen = 32 * zbits, P["w1"]
    t1 = [_unpack(pk[32 + 320 * r:32 + 320 * (r + 1)], 10) for r in range(k)]
    zh = [_ntt([P["g1"] - u for u in _unpack(sig[ct + zlen * s:ct + zlen * (s + 1)], zbits)])
          for s in range(ell)]
    w1 = [_unpack(w1_packed[wlen * r:wlen * (r + 1)], 6 if wlen == 192 else 4) for r in range(k)]
    ch = _ntt(_sample_in_ball(sig[:ct], P["tau"]))
    out = []
    for r in range(k):
        t1h = _ntt([x << 13 for x in t1[r]])
        acc = [-ch[j] * t1h[j] for j in range(256)]
        for s in range(ell):
            a, b = _rej_ntt_poly(pk[:32] + bytes([s, r])), zh[s]
            for j in range(256):
                acc[j] += a[j] * b[j]
        w = _intt([x % Q for x in acc])
        out.append([(w[j] - 2 * P["g2"] * w1[r][j]) % Q for j in range(256)])
    return out


# --- the log and the policy

def _norm(fn, expr):
    """A site: (function, expression), with the API's namespace prefix and the
    annotation macro's enclosing parentheses removed."""
    e = expr.strip()
    while e.startswith("(") and e.endswith(")"):
        e = e[1:-1].strip()
    for api in ("keypair_internal", "signature_internal"):
        if fn.endswith("_" + api) or fn == api:
            return api, e
    return fn, e


def parse_log(path):
    """[event]: ('N', text) for a driver note, or
    (kind, (function, expression), length, bytes, 'file:line') with kind 'S'
    for a secret mark and 'D' for a declassification."""
    out = []
    if not os.path.exists(path):
        return out
    with open(path) as fh:
        for raw in fh:
            f = raw.rstrip("\n").split("\t")
            if f[0] == "N" and len(f) > 1:
                out.append(("N", f[1]))
            elif f[0] in ("S", "D") and len(f) >= 5:
                data = bytes.fromhex(f[5]) if f[0] == "D" and len(f) > 5 else b""
                out.append((f[0], _norm(f[1], f[3]), int(f[4]), data, f[2]))
    return out


def segments(events):
    """{name: [events]} between the driver's 'X begin' and 'X end' notes, and
    under None every event outside them."""
    seg, cur = {None: []}, None
    for e in events:
        if e[0] == "N":
            words = e[1].split()
            if words and words[-1] == "begin":
                cur = " ".join(words[:-1])
                seg[cur] = []
            elif words and words[-1] == "end":
                cur = None
            continue
        seg[cur].append(e)
    return seg


def _site_counts(events):
    out = {}
    for e in events:
        if e[0] == "D":
            key = f"{e[1][0]}: {e[1][1]}"
            out[key] = out.get(key, 0) + 1
    return out


def attempt_stats(events, rc=0):
    """{'attempts', 'hint_rejections'} for one signing call, from where its
    challenges and w1 encodings were declassified."""
    reached = []                # per attempt: did it declassify w1_packed?
    for e in events:
        if e[0] == "D" and e[1][1] == "challenge_bytes":
            reached.append(False)
        elif e[0] == "D" and e[1][1] == "w1_packed" and reached:
            reached[-1] = True
    rejected = reached[:-1] if rc == 0 else reached
    return {"attempts": len(reached), "hint_rejections": sum(rejected)}


def label(stats):
    """How a signing call went, for a reader."""
    if stats["attempts"] == 1:
        return "accepted at its first attempt"
    hint = ", with a hint-weight rejection" if stats["hint_rejections"] else ""
    return f"{stats['attempts']} attempts{hint}"


def _finder():
    found = []

    def find(msg):
        if msg not in found:
            found.append(msg)
    return found, find


def check_keygen(events, pk, P, policy="mldsa-native"):
    """Policy findings for one key generation."""
    allowed = POLICIES[policy]["keyGen"]
    findings, find = _finder()
    rho = pkn = accepted = 0
    for _kind, site, n, data, where in (e for e in events if e[0] == "D"):
        name = f"{site[0]} ({site[1]})"
        if site not in allowed:
            find(f"declassified at an undocumented site: {name} at {where}")
            continue
        if pkn:
            find(f"{name} declassified after the public key")
        if site[1] == "rho":
            rho += 1
            if n != 32 or data != pk[:32]:
                find("rho declassified is not the public key's rho")
        elif site[1] == "pk":
            pkn += 1
            if data != pk:
                find("the public key declassified is not the one returned")
        else:
            if not rho:
                find(f"{name} declassified before rho")
            v = int.from_bytes(data, "little") if n == 4 else None
            if v not in (0, 1):
                find("a rejection-sampling outcome for s1 or s2 is not 0 or 1")
            accepted += v == 1
    if rho != 1:
        find(f"rho declassified {rho} times, expected once")
    if pkn != 1:
        find(f"the public key declassified {pkn} times, expected once")
    # Every coefficient of s1 and s2 passes one declassified decision. The
    # four-way sampler also draws one discarded polynomial for ML-DSA-65 and
    # -87, and a polynomial's last byte can end with one unused acceptance.
    polys = P["k"] + P["l"]
    drawn = -(-polys // 4) * 4
    if not 256 * polys <= accepted <= 257 * drawn:
        find(f"{accepted} accepted sampling outcomes: s1 and s2 need {256 * polys}, "
             f"and {drawn} polynomials drawn in fours allow at most {257 * drawn}")
    return findings


def check_sign(events, sig, sk, message, P, policy="mldsa-native", rc=0, pk=None):
    """(findings, stats) for one signing call, against the site table and the
    attempt structure of CONSTANT-TIME.md, section 3. With the public key,
    the accepting attempt's w0 is compared too."""
    allowed = POLICIES[policy]["sign"]
    k, ell, ct_n, w1_n = P["k"], P["l"], P["ctilde"], P["k"] * P["w1"]
    mu = hashlib.shake_256(sk[64:128] + PRE + message).digest(64)
    findings, find = _finder()
    attempts, cur, rho = [], None, 0
    for _kind, site, n, data, where in (e for e in events if e[0] == "D"):
        name, what = f"{site[0]} ({site[1]})", site[1]
        if site not in allowed:
            find(f"declassified at an undocumented site: {name} at {where}")
            continue
        if what == "rho":
            rho += 1
            if attempts:
                find("rho declassified after the first attempt began")
            if n != 32 or data != sk[:32]:
                find("rho declassified is not the key's public rho")
            continue
        if what == "challenge_bytes":
            if n != ct_n:
                find(f"a challenge of {n} bytes, expected {ct_n}")
            cur = {"ctilde": data, "z": [], "w0f": [], "hf": [], "w0": None,
                   "w1": None, "sig": None, "rejected": False}
            attempts.append(cur)
            continue
        if cur is None:
            find(f"{name} declassified before the first attempt began")
            continue
        if cur["rejected"]:
            find(f"{name} declassified after a check rejected its attempt")
            continue
        if what in FLAGS:
            v = int.from_bytes(data, "little") if n == 4 else None
            if v not in FLAG_VALUES:
                find(f"{name} is not 0 or 0xFFFFFFFF")
            if cur["w0"] is not None or cur["w1"] is not None or cur["sig"] is not None:
                find(f"{name} declassified after w0, w1_packed or the signature")
            if what == "&z_invalid":
                if cur["w0f"]:
                    find("a z check after the w0 and h checks began")
                cur["z"].append(v)
            elif what == "&w0_invalid":
                if len(cur["z"]) != ell:
                    find("a w0 check before every z check passed")
                if len(cur["w0f"]) != len(cur["hf"]):
                    find("the w0 and h checks out of turn")
                cur["w0f"].append(v)
            else:
                if len(cur["hf"]) + 1 != len(cur["w0f"]):
                    find("the w0 and h checks out of turn")
                cur["hf"].append(v)
            if len(cur["z"]) > ell or len(cur["w0f"]) > k or len(cur["hf"]) > k:
                find(f"more {name} checks than polynomials")
            if v != 0:
                cur["rejected"] = True
            continue
        passed = len(cur["z"]) == ell and len(cur["w0f"]) == k and len(cur["hf"]) == k
        if what in ("w0", "w1_packed"):
            key, want = ("w0", k * 1024) if what == "w0" else ("w1", w1_n)
            if not passed:
                find(f"{name} declassified before every check of its attempt passed")
            if cur[key] is not None:
                find(f"{name} declassified twice in one attempt")
            if cur["sig"] is not None:
                find(f"{name} declassified after the signature")
            if n != want:
                find(f"{name} of {n} bytes, expected {want}")
            elif key == "w1" and hashlib.shake_256(mu + data).digest(ct_n) != cur["ctilde"]:
                find("w1_packed declassified does not hash to its attempt's challenge")
            cur[key] = data
            continue
        # the signature
        if cur["w0"] is None or cur["w1"] is None:
            find("the signature declassified before w0 and w1_packed of its attempt")
        if cur["sig"] is not None:
            find("the signature declassified twice in one attempt")
        if data != sig:
            find("the signature declassified is not the one returned")
        cur["sig"] = data
    if rho != 1:
        find(f"rho declassified {rho} times, expected once")
    for a in attempts[:-1]:
        if a["sig"] is not None:
            find("the signature declassified in an attempt that was rejected")
        if not a["rejected"] and a["w1"] is None:
            find("an attempt ended with no declassified reason")
    last = attempts[-1] if attempts else None
    if rc != 0:
        find(f"signing failed (returned {rc})")
    elif last is None or last["sig"] is None:
        find("the call returned a signature, but its last attempt did not declassify it")
    else:
        if last["ctilde"] != sig[:ct_n]:
            find("the accepting attempt's challenge is not the signature's")
        w0, w1 = last["w0"], last["w1"]
        if pk is not None and w0 is not None and w1 is not None \
                and len(w0) == k * 1024 and len(w1) == w1_n:
            got = [int.from_bytes(w0[4 * i:4 * i + 4], "little", signed=True) % Q
                   for i in range(256 * k)]
            if got != [x for row in w0_public(pk, sig, w1, P) for x in row]:
                find("w0 declassified on the accepting attempt is not its public value, "
                     "Az - c*t1*2^d - 2*gamma2*w1")
    return findings, attempt_stats(events, rc)


# --- running it

def _shake(what, i, n):
    return hashlib.shake_256(f"pq-verify ct-dsa {what} {i}".encode()).digest(n)


def _driver(work):
    src = os.path.join(work, "pqv_ct_dsa_driver.c")
    exe = os.path.join(work, "pqv_ct_dsa_driver")
    with open(src, "w") as fh:
        fh.write(DRIVER_C)
    cc = shutil.which("cc") or shutil.which("gcc")
    p = subprocess.run([cc, "-O1", "-g", "-o", exe, src, "-ldl"], capture_output=True, text=True)
    if p.returncode:
        raise Unavailable(f"the driver did not build: {p.stderr.strip()[-300:]}")
    return exe


def _go(exe, args, log, timeout, memcheck=None):
    """Run the driver, natively or under memcheck (memcheck = xml path)."""
    env = dict(os.environ, PQV_CT_LOG=log)
    cmd = [exe, *args]
    if memcheck:
        cmd = ["valgrind", "--tool=memcheck", *MEMCHECK, "--xml=yes",
               f"--xml-file={memcheck}", *cmd]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
    if p.returncode:
        raise RuntimeError(f"the driver failed (exit {p.returncode}): "
                           f"{(p.stderr or '').strip().splitlines()[-1:]}")


def _outputs(path):
    sigs, pk, sk = {}, None, None
    with open(path) as fh:
        for line in fh:
            f = line.split()
            if f[0] == "sig":
                sigs[int(f[1])] = (int(f[2]), bytes.fromhex(f[3]))
            elif f[0] == "pk":
                pk = bytes.fromhex(f[1])
            elif f[0] == "sk":
                sk = bytes.fromhex(f[1])
    return sigs, pk, sk


def _choose(calls):
    """Message indices for the memcheck run, from the native runs' per-call
    stats: the first accepted at its first attempt, the two with the most
    attempts, and the first with a hint-weight rejection."""
    first = next((i for i, s in sorted(calls.items()) if s["attempts"] == 1), None)
    most = sorted((i for i, s in calls.items() if s["attempts"] > 1),
                  key=lambda i: (-calls[i]["attempts"], i))[:2]
    hint = next((i for i, s in sorted(calls.items()) if s["hint_rejections"]), None)
    return sorted({i for i in (first, *most, hint) if i is not None})


def _search(exe, base, seed, P, policy, work, cap, timeout, batch=128):
    """Sign messages outside Valgrind, where the annotations are no-ops and
    the library behaves identically, in batches until the run has a message
    accepted at its first attempt, two with rejections and one with a
    hint-weight rejection, or `cap` messages. The shim logs here too, so the
    policy judges every one of these calls. -> (messages, {i: stats},
    {finding: [first message, calls]})."""
    msgs, calls, broke = [], {}, {}
    while len(msgs) < cap:
        lo = len(msgs)
        new = [_shake("message", i, 32) for i in range(lo, min(lo + batch, cap))]
        msgs += new
        mfile, log, out = (os.path.join(work, f"search{lo}.{x}") for x in ("msgs", "log", "out"))
        with open(mfile, "w") as fh:
            fh.write("".join(m.hex() + "\n" for m in new))
        _go(exe, ["sign", *base, seed.hex(), out, mfile], log, timeout)
        sigs, _pk, sk = _outputs(out)
        seg = segments(parse_log(log))
        for j, m in enumerate(new):
            i = lo + j
            found, calls[i] = check_sign(seg.get(f"call {j}", []), sigs[j][1], sk, m, P,
                                         policy, sigs[j][0])
            for f in found:
                broke.setdefault(f, [i, 0])[1] += 1
        for f in (f"declassified outside any call: {e[1][0]} ({e[1][1]})"
                  for e in seg[None] if e[0] == "D"):
            broke.setdefault(f, [None, 0])[1] += 1
        os.remove(log)
        c = _choose(calls)
        if (any(calls[i]["attempts"] == 1 for i in c)
                and sum(calls[i]["attempts"] > 1 for i in c) >= 2
                and any(calls[i]["hint_rejections"] for i in c)):
            break
    return msgs, calls, broke


def run_dsa(lib, param_set, keypair, sign, search=2048, timeout=1800):
    """ML-DSA key generation and signing under memcheck, judged by the site
    table. -> {'stages': {op: (p, 1)}, 'leaks', 'findings', 'calls',
    'declassified', 'coverage', 'divisions', 'selftest', 'policy', 'tool'}.
    Raises NotHooked for a library this check cannot judge (CANNOT VERIFY)
    and Unavailable when Valgrind, its headers or a compiler is missing."""
    exported = exported_functions(lib)
    if "pqv_ct_mark" not in exported:
        raise NotHooked("the library does not carry pq-verify's constant-time shim, so "
                        "its declarations of what is public cannot be seen from outside "
                        "(CONSTANT-TIME.md, section 1)")
    policy = policy_for(lib, exported)
    if policy is None:
        raise NotHooked("no declassification policy covers this implementation yet "
                        "(CONSTANT-TIME.md, section 3)")
    why = available()
    if why:
        raise Unavailable(why)
    P = SETS[param_set]
    work = tempfile.mkdtemp(prefix="pqv-ct-dsa-")
    try:
        exe = _driver(work)
        base = [lib, keypair, sign, str(P["pk"]), str(P["sk"]), str(P["sig"])]
        # 0. memcheck must see a deliberate branch on a marked secret, and a
        # read indexed by one whose value is discarded
        xml = os.path.join(work, "selftest.xml")
        _go(exe, ["selftest"], os.path.join(work, "selftest.log"), timeout, memcheck=xml)
        if not SELFTEST_KINDS <= {kind for kind, _ in _parse(xml)}:
            raise Unavailable(SELFTEST_MISSED)
        # 1. key generation under memcheck, with a secret seed
        klog, kout, kxml = (os.path.join(work, f) for f in ("keygen.log", "keygen.out", "keygen.xml"))
        _go(exe, ["keygen", *base, _shake("keygen seed", 0, 32).hex(), kout], klog,
            timeout, memcheck=kxml)
        kseg = segments(parse_log(klog))
        kev = kseg.get("keygen", [])
        if not any(e[0] == "D" for e in kev):
            raise NotHooked("the library carries pq-verify's shim but declared nothing "
                            "public: it was built without its constant-time annotations "
                            "(for mldsa-native, MLD_CONFIG_CT_TESTING_ENABLED)")
        with open(kout) as fh:
            kres = dict(x.split(None, 1) for x in fh if x.strip())
        kpk = bytes.fromhex(kres["pk"].strip())
        kfind = check_keygen(kev, kpk, P, policy)
        if int(kres["rc"]) != 0:
            kfind.append(f"key generation failed (returned {int(kres['rc'])})")
        kfind += [f"declassified outside the call: {e[1][0]} ({e[1][1]})"
                  for e in kseg[None] if e[0] == "D"]
        kleaks = _attribute(_parse(kxml), lib)
        # 2. choose messages from native runs; the policy judges every call
        seed = _shake("signing key seed", 0, 32)
        msgs, native, broke = _search(exe, base, seed, P, policy, work, search, timeout)
        chosen = _choose(native)
        sfind = [f"in {n} of the {len(msgs)} calls signed outside Valgrind"
                 + (f", first message {i} ({label(native[i])})" if i is not None else "")
                 + f": {f}" for f, (i, n) in broke.items()]
        # 3. signing under memcheck: the chosen messages, the key marked secret
        cfile = os.path.join(work, "chosen.msgs")
        with open(cfile, "w") as fh:
            fh.write("".join(msgs[i].hex() + "\n" for i in chosen))
        slog, sout, sxml = (os.path.join(work, f) for f in ("sign.log", "sign.out", "sign.xml"))
        _go(exe, ["sign", *base, seed.hex(), sout, cfile], slog, timeout, memcheck=sxml)
        ssigs, spk, ssk = _outputs(sout)
        sseg = segments(parse_log(slog))
        sev, calls = [], []
        for j, i in enumerate(chosen):
            ev = sseg.get(f"call {j}", [])
            sev += ev
            f, st = check_sign(ev, ssigs[j][1], ssk, msgs[i], P, policy, ssigs[j][0], pk=spk)
            calls.append({"message": i, "how": label(st), **st, "findings": f})
            sfind += [f"message {i} ({label(st)}): {x}" for x in f]
        sfind += [f"declassified outside any call: {e[1][0]} ({e[1][1]})"
                  for e in sseg[None] if e[0] == "D"]
        coverage = {"native_calls": len(msgs),
                    "native_attempts": sum(s["attempts"] for s in native.values()),
                    "memcheck_calls": len(calls),
                    "memcheck_attempts": sum(c["attempts"] for c in calls),
                    "first_attempt": sum(c["attempts"] == 1 for c in calls),
                    "rejecting": sum(c["attempts"] > 1 for c in calls),
                    "hint_rejections": sum(c["hint_rejections"] for c in calls)}
        if not coverage["first_attempt"] or not coverage["rejecting"]:
            sfind.append("coverage: the memcheck run needs a message accepted at its first "
                         "attempt and one with a rejection")
        sleaks = _attribute(_parse(sxml), lib)

        def leaks(found):
            return [{"kind": KINDS[kd], "function": fn, "count": n}
                    for (kd, fn), n in sorted(found.items())]
        return {"stages": {"keyGen": (int(not kleaks and not kfind), 1),
                           "sign": (int(not sleaks and not sfind), 1)},
                "leaks": {"keyGen": leaks(kleaks), "sign": leaks(sleaks)},
                "findings": {"keyGen": kfind, "sign": sfind},
                "calls": calls,
                "declassified": {"keyGen": _site_counts(kev), "sign": _site_counts(sev)},
                "coverage": coverage, "selftest": True,
                "policy": f"{policy} @ {POLICIES[policy]['commit'][:7]}",
                "divisions": divisions(lib),
                "tool": subprocess.run(["valgrind", "--version"], capture_output=True,
                                       text=True).stdout.strip()}
    finally:
        shutil.rmtree(work, ignore_errors=True)
