#!/usr/bin/env python3
"""Rebuild each pinned third-party ML-KEM / ML-DSA library and re-audit it.

  python3 tools/vendor_audit.py              build every row, check its result
  python3 tools/vendor_audit.py --markdown   print the AUDITS.md tables (offline)
  python3 tools/vendor_audit.py --only ML-DSA   just one scheme (ML-KEM, ML-DSA, LMS/XMSS,
                                                FN-DSA)

ML-KEM rows are re-run with --audit-kem, ML-DSA rows with --audit-dsa. ML-DSA
libraries are linked with pq-verify's randomness harness
(pq_verify/harness/pqv_randombytes.c), so their randomised keypair() and
signature() APIs are audited byte-exactly, not only the seed-taking ones.

Mutants. An audit that passes correct libraries has shown half of what it
must. Each ML-DSA row also lists mutants: a one-line source change that plants
a known bug class (a verifier that skips the challenge comparison, a hint
decoder that accepts a repeated index, a signer that ignores rnd, ...). CI
builds every mutant and requires the audit to FAIL it in the stages the row
names. A mutant the audit passes is a hole in pq-verify, reported as such.

Every input is pinned: the library to an exact commit (tools/vendor_audits.json),
the NIST vectors to the bundle pq-verify ships, the reference implementations
to constraints-reference.txt. So when a row's result differs from what the
table records, the only thing that changed is pq-verify -- a regression, or a
deliberate change that must update the table in the same PR.

This is the check that would have caught the symbol-resolution bug fixed in
2.8.1: pq-verify bound mlkem-native's internal indcpa_keypair_derand and
reported a correct library as 35/60. Its unit tests use stub libraries and
could not see it; a real, pinned library does.

EXIT  0 every row reproduces   1 a row differs   2 a library could not be built
"""
import argparse
import contextlib
import io
import itertools
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TABLE = REPO / "tools" / "vendor_audits.json"
HARNESS = REPO / "pq_verify" / "harness" / "pqv_randombytes.c"
STAGES = ("keyGen", "encaps", "decaps", "ekCheck", "dkCheck")
# Wycheproof/CCTV edge cases (pq_verify/edge.py). Their counts differ per
# parameter set, so each row records them per set under "edge".
EDGE_STAGES = ("edgeValid", "edgeEk", "edgeDk")
BEGIN, END = "<!-- vendor-audits:begin -->", "<!-- vendor-audits:end -->"
DSA_BEGIN, DSA_END = "<!-- vendor-audits-dsa:begin -->", "<!-- vendor-audits-dsa:end -->"
DSA_STAGES = ("keyGen", "sigGenInternal", "sigGenPure", "sigGenPreHash", "sigGenMu",
              "sigVerInternal", "sigVerPure", "sigVerPreHash", "sigVerMu")
DSA_EDGE_STAGES = ("edge:sigVerify", "edge:sigGen", "edge:edgeLength")
ACC_STAGES = ("accumulated",)        # pq_verify/accumulated.py, every scheme
DSA_BUILDS = ("mldsa-native", "pqcrystals-ref", "pqclean-mldsa", "liboqs")
HBS_BEGIN, HBS_END = "<!-- vendor-audits-hbs:begin -->", "<!-- vendor-audits-hbs:end -->"
HBS_BUILDS = ("hash-sigs", "xmss-reference")
HBS_ADAPTERS = REPO / "pq_verify" / "harness" / "hbs"
FNDSA_BEGIN, FNDSA_END = "<!-- vendor-audits-fndsa:begin -->", "<!-- vendor-audits-fndsa:end -->"
FNDSA_BUILDS = ("pqclean-falcon", "liboqs")
FNDSA_STAGES = ("verify", "open", "reject", "keyGen", "sign")
MCE_BEGIN, MCE_END = "<!-- vendor-audits-mceliece:begin -->", "<!-- vendor-audits-mceliece:end -->"
HQC_BEGIN, HQC_END = "<!-- vendor-audits-hqc:begin -->", "<!-- vendor-audits-hqc:end -->"
HQC_BUILDS = ("pqclean-hqc", "hqc-ref", "hqc-avx256")
HQC_STAGES = ("encode", "rm-decode", "rs-decode", "code-decode", "bounds")
MCE_BUILDS = ("pqclean-mceliece", "liboqs", "liboqs-generic")
MCE_STAGES = ("keyGen", "encaps", "decaps", "padding")

_RANDOMBYTES = (b"#include <stdint.h>\n#include <stddef.h>\n"
                b"int randombytes(uint8_t *o, size_t n)"
                b"{ for (size_t i = 0; i < n; i++) o[i] = (uint8_t)i; return 0; }\n")


def load_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh)["audits"]


def load_dsa_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh).get("dsa_audits", [])


def load_hbs_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh).get("hbs_audits", [])


# ─────────────────────────────── build ───────────────────────────────

# liboqs: one shared library for every parameter set, configured as
# distributions ship it -- OQS_DIST_BUILD compiles every backend in and picks
# one at run time by CPU -- with only the algorithms audited here.
LIBOQS_ALGS = ("KEM_ml_kem_512;KEM_ml_kem_768;KEM_ml_kem_1024;"
               "SIG_ml_dsa_44;SIG_ml_dsa_65;SIG_ml_dsa_87;"
               "SIG_falcon_512;SIG_falcon_1024;SIG_falcon_padded_512;SIG_falcon_padded_1024")
# Classic McEliece (not FIPS) is built separately, so its ten sets do not
# slow every other liboqs row; "generic" is the portable configuration, whose
# public API can only run the clean backend.
LIBOQS_MCE_ALGS = ";".join(f"KEM_classic_mceliece_{s}" for s in (
    "348864", "348864f", "460896", "460896f", "6688128", "6688128f",
    "6960119", "6960119f", "8192128", "8192128f"))
_LIBOQS_BUILT = {}
_LIBOQS_MUTANTS = itertools.count()


def build_liboqs(src, out_dir, tag="", algs=LIBOQS_ALGS, generic=False):
    """The pinned tree is built once per configuration and shared by every row
    and set. A mutant (tag) is always rebuilt, to a path of its own: every
    liboqs row mutates the same tree path and numbers its mutants from 0, so a
    cache keyed on either would hand one row's mutant to another."""
    config = ("" if algs == LIBOQS_ALGS else "-mce") + ("-generic" if generic else "")
    key = (str(src), config)
    if not tag and key in _LIBOQS_BUILT:
        return _LIBOQS_BUILT[key]
    tag = config + (f"{tag}-{next(_LIBOQS_MUTANTS)}" if tag else "")
    bdir = Path(out_dir) / f"liboqs-build{tag}"
    if bdir.exists():
        shutil.rmtree(bdir)
    target = (["-DOQS_DIST_BUILD=OFF", "-DOQS_OPT_TARGET=generic"] if generic
              else ["-DOQS_DIST_BUILD=ON"])
    subprocess.run(["cmake", "-S", str(src), "-B", str(bdir), "-DBUILD_SHARED_LIBS=ON",
                    "-DOQS_USE_OPENSSL=OFF", "-DOQS_BUILD_ONLY_LIB=ON", *target,
                    "-DCMAKE_BUILD_TYPE=Release", f"-DOQS_MINIMAL_BUILD={algs}"],
                   check=True, capture_output=True)
    subprocess.run(["cmake", "--build", str(bdir), "-j", str(os.cpu_count() or 2)],
                   check=True, capture_output=True)
    lib = next(p for p in sorted((bdir / "lib").glob("liboqs.so*")) if not p.is_symlink())
    # A distinct path per build: the loader hands back a library already
    # loaded from the same path, which would audit the first build every time.
    so = Path(out_dir) / f"liboqs{tag}.so"
    shutil.copy2(lib, so)
    if tag != config:
        shutil.rmtree(bdir, ignore_errors=True)
    else:
        _LIBOQS_BUILT[key] = str(so)
    return str(so)


def prefix_for(row, param_set, mutant=None):
    """The row's --symbol-prefix for one parameter set ({level} filled in),
    or None: a library exporting several implementations names one."""
    t = (mutant or {}).get("prefix") or row.get("prefix")
    return t.format(level=param_set.rsplit("-", 1)[-1]) if t else None

def fetch(url, commit, dest):
    """Exactly `commit`, nothing newer: fetch that object and check it out."""
    run = lambda *a: subprocess.run(a, cwd=dest, check=True, capture_output=True)
    os.makedirs(dest, exist_ok=True)
    run("git", "init", "-q")
    run("git", "fetch", "-q", "--depth", "1", url, commit)
    run("git", "checkout", "-q", "FETCH_HEAD")
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=dest, check=True,
                          capture_output=True, text=True).stdout.strip()
    if head != commit:
        raise RuntimeError(f"fetched {head}, pinned {commit}")


def build(recipe, src, param_set, out_dir, tag=""):
    """Compile one parameter set of a library to a shared object."""
    if recipe == "liboqs":
        return build_liboqs(src, out_dir, tag)
    level = param_set.rsplit("-", 1)[1]
    so = Path(out_dir) / f"{recipe}{level}{tag}.so"
    cc = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared"]
    if recipe == "mlkem-native":
        rb = Path(out_dir) / "randombytes.c"
        rb.write_bytes(_RANDOMBYTES)
        cmd = cc + [f"-DMLK_CONFIG_PARAMETER_SET={level}", "-I", f"{src}/mlkem",
                    "-o", str(so), f"{src}/mlkem/mlkem_native.c", str(rb)]
    elif recipe == "pqclean":
        d = Path(src) / "crypto_kem" / f"ml-kem-{level}" / "clean"
        common = Path(src) / "common"
        cmd = cc + ["-I", str(common), "-o", str(so),
                    *sorted(str(p) for p in d.glob("*.c")),
                    str(common / "fips202.c"), str(common / "randombytes.c")]
    else:
        raise ValueError(f"unknown build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


def build_dsa(recipe, src, param_set, out_dir, tag=""):
    """Compile one ML-DSA parameter set, linked with the randomness harness
    (liboqs: its own RNG hook supplies the randomness instead)."""
    if recipe == "liboqs":
        return build_liboqs(src, out_dir, tag)
    level = param_set.rsplit("-", 1)[1]
    so = Path(out_dir) / f"{recipe}{level}{tag}.so"
    cc = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared"]
    src = Path(src)
    if recipe == "mldsa-native":
        cmd = cc + [f"-DMLD_CONFIG_PARAMETER_SET={level}", "-I", str(src / "mldsa"),
                    "-o", str(so), str(src / "mldsa" / "mldsa_native.c"), str(HARNESS)]
    elif recipe == "pqcrystals-ref":
        mode = {"44": 2, "65": 3, "87": 5}[level]
        ref = src / "ref"
        files = ("sign.c", "packing.c", "polyvec.c", "poly.c", "ntt.c", "reduce.c",
                 "rounding.c", "fips202.c", "symmetric-shake.c")
        cmd = cc + [f"-DDILITHIUM_MODE={mode}", "-o", str(so),
                    *(str(ref / f) for f in files), str(HARNESS)]
    elif recipe == "pqclean-mldsa":
        d = src / "crypto_sign" / f"ml-dsa-{level}" / "clean"
        common = src / "common"
        cmd = cc + ["-I", str(common), "-o", str(so),
                    *sorted(str(p) for p in d.glob("*.c")),
                    str(common / "fips202.c"), str(HARNESS)]
    else:
        raise ValueError(f"unknown ML-DSA build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


def build_hbs(recipe, src, out_dir, tag=""):
    """Compile an LMS/XMSS library with its pqv_hbs adapter. Both use OpenSSL
    for SHA-2, so -lcrypto."""
    so = Path(out_dir) / f"{recipe}{tag}.so"
    cc = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared", "-w",
          "-I", str(HBS_ADAPTERS), "-I", str(src)]
    src = Path(src)
    if recipe == "hash-sigs":
        files = ("hss hss_alloc hss_aux hss_common hss_compute hss_generate hss_keygen "
                 "hss_param hss_reserve hss_sign hss_sign_inc hss_thread_single hss_verify "
                 "hss_verify_inc hss_derive hss_zeroize lm_common lm_ots_common lm_ots_sign "
                 "lm_ots_verify lm_verify endian hash sha256").split()
        cmd = cc + ["-o", str(so), str(HBS_ADAPTERS / "adapter_hash_sigs.c"),
                    *(str(src / f"{f}.c") for f in files), "-lcrypto"]
    elif recipe == "xmss-reference":
        files = ("params hash fips202 hash_address wots xmss xmss_core xmss_commons "
                 "utils").split()
        cmd = cc + ["-o", str(so), str(HBS_ADAPTERS / "adapter_xmss_reference.c"),
                    *(str(src / f"{f}.c") for f in files), "-lcrypto"]
    else:
        raise ValueError(f"unknown LMS/XMSS build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


def mutate(src, mutant, dest):
    """A copy of the source tree with one planted bug. The change must apply
    exactly once: a pattern that no longer matches would test nothing."""
    dest = Path(dest)
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(src, dest, ignore=shutil.ignore_patterns(".git"))
    f = dest / mutant["file"]
    text = f.read_text()
    n = text.count(mutant["find"])
    if n != 1:
        raise RuntimeError(f"mutant {mutant['name']!r}: pattern found {n} times in "
                           f"{mutant['file']}, expected once")
    f.write_text(text.replace(mutant["find"], mutant["replace"]))
    return dest


def load_fndsa_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh).get("fndsa_audits", [])


def load_mceliece_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh).get("mceliece_audits", [])


def load_hqc_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh).get("hqc_audits", [])


def build_mceliece(recipe, src, param_set, out_dir, tag=""):
    """Compile one Classic McEliece parameter set. Encapsulation draws its
    error vector from the system RNG: it is audited for validity and
    repetition, so no randomness harness is linked. liboqs: every set in one
    library, its distribution build (the AVX2 backend on an AVX2/POPCNT CPU)
    or the portable one (the clean backend only)."""
    if recipe in ("liboqs", "liboqs-generic"):
        return build_liboqs(src, out_dir, tag, algs=LIBOQS_MCE_ALGS,
                            generic=recipe == "liboqs-generic")
    so = Path(out_dir) / f"{recipe}-{param_set}{tag}.so"
    src = Path(src)
    if recipe == "pqclean-mceliece":
        d = src / "crypto_kem" / param_set / "clean"
        common = src / "common"
        cmd = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared", "-w", "-I", str(common),
               "-o", str(so), *sorted(str(p) for p in d.glob("*.c")),
               str(common / "fips202.c"), str(common / "aes.c"), str(common / "randombytes.c")]
    else:
        raise ValueError(f"unknown Classic McEliece build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


HQC_DIRS = {"HQC-1": ("hqc-128", "hqc-1"), "HQC-3": ("hqc-192", "hqc-3"),
            "HQC-5": ("hqc-256", "hqc-5")}
_RANDOMBYTES_STUB = """#include <stddef.h>
#include <stdint.h>
#include <sys/random.h>
int randombytes(uint8_t *out, size_t n) {
    while (n) { ssize_t r = getrandom(out, n, 0); if (r <= 0) return -1; out += r; n -= (size_t)r; }
    return 0;
}
"""


def build_hqc(recipe, src, param_set, out_dir, tag=""):
    """Compile one HQC parameter set with its decoder symbols visible.
    pqclean-hqc: PQClean's clean code (the 2023-04-30 submission).
    hqc-ref / hqc-avx256: the submitters' repository, as its CMake build
    assembles each variant (src/common, the architecture's sources, the
    set's headers, lib/fips202). Releases from next-release on declare
    randombytes() without defining it; a getrandom() stub is linked then.
    The submitters' code is built at -O3, as their CMake does: their AVX2
    Reed-Muller decoder reads an __m256i through a uint16_t pointer, and GCC
    13 at -O2 then returns the wrong sign bit for every block (AUDITS.md).
    The decoder is deterministic, so no randomness harness is needed."""
    old, new = HQC_DIRS[param_set]
    so = Path(out_dir) / f"{recipe}-{new}{tag}.so"
    src = Path(src)
    cc = os.environ.get("CC", "gcc")
    if recipe == "pqclean-hqc":
        d, common = src / "crypto_kem" / old / "clean", src / "common"
        cmd = [cc, "-O2", "-fPIC", "-shared", "-w", "-I", str(common), "-I", str(d),
               "-o", str(so), *sorted(str(p) for p in d.glob("*.c")),
               str(common / "fips202.c"), str(common / "randombytes.c")]
    elif recipe in ("hqc-ref", "hqc-avx256"):
        s = src / "src"
        if recipe == "hqc-ref":
            arch = plat = s / "ref"
            flags = []
        else:
            arch, plat = s / "x86_64" / "common", s / "x86_64" / "avx256"
            flags = ["-mavx", "-mavx2", "-mbmi", "-mpclmul"]
        dirs = [s / "common", s / "common" / new, arch, arch / new, plat, plat / new,
                src / "lib" / "fips202"]
        files = sorted({str(p) for d in (s / "common", arch, arch / new, plat, plat / new)
                        for p in d.glob("*.c")}) + [str(src / "lib" / "fips202" / "fips202.c")]
        if (s / "common" / "randombytes.h").exists():
            stub = Path(out_dir) / "pqv_randombytes_stub.c"
            stub.write_text(_RANDOMBYTES_STUB)
            files.append(str(stub))
        cmd = [cc, "-O3", "-fPIC", "-shared", "-w", *flags,
               *[f"-I{d}" for d in dirs], "-o", str(so), *files]
    else:
        raise ValueError(f"unknown HQC build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


def build_fndsa(recipe, src, param_set, out_dir, tag=""):
    """Compile one FN-DSA (Falcon) parameter set. Signing draws its nonce
    and seeds from the system RNG: FN-DSA signing is audited for validity,
    not byte-for-byte, so no randomness harness is linked."""
    if recipe == "liboqs":
        return build_liboqs(src, out_dir, tag)
    n = param_set.rsplit("-", 1)[1]
    so = Path(out_dir) / f"{recipe}{n}{tag}.so"
    src = Path(src)
    if recipe == "pqclean-falcon":
        d = src / "crypto_sign" / f"falcon-{n}" / "clean"
        common = src / "common"
        cmd = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared", "-I", str(common),
               "-o", str(so), *sorted(str(p) for p in d.glob("*.c")),
               str(common / "fips202.c"), str(common / "randombytes.c")]
    else:
        raise ValueError(f"unknown FN-DSA build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


# ─────────────────────────────── audit ───────────────────────────────

def audit_dsa(so, param_set, prefix=None):
    sys.path.insert(0, str(REPO))
    from pq_verify.dsa_audit import pqverify_audit_dsa
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_dsa(so, param_set, verbose=False, prefix=prefix)
    if r is None:
        return None
    return {"results": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"], "rng": r["rng"]}


def audit_hbs(so):
    sys.path.insert(0, str(REPO))
    from pq_verify.hbs_audit import pqverify_audit_hbs
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_hbs(so, verbose=False)
    return {"results": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"], "not_run": r["not_run_total"],
            # Which checks fail, by name: pinned for a library with known
            # defects, so a mutant is judged on what it ADDS (below).
            "failing": sorted(f"{f['stage']}: {f['case']}" for f in r["failures"])}


def audit_fndsa(so, param_set, prefix=None):
    sys.path.insert(0, str(REPO))
    from pq_verify.fndsa_audit import pqverify_audit_fndsa
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_fndsa(so, param_set, verbose=False, prefix=prefix)
    if r is None:
        return None
    return {"results": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"]}


def audit_mceliece(so, param_set, prefix=None):
    sys.path.insert(0, str(REPO))
    from pq_verify.mceliece_audit import pqverify_audit_mceliece
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_mceliece(so, param_set, verbose=False, prefix=prefix)
    if r is None:
        return None
    return {"results": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"]}


def audit_hqc(so, param_set, profile, seed, prefix=None):
    sys.path.insert(0, str(REPO))
    from pq_verify.hqc_audit import pqverify_audit_hqc
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_hqc(so, param_set, verbose=False, prefix=prefix,
                               profile=profile, seed=seed)
    if r is None:
        return None
    return {"results": {k: list(v) for k, v in r["detail"].items()}}


def audit_ct(so, param_set, prefix=None):
    """The --constant-time stages alone: {stage: [p, t]} and the leaks."""
    sys.path.insert(0, str(REPO))
    from pq_verify.ct_audit import run_kem
    from pq_verify.core import _resolve_kem_symbols
    from pq_verify.symbols import exported_functions
    f, _ = _resolve_kem_symbols(exported_functions(so), param_set, prefix=prefix)
    r = run_kem(so, param_set, f["keypair"], f["encaps"], f["decaps"])
    return ({"ct:" + k: list(v) for k, v in r["stages"].items()},
            {k: [f"{l['kind']} in {l['function']}" for l in v] for k, v in r["leaks"].items()})


def check_ct(rows, workdir):
    """ML-KEM rows' "ct" results, and every "ct_mutants" leak caught."""
    sys.path.insert(0, str(REPO))
    from pq_verify.ct_audit import available
    why = available()
    if why:
        print(f"  ERROR  constant-time rows cannot run: {why}")
        return 2
    failures = 0
    for row in rows:
        if "ct" not in row:
            continue
        src = Path(workdir) / row["build"] / row["commit"][:12]
        if not (src / ".git").exists():
            fetch(row["url"], row["commit"], src)
        for ps in row["sets"]:
            label = f"{row['library']} @ {row['commit'][:7]} {ps} (constant time)"
            got, leaks = audit_ct(build(row["build"], src, ps, workdir), ps,
                                  prefix_for(row, ps))
            if got == row["ct"][ps]:
                print(f"  ok     {label}: no secret-dependent branch or access, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}: recorded {row['ct'][ps]}  now {got}  {leaks}")
        for i, m in enumerate(row.get("ct_mutants", [])):
            label = f"{row['library']} ct mutant {m['name']!r} ({m['set']})"
            try:
                msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
                so = build(row["build"], msrc, m["set"], workdir, tag=f"-ctmut{i}")
            except (RuntimeError, subprocess.CalledProcessError) as e:
                print(f"  ERROR  {label}: {e}")
                return 2
            got, leaks = audit_ct(so, m["set"], prefix_for(row, m["set"], m))
            missed = [s for s in m["fails"] if got.get(s, [0, 0])[0] == got.get(s, [0, 0])[1]]
            if missed:
                failures += 1
                print(f"  MISSED {label}: {', '.join(missed)} passed. pq-verify cannot "
                      f"see this leak.")
            else:
                print(f"  caught {label}: {'; '.join(x for v in leaks.values() for x in v)}")
    if failures:
        print(f"\n  {failures} constant-time row(s) or mutant(s) differ.")
        return 1
    return 0


def audit(so, param_set, prefix=None):
    sys.path.insert(0, str(REPO))
    from pq_verify.core import pqverify_audit_kem
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_kem(so, param_set, verbose=False, prefix=prefix)
    if r is None:
        return None
    return {k: list(v) for k, v in r["detail"].items()}


def total(stages):
    return (sum(v[0] for v in stages.values()), sum(v[1] for v in stages.values()))


def check_all(rows, workdir):
    failures = 0
    for row in rows:
        src = Path(workdir) / row["build"] / row["commit"][:12]
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
        except Exception as e:
            print(f"  ERROR  {row['library']} @ {row['commit'][:7]}: fetch failed: {e}")
            return 2
        for ps in row["sets"]:
            want = {k: list(v) for k, v in row["expected"].items()}
            want.update({k: list(v) for k, v in row["edge"][ps].items()})
            if "accumulated" in row:
                want["accumulated"] = list(row["accumulated"][ps])
            label = f"{row['library']} @ {row['commit'][:7]} {ps}"
            try:
                so = build(row["build"], src, ps, workdir)
            except subprocess.CalledProcessError as e:
                print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
                return 2
            got = audit(so, ps, prefix_for(row, ps))
            if got == want:
                p, t = total(got)
                print(f"  ok     {label}: {p}/{t}, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}")
            if got is None:
                print("         pq-verify could not audit it (entry points not resolved)")
                continue
            for s in STAGES + EDGE_STAGES + ("accumulated",):
                if got.get(s) != want.get(s):
                    print(f"         {s:8s} recorded {want.get(s)}  now {got.get(s)}")
        for i, m in enumerate(row.get("mutants", [])):
            label = f"{row['library']} mutant {m['name']!r} ({m['set']})"
            try:
                msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
                so = build(row["build"], msrc, m["set"], workdir, tag=f"-kemmut{i}")
            except (RuntimeError, subprocess.CalledProcessError) as e:
                print(f"  ERROR  {label}: {e}")
                return 2
            got = audit(so, m["set"], prefix_for(row, m["set"], m))
            missed = [f"{st} {p}/{t}" for st in m["fails"]
                      for p, t in [(got or {}).get(st, (0, 0))] if not (t and p < t)]
            if got is not None and not missed:
                print(f"  caught {label}: fails "
                      f"{', '.join(sorted(s for s, (p, t) in got.items() if p < t))}")
                continue
            failures += 1
            print(f"  MISSED {label}: the audit did not fail "
                  + (", ".join(missed) if got else "(could not audit it)")
                  + ". pq-verify cannot see this bug class.")
    if failures:
        print(f"\n  {failures} row(s) differ. pq-verify's behaviour changed against a "
              f"pinned library and pinned vectors: fix the regression, or, if the "
              f"change is intended, update tools/vendor_audits.json and AUDITS.md "
              f"in the same PR and say why.")
        return 1
    return 0


def check_dsa(rows, workdir):
    failures = 0
    for row in rows:
        src = Path(workdir) / row["build"] / row["commit"][:12]
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
        except Exception as e:
            print(f"  ERROR  {row['library']} @ {row['commit'][:7]}: fetch failed: {e}")
            return 2
        for ps in row["sets"]:
            label = f"{row['library']} @ {row['commit'][:7]} {ps}"
            try:
                so = build_dsa(row["build"], src, ps, workdir)
            except subprocess.CalledProcessError as e:
                print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
                return 2
            got = audit_dsa(so, ps, prefix_for(row, ps))
            want = {"results": row["results"][ps],
                    "not_applicable": row["not_applicable"][ps], "rng": []}
            if got == want:
                p, t = total(got["results"])
                print(f"  ok     {label}: {p}/{t}, {got['not_applicable']} n/a, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}")
            if got is None:
                print("         pq-verify could not audit it (entry points not resolved)")
                continue
            for s in sorted(set(got["results"]) | set(want["results"])):
                if got["results"].get(s) != want["results"].get(s):
                    print(f"         {s:16s} recorded {want['results'].get(s)}  "
                          f"now {got['results'].get(s)}")
            if got["not_applicable"] != want["not_applicable"]:
                print(f"         not applicable recorded {want['not_applicable']}  "
                      f"now {got['not_applicable']}")
            for r in got["rng"][:3]:
                print(f"         randomness: {r}")
        for i, m in enumerate(row.get("mutants", [])):
            label = f"{row['library']} mutant {m['name']!r} ({m['set']})"
            try:
                msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
                # A distinct file per mutant: the dynamic loader hands back an
                # already-loaded library for a path it has seen, so reusing a
                # name would audit the first mutant every time.
                so = build_dsa(row["build"], msrc, m["set"], workdir, tag=f"-dsamut{i}")
            except (RuntimeError, subprocess.CalledProcessError) as e:
                print(f"  ERROR  {label}: {e}")
                return 2
            got = audit_dsa(so, m["set"], prefix_for(row, m["set"], m))
            missed = []
            for stage in m["fails"]:
                if stage == "rng":
                    if not (got and got["rng"]):
                        missed.append("rng")
                    continue
                p, t = (got or {"results": {}})["results"].get(stage, (0, 0))
                if not (t and p < t):
                    missed.append(f"{stage} {p}/{t}")
            if got is not None and not missed:
                bad = sorted(s for s, (p, t) in got["results"].items() if p < t)
                print(f"  caught {label}: fails {', '.join(bad + (['rng'] if got['rng'] else []))}")
                continue
            failures += 1
            print(f"  MISSED {label}: the audit did not fail "
                  + (", ".join(missed) if got else "(could not audit it)")
                  + ". pq-verify cannot see this bug class.")
    if failures:
        print(f"\n  {failures} ML-DSA row(s) or mutant(s) differ. Fix the regression, "
              f"or, if intended, update tools/vendor_audits.json and AUDITS.md in "
              f"the same PR and say why.")
        return 1
    return 0


def _check_mutants(row, src, workdir, build_fn, audit_fn):
    """Build each mutant of a row and require the audit to fail it in every
    listed stage. Returns the number missed (or 2 on a build error)."""
    missed_rows = 0
    for i, m in enumerate(row.get("mutants", [])):
        label = f"{row['library']} mutant {m['name']!r}"
        try:
            msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
            so = build_fn(msrc, i)
        except (RuntimeError, subprocess.CalledProcessError) as e:
            print(f"  ERROR  {label}: {e}")
            return None
        got = audit_fn(so)
        missed = []
        known = set(row.get("failing", []))
        for stage in m["fails"]:
            if stage == "rng":
                if not got.get("rng"):
                    missed.append("rng")
                continue
            p, t = got["results"].get(stage, (0, 0))
            if "failing" in got:
                # The library itself may already fail checks in this stage (an
                # upstream defect, pinned in the row): only a check that fails
                # for the mutant and NOT for the library shows the planted bug.
                if not any(x.startswith(stage + ": ") and x not in known
                           for x in got["failing"]):
                    missed.append(f"{stage} {p}/{t} (no check beyond the library's own)")
            elif not (t and p < t):
                missed.append(f"{stage} {p}/{t}")
        if not missed:
            bad = sorted(s for s, (p, t) in got["results"].items() if p < t)
            print(f"  caught {label}: fails {', '.join(bad)}")
            continue
        missed_rows += 1
        print(f"  MISSED {label}: the audit did not fail {', '.join(missed)}. "
              f"pq-verify cannot see this bug class.")
    return missed_rows


def check_hbs(rows, workdir):
    failures = 0
    for row in rows:
        src = Path(workdir) / row["build"] / row["commit"][:12]
        label = f"{row['library']} @ {row['commit'][:7]}"
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
            so = build_hbs(row["build"], src, workdir)
        except subprocess.CalledProcessError as e:
            print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
            return 2
        except Exception as e:
            print(f"  ERROR  {label}: fetch failed: {e}")
            return 2
        got = audit_hbs(so)
        want = {"results": row["results"], "not_applicable": row["not_applicable"],
                "not_run": row["not_run"], "failing": row.get("failing", [])}
        if got == want:
            p, t = total(got["results"])
            print(f"  ok     {label}: {p}/{t}, {got['not_applicable']} n/a, "
                  f"{got['not_run']} not run, as recorded")
        else:
            failures += 1
            print(f"  DIFF   {label}")
            for s in sorted(set(got["results"]) | set(want["results"])):
                if got["results"].get(s) != want["results"].get(s):
                    print(f"         {s:32s} recorded {want['results'].get(s)}  "
                          f"now {got['results'].get(s)}")
            for k in ("not_applicable", "not_run"):
                if got[k] != want[k]:
                    print(f"         {k} recorded {want[k]}  now {got[k]}")
            for x in sorted(set(got["failing"]) ^ set(want["failing"])):
                print(f"         {'now fails' if x in got['failing'] else 'now passes'}: {x}")
        missed = _check_mutants(
            row, src, workdir,
            lambda msrc, i, r=row: build_hbs(r["build"], msrc, workdir, tag=f"-mut{i}"),
            audit_hbs)
        if missed is None:
            return 2
        failures += missed
    if failures:
        print(f"\n  {failures} LMS/XMSS row(s) or mutant(s) differ. Fix the regression, "
              f"or, if intended, update tools/vendor_audits.json and AUDITS.md in "
              f"the same PR and say why.")
        return 1
    return 0


def check_fndsa(rows, workdir):
    """FN-DSA (draft track): each row's sets as recorded, and every mutant
    failed in the stages it names."""
    failures = 0
    for row in rows:
        src = Path(workdir) / row["build"] / row["commit"][:12]
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
        except Exception as e:
            print(f"  ERROR  {row['library']} @ {row['commit'][:7]}: fetch failed: {e}")
            return 2
        for ps in row["sets"]:
            label = f"{row['library']} @ {row['commit'][:7]} {ps}"
            try:
                so = build_fndsa(row["build"], src, ps, workdir)
            except subprocess.CalledProcessError as e:
                print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
                return 2
            got = audit_fndsa(so, ps, prefix_for(row, ps))
            want = {"results": row["results"][ps],
                    "not_applicable": row["not_applicable"][ps]}
            if got == want:
                p, t = total(got["results"])
                print(f"  ok     {label}: {p}/{t}, {got['not_applicable']} n/a, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}")
            if got is None:
                print("         pq-verify could not audit it (entry points not resolved)")
                continue
            for s in sorted(set(got["results"]) | set(want["results"])):
                if got["results"].get(s) != want["results"].get(s):
                    print(f"         {s:8s} recorded {want['results'].get(s)}  "
                          f"now {got['results'].get(s)}")
            if got["not_applicable"] != want["not_applicable"]:
                print(f"         not applicable recorded {want['not_applicable']}  "
                      f"now {got['not_applicable']}")
        for i, m in enumerate(row.get("mutants", [])):
            label = f"{row['library']} mutant {m['name']!r} ({m['set']})"
            try:
                msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
                so = build_fndsa(row["build"], msrc, m["set"], workdir, tag=f"-fnmut{i}")
            except (RuntimeError, subprocess.CalledProcessError) as e:
                print(f"  ERROR  {label}: {e}")
                return 2
            got = audit_fndsa(so, m["set"], prefix_for(row, m["set"], m))
            missed = [f"{st} {p}/{t}" for st in m["fails"]
                      for p, t in [(got or {"results": {}})["results"].get(st, (0, 0))]
                      if not (t and p < t)]
            if got is not None and not missed:
                bad = sorted(s for s, (p, t) in got["results"].items() if p < t)
                print(f"  caught {label}: fails {', '.join(bad)}")
                continue
            failures += 1
            print(f"  MISSED {label}: the audit did not fail "
                  + (", ".join(missed) if got else "(could not audit it)")
                  + ". pq-verify cannot see this bug class.")
    if failures:
        print(f"\n  {failures} FN-DSA row(s) or mutant(s) differ. Fix the regression, "
              f"or, if intended, update tools/vendor_audits.json and AUDITS.md in "
              f"the same PR and say why.")
        return 1
    return 0


def check_mceliece(rows, workdir):
    """Classic McEliece (not a FIPS standard): each row's sets as recorded,
    and every mutant failed in the stages it names."""
    failures = 0
    for row in rows:
        tree = "liboqs" if row["build"].startswith("liboqs") else row["build"]
        src = Path(workdir) / tree / row["commit"][:12]
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
        except Exception as e:
            print(f"  ERROR  {row['library']} @ {row['commit'][:7]}: fetch failed: {e}")
            return 2
        for ps in row["sets"]:
            label = f"{row['library']} @ {row['commit'][:7]} {ps}"
            try:
                so = build_mceliece(row["build"], src, ps, workdir)
            except subprocess.CalledProcessError as e:
                print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
                return 2
            got = audit_mceliece(so, ps, prefix_for(row, ps))
            want = {"results": row["results"][ps],
                    "not_applicable": row["not_applicable"][ps]}
            if got == want:
                p, t = total(got["results"])
                print(f"  ok     {label}: {p}/{t}, {got['not_applicable']} n/a, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}")
            if got is None:
                print("         pq-verify could not audit it (entry points not resolved)")
                continue
            for s in sorted(set(got["results"]) | set(want["results"])):
                if got["results"].get(s) != want["results"].get(s):
                    print(f"         {s:8s} recorded {want['results'].get(s)}  "
                          f"now {got['results'].get(s)}")
            if got["not_applicable"] != want["not_applicable"]:
                print(f"         not applicable recorded {want['not_applicable']}  "
                      f"now {got['not_applicable']}")
        for i, m in enumerate(row.get("mutants", [])):
            label = f"{row['library']} mutant {m['name']!r} ({m['set']})"
            try:
                msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
                so = build_mceliece(row["build"], msrc, m["set"], workdir, tag=f"-mcmut{i}")
            except (RuntimeError, subprocess.CalledProcessError) as e:
                print(f"  ERROR  {label}: {e}")
                return 2
            got = audit_mceliece(so, m["set"], prefix_for(row, m["set"], m))
            missed = [f"{st} {p}/{t}" for st in m["fails"]
                      for p, t in [(got or {"results": {}})["results"].get(st, (0, 0))]
                      if not (t and p < t)]
            if got is not None and not missed:
                bad = sorted(s for s, (p, t) in got["results"].items() if p < t)
                print(f"  caught {label}: fails {', '.join(bad)}")
                continue
            failures += 1
            print(f"  MISSED {label}: the audit did not fail "
                  + (", ".join(missed) if got else "(could not audit it)")
                  + ". pq-verify cannot see this bug class.")
    if failures:
        print(f"\n  {failures} Classic McEliece row(s) or mutant(s) differ. Fix the regression, "
              f"or, if intended, update tools/vendor_audits.json and AUDITS.md in "
              f"the same PR and say why.")
        return 1
    return 0


def check_hqc(rows, workdir):
    """HQC's code layer (standard not final): each row's sets as recorded --
    a row may record findings, the library's own defects, which must then
    reproduce exactly -- and every mutant failed in the stages it names."""
    failures = 0
    for row in rows:
        src = Path(workdir) / f"hqc-{row['build']}" / row["commit"][:12]
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
        except Exception as e:
            print(f"  ERROR  {row['library']} @ {row['commit'][:7]}: fetch failed: {e}")
            return 2
        for ps in row["sets"]:
            label = f"{row['library']} @ {row['commit'][:7]} {ps}"
            try:
                so = build_hqc(row["build"], src, ps, workdir, tag=f"-{row['commit'][:7]}")
            except subprocess.CalledProcessError as e:
                print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
                return 2
            got = audit_hqc(so, ps, row["profile"], row["seed"], prefix_for(row, ps))
            want = {"results": row["results"][ps]}
            if got == want:
                p, t = total(got["results"])
                print(f"  ok     {label}: {p}/{t}, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}")
            if got is None:
                print("         pq-verify could not audit it (entry points not resolved)")
                continue
            for st in sorted(set(got["results"]) | set(want["results"])):
                if got["results"].get(st) != want["results"].get(st):
                    print(f"         {st:11s} recorded {want['results'].get(st)}  "
                          f"now {got['results'].get(st)}")
        for i, m in enumerate(row.get("mutants", [])):
            label = f"{row['library']} mutant {m['name']!r} ({m['set']})"
            try:
                msrc = mutate(src, m, Path(workdir) / "mutants" / f"hqc-{row['build']}")
                so = build_hqc(row["build"], msrc, m["set"], workdir, tag=f"-hqcmut{i}")
            except (RuntimeError, subprocess.CalledProcessError) as e:
                print(f"  ERROR  {label}: {e}")
                return 2
            got = audit_hqc(so, m["set"], row["profile"], row["seed"],
                            prefix_for(row, m["set"], m))
            missed = [f"{st} {p}/{t}" for st in m["fails"]
                      for p, t in [(got or {"results": {}})["results"].get(st, (0, 0))]
                      if not (t and p < t)]
            if got is not None and not missed:
                bad = sorted(st for st, (p, t) in got["results"].items() if p < t)
                print(f"  caught {label}: fails {', '.join(bad)}")
                continue
            failures += 1
            print(f"  MISSED {label}: the audit did not fail "
                  + (", ".join(missed) if got else "(could not audit it)")
                  + ". pq-verify cannot see this bug class.")
    if failures:
        print(f"\n  {failures} HQC row(s) or mutant(s) differ. Fix the regression, or, if "
              f"intended, update tools/vendor_audits.json and AUDITS.md in the same PR "
              f"and say why.")
        return 1
    return 0


# ─────────────────────────────── table ───────────────────────────────

def edge_total(row):
    return tuple(sum(row["edge"][ps][s][i] for ps in row["sets"] for s in EDGE_STAGES)
                 for i in (0, 1))


def markdown(rows):
    lines = ["| Library | Commit | Sets | keyGen | encaps | decaps | ekCheck "
             "| dkCheck | Edge cases | Accumulated | Constant time | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        e = row["expected"]
        ct = row.get("ct", {})
        cp, cq = (sum(v[i] for ps in ct for v in ct[ps].values()) for i in (0, 1))
        nm = len(row.get("mutants", [])) + len(row.get("ct_mutants", []))
        p, t = total(e)
        ep, et = edge_total(row)
        acc = row.get("accumulated", {})
        ap, at = (sum(acc[ps][i] for ps in acc) for i in (0, 1))
        ok = p == t and ep == et and ap == at and cp == cq
        verdict = "**VERIFIED**" if ok else "findings"
        sets = " / ".join(s.rsplit("-", 1)[1] for s in row["sets"])
        cells = [f"{e[s][0]}/{e[s][1]}" for s in STAGES]
        lines.append(f"| {row['library']} | [`{row['commit'][:7]}`]"
                     f"({row['url']}/commit/{row['commit']}) ({row['date']}) "
                     f"| {sets} | " + " | ".join(cells) +
                     f" | {ep:,}/{et:,} | {f'{ap}/{at}' if at else '—'} "
                     f"| {f'{cp}/{cq}' if cq else '—'} | {f'{nm}/{nm}' if nm else '—'} "
                     f"| {p}/{t} + {ep:,}/{et:,}{f' + {ap}/{at}' if at else ''} {verdict} |")
    return "\n".join(lines)


def dsa_markdown(rows):
    lines = ["| Library | Commit | Sets | keyGen | sigGen int / pure / pre-hash / μ "
             "| sigVer int / pure / pre-hash / μ | Wycheproof verify / sign / length "
             "| Accumulated | Not applicable | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        def cell(stages):
            out = []
            for s in stages:
                p = sum(row["results"][ps].get(s, [0, 0])[0] for ps in row["sets"])
                t = sum(row["results"][ps].get(s, [0, 0])[1] for ps in row["sets"])
                out.append(f"{p}/{t}" if t else "n/a")
            return " / ".join(out)
        p, t = (sum(v[i] for ps in row["sets"] for v in row["results"][ps].values())
                for i in (0, 1))
        na = sum(row["not_applicable"][ps] for ps in row["sets"])
        muts = row.get("mutants", [])
        sets = " / ".join(s.rsplit("-", 1)[1] for s in row["sets"])
        lines.append(" | ".join([
            f"| {row['library']}",
            f"[`{row['commit'][:7]}`]({row['url']}/commit/{row['commit']}) ({row['date']})",
            sets, cell(["keyGen"]),
            cell(["sigGenInternal", "sigGenPure", "sigGenPreHash", "sigGenMu"]),
            cell(["sigVerInternal", "sigVerPure", "sigVerPreHash", "sigVerMu"]),
            cell(list(DSA_EDGE_STAGES)), cell(["accumulated"]), f"{na:,}",
            f"{len(muts)}/{len(muts)}" if muts else "—",
            f"{p:,}/{t:,} {'**VERIFIED**' if p == t else 'findings'} |"]))
    return "\n".join(lines)


def hbs_markdown(rows):
    lines = ["| Library | Commit | Schemes | Verify | keyGen | sigGen | Malformed rejected "
             "| Key state | Not applicable | Not run | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        r = row["results"]

        def cell(kind):
            ks = [k for k in r if k.split(" ")[1].startswith(kind)]
            if not ks:
                return "n/a"
            return f"{sum(r[k][0] for k in ks):,}/{sum(r[k][1] for k in ks):,}"
        p, t = total(r)
        muts = row.get("mutants", [])
        lines.append(" | ".join([
            f"| {row['library']}",
            f"[`{row['commit'][:7]}`]({row['url']}/commit/{row['commit']}) ({row['date']})",
            row["schemes"], cell("verify"), cell("keyGen"), cell("sigGen"),
            cell("malformed"), cell("state"), f"{row['not_applicable']:,}",
            f"{row['not_run']:,}",
            f"{len(muts)}/{len(muts)}" if muts else "—",
            f"{p:,}/{t:,} {'**VERIFIED**' if p == t else 'findings'} |"]))
    return "\n".join(lines)


def fndsa_markdown(rows):
    lines = ["| Library | Commit | Sets | Verify (pinned) | Open (pinned) | Malformed rejected "
             "| keyGen | sign | Not applicable | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        def cell(stage):
            p = sum(row["results"][ps].get(stage, [0, 0])[0] for ps in row["sets"])
            t = sum(row["results"][ps].get(stage, [0, 0])[1] for ps in row["sets"])
            return f"{p}/{t}" if t else "n/a"
        p, t = (sum(v[i] for ps in row["sets"] for v in row["results"][ps].values())
                for i in (0, 1))
        na = sum(row["not_applicable"][ps] for ps in row["sets"])
        muts = row.get("mutants", [])
        sets = " / ".join(s.rsplit("-", 1)[1] for s in row["sets"])
        lines.append(" | ".join([
            f"| {row['library']}",
            f"[`{row['commit'][:7]}`]({row['url']}/commit/{row['commit']}) ({row['date']})",
            sets, cell("verify"), cell("open"), cell("reject"), cell("keyGen"),
            cell("sign"), f"{na:,}", f"{len(muts)}/{len(muts)}" if muts else "—",
            f"{p:,}/{t:,} {'**VERIFIED** (draft)' if p == t else 'findings'} |"]))
    return "\n".join(lines)


def mceliece_markdown(rows):
    lines = ["| Library | Commit | Sets | keyGen (regenerated) | encaps | decaps (crafted) "
             "| padding | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        def cell(stage):
            p = sum(row["results"][ps].get(stage, [0, 0])[0] for ps in row["sets"])
            t = sum(row["results"][ps].get(stage, [0, 0])[1] for ps in row["sets"])
            return f"{p}/{t}" if t else "—"
        p, t = (sum(v[i] for ps in row["sets"] for v in row["results"][ps].values())
                for i in (0, 1))
        muts = row.get("mutants", [])
        lines.append(" | ".join([
            f"| {row['library']}",
            f"[`{row['commit'][:7]}`]({row['url']}/commit/{row['commit']}) ({row['date']})",
            f"all {len(row['sets'])}", cell("keyGen"), cell("encaps"), cell("decaps"),
            cell("padding"), f"{len(muts)}/{len(muts)}" if muts else "—",
            f"{p:,}/{t:,} {'**VERIFIED**' if p == t else 'findings'} |"]))
    return "\n".join(lines)


def hqc_markdown(rows):
    lines = ["| Library | Commit | Profile | Sets | encode | rm-decode | rs-decode "
             "| code-decode | bounds | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        def cell(stage):
            p = sum(row["results"][ps].get(stage, [0, 0])[0] for ps in row["sets"])
            t = sum(row["results"][ps].get(stage, [0, 0])[1] for ps in row["sets"])
            return (f"{p}/{t}" if p == t else f"**{p}/{t}**") if t else "—"
        p, t = (sum(v[i] for ps in row["sets"] for v in row["results"][ps].values())
                for i in (0, 1))
        muts = row.get("mutants", [])
        url = (f"{row['url'].removesuffix('.git')}/-/commit/{row['commit']}"
               if "gitlab.com" in row["url"] else f"{row['url']}/commit/{row['commit']}")
        lines.append(" | ".join([
            f"| {row['library']}", f"[`{row['commit'][:7]}`]({url}) ({row['date']})",
            row["profile"], ", ".join(row["sets"]), cell("encode"), cell("rm-decode"),
            cell("rs-decode"), cell("code-decode"), cell("bounds"),
            f"{len(muts)}/{len(muts)}" if muts else "—",
            f"{p:,}/{t:,} {'**VERIFIED**' if p == t else '**findings**'} |"]))
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--markdown", action="store_true",
                    help="print the AUDITS.md table from the pinned rows; no build")
    ap.add_argument("--workdir", help="where to fetch and build (default: a "
                                      "temporary directory, removed afterwards)")
    ap.add_argument("--only", choices=("ML-KEM", "ML-DSA", "LMS/XMSS", "FN-DSA", "McEliece",
                                       "HQC"),
                    help="re-audit one scheme's rows")
    a = ap.parse_args(argv)
    rows, dsa_rows, hbs_rows = load_table(), load_dsa_table(), load_hbs_table()
    fndsa_rows = load_fndsa_table()
    mce_rows = load_mceliece_table()
    hqc_rows = load_hqc_table()
    if a.markdown:
        print(markdown(rows))
        print()
        print(dsa_markdown(dsa_rows))
        print()
        print(hbs_markdown(hbs_rows))
        print()
        print(fndsa_markdown(fndsa_rows))
        print()
        print(mceliece_markdown(mce_rows))
        print()
        print(hqc_markdown(hqc_rows))
        return 0

    def run(work):
        code = 0
        if a.only in (None, "ML-KEM"):
            code = max(code, check_all(rows, work))
            code = max(code, check_ct(rows, work))
        if a.only in (None, "ML-DSA"):
            code = max(code, check_dsa(dsa_rows, work))
        if a.only in (None, "LMS/XMSS"):
            code = max(code, check_hbs(hbs_rows, work))
        if a.only in (None, "FN-DSA"):
            code = max(code, check_fndsa(fndsa_rows, work))
        if a.only in (None, "McEliece"):
            code = max(code, check_mceliece(mce_rows, work))
        if a.only in (None, "HQC"):
            code = max(code, check_hqc(hqc_rows, work))
        return code
    if a.workdir:
        return run(a.workdir)
    work = tempfile.mkdtemp(prefix="pqv-vendor-")
    try:
        return run(work)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
