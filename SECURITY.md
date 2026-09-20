# Security Policy

## Reporting a vulnerability

Report privately through GitHub's **[Report a vulnerability]** button on the
[Security tab](https://github.com/bigDSanalyst/pq-verify/security/advisories/new).
Please do not open a public issue for a security problem.

Expect an acknowledgement within 7 days. If you have not heard back in that
time, escalate by opening a public issue that says only that you sent a private
report and have not had a reply — no details.

## Supported versions

| Version | Supported |
|---------|-----------|
| 2.8.x   | yes |
| < 2.8   | no — upgrade |

## What pq-verify does on purpose

**Auditing an untrusted library executes it.** `--audit-so` and `--audit-kem`
call `dlopen` on the path you give them, and loading a shared object runs its
initialisers before pq-verify calls anything. That is not a flaw — driving the
vendor's own code with NIST's vectors is the entire point — but it means:

> **Treat `--audit-so` / `--audit-kem` as running the vendor's code, because
> that is what it does.** Audit unfamiliar binaries inside a container, a VM, or
> a throwaway user account, not on a build host with credentials on it.

The prompt/response path (`--emit-prompt` / `--verify-response`) exists partly
for this reason: it never loads anything, so it carries none of this risk. The
report says which applies to each run, in the `artifact` field.

Other things that are deliberate, not bugs:

- **The C engines are compiled at runtime** with `gcc`, from source embedded in
  `pq_verify/core.py`, into a private `0700` directory created per process.
  Where no compiler is available the affected checks are reported as skipped
  rather than passed.
- **`PQV_CFL_SO`**, if set, is `dlopen`ed. It must be an absolute path, it is
  never discovered implicitly, and it is only an optional benchmark.
- **Vectors are pinned and offline by default.** `--live` opts in to fetching
  from NIST's GitHub; only then does the tool make a network request.

## Out of scope

- Findings that require an attacker who can already write the files you are
  asking pq-verify to audit, or the package's own installed files.
- Optional dependencies (`kyber-py`, `dilithium-py`, `sympy`, `coq`,
  `cryptominisat`) — report those upstream.
- The parameter estimator producing a different security estimate than another
  estimator. That is a modelling disagreement; open a normal issue with the
  parameters so it can be compared.

## Fixed in 2.7.0

Both were found by auditing this repository against its own standards, and both
are demonstrated by tests in `tests/test_pqverify.py` so they cannot return.

- **Untrusted library load (CWE-426).** The CFL benchmark loaded
  `./libgf2_cfl.so` from the current working directory and `/tmp/libgf2_cfl.so`
  if either existed. `ctypes.CDLL` runs a library's constructors, so anyone who
  could write the directory pq-verify ran in — routinely a vendor build tree or
  an extracted tarball — or any local user, via `/tmp`, got arbitrary code
  execution inside the verifying process. The library is now opt-in by absolute
  path via `PQV_CFL_SO` and is never discovered implicitly.
- **Symlink-following writes to predictable paths (CWE-59).** Generated C and
  Coq sources were written to fixed paths such as `/tmp/pqv_gf2.c`.
  `open(path, 'w')` follows symlinks, so a local user who pre-created one of
  those paths as a symlink caused an arbitrary file overwrite with the running
  user's privileges. All generated files now go to a per-process `mkdtemp`
  directory with mode `0700`.

Users of 2.6.7 and earlier on shared or multi-user hosts should upgrade.
