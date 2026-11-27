"""
pq_verify.coverage -- a verdict covers only what ran.

A stage that NIST publishes vectors for, which the library can be asked, and
which no vector reached, was not checked; an audit that did not check it is
not verified. The pinned bundle is the measure of what NIST publishes for a
parameter set, whatever source a run reads (the bundle itself, a
--vector-dir, or NIST's live files): each audit lists the stages the bundle
has groups for, keeps those the library has an entry point for, and fails
any that no vector reached as "not_run:<stage>", reported as "no NIST vector
ran, so it was not checked" (rule PQV000). With the pinned bundle as the
source every such stage is reached, so this changes nothing there; it is
what stops a directory, or a live file, that lacks a group from verifying a
library that was never asked it.

A run whose only failures are of that kind, or of another check that could
not run (constant time requested and unavailable, a vector that could not be
run), is CANNOT VERIFY, not FINDINGS PRESENT: nothing was found.

The ACVP suites check pq-verify's own references, not a library, against the
vectors a run reads. A group the bundle has and that source lacks is listed,
and the run is marked degraded (DEGRADED['skipped_checks'], so the integrity
report says so and --require-full-coverage fails it); no line claims every
group, set or level ran unless every one did.
"""
import os

NOT_RUN = "not_run:"
WHY = "no NIST vector ran, so it was not checked"


def pinned(suite, name):
    """One file of the pinned bundle, e.g. ("ML-DSA-sigVer-FIPS204", "prompt.json")."""
    from .core import _load_vector_json, _pkg_dir
    return _load_vector_json(os.path.join(_pkg_dir(), "vectors", suite, name),
                             f"{suite}/{name}")


def groups(doc, param_set=None):
    """A vector file's test groups that hold at least one test, for one
    parameter set or for every set."""
    for g in (doc or {}).get("testGroups", ()):
        if g.get("tests") and (param_set is None or g.get("parameterSet") == param_set):
            yield g


def require(tally, expected, not_applicable=()):
    """Fail each stage of `expected` that no vector reached -- absent from the
    tally, or there with no case, and not reported not applicable -- as
    tally["not_run:<stage>"] = (0, 1). Returns those stages, sorted."""
    gone = sorted(s for s in expected
                  if not tally.get(s, (0, 0))[1] and s not in not_applicable)
    for s in gone:
        tally[NOT_RUN + s] = (0, 1)
    return gone


def status(verified, tally, cannot=(), findings=False):
    """The run's status. VERIFIED when it verified. CANNOT VERIFY when nothing
    was checked, or when every failing stage is one that could not be
    checked: a stage no vector reached, or one named in `cannot`. Otherwise
    FINDINGS PRESENT; `findings` says there are findings outside the tally
    (the ML-DSA audit's randomness checks), which always count."""
    if verified:
        return "VERIFIED"
    if findings:
        return "FINDINGS PRESENT"
    failing = [s for s, (p, t) in tally.items() if p < t]
    if all(s.startswith(NOT_RUN) or s in cannot for s in failing):
        return "CANNOT VERIFY"
    return "FINDINGS PRESENT"


def finding(stage):
    """The finding for a stage no vector reached."""
    return f"stage {stage}: {WHY}"


def missing(suite, seen, expected):
    """The vector groups `expected` holds and `seen` does not, sorted: groups
    the vectors read lack, or hold and the suite could not run. When there
    are any, the run is degraded: the integrity report lists the suite, and
    --require-full-coverage fails the run."""
    gone = sorted(set(expected) - set(seen))
    if gone:
        from .core import DEGRADED
        DEGRADED["skipped_checks"].append(
            f"{suite} ({len(gone)} vector group(s) of the pinned bundle not run)")
    return gone


def print_missing(gone, limit=8):
    """The report lines for what a suite's source lacked."""
    if not gone:
        return
    print(f"  NOT RUN: {len(gone)} vector group(s) the pinned bundle has did not run "
          f"from the vectors read:")
    for g in gone[:limit]:
        print(f"    - {g}")
    if len(gone) > limit:
        print(f"    ... and {len(gone) - limit} more")
