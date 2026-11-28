"""
pq_verify.verdict -- a report's verdict, from each stage's outcome.

An audit reduces to stages, and each stage to one outcome:

  pass             checked, and every case passed
  fail             checked, and a case failed: a finding
  cannot_check     asked for and could not be checked (a tool that is not
                   installed, a run that stopped): not a finding, not a pass
  not_run          expected, and nothing reached it
  not_applicable   does not exist for this library or parameter set (an
                   entry point it does not have): not a gap

The verdict follows from the outcomes, and from whether there are findings
outside the stages (the ML-DSA audit's randomness checks), and from nothing
else:

  VERIFIED          a stage passed, every stage passed or does not apply,
                    and there is no finding outside the stages
  FINDINGS PRESENT  a stage failed, or there is a finding outside them
  CANNOT VERIFY     anything else: nothing was checked, or every stage that
                    did not pass could not be checked or was not run

Each audit keeps its own policy: which stages it requires, which do not
apply, and what a stage's cases are. finalize() gives a report its status
and `verified` from the rule, after checking the report's own fields agree
with the outcomes. A report that disagrees with them is a pq-verify defect:
it is CANNOT VERIFY, and says so in its findings.

The tests enumerate every combination of outcomes, up to five stages, with
and without findings outside them, against the rule as written above. That
validates this function on its whole modelled domain. It is not a proof of
the Python around it: an audit that reports the wrong outcome for a stage
gets the verdict that outcome deserves.

Migration: the reports that go through finalize() are listed in
tests/test_pqverify.py (_FINALIZED); every other report builder is listed
there as not yet migrated, so a new one cannot bypass both lists.
"""
from .coverage import NOT_RUN as _NOT_RUN_PREFIX

PASS, FAIL, CANNOT_CHECK, NOT_RUN, NOT_APPLICABLE = (
    "pass", "fail", "cannot_check", "not_run", "not_applicable")
OUTCOMES = (PASS, FAIL, CANNOT_CHECK, NOT_RUN, NOT_APPLICABLE)
VERIFIED, FINDINGS, CANNOT = "VERIFIED", "FINDINGS PRESENT", "CANNOT VERIFY"


def _cases(stage, counts):
    """(passed, total) as two integers 0 <= passed <= total, or ValueError."""
    try:
        p, t = counts
    except (TypeError, ValueError):
        raise ValueError(f"stage {stage!r}: {counts!r} is not (passed, total)") from None
    if not all(type(x) is int for x in (p, t)) or not 0 <= p <= t:
        raise ValueError(f"stage {stage!r}: {counts!r} is not (passed, total)")
    return p, t


def stage_outcomes(tally, required=(), cannot=(), not_applicable=()):
    """Each stage's outcome.

    `tally` maps a stage to its (passed, total) cases. A stage in `cannot`
    that has a failing case could not be checked; one named
    "not_run:<stage>" (pq_verify.coverage) or with no case was not run. A
    stage in `not_applicable` and not in the tally does not apply. A
    `required` stage in neither was not run. Counts that are not two
    integers 0 <= passed <= total raise ValueError: a malformed tally is a
    pq-verify defect, never a pass."""
    out = {}
    for stage, counts in tally.items():
        p, t = _cases(stage, counts)
        if stage.startswith(_NOT_RUN_PREFIX) or t == 0:
            out[stage] = NOT_RUN
        elif p < t:
            out[stage] = CANNOT_CHECK if stage in cannot else FAIL
        else:
            out[stage] = PASS
    for stage in not_applicable:
        out.setdefault(stage, NOT_APPLICABLE)
    for stage in required:
        out.setdefault(stage, NOT_RUN)
    return out


def verdict(outcomes, findings=False):
    """(status, verified) from the stages' outcomes, as the module says."""
    values = list(outcomes.values())
    bad = sorted(str(s) for s, o in outcomes.items() if o not in OUTCOMES)
    if bad:
        raise ValueError(f"not an outcome, for stage(s) {', '.join(bad)}")
    if findings or FAIL in values:
        return FINDINGS, False
    if PASS in values and all(o in (PASS, NOT_APPLICABLE) for o in values):
        return VERIFIED, True
    return CANNOT, False


def disagreements(doc, outcomes, status):
    """Where a report's own fields disagree with its outcomes and status:
    a stage's counts against its outcome, a stage without an outcome, the
    summary's counts against the stages', and the findings listed against
    the status. Empty when they agree."""
    out = []
    stages = doc.get("stages") or {}
    for stage, v in stages.items():
        o, p, t = outcomes.get(stage), v.get("passed"), v.get("total")
        if o is None:
            out.append(f"stage {stage} has no outcome")
        elif o == PASS and not (t and p == t):
            out.append(f"stage {stage} is a pass at {p}/{t}")
        elif o in (FAIL, CANNOT_CHECK) and not (isinstance(p, int) and isinstance(t, int)
                                               and p < t):
            out.append(f"stage {stage} is {o} at {p}/{t}")
    for stage, o in outcomes.items():
        if o in (PASS, FAIL) and stage not in stages and stages:
            out.append(f"stage {stage} is {o} and not among the stages reported")
    summary = doc.get("summary") or {}
    if stages and "checks_total" in summary:
        counted = (sum(v.get("passed", 0) for v in stages.values()),
                   sum(v.get("total", 0) for v in stages.values()))
        if (summary.get("checks_passed"), summary.get("checks_total")) != counted:
            out.append(f"the summary counts {summary.get('checks_passed')}/"
                       f"{summary.get('checks_total')}, the stages {counted[0]}/{counted[1]}")
    listed = doc.get("findings") or []
    if status == VERIFIED and listed:
        out.append(f"verified with {len(listed)} finding(s) listed")
    if status != VERIFIED and not listed:
        out.append(f"{status} with no finding listed to say why")
    return out


def finalize(doc, outcomes, findings=False):
    """Give the report `doc` its status, `verified` and `outcomes` from the
    rule. If the report's own fields disagree with the outcomes, it is not
    verified: CANNOT VERIFY, with a finding naming each disagreement."""
    status, verified = verdict(outcomes, findings)
    problems = disagreements(doc, outcomes, status)
    if problems:
        status, verified = CANNOT, False
        doc["findings"] = list(doc.get("findings") or []) + [
            "cannot verify: the report disagrees with its own checks ("
            + "; ".join(problems) + "), a pq-verify defect"]
        if isinstance(doc.get("summary"), dict) and "findings" in doc["summary"]:
            doc["summary"]["findings"] = len(doc["findings"])
    doc["status"], doc["verified"] = status, verified
    doc["outcomes"] = dict(sorted(outcomes.items()))
    return doc
