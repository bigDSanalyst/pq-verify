# Re-pinning NIST vectors

pq-verify ships a frozen snapshot of NIST's ACVP vectors, so a result means the
same thing on every machine and every day. NIST corrects those files from time
to time. This is the procedure for taking a correction, and for refusing a bad
one.

Why it exists: 2.8.0 shipped NIST's `c924096` ML-KEM files, whose invalid
encapsulation keys were 416 bytes too long. Every "invalid key" check passed on
length alone, the ACVP suite still reported 240/240, and NIST had already
published the fix (`ad33b3d`). Nothing was wrong with the watcher; no step
between "NIST changed" and "bundle re-cut" was ever run. The doctor runs them.

## The steps

**1. The watcher reports a change.** The weekly workflow opens (or comments on)
an issue: *NIST ACVP vectors changed upstream*. Nothing in the package changes.

**2. Run the doctor against NIST's current files.**

```bash
python3 tools/doctor.py --candidate
```

It writes nothing. It fetches the changed files into a scratch directory and
runs, against pinned and candidate side by side:

| Check | Refuses the candidate when |
|---|---|
| `keycheck:candidate` | a key-check key does not have its FIPS 203 length |
| `control` | a length-only checker is **not** fooled by every invalid key — i.e. some invalid key is rejected on length alone and tests nothing |
| `suite:ML-KEM` / `ML-DSA` / `SLH-DSA` | the reference implementations do not pass the candidate in full |
| `parse:<file>` | a file is not valid JSON (NIST mid-publish) |
| `stable` | a change is younger than 14 days (NIST has reverted within a day) |
| `provenance` | the NIST commit behind a file cannot be named |

**3. Read the verdict.**

| Result | Meaning | Do |
|---|---|---|
| any `BLOCK` | the candidate is wrong, or cannot be shown right | do not pin; if NIST's files are malformed, report it at `usnistgov/ACVP-Server` |
| `DECIDE stable` | sound so far, but recent | wait; re-run after the date it names |
| `WARN provenance` | the GitHub API was unreachable | find the commit (the doctor prints the `git log` command) and pass `--commit FILE=SHA` |
| all `ok` | safe to pin | step 4 |

A suite failing on the candidate is a finding, not noise: either NIST's new
answers or a reference implementation is wrong. Compare the failing tcIds
against NIST's commit message before deciding which.

**4. Re-pin.**

```bash
python3 tools/doctor.py --candidate --apply
```

`--apply` is refused while anything on the candidate side BLOCKs, while any
change is under 14 days old, or while a NIST commit is unknown. It rewrites the
bundle and `MANIFEST.json` (with each file's `nist_commit`) deterministically —
the same inputs always produce byte-identical files — and then re-checks what
it wrote, from disk.

The vectors live in two archives. `acvp_vectors.json.gz` holds every suite's
files as parsed JSON; `slhdsa_sig_vectors.json.gz` holds the SLH-DSA sigGen and
sigVer files as NIST's text verbatim, so the doctor checks each against its
`MANIFEST.json` sha256 offline. `--apply` rewrites only the archive that holds a
changed file. A changed SLH-DSA sigGen file is re-checked by signing all 624
vectors, which takes about half an hour.

**5. Record and release.**

- Add the revisions to the table in `pq_verify/vectors/PROVENANCE.md`, and the
  superseded ones below it, with NIST's reason.
- Add a CHANGELOG entry. Say what changes for users:
  - **counts** — if NIST added or removed tests, the ACVP totals change;
  - **prompt IDs** — `--emit-prompt` IDs change for every parameter set whose
    questions changed, so outstanding prompts must be re-issued;
  - **old results** — the previous release still reproduces them.
- Run `pytest` and `python3 tools/doctor.py` (it must be all `ok`), then open a
  PR. A re-pin is a patch release unless the counts or schema changed.

## What is never done

- Pinning a candidate the doctor BLOCKs, or hand-editing the bundle to get past
  one. If a check is wrong, fix the check in its own PR, with a test.
- Pinning from `--live` results. `--live` is for comparing against NIST today;
  the bundle is only ever changed through `--apply`.
- Advancing `tools/vector_state/baseline.json` without re-cutting the bundle.
  That is how 2.8.0 came to ship stale vectors: the watcher's record moved and
  the package did not. The watcher now also compares NIST against
  `MANIFEST.json`, so it keeps reporting until the bundle catches up.
