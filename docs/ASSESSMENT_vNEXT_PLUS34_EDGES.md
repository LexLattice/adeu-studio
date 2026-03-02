# Assessment vNext+34 Edges (Draft)

This document tracks v34 (`V31-C`, `H1`-`H2`) edge assessment and pre-freeze calibration notes.

Status: draft working notes (not frozen).

## Scope

- Formal ODEU evidence contract closure (`H1`)
- Formal-lane determinism/regression guards (`H2`)

## Timeout Calibration Evidence (Pre-Freeze)

Calibration target:

- `formal_lean_timeout_ms = 15000`
- CI lane: `.github/workflows/ci.yml` job `lean-formal`

Required evidence rule (from lock draft):

- Record at least two CI-run observations for timed formal checks before freeze.

Observed runs:

1. Pending
2. Pending

## Open Edges (Draft)

- Process-group timeout cleanup correctness on Linux/POSIX lane.
- Cold-start warm-up effectiveness before timed pytest execution.
- Structured reason-token coverage for:
  - `LEAN_TIMEOUT`
  - `LEAN_NONZERO_EXIT`
  - `LEAN_LAUNCH_FAILED`
  - `SEMANTICS_VERSION_MISMATCH`

## Notes

- This file is assessment evidence only; it does not authorize runtime contract changes.
