# Draft Stop-Gate Decision vNext+186

Status: proposed starter gate for `V67-B`.

Authority layer: planning / starter gate.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS186.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- `V67-B` consumes the shipped `V67-A` artifact language intact and does not mint
  a new ergonomic schema family by default
- deterministic adjudication helpers evaluate only the finite repo-native
  candidate rows in the shipped candidate table
- hard-block reason families fire before any advisory ranking
- effective hard floors compose as max of applicable hard floors plus lawful
  upward user preference inflation only
- `report_status` remains artifact-validity-only
- `overall_judgment` remains ergonomic-outcome-only
- blocked candidate rows carry stable blocking reason-code families
- feasible candidate rows carry ordinal tiers only:
  - `discouraged`
  - `marginal`
  - `acceptable`
  - `preferred`
- top-tier ties that cannot be resolved by deterministic ladder rules surface as
  explicit `needs_review` posture with stable tie reason codes
- inadmissible physical / visual chains block only dependent computations and do
  not over-block CSS-only adjudication
- computed outputs preserve exact source refs and hashes
- no runtime measurement evidence artifact or runtime bridge report lands in this
  slice.

## Do Not Accept If

- `V67-B` introduces new ergonomic schema ids by default instead of computing
  over the shipped `V67-A` surfaces
- blocked candidates can become feasible through utility ranking or heuristic tie
  breaking
- `report_status` and `overall_judgment` are collapsed into one mixed status
- decimal ergonomic scores or hidden weights appear in exported results
- physical / visual inadmissibility blocks the whole adjudication when the
  dependent reasoning is not actually required
- computed outputs stop carrying exact replayable source lineage
- `V67-B` widens into runtime measurement harvesting, advisory bridge output,
  generic layout solving, or mutation of released UX diagnostics / conformance
  law.

## Local Gate

- run `git diff --check`
- run `make arc-start-check ARC=186`

Full Python lane may remain skipped here because this is a docs-only starter
bundle.
