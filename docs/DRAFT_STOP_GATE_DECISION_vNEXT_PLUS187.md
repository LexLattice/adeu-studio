# Draft Stop-Gate Decision vNext+187

Status: proposed starter gate for `V67-C`.

Authority layer: planning / starter gate.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS187.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- `V67-C` consumes the shipped ergonomic adjudication lineage intact and does
  not reopen `V67-A` or `V67-B` law
- the slice emits only the bounded runtime-bridge pair:
  - `ux_ergonomic_runtime_measurement_evidence@1`
  - `ux_ergonomic_runtime_bridge_report@1`
- bridge helpers preserve exact source refs and hashes across adjudication and
  realized evidence
- bridge statuses stay advisory-only:
  - `advisory_clean`
  - `advisory_drift_detected`
  - `advisory_incomplete_missing_evidence`
  - `invalid_basis_mismatch`
  - `invalid_runtime_evidence_shape`
- advisory bridge status remains separate from prior ergonomic
  `overall_judgment`
- advisory bridge status remains separate from released UX conformance posture
- missing required runtime evidence is surfaced explicitly
- runtime provenance inadmissibility is surfaced explicitly
- realized drift is surfaced only through stable mismatch-family rows
- `ux_morph_diagnostics@1` and `ux_conformance_report@1` remain unchanged
- no runtime adaptation daemon or direct runtime layout authority lands in this
  slice.

## Do Not Accept If

- `V67-C` mutates released UX diagnostics / conformance artifacts instead of
  emitting its own bounded bridge artifacts
- runtime bridge status is collapsed into ergonomic `overall_judgment` or into
  released conformance posture
- missing runtime evidence is treated as silent success
- screenshot-only evidence is overread as authoritative runtime evidence
- runtime bridge mismatch families drift into unstable prose strings
- `V67-C` widens into adaptive runtime control, direct layout mutation, or a
  generic layout solver.

## Local Gate

- run `git diff --check`
- run `make arc-start-check ARC=187`

Full Python lane may remain skipped here because this is a docs-only starter
bundle.
