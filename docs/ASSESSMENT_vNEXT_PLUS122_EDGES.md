# Assessment vNext+122 Edges

Status: pre-lock edge assessment for `V50-B` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS122_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Closure Truth Laundering

- Risk:
  semantic-audit rows could quietly redefine or supersede released `V50-A` completion
  truth.
- Planned Response:
  keep closure/completion in released `V50-A` only and treat `V50-B` uncertainty rows
  as ledger support, not closure truth.

### Edge 2: Hidden `V49` Smuggling

- Risk:
  implementation could import released `V49` terminology or fields without an explicit
  family decision and accidentally create a second hidden bridge.
- Planned Response:
  freeze explicit independence from released `V49` primitives in this slice and fail
  closed on ambient `V49` coupling.

### Edge 3: Duplicate Or Missing Audit Coverage

- Risk:
  a ledger artifact could omit census symbols or duplicate them while still looking
  superficially complete.
- Planned Response:
  require exactly one audit row per released census symbol and fail closed on missing
  or duplicate `symbol_id`s.

### Edge 4: Evidence-Thin Hypothesis Laundering

- Risk:
  hypotheses could ship without enough explicit evidence to support review.
- Planned Response:
  require at least one `evidence_ref` and at least one `source_span` per audit row.

### Edge 5: Status Inflation

- Risk:
  low-confidence or unresolved rows could be silently upgraded into stronger statuses
  by implementation taste.
- Planned Response:
  freeze the starter `audit_status` and `confidence_band` vocabularies and reject
  unsupported values.

### Edge 6: Non-Deterministic Audit Ordering

- Risk:
  repeated runs over the same census could reorder rows and make replay unstable.
- Planned Response:
  key ordering to released census order and require byte-identical replay.

### Edge 7: Prototype Precedent Laundering

- Risk:
  the imported bundle could be copied into live paths or treated as authority rather
  than shaping evidence.
- Planned Response:
  keep the bundle support-only and re-author the live `spu.py`, models, fixtures, and
  tests in repo-native form.
