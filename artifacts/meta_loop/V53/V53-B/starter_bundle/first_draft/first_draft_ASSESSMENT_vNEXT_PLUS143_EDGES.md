# Assessment vNext+143 Edges

Status: planning-edge assessment for `V53-B` (April 7, 2026 UTC).

Authority layer: planning support.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS143_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Scope

- In scope:
  - repo-owned `adeu_symbol_edge_adjudication_ledger@1`
  - exact downstream consumption of released `V53-A` taxonomy/probe/applicability
  - fail-closed explicit override law
  - exact starter evidence/status semantics
  - slice-local starter mapping for what is instantiated here versus deferred
- Out of scope:
  - reopening released `V53-A` taxonomy or applicability law
  - cumulative revision register / lineage
  - direct `V45-D` test-intent integration
  - repo-wide scope widening
  - broader reviewer-platform or mutation/enforcement surfaces

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md`
- `docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_EDGE_LEDGER_V53B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS141.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md`

## Open Edges

### Edge 1: `V53-B` Quietly Reopens Released `V53-A` Law

- Risk:
  the adjudication slice could claim to be downstream while actually reclassifying
  released applicability rows or changing released row order and frame membership.
- Response:
  consume one released applicability frame as authoritative input and freeze the
  adjudication ledger to full-catalog row coverage in the same released order.

### Edge 2: Contradictory Explicit Overrides Still Resolve By Silent Precedence

- Risk:
  the same edge class could still appear in both witness and checked-no-witness input
  channels and silently resolve to one preferred output.
- Response:
  contradictory explicit override input must fail closed at the ledger boundary.

### Edge 3: Out-Of-Frame Explicit Overrides Still Disappear Silently

- Risk:
  a caller could submit explicit override evidence for an edge class not present in the
  released applicability frame and the helper could ignore it without audit signal.
- Response:
  every explicit override ref must already exist in the bound frame or the ledger must
  reject the input fail-closed.

### Edge 4: Explicit Overrides Still Outrank `not_applicable`

- Risk:
  explicit witness or checked-no-witness evidence could still force a positive result
  against a source row whose released applicability status is `not_applicable`.
- Response:
  `not_applicable` rows remain closed to explicit override input in starter `V53-B`.

### Edge 5: Soft Evidence Is Still Laundered Into Positive Status

- Risk:
  lexical test adjacency or structural cue overlap could re-enter through adjudication
  statuses like `covered_by_existing_tests` or `bounded_safe_by_structure`.
- Response:
  explicitly forbid those statuses in starter `V53-B` and require typed explicit
  evidence for all positive adjudication statuses.

### Edge 6: `underdetermined` Rows Are Promoted Too Aggressively

- Risk:
  starter adjudication could use explicit evidence to settle rows whose released
  applicability posture is still `underdetermined`, thereby weakening the authority of
  `V53-A`.
- Response:
  keep `underdetermined` rows either `underdetermined` or `deferred` in starter
  `V53-B`, with no positive promotion yet.

### Edge 7: Ledger Support Fields Stay Ambiguous

- Risk:
  the ledger could emit statuses without enough support-field discipline to audit
  whether witness versus checked-no-witness evidence was actually used.
- Response:
  freeze exact empty/non-empty rules for `supporting_witness_refs`,
  `supporting_checked_no_witness_refs`, and `deferral_reason` by status.

### Edge 8: Adjudication Coverage Collapses Back Into Sparse Positive Rows

- Risk:
  the new ledger could emit only rows with explicit evidence and leave the rest ambient.
- Response:
  require one adjudication row for every released edge class in catalog order, not only
  the positive or overridden rows.

### Edge 9: Revision/Register Semantics Sneak In Through Adjudication Vocabulary

- Risk:
  starter adjudication could begin to carry split/merge/history semantics that belong
  to `V53-C`.
- Response:
  keep `V53-B` bounded to per-symbol adjudication only and defer cumulative
  revision/register work explicitly to `V53-C`.

### Edge 10: Test-Intent Integration Reappears Too Early

- Risk:
  the adjudication lane could try to justify itself by directly consuming released
  `V45-D` test-intent surfaces before the core ledger semantics are stable.
- Response:
  keep `V53-B` bounded to released `V53-A` plus typed explicit override input only and
  defer test-intent integration explicitly to `V53-D`.

## Current Judgment

- `V53-B` is the right next slice because the strongest remaining blocker cluster from
  the imported prototype is no longer taxonomy or applicability:
  - contradictory override precedence
  - out-of-frame override dropping
  - applicability-violating overrides
  - overclaimed evidence/status semantics
- the proposed starter bundle is directionally correct and properly bounded when read
  against the controlling planning, support-mapping, and intake docs:
  - one new adjudication ledger contract only
  - exact downstream consumption of released `V53-A`
  - one explicit fail-closed override law
  - one exact starter evidence/status law
  - no release of proof-flavored soft-evidence statuses
  - explicit deferment of revision/register and test-intent seams
- the main remaining review focus should be whether the starter row-mapping law is
  finite and tight enough that implementation cannot recover adjudication semantics by
  helper taste.
