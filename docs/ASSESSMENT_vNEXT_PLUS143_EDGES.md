# Assessment vNext+143 Edges

Status: post-closeout edge assessment for `V53-B` (April 7, 2026 UTC).

Authority layer: closeout evidence on `arc/v53-r4`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS143_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V53-B` Quietly Reopens Released `V53-A` Law

- Risk:
  the adjudication slice could claim to be downstream while actually reclassifying
  released applicability rows or changing released row order and frame membership.
- Response:
  consume one released applicability frame as authoritative input and freeze the
  adjudication ledger to full-catalog row coverage in the same released order.
- Closeout Evidence:
  the shipped validator requires every adjudication row to match the bound frame and
  cover every frame row exactly once in frame order.

### Edge 2: Contradictory Explicit Overrides Still Resolve By Silent Precedence

- Risk:
  the same edge class could still appear in both witness and checked-no-witness input
  channels and silently resolve to one preferred output.
- Response:
  contradictory explicit override input must fail closed at the ledger boundary.
- Closeout Evidence:
  the shipped derivation helper rejects contradictory override input directly, and
  review-hardening commit `2ae752a` added explicit contradictory deferred-support
  rejection coverage in models/tests.

### Edge 3: Out-Of-Frame Explicit Overrides Still Disappear Silently

- Risk:
  a caller could submit explicit override evidence for an edge class not present in the
  released applicability frame and the helper could ignore it without audit signal.
- Response:
  every explicit override ref must already exist in the bound frame or the ledger must
  reject the input fail-closed.
- Closeout Evidence:
  the shipped helper rejects witness and checked-no-witness refs that do not already
  exist in the applicability frame, and the adjudication test suite covers that path.

### Edge 4: Explicit Overrides Still Outrank `not_applicable`

- Risk:
  explicit witness or checked-no-witness evidence could still force a positive result
  against a source row whose released applicability status is `not_applicable`.
- Response:
  `not_applicable` rows remain closed to explicit override input in starter `V53-B`.
- Closeout Evidence:
  the shipped helper rejects explicit override input against `not_applicable` rows, and
  the adjudication tests exercise that failure path.

### Edge 5: Soft Evidence Is Still Laundered Into Positive Status

- Risk:
  lexical test adjacency or structural cue overlap could re-enter through adjudication
  statuses like `covered_by_existing_tests` or `bounded_safe_by_structure`.
- Response:
  explicitly forbid those statuses in starter `V53-B` and require typed explicit
  evidence for all positive adjudication statuses.
- Closeout Evidence:
  the shipped adjudication vocabulary remains bounded to `not_applicable`,
  `applicable_unchecked`, `witness_found`, `checked_no_witness_found`,
  `underdetermined`, and `deferred`, with positive statuses driven only by typed
  witness or checked-no-witness inputs.

### Edge 6: `underdetermined` Rows Are Promoted Too Aggressively

- Risk:
  starter adjudication could use explicit evidence to settle rows whose released
  applicability posture is still `underdetermined`, thereby weakening the authority of
  `V53-A`.
- Response:
  keep `underdetermined` rows either `underdetermined` or `deferred` in starter
  `V53-B`, with no positive promotion yet.
- Closeout Evidence:
  the shipped helper emits a frozen deferral reason for explicit-evidence
  `underdetermined` rows and never promotes them to `witness_found` or
  `checked_no_witness_found`.

### Edge 7: Ledger Support Fields Stay Ambiguous

- Risk:
  the ledger could emit statuses without enough support-field discipline to audit
  whether witness versus checked-no-witness evidence was actually used.
- Response:
  freeze exact empty/non-empty rules for `supporting_witness_refs`,
  `supporting_checked_no_witness_refs`, and `deferral_reason` by status.
- Closeout Evidence:
  the shipped row models and committed reference fixture enforce exact status/support
  coupling and reject contradictory support-field combinations.

### Edge 8: Starter Support Refs Do Not Denote Stable Evidence Records

- Risk:
  the starter ledger could emit `supporting_witness_refs` or
  `supporting_checked_no_witness_refs` without freezing what those refs actually point
  to, leaving the evidentiary surface recoverable only by helper taste.
- Response:
  freeze exact starter support-ref identity law:
  - witness support refs must carry through stable `witness_ref` values from ordered
    typed witness records
  - checked-no-witness support refs must carry through the ordered admitted edge-class
    refs from `checked_no_witness_edge_class_refs`
  - duplicates must fail closed rather than being normalized away
- Closeout Evidence:
  the shipped models preserve ordered witness and checked-no-witness refs directly from
  the typed input channels and reject support-ref drift in validation tests.

### Edge 9: Adjudication Coverage Collapses Back Into Sparse Positive Rows

- Risk:
  the new ledger could emit only rows with explicit evidence and leave the rest ambient.
- Response:
  require one adjudication row for every released edge class in catalog order, not only
  the positive or overridden rows.
- Closeout Evidence:
  the committed reference ledger covers every admitted edge class from the bound frame,
  and the binding validator rejects any row-order or row-coverage drift.

### Edge 10: Revision/Register Semantics Sneak In Through Adjudication Vocabulary

- Risk:
  starter adjudication could begin to carry split/merge/history semantics that belong
  to `V53-C`.
- Response:
  keep `V53-B` bounded to per-symbol adjudication only and defer cumulative
  revision/register work explicitly to `V53-C`.
- Closeout Evidence:
  the shipped slice adds only the adjudication ledger contract, helper, schema export,
  fixtures, and tests; no cumulative revision/register surfaces were released.

### Edge 11: Test-Intent Integration Reappears Too Early

- Risk:
  the adjudication lane could try to justify itself by directly consuming released
  `V45-D` test-intent surfaces before the core ledger semantics are stable.
- Response:
  keep `V53-B` bounded to released `V53-A` plus typed explicit override input only and
  defer test-intent integration explicitly to `V53-D`.
- Closeout Evidence:
  the shipped package and tests add no direct `V45-D` joins, no probe strategy
  integration, and no broader reviewer-platform widening.

## Current Judgment

- `V53-B` was the right next slice because the strongest remaining blocker cluster after
  released `V53-A` was no longer taxonomy or applicability:
  - contradictory override precedence
  - out-of-frame override dropping
  - applicability-violating overrides
  - overclaimed evidence/status semantics
- the shipped result remained properly bounded:
  - one repo-owned package
  - one released adjudication ledger schema
  - exact downstream `V53-A` consumption only
  - one exact fail-closed override law
  - one exact support-ref identity/order law
  - underdetermined rows deferred rather than promoted
  - no cumulative revision/register
  - no direct test-intent integration
- `V53-B` is now closed on `arc/v53-r4` in the branch-local sense:
  - symbol-local adjudication ledger
  - fail-closed override constitutionality
  - explicit witness / checked-no-witness support law
- the next meaningful slice is `V53-C`:
  - cumulative revision lineage / register
  - not a reopening of released `V53-A` or closed `V53-B`
