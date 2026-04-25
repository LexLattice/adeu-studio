# Assessment vNext+191 Edges

Status: pre-lock edge assessment for `V69-A` (April 25, 2026 UTC).

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS191_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Candidate Intake Could Become Adoption

- Risk:
  a candidate row could be mistaken for a released schema, selected family, or
  implementation decision.
- Response:
  every admitted candidate must carry a non-adoption guardrail, admissible roles,
  forbidden roles, and an immediate review surface.

### Edge 2: Source Absence Could Become Source-Free Invention

- Risk:
  explicit source absence could be implemented as permission to create candidates
  without source rows.
- Response:
  candidate `source_refs` must be non-empty. Missing, unavailable, generated-later,
  or uncommitted operator sources must be represented as source rows with
  source-presence posture.

### Edge 3: Review Targets Could Select Downstream Families

- Risk:
  `required_next_review_surface` could accidentally schedule `V71` through `V75`
  or the conditional `V43` branch.
- Response:
  immediate review targets are limited to `V70`, `future_family_review`, or
  deferral. Later families and `V43` appear only as `eventual_family_hint`.

### Edge 4: ODEU Pressure Could Be Flattened

- Risk:
  multi-lane candidates such as product projection or self-evidencing workflow
  residue could be flattened into opaque `mixed` pressure.
- Response:
  the starter supports `primary_odeu_lane` plus sorted unique `odeu_lanes` and
  rejects `primary_odeu_lane=mixed` when `odeu_lanes` is absent.

### Edge 5: Forbidden Roles Could Be Too Weak

- Risk:
  a candidate could carry a generic forbidden role that misses the relevant
  authority risk.
- Response:
  forbidden roles must be risk-aware by `origin_class` and `admissible_roles`,
  including `released_schema`, `product_authorization`, `lock_authority`,
  `implementation_task`, `ratified_decision`, `self_validation`, and
  `transcript_truth` where required.

### Edge 6: Support Docs Could Become Released Schema Evidence

- Risk:
  conceptual-diff schema support, product-wedge notes, or review artifacts could
  be overread as released schema or lock authority.
- Response:
  support docs and reviews may be source rows or candidate inputs only. They cannot
  satisfy released-schema, lock, ratification, or implementation authority.

### Edge 7: Operator Turns Could Become Truth Or Runtime Permission

- Risk:
  operator-originated text could become truth, hidden candidate invention, runtime
  permission, or dispatch authority.
- Response:
  `V69-A` may represent `operator_turn_not_committed` only as source-presence
  posture. Actual operator-turn binding belongs to `V69-C`; live runtime behavior
  is out of scope.

### Edge 8: Model Outputs Could Self-Validate

- Risk:
  model-output candidates could be treated as adopted or self-validating because
  they appear in a typed intake object.
- Response:
  model-output candidates must forbid `ratified_decision` and `self_validation`.
  Intake records only admit them for later review.

### Edge 9: V69-A Could Begin V69-B Or V69-C

- Risk:
  adding candidate-intake rows could expand into deterministic derivation,
  operator-ingress binding, recursive residue reporting, or pre-`V70` handoff.
- Response:
  `V69-A` ships only schema/model/validator/export and hand-curated fixtures.
  Derivation belongs to `V69-B`; operator ingress and recursive residue belong to
  `V69-C`.

### Edge 10: V70 Evidence Classification Could Leak In

- Risk:
  the starter might include verdicts about candidate truth, usefulness, quality, or
  adversarial review outcome.
- Response:
  `V69-A` may name `v70_evidence_classification` or `v70_adversarial_review` as a
  required next review surface, but cannot perform or settle that review.

## Current Judgment

- `V69-A` is the right starter slice because the repo needs source-bound candidate
  admission before derivation, evidence classification, ratification, or product
  projection.
- The slice is finite:
  - three starter schema surfaces;
  - one shared candidate/source/guardrail row vocabulary;
  - one hand-curated reference fixture seeded from the `V69` preflight dogfood
    report;
  - reject fixtures for source, guardrail, ODEU, role, and downstream-family
    leakage.
- `V69-B` and `V69-C` remain drafted support specs only until their own future
  starter locks select them.
- `V70` through `V75` and `V43` remain unselected by this starter bundle.
