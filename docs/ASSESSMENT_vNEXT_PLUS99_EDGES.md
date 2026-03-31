# Assessment vNext+99 Edges

Status: post-closeout edge assessment for `V45-A` (March 31, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS99_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Schema-Core Overclaim

- Risk:
  the current core-plus-overlays model could be treated as settled doctrine rather than
  bounded working hypothesis.
- Response:
  require a representative reconstruction appendix before the hypothesis can shape
  stronger lock surfaces.
- Closeout Evidence:
  reconstruction subset and round-trip checks in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py` plus rejection
  fixture
  `.../repo_schema_family_registry_v99_reject_non_round_tripping_reconstruction.json`.

### Edge 2: Naming-Only Classification Drift

- Risk:
  schema role-form classification could collapse back into filename/style clustering.
- Response:
  freeze precedence order and require structural/semantic/governance evidence ahead of
  lexical naming.
- Closeout Evidence:
  rejection fixture
  `.../repo_schema_family_registry_v99_reject_naming_only_role_form_classification.json`
  and explicit failure assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45a.py`.

### Edge 3: Adjudication Gap

- Risk:
  inferred classifications could appear settled without explicit promotion law.
- Response:
  carry explicit `inferred`, `adjudicated`, and `settled` posture with support
  requirements for promotion.
- Closeout Evidence:
  settled-posture gating in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py` and rejection
  fixture
  `.../repo_schema_family_registry_v99_reject_settled_posture_without_adjudication_support.json`.

### Edge 4: Classification-Policy Air Gap

- Risk:
  `classification_policy_ref` could exist as an anchor while still pointing at
  unfrozen interpretive air.
- Response:
  require immutable policy binding through explicit reference plus hash posture.
- Closeout Evidence:
  policy hash computation and binding enforcement in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`.

### Edge 5: Precedence Contradiction Laundering

- Risk:
  lexical naming could point one way while stronger structural or semantic evidence
  points another, yet the row could still appear settled.
- Response:
  require fail-closed rejection of precedence contradictions and keep typed evidence
  kinds inspectable.
- Closeout Evidence:
  rejection fixture `.../repo_schema_family_registry_v99_reject_precedence_contradiction.json`
  plus precedence checks in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`.

### Edge 6: Residual Laundering

- Risk:
  legacy/open-map drift could be hidden under a false appearance of clean convergence.
- Response:
  require narrow named residual flags and representative legacy coverage in the bounded
  subset.
- Closeout Evidence:
  residual-flag surfaces and bounded representative schema set in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py` and accepted
  reference fixture
  `.../repo_schema_family_registry_v99_reference.json`.

### Edge 7: Whole-Repo Scope Creep

- Risk:
  the first slice could widen into whole-repo exhaustive entity cataloging too early.
- Response:
  keep `v99` bounded to schema-visible and schema-adjacent surfaces only.
- Closeout Evidence:
  extraction source set is bounded to schema-visible paths in `extract.py`; entity
  coverage mode remains `bounded_schema_visible_slice` in accepted entity fixture.

### Edge 8: Scoped-Issuance Ambiguity

- Risk:
  the first `repo_entity_catalog@1` issuance could be overread as whole-family
  semantic closure rather than a bounded schema-visible slice.
- Response:
  require explicit coverage mode such as `bounded_schema_visible_slice`.
- Closeout Evidence:
  accepted entity fixture
  `.../repo_entity_catalog_v99_reference.json` plus model-level enforcement in
  `models.py`.

### Edge 9: Mutation-Entitlement Creep

- Risk:
  descriptive diagnostics could be overread as optimization or amendment permission.
- Response:
  keep outputs explicitly descriptive-first and non-promotional.
- Closeout Evidence:
  `V45-A` emitted artifacts are descriptive-only schema/model/extraction surfaces under
  `packages/adeu_repo_description`; no mutation or recursive-amendment execution
  surfaces were introduced in v99.

### Edge 10: Reconstruction Handwave

- Risk:
  the appendix could remain persuasive prose without auditable decomposition and explicit
  reconstruction.
- Response:
  require machine-checkable representative subset inputs and explicit round-trip checks.
- Closeout Evidence:
  representative reconstruction rows in accepted registry fixture and fail-closed
  rejection for non-round-tripping reconstruction in
  `.../repo_schema_family_registry_v99_reject_non_round_tripping_reconstruction.json`.

### Edge 11: Stale-Snapshot Overread

- Risk:
  one snapshot-bound self-description could later be overread as current repo truth.
- Response:
  keep outputs valid for the bound snapshot only and historical when stale unless later
  rebound by an explicit fresh extraction lane.
- Closeout Evidence:
  snapshot validity posture is carried explicitly in accepted artifacts and validated in
  `models.py`.

## Current Judgment

- `V45-A` closeout on `main` resolves the bounded descriptive seam by shipping
  deterministic `repo_schema_family_registry@1` and bounded
  `repo_entity_catalog@1` surfaces with typed classification posture, immutable
  policy binding, and precedence-bound fail-closed rejection behavior.
- The shipped baseline remains descriptive-first and non-promotional, preserving
  deferral of mutation entitlement and later widening lanes (`V45-B+`).
