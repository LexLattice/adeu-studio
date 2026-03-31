# Assessment vNext+100 Edges

Status: post-closeout edge assessment for `V45-C` (March 31, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS100_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Dependency-As-Authority Drift

- Risk:
  dependency outputs could be overread as automatic planning priority or scheduling
  entitlement.
- Response:
  keep register outputs descriptive-first and non-promotional.
- Closeout Evidence:
  authority-laundering rejection fixture
  `.../repo_arc_dependency_register_v100_reject_authority_laundering_scheduling_entitlement.json`
  plus `register_scope` validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`.

### Edge 2: Dangling Dependency Laundering

- Risk:
  dependency edges could reference unknown arc IDs while still appearing valid.
- Response:
  fail closed on any edge whose endpoints are not present in typed arc-entry surfaces.
- Closeout Evidence:
  rejection fixture
  `.../repo_arc_dependency_register_v100_reject_dangling_dependency_target_arc.json`
  and explicit rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45c.py`.

### Edge 3: Status Contradiction Drift

- Risk:
  an arc could be marked `ready` while hard blockers remain unresolved.
- Response:
  enforce readiness/blocker consistency laws and reject contradictions.
- Closeout Evidence:
  rejection fixture
  `.../repo_arc_dependency_register_v100_reject_unresolved_blocker_ready_posture.json`
  plus blocker/readiness validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`.

### Edge 4: Cycle Blindness

- Risk:
  dependency cycles could silently exist when the edges are not unresolved hard
  blockers, creating hidden planning knots while still passing validation.
- Response:
  reject cycles across the full dependency-edge set unless an explicit typed cycle
  posture exists.
- Closeout Evidence:
  full-edge cycle detection in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py` and
  `test_v100_rejects_dependency_cycles_even_when_edges_are_non_blocking`.

### Edge 5: Policy-Binding Air Gap

- Risk:
  dependency-policy anchors could exist without immutable hash binding.
- Response:
  require explicit `dependency_policy_ref` plus `dependency_policy_hash`.
- Closeout Evidence:
  policy hash computation and binding enforcement in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`.

### Edge 6: Snapshot Overread

- Risk:
  one snapshot-bound dependency register could be overread as current truth after repo
  drift.
- Response:
  keep snapshot validity posture explicit and treat stale outputs as historical.
- Closeout Evidence:
  explicit snapshot posture in accepted fixture
  `.../repo_arc_dependency_register_v100_reference.json` and validation in `models.py`.

### Edge 7: Selection-Cue Fragility

- Risk:
  dependency extraction could fail closed too easily because it depends on one exact
  wording choice in the planning doc.
- Response:
  accept multiple consistent selection cues and require them to agree on one selected
  path.
- Closeout Evidence:
  multi-signal selection extraction in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py` and
  `test_v100_selected_path_extraction_accepts_consistent_non_phrase_markers`.

### Edge 8: Natural-Language Authority Separator Bypass

- Risk:
  forbidden authority claims could bypass validation through spaces, hyphens, or other
  natural-language separators.
- Response:
  normalize authority text before forbidden-term checks.
- Closeout Evidence:
  token normalization in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py` and
  `test_v100_rejects_authority_terms_with_natural_language_separators`.

### Edge 9: Scope Creep

- Risk:
  this seam could widen early into symbol graphs, test-intent matrices, optimization
  registers, or descriptive-to-normative binding.
- Response:
  keep `v100` narrowly scoped to dependency-register release only.
- Closeout Evidence:
  shipped surfaces are limited to `repo_arc_dependency_register@1`,
  `adeu_repo_description` extraction/model/schema updates, fixtures, and tests; no
  `V45-B`, `V45-D`, `V45-E`, or `V45-F` runtime surfaces were introduced in v100.

## Current Judgment

- `V45-C` closeout on `main` resolves the bounded dependency-register seam by shipping
  deterministic `repo_arc_dependency_register@1` surfaces with typed open-arc entries,
  typed dependency edges, immutable policy binding, snapshot-bound posture, and
  fail-closed rejection of dependency/status/authority contradictions.
- The shipped baseline remains descriptive-first and non-promotional, preserving
  deferral of scheduler automation, mutation entitlement, and later widening lanes.
