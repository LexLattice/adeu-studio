# Assessment vNext+102 Edges

Status: post-closeout edge assessment for `V45-C` corrective hardening (March 31, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS102_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Silent Rewrite Drift

- Risk:
  the corrective slice could quietly mutate the released `@1` surface rather than make
  the corrective-release posture explicit.
- Response:
  prefer `repo_arc_dependency_register@2` and keep the released `@1` artifact as
  historical baseline context.
- Closeout Evidence:
  versioned `@2` schema/model release in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  authoritative schema
  `packages/adeu_repo_description/schema/repo_arc_dependency_register.v2.json`,
  and accepted fixture
  `apps/api/fixtures/repo_description/vnext_plus102/repo_arc_dependency_register_v102_reference.json`.

### Edge 2: Provenance Laundering

- Risk:
  generic evidence lists could continue to hide which source surfaces actually support
  each entry and edge.
- Response:
  require explicit source-set provenance plus per-entry and per-edge source artifact
  refs, and require every `source_artifact_ref` to resolve inside the declared
  `source_set`.
- Closeout Evidence:
  source-set and membership enforcement in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  plus reject fixtures
  `.../repo_arc_dependency_register_v102_reject_missing_source_set_provenance.json`
  and
  `.../repo_arc_dependency_register_v102_reject_source_artifact_ref_outside_source_set.json`.

### Edge 3: Blocker Projection Drift

- Risk:
  entry-level blocker lists could drift away from the dependency-edge subset that
  actually carries blocking force.
- Response:
  require exact reconciliation between `blocker_arc_ids` / `blocked_by_arc_ids` and the
  incoming unresolved hard-edge subset for each blocked entry.
- Closeout Evidence:
  blocker reconciliation validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `.../repo_arc_dependency_register_v102_reject_blocker_dependency_inconsistency.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45c.py`.

### Edge 4: Epistemic Posture Blur

- Risk:
  consumers could overread inferred dependency claims as direct observation if
  derivation posture and method remain implicit.
- Response:
  require explicit artifact-level extraction posture and explicit entry/edge derivation
  posture and method.
- Closeout Evidence:
  required `extraction_posture` / `extraction_method` / `derivation_posture` /
  `derivation_method` fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  plus reject fixtures
  `.../repo_arc_dependency_register_v102_reject_missing_entry_derivation_posture.json`
  and
  `.../repo_arc_dependency_register_v102_reject_missing_edge_source_artifact_refs.json`.

### Edge 5: Cycle Law Without Representation

- Risk:
  the seam could keep talking about cycle posture without a field that actually carries
  it.
- Response:
  add explicit cycle posture and cycle detection scope to the corrected artifact shape.
- Closeout Evidence:
  cycle-posture/scope fields and validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  with reject fixture
  `.../repo_arc_dependency_register_v102_reject_missing_cycle_posture.json`
  and cycle assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45c.py`.

### Edge 6: Vocabulary Folklore

- Risk:
  underdefined terms such as `supports_all_three_way_claim` or an unexplained
  machine-enforced pending list could harden into folklore rather than doctrine.
- Response:
  remove undefined vocabulary and replace it only with bounded explicitly defined
  posture and method vocabularies.
- Closeout Evidence:
  bounded vocabulary policy hash binding in `models.py`,
  reject fixtures
  `.../repo_arc_dependency_register_v102_reject_undefined_pending_list_posture.json`
  and
  `.../repo_arc_dependency_register_v102_reject_supports_all_three_way_claim.json`.

### Edge 7: Object-Boundary Collapse

- Risk:
  the corrected register could be mistaken for the later code dependency graph and then
  consumed with stronger authority than intended.
- Response:
  keep the artifact boundary explicit: this slice is planning/open-arc dependency
  posture only.
- Closeout Evidence:
  `register_scope` boundary checks in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and the lock-level boundary statement in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md`.

### Edge 8: Authority Creep

- Risk:
  better dependency visibility could still be overread as scheduling, plan-resolution,
  or mutation entitlement.
- Response:
  keep the corrected surface descriptive-first and non-promotional.
- Closeout Evidence:
  authority-laundering reject fixture
  `.../repo_arc_dependency_register_v102_reject_authority_laundering_scheduling_entitlement.json`
  and normalization checks in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`.

### Edge 9: Corrective Marker Drift

- Risk:
  planning-surface drift could desynchronize corrective path selection from the lock
  target and silently emit mixed-state dependency metadata.
- Response:
  require corrective planning markers and lock target path to agree exactly.
- Closeout Evidence:
  `_validate_v45c_corrective_planning_markers` in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  and tests
  `test_v102_corrective_selected_path_extraction_reads_bounded_followup_note` plus
  `test_v102_corrective_planning_validation_rejects_table_drift`.

## Current Judgment

- `V45-C` corrective hardening on `main` resolves the bounded released-surface gaps by
  shipping deterministic `repo_arc_dependency_register@2` surfaces with explicit
  source-set provenance, explicit extraction/derivation posture, explicit cycle
  posture/scope, and fail-closed vocabulary and authority guards.
- the shipped baseline remains descriptive-first and non-promotional, preserving
  deferral of `V45-B` code dependency-graph widening, scheduler automation, mutation
  entitlement, and recursive-governance binding.
