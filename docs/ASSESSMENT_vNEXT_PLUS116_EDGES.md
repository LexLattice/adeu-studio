# Assessment vNext+116 Edges

Status: post-closeout edge assessment for `V48-E` (April 3, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS116_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released `V48-D` Bypass

- Risk:
  the topology lane could silently bypass the released conformance surface and bind
  directly to raw boundary, attestation, provenance, or compiled-binding carriers.
- Response:
  freeze one starter input shape only:
  exactly one released parent `worker_boundary_conformance_report@1` and exactly one
  released child `worker_boundary_conformance_report@1`.
- Closeout Evidence:
  input-source validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`
  and test `test_v48e_rejects_raw_v48d_bypass`.

### Edge 2: Parent/Child Role Ambiguity

- Risk:
  a topology artifact could look typed while leaving parent/child ordering or role
  posture ambiguous.
- Response:
  freeze one explicit edge kind only:
  `supervisor_to_worker`, with parent role `supervisor` and child role `worker`.
- Closeout Evidence:
  role validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`
  and test `test_v48e_marks_swapped_roles_as_rejected`.

### Edge 3: Child-Lineage Omission

- Risk:
  the topology lane could overread one parent conformance report as enough evidence,
  leaving the child side underdefined.
- Response:
  require exactly one explicit child conformance report and fail closed on omission.
- Closeout Evidence:
  cardinality and schema-validation guards in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`
  plus test `test_v48e_parent_and_child_reports_keep_v48d_schema`.

### Edge 4: Compiled-Boundary Equality Drift

- Risk:
  the child side could silently widen beyond the parent compiled boundary while still
  appearing reachable.
- Response:
  select exact parent/child compiled-boundary equality only in the starter slice as a
  deliberate first-slice restriction and do not authorize any widening algebra here.
- Closeout Evidence:
  reference rejected fixture
  `packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology_rejected_compiled_boundary_mismatch.json`,
  replay test
  `test_v48e_reference_rejected_compiled_boundary_mismatch_fixture_replays`, and
  compiled-boundary comparison in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`.

### Edge 5: Repo / Snapshot Identity Drift

- Risk:
  parent and child could appear connected while actually drifting across repo or
  snapshot identity.
- Response:
  require exact same `repo_ref`, `snapshot_id`, and `snapshot_sha256` posture across
  the emitted topology.
- Closeout Evidence:
  lineage comparison in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`
  and committed reference fixtures under
  `packages/adeu_agent_harness/tests/fixtures/v48e/`.

### Edge 6: Non-Conformant Parent/Child Laundering

- Risk:
  a parent or child run that is `non_conformant` or `incomplete_evidence` could still
  be treated as an accepted delegation topology by local convention.
- Response:
  freeze accepted starter topology to already conformant parent and child reports
  only, and emit typed `rejected` or `incomplete_lineage` posture otherwise.
- Closeout Evidence:
  outcome aggregation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`,
  reference incomplete-lineage fixture
  `packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology_incomplete_lineage.json`,
  and replay test `test_v48e_reference_incomplete_lineage_fixture_replays`.

### Edge 7: Task Identity Ambiguity

- Risk:
  the topology edge could be typed while leaving parent task identity, delegated task
  identity, or child task identity ambiguous, implicit, or only described in prose.
- Response:
  require one explicit parent task identity, one explicit delegated task identity,
  one explicit child task identity, and one explicit delegation-edge identity in
  every emitted topology.
- Closeout Evidence:
  required fields in
  `packages/adeu_agent_harness/schema/worker_delegation_topology.v1.json`,
  model validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`,
  and accepted replay fixture
  `packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology.json`.

### Edge 8: Handoff Result / Topology Identity Ambiguity

- Risk:
  the first topology release could rely on prose to explain whether a handoff was
  completed, rejected, or unresolved, and different resolved outcomes could collide
  on one topology identity.
- Response:
  freeze one bounded handoff-result vocabulary, derive topology identity from the
  resolved outcome surface, and keep accepted starter topology at `completed` only.
- Closeout Evidence:
  topology-id derivation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`
  and test `test_v48e_topology_id_changes_when_resolved_outcome_changes`.

### Edge 9: Self-Edge Laundering

- Risk:
  the same worker subject could appear as both parent and child, turning topology into
  a relabelled single-worker replay.
- Response:
  require parent and child worker subjects to be distinct and fail closed on
  self-edge posture.
- Closeout Evidence:
  subject-distinctness checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`
  and test `test_v48e_marks_same_worker_subject_as_rejected`.

### Edge 10: Diagnostic-Family Drift

- Risk:
  the surface could expose `supporting_diagnostic_ids` while leaving the actual
  failure-family taxonomy underdefined or silently normalized.
- Response:
  freeze one starter supporting-diagnostic family vocabulary and reject duplicate or
  misordered diagnostics rather than repairing them.
- Closeout Evidence:
  schema enum and model validation in
  `packages/adeu_agent_harness/schema/worker_delegation_topology.v1.json` and
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`,
  plus test `test_v48e_model_rejects_out_of_order_or_duplicate_diagnostics`.

### Edge 11: Worker/Worker And Recursive Topology Creep

- Risk:
  the first topology release could quietly widen from one bounded supervisor/worker
  edge into worker/worker doctrine, recursive trees, many-child algebra, or repo-wide
  orchestration regime.
- Response:
  freeze one parent, one child, one edge only and keep wider topology deferred.
- Closeout Evidence:
  released schema constants `delegation_edge_kind = supervisor_to_worker` and
  `topology_scope_posture = one_parent_one_child_one_edge_only`, bounded emitted
  fixtures, and absence of wider topology surfaces in the committed `v116`
  implementation.

### Edge 12: Prompt Authority Drift

- Risk:
  prompt text, chat prose, or `AGENTS.md` could still define delegated topology even
  after typed parent/child lineage exists.
- Response:
  keep prose projection-only and make topology-conflicting prose fail closed.
- Closeout Evidence:
  lock doctrine in `docs/LOCKED_CONTINUATION_vNEXT_PLUS116.md`, bounded topology
  implementation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`,
  and absence of prompt-derived authority fields in the released schema/fixtures.

### Edge 13: Authority Expansion Through Topology

- Risk:
  because `V48-E` explicitly links workers, it could be overread as minting broader
  execution or approval authority than the released shared compiled boundary already
  allows.
- Response:
  keep the surface constrain-only, non-executive, non-approving, and same-boundary
  only.
- Closeout Evidence:
  `authority_relation_posture = same_compiled_boundary_no_widening` in the released
  schema and fixtures, bounded implementation footprint under
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`,
  and absence of any new authority-bearing execution surface in the committed `v116`
  release.

## Current Judgment

- `V48-E` was the right fifth and final `V48` move because `V48-A`, `V48-B`,
  `V48-C`, and `V48-D` had already released the binding, compiled-boundary,
  worker-envelope, and single-worker conformance halves of the bridge on `main`,
  while typed delegated topology remained the only selected unshipped seam.
- the shipped result is properly narrow: one released parent `V48-D` report in, one
  released child `V48-D` report in, one canonical
  `worker_delegation_topology@1` out, one explicit `supervisor_to_worker` edge, exact
  same repo/snapshot/compiled-boundary posture, distinct worker subjects, typed
  `completed` / `rejected` / `incomplete_lineage` outcomes, and no recursive or
  repo-wide orchestration widening.
- `V48` is now complete on `main`; `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md` now records
  `V48-A` through `V48-E` as closed and no further internal `V48` path is currently
  selected.
