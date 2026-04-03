# Assessment vNext+115 Edges

Status: post-closeout edge assessment for `V48-D` (April 3, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS115_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released `V48-C` Bypass

- Risk:
  the conformance lane could silently bypass the released worker-envelope chain and
  bind directly to raw compiled bindings or raw policy/scope starters.
- Response:
  freeze one starter input shape only:
  exactly one released boundary instance, one released worker execution attestation,
  and one released worker execution provenance.
- Closeout Evidence:
  input-source validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`
  and test `test_v48d_rejects_raw_v48b_bypass`.

### Edge 2: Observed-Action Carrier Ambience

- Risk:
  filesystem, command, emitted-artifact, or execution-repository identity observation
  could be recovered from ambient repo search rather than explicit typed carriers.
- Response:
  require one explicit four-carrier observed-action set, freeze one source-of-truth /
  acquisition rule per carrier kind, and forbid hidden repo search.
- Closeout Evidence:
  carrier-loading logic and source-of-truth anchors in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`,
  released schema anchors in
  `packages/adeu_agent_harness/schema/worker_boundary_conformance_report.v1.json`,
  and test `test_v48d_rejects_missing_observed_action_carrier`.

### Edge 3: Support vs Observation Collapse

- Risk:
  support-artifact provenance from `V48-C` could be mistaken for the actual observed
  action set, collapsing lineage evidence into conformance evidence.
- Response:
  keep support lineage and observed-action carriers structurally distinct and forbid
  provenance/support artifacts from substituting for the frozen observed carriers.
- Closeout Evidence:
  substitution guards in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`
  and test `test_v48d_rejects_support_artifact_substitution_posture`.

### Edge 4: Repo / Task / Worker Identity Drift

- Risk:
  a report could look structurally valid while the observed run no longer matches the
  repo ref, task instance, worker subject, or provider/model/adapter tuple bound by
  the released `V48-C` envelope.
- Response:
  require explicit lineage coherence and fail closed on mismatch.
- Closeout Evidence:
  identity validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`
  and tests `test_v48d_models_accept_committed_reference_payloads` plus
  `test_v48d_rejects_carrier_repo_identity_mismatch`.

### Edge 5: Relative-Path Normalization Leak

- Risk:
  malformed relative carrier refs could leak lower-level path or runner errors instead
  of surfacing one fail-closed conformance error posture.
- Response:
  normalize carrier-path failures into typed `WorkerBoundaryConformanceError`
  rejection.
- Closeout Evidence:
  path normalization in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`
  and test `test_v48d_rejects_invalid_relative_path_with_conformance_error`.

### Edge 6: Off-Boundary Mutation Underread

- Risk:
  filesystem mutations outside the bound allowlist or inside forbidden paths could be
  underread as informational rather than conformance-breaking.
- Response:
  freeze explicit mutation validation over the bound compiled boundary and fail closed
  on off-boundary mutation.
- Closeout Evidence:
  reference non-conformant mutation fixture
  `packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report_nonconformant_mutation.json`,
  replay test `test_v48d_reference_nonconformant_mutation_fixture_replays`, and
  filesystem checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`.

### Edge 7: Forbidden Operation Kind Underread

- Risk:
  a mutation could stay path-in-scope while still performing a forbidden operation
  kind such as `delete`, and the report could misread that as conformant.
- Response:
  enforce `forbidden_operation_kinds` in the filesystem conformance check itself.
- Closeout Evidence:
  mutation operation-kind checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`
  and test `test_v48d_marks_forbidden_operation_kind_non_conformant`.

### Edge 8: Command Drift Underread

- Risk:
  command invocation logs could contain unallowlisted commands or forbidden effects
  while the report still claims conformant posture.
- Response:
  require explicit command validation over the bound command posture and fail closed on
  drift.
- Closeout Evidence:
  reference non-conformant command fixture
  `packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report_nonconformant_command.json`,
  replay test `test_v48d_reference_nonconformant_command_fixture_replays`, and
  command validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`.

### Edge 9: Emitted-Artifact Contradiction

- Risk:
  the observed emitted artifact set could contradict the bound compiled boundary or
  the support-only provenance surface while remaining structurally plausible.
- Response:
  keep observed emitted artifacts distinct from provenance support refs and fail closed
  on contradiction.
- Closeout Evidence:
  emitted-artifact carrier models and checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`
  plus deterministic replay of the committed reference fixtures.

### Edge 10: Execution-Repository Identity Ambiguity

- Risk:
  execution-repository identity could remain ambiguous, loose, or drift away from the
  exact repository identity already bound in `V48-C`.
- Response:
  require one explicit exact execution-repository identity / branch-ref carrier
  coherent with the bound repo identity and snapshot.
- Closeout Evidence:
  execution-repository identity carrier models in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`
  and tests `test_v48d_marks_branch_identity_mismatch_non_conformant` plus
  `test_v48d_rejects_carrier_repo_identity_mismatch`.

### Edge 11: Prompt Authority Drift

- Risk:
  prompt text, chat prose, or `AGENTS.md` could still decide conformance even after
  typed lineage and observed-action carriers exist.
- Response:
  keep prose projection-only and make prompt-boundary conflict fail closed.
- Closeout Evidence:
  frozen `prompt_conflict` check family in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`,
  bounded prompt posture in
  `packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report.json`,
  and lock doctrine in `docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md`.

### Edge 12: Judgment Aggregation Ambiguity

- Risk:
  overall conformance judgment could become a prose choice rather than a deterministic
  function of the frozen check results.
- Response:
  freeze one exact precedence rule and derive supporting diagnostics from the same
  frozen check set.
- Closeout Evidence:
  frozen judgment vocabularies in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md`,
  aggregation logic in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`,
  and deterministic replay of the committed reference fixtures.

### Edge 13: Incomplete Evidence Overread

- Risk:
  missing observed-action carriers or unresolved lineage could be silently treated as
  pass or warning rather than explicit incomplete-evidence posture.
- Response:
  freeze `incomplete_evidence` as a first-class judgment and fail closed on missing
  evidence.
- Closeout Evidence:
  frozen precedence in `docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md`,
  report aggregation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`,
  and test `test_v48d_rejects_missing_observed_action_carrier`.

### Edge 14: Multi-Worker Topology Creep

- Risk:
  the first conformance release could quietly widen into supervisor/worker or
  worker/worker judgment before the single-worker case is stable.
- Response:
  keep topology deferred to `V48-E`.
- Closeout Evidence:
  bounded single-worker vocabularies in `docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md`
  and absence of topology surfaces in the committed `v115` implementation.

### Edge 15: Authority Expansion Through Conformance

- Risk:
  because `V48-D` issues pass/fail judgment over real runs, it could be overread as
  minting broader execution or approval authority than the bound compiled boundary
  already allows.
- Response:
  keep the surface constrain-only, non-executive, and non-approving.
- Closeout Evidence:
  no execution/approval widening in `docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md`,
  bounded implementation footprint under
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`,
  and absence of new authority-bearing topology surfaces in the committed `v115`
  release.

## Current Judgment

- `V48-D` was the right fourth `V48` move because `V48-A`, `V48-B`, and `V48-C`
  had already released the binding, compiled-boundary, and worker-envelope halves of
  the bridge on `main`, while replayable observed-action conformance remained an
  unshipped seam.
- the shipped result is properly narrow: one released `V48-C` worker-envelope chain
  in, one explicit four-carrier observed-action set in, one canonical
  `worker_boundary_conformance_report@1` out, exact
  `conformant` / `non_conformant` / `incomplete_evidence` aggregation, and no
  topology widening.
- `V48-E` is now the right next move because single-worker conformance is released on
  `main`, while bounded supervisor/worker or worker/worker delegation topology remains
  the only unshipped seam inside the currently planned `V48` family.
