# Assessment vNext+114 Edges

Status: post-closeout edge assessment for `V48-C` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS114_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released `V48-B` Bypass

- Risk:
  the worker-envelope lane could silently bypass the released compiled binding and
  bind directly to raw `V48-A`, `V45`, `V47`, or raw taskpack component carriers.
- Response:
  freeze one starter boundary-input kind only:
  `released_compiled_policy_taskpack_binding_ref`.
- Closeout Evidence:
  input-source validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`
  and test `test_v48c_rejects_raw_v48a_bypass`.

### Edge 2: Task / Repo Identity Ambiguity

- Risk:
  a task/run boundary instance could look typed while leaving repo ref or task
  instance identity underdefined.
- Response:
  require exactly one repo ref and exactly one declared task instance identity per
  accepted boundary instance.
- Closeout Evidence:
  reference boundary-instance fixture
  `packages/adeu_agent_harness/tests/fixtures/v48c/reference_task_run_boundary_instance.json`,
  identity validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`,
  and deterministic replay coverage in
  `test_v48c_reference_worker_execution_envelope_replays_deterministically`.

### Edge 3: Worker Identity Laundering

- Risk:
  worker subject kind / ref or provider / model / adapter identity could be inferred
  from prose or ambient runtime state instead of explicit typed fields.
- Response:
  freeze explicit worker subject and provider / model / adapter anchors and fail closed
  on omission or contradiction.
- Closeout Evidence:
  committed reference fixtures under
  `packages/adeu_agent_harness/tests/fixtures/v48c/`,
  model acceptance coverage in `test_v48c_models_accept_committed_reference_payloads`,
  and explicit field validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`.

### Edge 4: Provider-Identity Conflation

- Risk:
  worker provider/model identity could be conflated with the attestation-provider
  `provider_id` carried by released attestation support artifacts.
- Response:
  freeze worker provider/model identity as `V48-C` envelope facts rather than generic
  attestation-kernel facts and forbid inference from attestation-provider fields.
- Closeout Evidence:
  identity-separation checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`
  and test `test_v48c_rejects_worker_provider_conflation_with_attestation_provider`.

### Edge 5: Ambient Support-Artifact Search

- Risk:
  runner-result, runner-provenance, verifier-result, or attestation-validator inputs
  could be discovered by local repo search rather than explicit typed refs.
- Response:
  require explicit support refs only and forbid hidden repo search in the starter
  slice.
- Closeout Evidence:
  explicit support-ref fields in the released boundary / attestation / provenance
  schemas, committed reference fixtures, and support-resolution logic in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`.

### Edge 6: Runner Result / Provenance Drift

- Risk:
  boundary instance, attestation, and provenance surfaces could bind contradictory
  runner-result / runner-provenance artifacts while remaining structurally plausible.
- Response:
  require explicit hash-coherence and fail closed on mismatch.
- Closeout Evidence:
  committed attestation / provenance fixtures, hash validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`,
  and test `test_v48c_rejects_runner_provenance_hash_mismatch`.

### Edge 7: Repo-Identity Ambiguity

- Risk:
  `repo_ref` could drift into a floating branch/ref label instead of naming one exact
  execution repository identity coherent with the bound snapshot.
- Response:
  freeze `repo_ref` as exact execution repository identity and keep it coherent with
  `snapshot_id` / `snapshot_sha256`.
- Closeout Evidence:
  released boundary-instance schema pair and reference fixture
  `packages/adeu_agent_harness/tests/fixtures/v48c/reference_task_run_boundary_instance.json`.

### Edge 8: Stale Compiled Boundary Reuse

- Risk:
  a stale or cross-repo released compiled binding could still be reused inside a
  seemingly valid task/run boundary instance.
- Response:
  require same-snapshot / same-repo coherence and fail-closed unresolved-lineage
  handling.
- Closeout Evidence:
  compiled-boundary lineage checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`
  and deterministic replay coverage through the committed reference envelope set.

### Edge 9: Thin Attestation Integrity Surface

- Risk:
  the attestation surface could claim support-chain integrity while carrying only refs
  and not the corresponding hash anchors.
- Response:
  freeze explicit attestation hash anchors for runner provenance and any selected
  runner-result / verifier-result / attestation-validator support carriers.
- Closeout Evidence:
  released attestation schema pair,
  `packages/adeu_agent_harness/tests/fixtures/v48c/reference_worker_execution_attestation.json`,
  and fail-closed missing-field tests
  `test_v48c_rejects_missing_verification_result_required_field`,
  `test_v48c_rejects_missing_attestation_verification_required_field`, and
  `test_v48c_rejects_missing_attestation_output_remote_fields`.

### Edge 10: Attestation Overread

- Risk:
  because `V48-C` names attestation directly, the first worker-envelope slice could be
  overread as silently redefining generic attestation kernel semantics.
- Response:
  keep generic attestation / verifier surfaces as released support carriers and release
  only the bridge-specific typed binding over them here.
- Closeout Evidence:
  bounded implementation footprint in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`
  and schema/export additions limited to the three `V48-C` bridge surfaces.

### Edge 11: Prompt Authority Drift

- Risk:
  prompt text, chat prose, or `AGENTS.md` could remain de facto worker authority even
  after a typed task/run boundary instance exists.
- Response:
  freeze projection-only posture and make prompt-boundary conflict fail closed.
- Closeout Evidence:
  prompt-authority guards in
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`
  and test `test_v48c_rejects_prompt_authority_drift`.

### Edge 12: Support-Artifact Emission Drift

- Risk:
  provenance `emitted_artifact_refs` could quietly become an implicit observed-action
  carrier by listing arbitrary mutation inventory or action traces.
- Response:
  constrain `emitted_artifact_refs` to support-artifact outputs only and defer observed
  action carriers to `V48-D`.
- Closeout Evidence:
  released provenance schema pair and committed reference fixture
  `packages/adeu_agent_harness/tests/fixtures/v48c/reference_worker_execution_provenance.json`.

### Edge 13: Conformance Bleed

- Risk:
  a typed task/run boundary instance plus attestation could be mistaken for proof that
  later worker behavior already stayed inside the boundary.
- Response:
  keep replayable post-run conformance and observed-action carriers outside this slice
  and defer them to `V48-D`.
- Closeout Evidence:
  frozen lock scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md`,
  bounded release surface under
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`,
  and absence of new conformance schema surfaces in the committed `v114` release.

### Edge 14: Multi-Worker Topology Creep

- Risk:
  the first worker-envelope slice could quietly grow supervisor / worker or
  worker / worker topology semantics before the single-worker case is proven.
- Response:
  keep topology and handoff doctrine deferred to `V48-E`.
- Closeout Evidence:
  bounded single-worker vocabularies in `docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md`
  and absence of topology surfaces in the committed `v114` implementation.

### Edge 15: Transitive Signature Overread

- Risk:
  released signature-envelope and trust-anchor inputs that sit behind released
  verifier / attestation carriers could be re-surfaced as new direct `V48-C`
  authority objects.
- Response:
  keep those surfaces transitive support prerequisites only and do not re-release them
  inside the starter worker-envelope lane.
- Closeout Evidence:
  frozen `V48-C` scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md` and bounded
  bridge-specific implementation under
  `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`.

### Edge 16: Authority Expansion Through Attestation

- Risk:
  because `V48-C` binds actual worker-run support carriers, the slice could be
  overread as minting broader execution or approval authority than the released
  compiled boundary allows.
- Response:
  keep the released surface attestation-first and constrain-only with no authority
  expansion beyond the already released compiled boundary.
- Closeout Evidence:
  no execution/approval widening in `docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md`,
  bounded released schema surfaces, and absence of new authority-bearing runtime
  output surfaces in the committed `v114` implementation.

### Edge 17: Package-Boundary Sprawl

- Risk:
  the worker-envelope lane could sprawl back into `adeu_repo_description`,
  `adeu_semantic_source`, or `adeu_commitments_ir` instead of first stabilizing as a
  harness-owned bridge surface.
- Response:
  keep `V48-C` bounded to `adeu_agent_harness` and consume earlier released bridge
  surfaces as upstream inputs only.
- Closeout Evidence:
  `V48-C` implementation landed only in `packages/adeu_agent_harness`, with upstream
  `V45` / `V47` / `V48-A` / `V48-B` surfaces consumed through already released bridge
  artifacts rather than reopened packages.

## Current Judgment

- `V48-C` was the right third `V48` move because `V48-A` and `V48-B` had already
  released the binding and compiled-boundary halves of the bridge on `main`, while
  explicit worker-run boundary identity, attestation, and provenance remained a
  distinct and still-unshipped seam.
- the shipped result is properly narrow: one released compiled boundary in, one
  task/run boundary instance out, one worker execution attestation out, one worker
  execution provenance carrier out, explicit released support-artifact refs, and no
  replayable post-run conformance or topology widening.
- `V48-D` is now the right next move because the bound compiled boundary and bound
  worker-run lineage are released on `main`, while replayable observed-action carriers
  and boundary-conformance judgment remain unshipped.
