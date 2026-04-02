# Locked Continuation vNext+114

Status: `V48-C` implementation contract.

## V114 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v48c_worker_execution_envelope_attestation_contract@1",
  "target_arc": "vNext+114",
  "target_path": "V48-C",
  "target_scope": "bounded_task_run_boundary_instance_and_worker_execution_attestation_provenance",
  "implementation_packages": [
    "adeu_agent_harness"
  ],
  "governing_released_stack": "V48A_and_V48B_released_bridge_stack_plus_released_agent_harness_runner_verifier_and_attestation_kernel_on_main",
  "governing_stack_consumption_mode": "released_compiled_boundary_to_single_worker_run_boundary_instance_attestation_and_provenance_only_not_raw_binding_profile_compile_bypass_post_run_conformance_signature_envelope_redefinition_or_multi_worker_topology",
  "requires_released_v48a_binding_profile_surfaces": true,
  "requires_released_v48b_compiled_binding_surfaces": true,
  "requires_released_taskpack_runner_surfaces": true,
  "requires_released_taskpack_verifier_surfaces": true,
  "requires_released_attestation_validator_surfaces": true,
  "task_run_boundary_instance_schema": "task_run_boundary_instance@1",
  "worker_execution_attestation_schema": "worker_execution_attestation@1",
  "worker_execution_provenance_schema": "worker_execution_provenance@1",
  "exactly_one_compiled_binding_ref_required": true,
  "exactly_one_repo_ref_required": true,
  "exactly_one_task_instance_identity_required": true,
  "exactly_one_worker_subject_kind_and_ref_required": true,
  "worker_provider_model_adapter_binding_required": true,
  "worker_provider_model_identity_not_equal_attestation_provider_identity_required": true,
  "repo_ref_execution_repository_identity_required": true,
  "runner_result_and_provenance_binding_required": true,
  "attestation_support_binding_required": true,
  "attestation_hash_anchor_fields_required": true,
  "compiled_boundary_identity_hash_match_required": true,
  "runner_result_and_provenance_hash_consistency_required": true,
  "emitted_artifact_refs_support_only_required": true,
  "prompt_projection_only_conflict_fail_closed_required": true,
  "stale_or_unresolved_compiled_boundary_reuse_fail_closed_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "boundary_instance_and_attestation_examples_required": true,
  "no_post_run_conformance_release_yet": true,
  "no_observed_action_carrier_release_yet": true,
  "no_multi_worker_topology_yet": true,
  "no_signature_envelope_or_execution_result_redefinition": true,
  "released_signature_and_trust_anchor_inputs_transitive_support_only_required": true,
  "no_execution_or_approval_authority_expansion": true,
  "no_automatic_waiver_or_deferral_issuance": true,
  "required_released_contracts": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS113.md"
  ],
  "source_architecture_doc": "docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md",
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v31.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v7.md",
    "docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v31.md"
}
```

## Slice

- Arc label: `vNext+114`
- Family label: `V48-C`
- Scope label: bounded task/run boundary instance and worker execution attestation / provenance

## Objective

Release the bounded `V48-C` worker execution envelope + attestation lane by
materializing one canonical doctrine surface over the released `V48-A` binding
profile, released `V48-B` compiled binding, and released agent-harness runner /
verifier / attestation kernel on `main` that makes explicit:

- which single released `compiled_policy_taskpack_binding@1` governs one task/run
  boundary instance;
- how one explicit repo ref and one declared task instance identity bind one concrete
  worker-run context to that compiled boundary;
- how one explicit worker subject kind / ref and one explicit provider / model /
  adapter tuple remain typed rather than ambient, and are not conflated with the
  attestation-provider identity carried by released attestation support artifacts;
- how released runner-result, runner-provenance, verifier-result, and attestation
  validator surfaces are bound explicitly rather than by local convention;
- how one `task_run_boundary_instance@1`, one `worker_execution_attestation@1`, and
  one `worker_execution_provenance@1` remain hash-coherent with the released compiled
  boundary and with the released run-support artifacts they consume;
- how emitted provenance artifact refs remain bounded to support-artifact outputs only
  rather than silently becoming an observed-action carrier;
- how released signature-envelope and trust-anchor inputs remain transitive support
  prerequisites behind released verifier / attestation carriers rather than new
  `V48-C` authority objects;
- what fail-closed rules prevent raw `V48-A` / `V45` / `V47` bypass, stale compiled
  boundary reuse, worker-identity laundering, prompt-shaped authority drift, or
  hidden support-artifact search.

This slice is attestation-first and still pre-conformance. It does not reopen released
`V48-A` binding semantics, released `V48-B` compiler semantics, generic runner
semantics, generic verifier semantics, generic attestation semantics, generic signing
semantics, or post-run conformance semantics. It also does not widen into multi-worker
topology, observed-action carrier release, benchmark / contest / structural-assessment
doctrine, execution authority expansion, approval authority expansion, or automatic
waiver / deferral issuance.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V48-C` releases one typed task/run boundary-instance surface plus one typed
     worker-execution attestation surface plus one typed worker-execution provenance
     surface over the already released `V48-A` and `V48-B` bridge stack and the
     already released harness runner / verifier / attestation kernel on `main`;
   - it does not reopen descriptive semantics, ANM semantics, released `V48-A`
     semantics, released `V48-B` semantics, or generic runner / verifier /
     attestation kernel semantics.
2. Package-ownership strategy:
   - `adeu_agent_harness` remains the sole implementation owner in this slice;
   - released `adeu_repo_description`, `adeu_semantic_source`, and
     `adeu_commitments_ir` artifacts remain upstream authority inputs only through the
     released `V48-A` and `V48-B` bridge surfaces and are not reopened directly here.
3. Input-source strategy:
   - the first `V48-C` release supports exactly one boundary-source kind:
     - `released_compiled_policy_taskpack_binding_ref`
   - every accepted derivation input must resolve to exactly one released
     `compiled_policy_taskpack_binding@1`;
   - no `V48-C` derivation may bypass the released compiled binding by binding
     directly to raw `anm_taskpack_binding_profile@1`, raw `V45` scope artifacts, raw
     `V47-E` rows, raw taskpack components, or raw `D-IR` clause refs.
4. Boundary-instance strategy:
   - each accepted task/run boundary instance governs exactly:
     - one released compiled binding;
     - one exact execution repository identity;
     - one declared task instance identity;
     - one worker subject kind;
     - one worker subject ref;
     - one execution adapter kind / ref;
     - one worker provider id;
     - one worker model id.
   - worker subject, provider, model, or adapter identity may not be inferred from
     prompt prose, `AGENTS.md`, or unstated local runtime convention.
   - `worker_provider_id` and `worker_model_id` are `V48-C` envelope facts rather
     than generic runner-kernel facts or generic attestation-kernel facts;
   - `worker_provider_id` or `worker_model_id` may not be inferred from the
     attestation-provider `provider_id` carried by released attestation support
     artifacts.
5. Run-support strategy:
   - every accepted attestation / provenance derivation must bind explicit released
     run-support carriers rather than ambiently:
     - `taskpack_runner_result@1`;
     - `taskpack_runner_provenance@1`;
     - `taskpack_verification_result@1`;
     - `taskpack_attestation_validator_result@1` when selected.
   - runner-result and runner-provenance refs are required;
   - verifier-result and attestation-validator refs may remain explicit optional
     support surfaces where the starter flow does not yet require every generic kernel
     lane simultaneously;
   - hidden repo search for support artifacts is forbidden.
   - released signature-envelope and trust-anchor inputs that sit behind released
     verifier / attestation carriers remain transitive support prerequisites only in
     this slice and may not be re-surfaced as new `V48-C` authority objects.
6. Attestation strategy:
   - `V48-C` releases exactly one typed `worker_execution_attestation@1` posture over
     one explicit task/run boundary instance;
   - attestation must carry explicit binding to:
     - boundary-instance ref;
     - compiled-binding ref;
     - runner-result ref;
     - runner-provenance ref;
     - verifier-result ref when present;
     - attestation-validator-result ref when present.
   - attestation must also carry explicit hash anchors sufficient to keep the consumed
     support chain machine-checkable:
     - `runner_result_hash` when that carrier hash subject is selected;
     - `runner_provenance_hash`;
     - `verification_result_hash` when present;
     - `attestation_validator_result_hash` when present.
   - generic attestation kernel artifacts remain support carriers here; `V48-C` may
     not silently redefine their semantics.
7. Provenance strategy:
   - `V48-C` releases exactly one typed `worker_execution_provenance@1` posture over
     one explicit task/run boundary instance;
   - provenance must carry explicit binding to:
     - boundary-instance ref;
     - runner-provenance ref;
     - runner-provenance hash;
     - repo ref;
     - task instance identity;
     - worker provider id;
     - worker model id;
     - execution adapter ref.
   - any `emitted_artifact_refs` carried by provenance must remain bounded to
     support-artifact outputs only and may not widen into arbitrary filesystem
     mutation inventory, action traces, or other observed-action carriers.
8. Hash / lineage strategy:
   - the released compiled boundary identity hash consumed by `V48-C` must match the
     released compiled binding exactly;
   - runner-result and runner-provenance artifacts must remain hash-consistent with the
     attestation / provenance surfaces that consume them;
   - stale, dangling, unresolved, or cross-repo compiled boundary reuse must fail
     closed.
   - `repo_ref` must name one exact execution repository identity coherent with the
     bound `snapshot_id` and `snapshot_sha256`; it may not be a floating branch or
     ref label.
9. Prompt-authority strategy:
   - prompt text, chat prose, and `AGENTS.md` remain projection/context only when a
     typed boundary-instance / attestation / provenance surface exists;
   - if prompt or prose claims conflict with the released compiled boundary, task/run
     boundary instance, or attestation / provenance surfaces, the typed surfaces must
     win and the conflict must fail closed.
10. Anti-overreach strategy:
   - `V48-C` may not emit replayable conformance reports or observed-action carriers;
   - `V48-C` may not silently widen into multi-worker topology, signature-envelope
     redefinition, execution-result redefinition, or execution / approval authority
     expansion;
   - `V48-C` may not treat worker-run attestation as proof that later conformance
     already shipped.

## Bounded Worker-Envelope Vocabularies

The first `V48-C` release should freeze bounded worker-envelope vocabularies rather
than leave execution-envelope posture to implementation taste.

The intended bounded starter vocabularies are:

- `compiled_binding_source_kind`:
  - `released_compiled_policy_taskpack_binding_ref`
- `worker_subject_kind`:
  - `repo_internal_single_codex_worker`
- `execution_adapter_kind`:
  - `released_taskpack_runner_adapter`
- `repo_ref_kind`:
  - `exact_execution_repository_identity`
- `support_ref_kind`:
  - `released_taskpack_runner_result_ref`
  - `released_taskpack_runner_provenance_ref`
  - `released_taskpack_verification_result_ref`
  - `released_taskpack_attestation_validator_result_ref`
- `prompt_authority_posture`:
  - `projection_only_conflict_fail_closed`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent doctrine creep.

## Required Deliverables

1. New typed worker-envelope surfaces:
   - canonical `task_run_boundary_instance@1` artifact;
   - canonical `worker_execution_attestation@1` artifact;
   - canonical `worker_execution_provenance@1` artifact;
   - authoritative and mirrored schema export parity for each released artifact.
2. Deterministic worker-envelope derivation entrypoint(s) that:
   - consume exactly one released `compiled_policy_taskpack_binding@1`;
   - consume exactly one repo ref and one declared task instance identity;
   - bind exactly one worker subject kind / ref and one provider / model / adapter
     tuple;
   - consume explicit released runner-result / runner-provenance support carriers and
     explicit verifier / attestation support carriers only when selected;
   - keep worker provider/model identity explicit as envelope-owned facts rather than
     inferring them from attestation-provider fields;
   - fail closed on raw bypass, stale reuse, prompt-authority drift, contradictory
     worker identity, or support-artifact hash mismatch.
3. Top-level schema anchors for `task_run_boundary_instance@1`:
   - `schema`
   - `boundary_instance_id`
   - `compiled_binding_source_kind`
   - `compiled_binding_ref`
   - `compiled_boundary_identity_hash`
   - `repo_ref_kind`
   - `repo_ref`
   - `task_instance_identity`
   - `snapshot_id`
   - `snapshot_sha256`
   - `worker_subject_kind`
   - `worker_subject_ref`
   - `execution_adapter_kind`
   - `execution_adapter_ref`
   - `worker_provider_id`
   - `worker_model_id`
   - `taskpack_manifest_ref`
   - `semantic_hash`
4. Top-level schema anchors for `worker_execution_attestation@1`:
   - `schema`
   - `worker_execution_attestation_id`
   - `boundary_instance_ref`
   - `compiled_binding_ref`
   - `runner_result_ref`
   - `runner_result_hash`
   - `runner_provenance_ref`
   - `runner_provenance_hash`
   - `verification_result_ref`
   - `verification_result_hash`
   - `attestation_validator_result_ref`
   - `attestation_validator_result_hash`
   - `prompt_authority_posture`
   - `semantic_hash`
   - invariants:
     - `runner_result_ref` required;
     - `runner_provenance_ref` required;
     - `runner_provenance_hash` required;
     - `compiled_binding_ref` must match the bound boundary instance;
     - if `runner_result_hash` is present, it must match the bound runner-result
       artifact hash subject;
     - if `verification_result_ref` is present, `verification_result_hash` must also
       be present;
     - if `attestation_validator_result_ref` is present,
       `attestation_validator_result_hash` must also be present;
     - if `attestation_validator_result_ref` is present, it may not contradict the
       bound runner-result / runner-provenance lineage.
5. Top-level schema anchors for `worker_execution_provenance@1`:
   - `schema`
   - `worker_execution_provenance_id`
   - `boundary_instance_ref`
   - `runner_provenance_ref`
   - `runner_provenance_hash`
   - `repo_ref`
   - `task_instance_identity`
   - `worker_provider_id`
   - `worker_model_id`
   - `execution_adapter_ref`
   - `emitted_artifact_refs`
   - `semantic_hash`
   - invariants:
     - `runner_provenance_ref` required;
     - `runner_provenance_hash` required and must match the bound artifact;
     - `repo_ref`, `task_instance_identity`, `worker_provider_id`, `worker_model_id`,
       and `execution_adapter_ref` must remain coherent with the bound boundary
       instance.
     - `emitted_artifact_refs` may contain support-artifact outputs only and may not
       encode arbitrary observed-action or mutation inventory.
6. Accepted doctrine fixtures:
   - at least one accepted task/run boundary instance fixture over the released `V48-B`
     reference compiled binding;
   - at least one accepted worker execution attestation fixture;
   - at least one accepted worker execution provenance fixture;
   - at least one accepted support-binding fixture using released runner-result /
     runner-provenance carriers.
7. Reject fixtures that fail closed on:
   - raw `V48-A` / `V45` / `V47` bypass;
   - multiple compiled binding refs or ambiguous task instance identity;
   - missing worker subject kind / ref, repo ref, or provider / model / adapter
     identity;
   - worker provider/model identity inferred from attestation-provider identity;
   - contradictory worker identity between boundary instance and provenance;
   - runner-result / runner-provenance hash mismatch;
   - attestation support refs present without the corresponding required hash anchors;
   - stale, dangling, or cross-repo compiled boundary reuse;
   - floating branch/ref-style `repo_ref` in place of exact execution repository
     identity;
   - prompt / chat / `AGENTS.md` authority drift;
   - conformance or observed-action carrier claims;
   - provenance `emitted_artifact_refs` widened into arbitrary mutation inventory or
     action traces;
   - signature / trust-anchor surfaces re-surfaced as new direct `V48-C` authority
     objects;
   - multi-worker topology claims;
   - execution, approval, waiver, or deferral authority claims.
8. Deterministic targeted tests covering:
   - reference boundary-instance replay retention;
   - worker execution attestation derivation;
   - worker execution provenance derivation;
   - support-artifact hash / lineage validation;
   - schema export parity;
   - reject-fixture fail-closed behavior.

## Acceptance

`V48-C` is complete when:

1. canonical `task_run_boundary_instance@1`, `worker_execution_attestation@1`, and
   `worker_execution_provenance@1` ship with authoritative / mirrored schema parity;
2. accepted fixtures show one released compiled boundary consumed by one explicit
   task/run boundary instance and one explicit attestation / provenance chain;
3. worker subject kind / ref and provider / model / adapter identity are always
   explicit rather than inferred;
4. worker provider/model identity is not conflated with attestation-provider identity;
5. runner-result / runner-provenance support carriers and any selected verifier /
   attestation support carriers remain explicit and hash-coherent;
6. prompt conflict fails closed rather than adding authority;
7. stale or unresolved compiled boundary reuse fails closed;
8. emitted provenance artifact refs remain support-only and not observed-action
   carriers;
9. released signature / trust-anchor inputs remain transitive support behind released
   verifier / attestation carriers rather than new `V48-C` authority objects;
10. the shipped slice remains pre-conformance, single-worker, and non-topological;
11. the shipped slice does not mint broader execution, approval, waiver, or deferral
    authority than the already released compiled boundary allows.

## Do Not Ship

Do not treat `V48-C` as authority to ship:

- replayable post-run conformance reports;
- observed-action carrier release;
- multi-worker topology;
- generic signature-envelope or generic execution-result redefinition;
- raw `V48-A` / `V45` / `V47` bypass into worker-run doctrine;
- execution, approval, mutation, scheduling, waiver, or deferral authority expansion.
