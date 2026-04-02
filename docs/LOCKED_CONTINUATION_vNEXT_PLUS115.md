# Locked Continuation vNext+115

Status: `V48-D` implementation contract.

## V115 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v48d_worker_boundary_conformance_replay_contract@1",
  "target_arc": "vNext+115",
  "target_path": "V48-D",
  "target_scope": "bounded_single_worker_post_run_conformance_over_released_worker_envelope_and_frozen_observed_action_carriers",
  "implementation_packages": [
    "adeu_agent_harness"
  ],
  "governing_released_stack": "V48A_to_V48C_released_bridge_stack_plus_released_agent_harness_runner_verifier_and_attestation_kernel_on_main",
  "governing_stack_consumption_mode": "released_worker_envelope_to_single_worker_post_run_conformance_only_not_raw_binding_or_compiled_boundary_bypass_signature_envelope_redefinition_execution_authority_expansion_or_multi_worker_topology",
  "requires_released_v48a_binding_profile_surfaces": true,
  "requires_released_v48b_compiled_binding_surfaces": true,
  "requires_released_v48c_worker_execution_envelope_surfaces": true,
  "requires_released_taskpack_runner_surfaces": true,
  "requires_released_taskpack_verifier_surfaces": true,
  "requires_released_attestation_validator_surfaces": true,
  "worker_boundary_conformance_report_schema": "worker_boundary_conformance_report@1",
  "exactly_one_boundary_instance_ref_required": true,
  "exactly_one_worker_execution_attestation_ref_required": true,
  "exactly_one_worker_execution_provenance_ref_required": true,
  "observed_action_carrier_set_explicit_required": true,
  "filesystem_mutation_set_explicit_required": true,
  "filesystem_mutation_set_source_of_truth_explicit_required": true,
  "command_invocation_log_explicit_required": true,
  "command_invocation_log_source_of_truth_explicit_required": true,
  "emitted_artifact_set_explicit_required": true,
  "emitted_artifact_set_source_of_truth_explicit_required": true,
  "branch_ref_identity_explicit_required": true,
  "execution_repository_identity_branch_ref_source_of_truth_explicit_required": true,
  "compiled_boundary_lineage_match_required": true,
  "repo_ref_and_task_identity_match_required": true,
  "worker_subject_and_provider_model_adapter_match_required": true,
  "observed_action_support_vs_provenance_distinction_required": true,
  "support_artifacts_cannot_substitute_for_observed_action_carriers": true,
  "off_boundary_mutation_validation_required": true,
  "command_allowlist_and_forbidden_effect_validation_required": true,
  "emitted_artifact_set_coherence_validation_required": true,
  "prompt_projection_only_conflict_fail_closed_required": true,
  "ambient_repo_search_for_observed_carriers_forbidden": true,
  "overall_judgment_aggregation_rule_frozen": true,
  "overall_judgment_precedence_frozen": true,
  "starter_check_family_vocabulary_frozen": true,
  "per_check_judgment_vocabulary_frozen": true,
  "supporting_diagnostics_derivation_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "conformant_and_non_conformant_examples_required": true,
  "no_multi_worker_topology_yet": true,
  "no_execution_or_approval_authority_expansion": true,
  "no_automatic_waiver_or_deferral_issuance": true,
  "required_released_contracts": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS113.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md"
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

- Arc label: `vNext+115`
- Family label: `V48-D`
- Scope label: bounded single-worker post-run conformance over released worker envelope and frozen observed-action carriers

## Objective

Release the bounded `V48-D` post-run conformance / replay lane by materializing one
canonical doctrine surface over the released `V48-C` worker-execution envelope and the
released agent-harness runner / verifier / attestation kernel on `main` that makes
explicit:

- how one released `task_run_boundary_instance@1`, one released
  `worker_execution_attestation@1`, and one released `worker_execution_provenance@1`
  govern one single-worker conformance judgment;
- how one frozen observed-action carrier set is bound explicitly rather than by
  ambient repo search:
  - one filesystem mutation set;
  - one command invocation log;
  - one emitted artifact set;
  - one exact execution-repository identity / branch-ref carrier;
- how observed-action carriers remain distinct from support-artifact provenance and
  from prompt/chat/`AGENTS.md` prose;
- how one canonical `worker_boundary_conformance_report@1` derives explicit
  `conformant`, `non_conformant`, or `incomplete_evidence` judgment over the bound
  compiled boundary;
- what fail-closed rules prevent raw `V48-B` or raw `V48-A` bypass, missing lineage,
  off-boundary mutation laundering, unallowlisted command use, emitted-artifact drift,
  prompt-shaped authority drift, or branch-identity mismatch.

This slice is conformance-first and still single-worker. It does not reopen released
`V48-A` binding semantics, released `V48-B` compiler semantics, released `V48-C`
worker-envelope semantics, generic runner semantics, generic verifier semantics,
generic attestation semantics, generic signing semantics, or multi-worker topology.
It also does not widen into execution authority expansion, approval authority
expansion, benchmark / contest / structural-assessment doctrine, automatic waiver /
deferral issuance, or worker-handoff doctrine.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V48-D` releases one typed worker-boundary conformance surface over the already
     released `V48-C` worker-envelope chain and the already released harness runner /
     verifier / attestation kernel on `main`;
   - it does not reopen descriptive semantics, ANM semantics, released `V48-A`
     semantics, released `V48-B` semantics, released `V48-C` semantics, or generic
     runner / verifier / attestation semantics.
2. Package-ownership strategy:
   - `adeu_agent_harness` remains the sole implementation owner in this slice;
   - earlier released descriptive, normative, binding, compiled-boundary, and
     worker-envelope surfaces remain upstream authority inputs only and are not
     reopened directly here.
3. Input-source strategy:
   - every accepted `V48-D` derivation must consume exactly:
     - one released `task_run_boundary_instance@1`;
     - one released `worker_execution_attestation@1`;
     - one released `worker_execution_provenance@1`.
   - no conformance derivation may bypass the released worker envelope by binding
     directly to raw `compiled_policy_taskpack_binding@1`, raw
     `anm_taskpack_binding_profile@1`, raw `V45` scope artifacts, raw `V47-E` rows,
     or raw `D-IR` clause refs.
4. Observed-action strategy:
   - the first `V48-D` release freezes one explicit observed-action carrier set only:
     - one filesystem mutation set;
     - one command invocation log;
     - one emitted artifact set;
     - one exact execution-repository identity / branch-ref carrier.
   - every accepted conformance report must bind explicit refs to all four carrier
     kinds;
   - filesystem mutation set must be sourced from observed execution-state change
     between one declared pre-run repo state and one declared post-run repo state, or
     from one equivalently governed replay artifact over that same exact run; it may
     not be reconstructed from the candidate plan, from the compiled boundary, or from
     provenance/support carriers alone;
   - command invocation log must be sourced from runner-observed executed command
     events, or from one equivalently governed replay artifact over that same exact
     run; it may not be reconstructed from `COMMANDS.json`, from proposed commands, or
     from provenance/support carriers alone;
   - emitted artifact set must be sourced from observed materialized run outputs, or
     from one equivalently governed replay artifact over that same exact run; it may
     not be reconstructed from support bookkeeping or provenance/support carriers
     alone;
   - branch/ref identity carrier must be sourced from one exact execution repository
     identity capture for that same observed run and must carry any selected
     branch/ref/commit fields explicitly rather than by prose or ambient workspace
     discovery;
   - hidden repo search for observed-action carriers is forbidden;
   - observed-action carriers may not be inferred from prompt prose, `AGENTS.md`,
     support-artifact refs, candidate-plan material, or ambient workspace state.
5. Lineage strategy:
   - every accepted conformance report must remain coherent with exactly one released
     compiled boundary through the consumed `V48-C` boundary instance / attestation /
     provenance chain;
   - repo ref, task-instance identity, worker subject, and provider / model / adapter
     identity must match across the consumed worker-envelope carriers and the observed
     action set;
   - stale, dangling, unresolved, or cross-repo lineage must fail closed.
6. Mutation-validation strategy:
   - the filesystem mutation set must be judged against the bound allowlist and
     forbidden-path posture carried through the released compiled boundary;
   - off-boundary mutations may not be silently repaired, ignored, or downcast into
     advisory-only status inside this slice;
   - a report may judge such a run only as `non_conformant` or
     `incomplete_evidence`, never `conformant`.
7. Command-validation strategy:
   - the command invocation log must be judged against the bound command posture
     carried through the released compiled boundary;
   - unallowlisted command use, forbidden effect drift, or malformed command lineage
     must fail closed;
   - no precedence algebra between prompt text and typed command posture is selected
     here.
8. Emitted-artifact strategy:
   - the emitted artifact set must remain distinct from support-only
     `emitted_artifact_refs` in released `worker_execution_provenance@1`;
   - conformance may use provenance only as support lineage, not as a substitute for
     the observed emitted artifact set;
   - contradictory emitted-artifact posture must fail closed.
9. Branch-identity strategy:
   - the branch/ref identity carrier must name one exact execution repository
     identity posture for the observed run, with any selected branch/ref/commit fields
     carried explicitly inside that carrier;
   - that carrier must remain coherent with the exact execution repository identity
     already bound in the released `V48-C` boundary instance and may not widen into
     floating repo search, loose git-branch prose, or multi-branch interpretation.
10. Judgment strategy:
   - `V48-D` releases exactly one typed `worker_boundary_conformance_report@1`
     aggregation posture;
   - overall judgment must be derived from the frozen check results rather than set by
     prose;
   - the first release freezes exactly:
     - `conformant`
     - `non_conformant`
     - `incomplete_evidence`
   - overall judgment precedence is frozen exactly as:
     - missing required observed-action carrier or unresolved lineage:
       `incomplete_evidence`;
     - any definite off-boundary mutation, command drift, emitted-artifact
       contradiction, branch-identity mismatch, or prompt conflict:
       `non_conformant`;
     - only when all required checks pass and evidence is complete:
       `conformant`;
   - supporting diagnostics and failed check families must be derivable from the same
     frozen check set.
11. Prompt-authority strategy:
   - prompt text, chat prose, and `AGENTS.md` remain projection/context only when a
     typed conformance surface exists;
   - if prose claims conflict with the bound compiled boundary, released worker
     envelope, or observed-action carriers, the typed surfaces must win and the
     conflict must fail closed.
12. Anti-overreach strategy:
   - `V48-D` may not widen into multi-worker topology, supervisor/worker handoff,
     worker/worker handoff, execution-result redefinition, signature-envelope
     redefinition, or execution / approval authority expansion;
   - `V48-D` may not treat conformance reporting as license to mint new authority
     beyond the already released compiled boundary.

## Bounded Conformance Vocabularies

The first `V48-D` release should freeze bounded conformance vocabularies rather than
leave post-run judgment posture to implementation taste.

The intended bounded starter vocabularies are:

- `observed_action_carrier_kind`:
  - `filesystem_mutation_set_ref`
  - `command_invocation_log_ref`
  - `emitted_artifact_set_ref`
  - `branch_ref_identity_ref`
- `check_family`:
  - `lineage_match`
  - `filesystem_mutation_scope`
  - `command_invocation_scope`
  - `emitted_artifact_coherence`
  - `execution_repository_identity_match`
  - `prompt_conflict`
- `check_judgment`:
  - `pass`
  - `fail`
  - `incomplete_evidence`
- `overall_judgment`:
  - `conformant`
  - `non_conformant`
  - `incomplete_evidence`
- `prompt_authority_posture`:
  - `projection_only_conflict_fail_closed`
- `worker_scope_posture`:
  - `single_worker_only`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent doctrine creep.

## Required Deliverables

1. New typed conformance surface:
   - canonical `worker_boundary_conformance_report@1` artifact;
   - authoritative and mirrored schema export parity for that artifact.
2. Deterministic conformance derivation entrypoint(s) that:
   - consume exactly one released `task_run_boundary_instance@1`;
   - consume exactly one released `worker_execution_attestation@1`;
   - consume exactly one released `worker_execution_provenance@1`;
   - consume one explicit observed-action carrier set over the frozen four-carrier
     vocabulary;
   - derive explicit conformance judgment, supporting diagnostics, and semantic hash;
   - fail closed on missing lineage, off-boundary mutation, command drift,
     contradictory emitted-artifact posture, or branch-identity mismatch.
   - treat support-artifact provenance as lineage support only and never as a
     substitute for the frozen observed-action carrier set.
3. Top-level schema anchors for `worker_boundary_conformance_report@1`:
   - `schema`
   - `worker_boundary_conformance_report_id`
   - `snapshot_id`
   - `snapshot_sha256`
   - `compiled_binding_ref`
   - `boundary_instance_ref`
   - `worker_execution_attestation_ref`
   - `worker_execution_provenance_ref`
   - `repo_ref`
   - `task_instance_identity`
   - `worker_subject_kind`
   - `worker_subject_ref`
   - `observed_action_carriers`
   - `conformance_checks`
   - `overall_judgment`
   - `supporting_diagnostic_ids`
   - `semantic_hash`
   - observed-action carrier anchors:
     - `filesystem_mutation_set_ref`
     - `command_invocation_log_ref`
     - `emitted_artifact_set_ref`
     - `branch_ref_identity_ref`
   - conformance-check row anchors:
     - `check_id`
     - `check_family`
     - `judgment`
     - `detail`
     - `supporting_observed_action_refs`
   - carrier acquisition anchors:
     - `carrier_source_of_truth`
     - `carrier_observation_scope`
4. Accepted doctrine fixtures:
   - at least one accepted conformant report fixture;
   - at least one accepted non-conformant report fixture;
   - at least one accepted deterministic replay fixture;
   - at least one accepted off-boundary mutation diagnostic fixture;
   - at least one accepted command-drift diagnostic fixture.
5. Reject fixtures that fail closed on:
   - raw `V48-B` or raw `V48-A` bypass;
   - missing `V48-C` boundary-instance / attestation / provenance carrier;
   - missing observed-action carrier;
   - repo/task/worker identity mismatch across the consumed lineage;
   - observed-action carrier reconstructed from provenance/support artifacts alone;
   - prompt-authority conflict;
   - off-boundary mutation judged as conformant;
   - unallowlisted command invocation judged as conformant;
   - contradictory emitted artifact set posture;
   - branch/ref identity mismatch;
   - multi-worker topology claims;
   - execution, approval, waiver, or deferral authority claims.
6. Deterministic targeted tests covering:
   - conformant replay;
   - non-conformant replay;
   - mutation and command validation;
   - lineage fail-closed behavior;
   - schema export parity.

## Acceptance

`V48-D` is complete when:

1. `worker_boundary_conformance_report@1` ships with authoritative/mirror schema
   parity;
2. accepted fixtures show both conformant and bounded non-conformant posture without
   ambiguity;
3. every accepted report binds the released `V48-C` worker-envelope chain explicitly
   rather than by ambient search;
4. the first observed-action carrier set remains frozen to the four planned carrier
   kinds;
5. each frozen observed-action carrier kind ships with one explicit source-of-truth /
   acquisition rule rather than ambient reconstruction posture;
6. support/provenance artifacts cannot substitute for observed-action carriers;
7. conformance judgment is derived from typed checks rather than prose assertion and
   follows the frozen precedence rule exactly;
8. starter `check_family` and per-check `judgment` vocabularies remain explicit and
   bounded;
9. off-boundary mutation, command drift, emitted-artifact contradiction, and branch
   identity mismatch fail closed;
10. the shipped slice remains single-worker, non-executive, and non-topological.

## Do Not Ship

Do not treat `V48-D` as authority to ship:

- multi-worker topology;
- supervisor/worker or worker/worker handoff doctrine;
- execution authority expansion;
- approval authority expansion;
- signature-envelope redefinition;
- automatic waiver or deferral issuance;
- benchmark, contest, or structural-assessment doctrine;
- provenance/support artifacts as a substitute for observed-action carriers;
- prompt-shaped authority as a substitute for typed conformance lineage.
