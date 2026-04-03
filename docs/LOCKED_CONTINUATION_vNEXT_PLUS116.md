# Locked Continuation vNext+116

Status: `V48-E` implementation contract.

## V116 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v48e_worker_delegation_topology_contract@1",
  "target_arc": "vNext+116",
  "target_path": "V48-E",
  "target_scope": "bounded_single_edge_supervisor_to_worker_topology_over_released_single_worker_conformance_lineage",
  "implementation_packages": [
    "adeu_agent_harness"
  ],
  "governing_released_stack": "V48A_to_V48D_released_bridge_stack_plus_released_agent_harness_runner_verifier_and_attestation_kernel_on_main",
  "governing_stack_consumption_mode": "released_single_worker_conformance_to_bounded_supervisor_worker_topology_only_not_raw_binding_compiled_boundary_worker_envelope_or_conformance_bypass_recursive_topology_repo_wide_orchestration_or_authority_expansion",
  "requires_released_v48a_binding_profile_surfaces": true,
  "requires_released_v48b_compiled_binding_surfaces": true,
  "requires_released_v48c_worker_execution_envelope_surfaces": true,
  "requires_released_v48d_worker_boundary_conformance_surfaces": true,
  "requires_released_taskpack_runner_surfaces": true,
  "requires_released_taskpack_verifier_surfaces": true,
  "requires_released_attestation_validator_surfaces": true,
  "worker_delegation_topology_schema": "worker_delegation_topology@1",
  "exactly_one_parent_worker_boundary_conformance_report_ref_required": true,
  "exactly_one_child_worker_boundary_conformance_report_ref_required": true,
  "parent_and_child_conformance_reports_transitively_required": true,
  "exactly_one_supervisor_role_required": true,
  "exactly_one_worker_role_required": true,
  "exactly_one_delegation_edge_id_required": true,
  "parent_task_instance_identity_explicit_required": true,
  "child_task_instance_identity_explicit_required": true,
  "delegated_task_identity_explicit_required": true,
  "parent_and_child_worker_subject_must_be_distinct": true,
  "parent_child_same_repo_ref_required": true,
  "parent_child_same_snapshot_required": true,
  "parent_child_same_compiled_binding_required": true,
  "same_compiled_boundary_is_deliberate_starter_restriction": true,
  "parent_child_conformant_required_for_accepted_topology": true,
  "prompt_projection_only_conflict_fail_closed_required": true,
  "starter_supporting_diagnostic_family_vocabulary_frozen": true,
  "supporting_diagnostics_derivation_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "accepted_supervisor_to_worker_example_required": true,
  "deterministic_replay_fixture_required": true,
  "worker_worker_topology_not_selected_here": true,
  "recursive_fan_out_forbidden": true,
  "repo_wide_orchestration_not_selected": true,
  "automatic_task_decomposition_not_selected": true,
  "no_execution_or_approval_authority_expansion": true,
  "no_automatic_waiver_or_deferral_issuance": true,
  "required_released_contracts": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS113.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md"
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

- Arc label: `vNext+116`
- Family label: `V48-E`
- Scope label: bounded single-edge supervisor-to-worker topology over released single-worker conformance lineage

## Objective

Release the bounded `V48-E` delegated topology lane by materializing one canonical
doctrine surface over the released `V48-D` single-worker conformance surface and the
already released `V48-C` / `V48-B` transitive lineage on `main` that makes explicit:

- how one released parent `worker_boundary_conformance_report@1` and one released
  child `worker_boundary_conformance_report@1` compose one typed delegation edge;
- how one explicit `supervisor` parent role and one explicit `worker` child role are
  bound without ambiguity;
- how one explicit parent task identity, one explicit delegated task identity, one
  explicit child task identity, one explicit delegation-edge identity, and one exact
  repo/snapshot identity remain coherent across both workers;
- how accepted topology remains bounded to the same released compiled boundary on both
  parent and child surfaces, as one deliberate first-slice restriction rather than a
  general delegation algebra, so handoff does not mint wider authority than the
  released single-worker bridge already allows;
- what fail-closed rules prevent raw `V48-D` / `V48-C` / `V48-B` bypass, parent/child
  role ambiguity, child non-conformance laundering, boundary drift, repo/snapshot
  drift, self-edge laundering, or recursive topology creep.

This slice is topology-first and still bounded. It does not reopen released `V48-A`
binding semantics, released `V48-B` compiler semantics, released `V48-C`
worker-envelope semantics, released `V48-D` conformance semantics, generic runner
semantics, generic verifier semantics, generic attestation semantics, or generic
signing semantics. It also does not widen into worker/worker doctrine, recursive
fan-out, repo-wide orchestration regime, execution authority expansion, approval
authority expansion, benchmark / contest / structural-assessment doctrine, automatic
waiver / deferral issuance, or automatic task-decomposition algebra.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V48-E` releases one typed worker-delegation topology surface over already
     released `V48-D` single-worker conformance reports and their transitive released
     `V48-C` / `V48-B` lineage;
   - it does not reopen descriptive semantics, ANM semantics, released `V48-A`
     semantics, released `V48-B` semantics, released `V48-C` semantics, released
     `V48-D` semantics, or generic runner / verifier / attestation semantics.
2. Package-ownership strategy:
   - `adeu_agent_harness` remains the sole implementation owner in this slice;
   - earlier released descriptive, normative, binding, compiled-boundary,
     worker-envelope, and conformance surfaces remain upstream authority inputs only
     and are not reopened directly here.
3. Input-source strategy:
   - every accepted `V48-E` derivation must consume exactly:
     - one released parent `worker_boundary_conformance_report@1`;
     - one released child `worker_boundary_conformance_report@1`.
   - those reports must resolve transitively to one released parent
     `task_run_boundary_instance@1`, one released parent
     `worker_execution_attestation@1`, one released parent
     `worker_execution_provenance@1`, and the corresponding single released child
     chain;
   - no topology derivation may bypass the released conformance surface by binding
     directly to raw `worker_execution_attestation@1`,
     `worker_execution_provenance@1`, raw `task_run_boundary_instance@1`, raw
     `compiled_policy_taskpack_binding@1`, raw `anm_taskpack_binding_profile@1`, raw
     `V45` scope artifacts, raw `V47-E` rows, or raw `D-IR` clause refs.
4. Parent/child role strategy:
   - the first `V48-E` release freezes one delegation-edge relation only:
     `supervisor_to_worker`;
   - every accepted topology must bind exactly one explicit parent role kind
     `supervisor` and exactly one explicit child role kind `worker`;
   - parent and child worker subjects must be distinct; a degenerate self-edge where
     the same worker subject appears as both `supervisor` and `worker` must fail
     closed;
   - worker/worker handoff doctrine is not selected in this slice.
5. Boundary-lineage strategy:
   - every accepted topology must remain coherent with one exact repo ref and one
     exact `snapshot_id` / `snapshot_sha256` posture across parent and child;
   - every accepted topology must bind parent and child to the same released compiled
     binding identity;
   - this exact parent/child compiled-boundary equality is a deliberate first-slice
     restriction that proves bounded handoff topology without yet releasing a general
     delegated-scope transformation algebra;
   - no parent-to-child widening algebra is selected here; the starter topology may
     consume only exact parent/child compiled-boundary equality;
   - stale, dangling, unresolved, or cross-repo lineage must fail closed.
6. Conformance-consumption strategy:
   - accepted topology is downstream of already released single-worker conformance;
   - every accepted topology must consume parent and child reports whose
     `overall_judgment` is `conformant`;
   - `non_conformant` or `incomplete_evidence` parent/child reports may not be
     silently laundered into accepted handoff topology.
7. Handoff-identity strategy:
   - every accepted topology must bind exactly one explicit `delegation_edge_id` and
     exactly one explicit `delegated_task_identity`;
   - every accepted topology must also bind exactly one explicit
     `parent_task_instance_identity` and exactly one explicit
     `child_task_instance_identity`;
   - parent task identity, delegated task identity, and child task identity must
     remain explicit and ordered rather than inferred from ambient repo search or
     prompt prose;
   - no multi-edge or many-child interpretation is selected here.
8. Handoff-result strategy:
   - `V48-E` releases one typed `worker_delegation_topology@1` surface with one
     explicit bounded handoff-result vocabulary;
   - accepted starter topology uses one explicit completed handoff posture;
   - `rejected` and `incomplete_lineage` remain typed emitted artifact states inside
     the released surface and may appear in reject fixtures or bounded diagnostics,
     but they are not accepted completion posture for this starter slice;
   - rejected or incomplete-lineage posture must remain typed and fail closed rather
     than being repaired by prose.
9. Diagnostic-family strategy:
   - `V48-E` freezes one bounded supporting-diagnostic family vocabulary for the
     starter slice:
     - `role_ambiguity`
     - `lineage_mismatch`
     - `compiled_boundary_mismatch`
     - `repo_snapshot_mismatch`
     - `non_conformant_parent`
     - `non_conformant_child`
     - `recursive_topology_forbidden`
   - supporting diagnostics may not widen beyond this starter family set without a
     later bounded continuation.
10. Prompt-authority strategy:
   - prompt text, chat prose, and `AGENTS.md` remain projection/context only when a
     typed topology surface exists;
   - if prose claims conflict with the released parent/child conformance lineage, the
     typed lineage must win and the conflict must fail closed.
11. Anti-overreach strategy:
   - `V48-E` may not widen into worker/worker topology, recursive fan-out,
     supervisor trees, repo-wide orchestration regime, scheduler semantics,
     execution-result redefinition, signature-envelope redefinition, or execution /
     approval authority expansion;
   - `V48-E` may not treat topology reporting as license to mint new authority beyond
     the already released compiled boundary shared by the bound parent and child runs.

## Bounded Topology Vocabularies

The first `V48-E` release should freeze bounded topology vocabularies rather than
leave delegated handoff posture to implementation taste.

The intended bounded starter vocabularies are:

- `delegation_edge_kind`:
  - `supervisor_to_worker`
- `worker_role_kind`:
  - `supervisor`
  - `worker`
- `handoff_result`:
  - `completed`
  - `rejected`
  - `incomplete_lineage`
- `supporting_diagnostic_family`:
  - `role_ambiguity`
  - `lineage_mismatch`
  - `compiled_boundary_mismatch`
  - `repo_snapshot_mismatch`
  - `non_conformant_parent`
  - `non_conformant_child`
  - `recursive_topology_forbidden`
- `topology_scope_posture`:
  - `one_parent_one_child_one_edge_only`
- `authority_relation_posture`:
  - `same_compiled_boundary_no_widening`
- `worker_scope_posture`:
  - `bounded_supervisor_worker_only`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent doctrine creep.

## Required Deliverables

1. New typed topology surface:
   - canonical `worker_delegation_topology@1` artifact;
   - authoritative and mirrored schema export parity for that artifact.
2. Deterministic topology derivation entrypoint(s) that:
   - consume exactly one released parent `worker_boundary_conformance_report@1`;
   - consume exactly one released child `worker_boundary_conformance_report@1`;
   - derive explicit parent/child role anchors, delegation-edge identity, delegated
     task identity, handoff result, starter supporting-diagnostic families, and
     semantic hash;
   - require exact same repo/snapshot identity and exact same compiled-binding
     identity across parent and child;
   - fail closed on raw bypass, role ambiguity, non-conformant lineage, self-edge
     worker-subject reuse, boundary drift, repo/snapshot drift, or
     recursive-topology claims.
3. Top-level schema anchors for `worker_delegation_topology@1`:
   - `schema`
   - `worker_delegation_topology_id`
   - `snapshot_id`
   - `snapshot_sha256`
   - `repo_ref`
   - `parent_worker_boundary_conformance_report_ref`
   - `child_worker_boundary_conformance_report_ref`
   - `parent_boundary_instance_ref`
   - `child_boundary_instance_ref`
   - `parent_compiled_binding_ref`
   - `child_compiled_binding_ref`
   - `parent_task_instance_identity`
   - `child_task_instance_identity`
   - `parent_worker_subject_kind`
   - `parent_worker_subject_ref`
   - `child_worker_subject_kind`
   - `child_worker_subject_ref`
   - `parent_role_kind`
   - `child_role_kind`
   - `delegation_edge_id`
   - `delegation_edge_kind`
   - `delegated_task_identity`
   - `handoff_result`
   - `topology_scope_posture`
   - `authority_relation_posture`
   - `supporting_diagnostic_ids`
   - `supporting_diagnostic_families`
   - `semantic_hash`
4. Accepted doctrine fixtures:
   - at least one accepted supervisor-to-worker topology fixture;
   - at least one accepted deterministic replay fixture;
   - at least one accepted handoff-edge fixture with explicit delegated task
     identity and explicit same-boundary posture;
   - accepted fixtures remain `handoff_result = completed` only in this starter
     slice.
5. Reject fixtures that fail closed on:
   - raw `V48-D`, raw `V48-C`, or raw `V48-B` bypass;
   - missing parent or missing child conformance report;
   - non-conformant or incomplete-evidence parent/child report;
   - identical parent and child worker-subject refs;
   - parent/child role ambiguity or swapped role posture;
   - parent/child compiled-boundary inequality;
   - repo or snapshot mismatch;
   - multiple-child or multiple-edge claims;
   - worker/worker claims;
   - recursive topology claims;
   - execution, approval, waiver, or deferral authority claims.
6. Deterministic targeted tests covering:
   - accepted supervisor-to-worker topology replay;
   - raw-input bypass rejection;
   - parent/child role and lineage validation;
   - boundary-equality fail-closed behavior;
   - schema export parity.

## Acceptance

`V48-E` is complete when:

1. `worker_delegation_topology@1` ships with authoritative/mirror schema parity;
2. accepted fixtures show one bounded supervisor-to-worker topology posture without
   ambiguity;
3. every accepted topology binds exactly one released parent and one released child
   `V48-D` conformance report explicitly rather than by ambient search;
4. parent and child remain coherent on exact repo/snapshot identity and exact
   compiled-boundary identity;
5. parent task identity, delegated task identity, and child task identity remain
   explicit and ordered;
6. parent and child worker subjects remain distinct;
7. parent role and child role remain explicit and bounded to
   `supervisor_to_worker`;
8. delegated task identity and delegation-edge identity remain explicit;
9. non-conformant or incomplete-evidence child lineage fails closed;
10. starter supporting-diagnostic families remain explicit and bounded;
11. worker/worker doctrine, recursive topology, and repo-wide orchestration do not
   appear in the shipped slice;
12. prompt authority remains projection-only and fail closed on conflict;
13. the shipped slice remains bounded, non-executive, and non-approving.

## Do Not Ship

Do not treat `V48-E` as authority to ship:

- worker/worker handoff doctrine;
- recursive fan-out or multi-edge topology;
- repo-wide orchestration regime;
- automatic task decomposition;
- execution authority expansion;
- approval authority expansion;
- signature-envelope redefinition;
- automatic waiver or deferral issuance;
- benchmark, contest, or structural-assessment doctrine;
- prompt-shaped authority as a substitute for typed topology lineage.
