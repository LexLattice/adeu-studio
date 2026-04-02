# Locked Continuation vNext+112

Status: `V48-A` implementation contract.

## V112 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v48a_policy_to_taskpack_binding_contract@1",
  "target_arc": "vNext+112",
  "target_path": "V48-A",
  "target_scope": "bounded_policy_scope_to_taskpack_binding_profile",
  "implementation_packages": [
    "adeu_agent_harness"
  ],
  "governing_released_stack": "V45_and_V47_released_stacks_plus_released_agent_harness_kernel_on_main",
  "governing_stack_consumption_mode": "released_scope_and_policy_binding_only_not_policy_composition_scope_widening_multi_worker_orchestration_execution_authority_expansion_or_harness_kernel_redefinition",
  "requires_released_v45f_binding_surfaces": true,
  "requires_released_v47e_policy_consumer_surfaces": true,
  "v47e_row_to_bound_d1_clause_authority_chain_required": true,
  "v45f_entry_scope_and_subject_admission_coherence_required": true,
  "v45f_entry_admission_not_execution_authority_required": true,
  "requires_released_taskpack_compile_surfaces": true,
  "released_taskpack_runner_surfaces_present_as_future_lane_context": true,
  "released_taskpack_signature_verification_surfaces_present_as_future_lane_context": true,
  "released_runner_provenance_surfaces_present_as_future_lane_context": true,
  "anm_taskpack_binding_profile_schema": "anm_taskpack_binding_profile@1",
  "exactly_one_policy_source_ref_required": true,
  "exactly_one_scope_source_ref_required": true,
  "exactly_one_scope_binding_entry_ref_required": true,
  "exactly_one_worker_subject_required": true,
  "exactly_one_binding_subject_required": true,
  "policy_composition_not_selected": true,
  "policy_conflict_resolution_not_selected": true,
  "scope_union_or_widening_not_selected": true,
  "taskpack_surface_category_mapping_explicit_required": true,
  "taskpack_surface_mapping_limited_to_released_kernel_categories_required": true,
  "projection_conflict_fail_closed_required": true,
  "command_and_evidence_projection_kernel_shape_required": true,
  "prompt_projection_only_required": true,
  "prompt_boundary_conflict_fail_closed_required": true,
  "soft_prompt_or_agents_authority_insufficient_required": true,
  "unsupported_policy_to_taskpack_mapping_fail_closed_required": true,
  "stale_or_unresolved_lineage_fail_closed_required": true,
  "same_snapshot_identity_required": true,
  "artifact_local_source_scope_compatibility_required": true,
  "binding_profile_examples_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "no_taskpack_manifest_or_bundle_emission_yet": true,
  "no_worker_attestation_or_conformance_release_yet": true,
  "no_multi_worker_topology_yet": true,
  "no_repo_wide_taskpack_generation_required": true,
  "no_execution_or_approval_authority_expansion": true,
  "no_automatic_waiver_or_deferral_issuance": true,
  "required_released_contracts": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS109.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS110.md"
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

- Arc label: `vNext+112`
- Family label: `V48-A`
- Scope label: bounded policy/scope-to-taskpack binding profile

## Objective

Release the bounded `V48-A` policy/scope-to-taskpack binding lane by materializing one
canonical doctrine surface over the released `V45` + `V47` stacks and the released
agent-harness kernel on `main` that makes explicit:

- which single released `V47` policy-bearing source governs one taskpack binding;
- which single released `V45` scope-bearing source bounds one worker-reachable task
  scope;
- which released `V45-F` binding entry admits that released scope surface to later
  normative / execution-envelope use;
- how one binding subject maps into released taskpack surface categories for:
  - allowlist paths;
  - forbidden paths / forbidden effects;
  - commands;
  - evidence slots;
- how prompt text, chat prose, and `AGENTS.md` remain projections of the typed
  boundary rather than execution authority;
- what fail-closed rules prevent hidden policy composition, hidden scope widening,
  stale-lineage reuse, or prompt-driven authority drift.

This slice is binding-first and non-orchestrational. It does not reopen released `V45`
or released `V47` semantics, generic taskpack-kernel semantics, taskpack manifest /
bundle compilation, signature verification semantics, worker attestation semantics,
post-run conformance semantics, or multi-worker topology doctrine. It also does not
widen into execution authority, approval authority, waiver / deferral issuance,
repo-wide taskpack generation, benchmark / contest / structural-assessment doctrine,
or prompt-shaped authority.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V48-A` releases one typed binding-profile surface only over the already
     released `V45` + `V47` stacks and the already released agent-harness kernel on
     `main`;
   - it does not reopen descriptive semantics, normative semantics, or generic
     taskpack / runner / signing semantics.
2. Package-ownership strategy:
   - `adeu_agent_harness` is the sole implementation owner in this first slice;
   - released `adeu_repo_description`, `adeu_semantic_source`, and
     `adeu_commitments_ir` artifacts are consumed as upstream authority inputs, not
     reopened as first-owner surfaces.
3. Policy-source strategy:
   - the first `V48-A` release supports exactly one policy-source kind:
     - `released_v47e_policy_consumer_row_ref`
   - the released `V47-E` row is the admitted policy carrier for this slice, but the
     row's bound released `D-IR` clause remains the upstream policy authority;
   - no `V48-A` binding row may treat the `V47-E` consumer row as self-authorizing
     apart from that bound clause lineage;
   - every admitted `V47-E` row must therefore resolve coherently to:
     - exactly one bound released `D-IR` clause source;
     - the same declared snapshot and source-scope-compatible baseline;
   - the first `V48-A` release does not select:
     - raw `D-IR` clause binding as a direct starter carrier;
     - benchmark-consumer rows from `V47-F`;
     - multi-policy sets;
     - policy precedence or conflict-resolution algebra.
4. Scope-source strategy:
   - the first `V48-A` release supports exactly one scope-source kind:
     - `released_v45_scope_surface_ref`
   - every bound scope source must also carry exactly one released `V45-F` admission
     surface:
     - `released_v45f_binding_entry_ref`
   - the released `V45-F` entry must resolve coherently to:
     - the same released scope surface named by `scope_source_ref`;
     - the same binding subject posture selected by this slice;
   - the released `V45-F` entry admits later constrained consumption of that scope
     surface, but it does not mint execution-envelope authority by itself;
   - the first `V48-A` release does not select:
     - scope union;
     - scope widening;
     - ambient repo discovery as authority;
     - prompt-defined scope expansion.
5. Binding-subject strategy:
   - each released binding profile governs exactly:
     - one policy source;
     - one scope source;
     - one scope-binding entry;
     - one worker subject;
     - one binding subject.
   - the first release supports only:
     - `repo_internal_single_codex_worker`
   - multi-worker topology, planner decomposition, and worker/worker handoff remain
     out of scope.
6. Taskpack-mapping strategy:
   - `V48-A` maps bound policy + scope only into already released taskpack surface
     categories:
     - allowlist paths;
     - forbidden paths;
     - forbidden effects;
     - commands;
     - evidence slots.
   - `V48-A` does not yet emit:
     - `taskpack/manifest@1`;
     - bundle hashes;
     - signature envelopes;
     - runner results;
     - attestation outputs;
     - conformance reports.
   - taskpack projections must remain kernel-shaped rather than prose-shaped:
     - `command_projection` may lower only into released command carriers shaped like
       `taskpack/commands@1` rows with:
       - `command_id`
       - `run`
       - `working_directory_or_repo_root`
       - `env_overrides`
     - `evidence_slot_projection` may lower only into released evidence-slot carriers
       shaped like `taskpack/evidence_slots@1` rows with:
       - `slot_id`
       - `description`
       - `required`
   - contradictory projections must fail closed rather than selecting precedence:
     - the same path may not be both allowed and forbidden;
     - the same forbidden effect may not be both required and forbidden through mixed
       projection posture;
     - the same command or evidence slot may not be multiply projected with
       contradictory kernel-shaped payloads.
   - unsupported mapping requests must fail closed rather than inventing ad hoc
     categories or local conventions.
7. Prompt-authority strategy:
   - prompt text, chat prose, and `AGENTS.md` are projection/context only when a typed
     binding profile exists;
   - if prompt/chat/`AGENTS.md` prose conflicts with the compiled boundary described
     by the binding profile, the typed boundary wins and the conflict must be treated
     as a verifier / compiler error rather than extra authority;
   - prose may restate or narrow only through already declared typed boundary
     parameters and may not add new authority.
8. Upstream-lineage strategy:
   - every binding profile must resolve coherently against:
     - one declared snapshot identity;
     - one source-scope-compatible baseline;
     - one released `V47-E` policy row;
     - one released `V45` scope surface;
     - one released `V45-F` binding entry admitting that scope surface to later
       constraint use.
   - stale, dangling, or unresolved lineage must fail closed.
   - released taskpack runner, signature-verification, and runner-provenance surfaces
     remain relevant baseline context on `main` for later `V48-B` through `V48-D`
     paths, but they are not semantic starter dependencies of the binding-profile
     release itself.
9. Anti-overreach strategy:
   - `V48-A` may not mint execution, approval, mutation, scheduling, waiver, or
     deferral authority;
   - `V48-A` may not silently redefine generic taskpack-kernel semantics;
   - `V48-A` may not silently widen into multi-worker orchestration or repo-wide
     taskpack generation.

## Bounded Binding Vocabularies

The first `V48-A` release should freeze bounded binding vocabularies rather than leave
policy/scope-to-taskpack posture to implementation taste.

The intended bounded starter vocabularies are:

- `policy_binding_source_kind`:
  - `released_v47e_policy_consumer_row_ref`
- `scope_binding_source_kind`:
  - `released_v45_scope_surface_ref`
- `scope_binding_authority_kind`:
  - `released_v45f_binding_entry_ref`
- `worker_subject_kind`:
  - `repo_internal_single_codex_worker`
- `taskpack_surface_category`:
  - `allowlist_projection`
  - `forbidden_projection`
  - `command_projection`
  - `evidence_slot_projection`
- `prompt_projection_posture`:
  - `projection_only_non_authoritative`
- `lineage_resolution_posture`:
  - `fail_closed_on_unresolved_or_stale_lineage`
- `unsupported_mapping_posture`:
  - `fail_closed`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent doctrine creep.

The first `V48-A` release also freezes these binding invariants:

- `policy_binding_source_kind = released_v47e_policy_consumer_row_ref`:
  - exactly one `policy_source_ref` is required
  - the resolved `V47-E` row must bind exactly one released `D-IR` clause source, and
    that bound clause remains the upstream policy authority
- `scope_binding_source_kind = released_v45_scope_surface_ref`:
  - exactly one `scope_source_ref` is required
- `scope_binding_authority_kind = released_v45f_binding_entry_ref`:
  - exactly one `scope_binding_entry_ref` is required
  - the resolved `V45-F` entry must admit the same scope surface and binding subject
    posture named by the binding profile and may not self-authorize execution
- `worker_subject_kind = repo_internal_single_codex_worker`:
  - exactly one `worker_subject_ref` is required
  - no topology or worker-count widening carrier is selected in this slice

## Required Deliverables

1. New typed binding surface:
   - canonical `anm_taskpack_binding_profile@1` artifact;
   - authoritative and mirrored schema export parity for that artifact.
2. Deterministic binding derivation entrypoint(s) that:
   - bind one declared snapshot identity;
   - consume one bounded source set over one released `V47-E` policy row plus one
     released `V45` scope surface and one released `V45-F` binding entry;
   - emit explicit taskpack-category projections only for:
     - allowlist;
     - forbidden;
     - commands;
     - evidence slots;
   - fail closed on multi-policy posture, multi-scope posture, stale lineage,
     unresolved lineage, unsupported mapping, or prompt-boundary conflict.
3. Top-level schema anchors for `anm_taskpack_binding_profile@1`:
   - `schema`
   - `binding_profile_id`
   - `snapshot_id`
   - `snapshot_sha256`
   - `binding_subject_id`
   - `task_scope_summary`
   - `policy_binding_source_kind`
   - `policy_source_ref`
   - `scope_binding_source_kind`
   - `scope_source_ref`
   - `scope_binding_authority_kind`
   - `scope_binding_entry_ref`
   - `worker_subject_kind`
   - `worker_subject_ref`
   - `allowlist_projection`
   - `forbidden_projection`
   - `command_projection`
   - `evidence_slot_projection`
   - `prompt_projection_posture`
   - `lineage_resolution_posture`
   - `unsupported_mapping_posture`
   - `semantic_hash`
   - `command_projection` row anchors:
     - `command_id`
     - `run`
     - `working_directory_or_repo_root`
     - `env_overrides`
   - `evidence_slot_projection` row anchors:
     - `slot_id`
     - `description`
     - `required`
4. Accepted doctrine fixtures:
   - at least one accepted single-policy / single-scope binding fixture over released
     `V47-E` + `V45-F` lineage;
   - at least one accepted prompt-projection-only fixture where prose restates but
     does not add authority;
   - at least one accepted taskpack-category mapping fixture with explicit allowlist,
     forbidden, command, and evidence-slot projections.
5. Reject fixtures that fail closed on:
   - more than one policy source;
   - more than one scope source;
   - missing or stale released `V47-E` policy lineage;
   - missing, stale, or mismatched bound `D-IR` clause lineage under the admitted
     `V47-E` row;
   - missing or stale released `V45` scope lineage;
   - missing or stale released `V45-F` scope-binding-entry lineage;
   - `V45-F` entries that do not admit the same scope surface and binding subject
     posture named by the binding profile;
   - unsupported taskpack-surface mapping requests;
   - contradictory allowlist / forbidden / command / evidence-slot projections;
   - prompt/chat/`AGENTS.md` prose that adds authority beyond the typed boundary;
   - hidden scope widening or ambient repo-discovery scope expansion;
   - multi-worker or topology claims;
   - execution, approval, waiver, or deferral authority claims.
6. Deterministic targeted tests covering:
   - exact starter vocabulary enforcement;
   - single-policy / single-scope / single-worker invariants;
   - released-lineage resolution and stale-lineage fail-closed behavior;
   - prompt-conflict fail-closed behavior;
   - schema export parity;
   - committed fixture replay.

## Acceptance

Accept this slice only if:

1. canonical `anm_taskpack_binding_profile@1` ships with authoritative / mirrored
   schema parity;
2. every accepted binding profile carries exactly one released policy source, one
   released scope source, one released scope-binding entry, and one worker subject;
3. released `V47-E` policy lineage and released `V45` / `V45-F` scope lineage are
   always explicit rather than inferred from repo prose or local convention;
4. every admitted `V47-E` row resolves to exactly one bound released `D-IR` clause,
   and that bound clause remains the upstream policy authority;
5. every admitted `V45-F` entry resolves to the same bound scope surface / binding
   subject posture and remains admission-only rather than execution-authorizing;
6. taskpack-category mappings stay bounded to allowlist, forbidden, command, and
   evidence-slot projections only, with contradictory projections failing closed;
7. command and evidence-slot projections remain kernel-shaped rather than prose-shaped;
8. prompt, chat, and `AGENTS.md` text remain projection-only and any conflict with the
   typed boundary fails closed;
9. unsupported mapping requests, stale lineage, and unresolved lineage fail closed;
10. the shipped slice remains non-executive, non-approving, non-orchestrational, and
    does not redefine generic taskpack-kernel semantics;
11. schema export parity, committed fixture replay, and scoped Python tests pass.

Do not accept this slice if:

- the first release accepts more than one policy source or more than one scope source;
- `V48-A` quietly invents policy precedence, policy composition, or scope-union
  semantics;
- the admitted `V47-E` row is treated as self-authorizing apart from its bound
  released `D-IR` clause lineage;
- the admitted `V45-F` entry is treated as execution-envelope authority instead of
  admission-only scope lineage;
- raw repo discovery, prompt text, chat prose, or `AGENTS.md` text can widen scope or
  add authority beyond the typed boundary;
- contradictory allowlist / forbidden / command / evidence-slot projections are
  tolerated;
- the binding profile emits manifest/bundle/signing/runner/attestation artifacts as if
  `V48-B` or `V48-C` had already shipped;
- taskpack surface categories are widened beyond the released kernel categories in this
  slice;
- stale or unresolved `V47-E`, `V45`, or `V45-F` lineage is tolerated;
- the slice widens into multi-worker topology, execution authority, approval
  authority, waiver issuance, or deferral issuance.

## Local Gate

- run `make arc-start-check ARC=112` while the bundle remains docs-only;
- run targeted Python checks for `adeu_agent_harness` once code work begins;
- do not treat this starter bundle as a substitute for the Python lane once source code
  changes begin.
