# Locked Continuation vNext+120

Status: `V49-D` implementation contract.

## V120 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v49d_semantic_forms_v48_bridge_contract@1",
  "target_arc": "vNext+120",
  "target_path": "V49-D",
  "target_scope": "bounded_repo_owned_semantic_forms_seed_to_v48_binding_profile_bridge_for_repo_policy_work",
  "implementation_packages": [
    "adeu_semantic_forms"
  ],
  "governing_released_stack": "V45_repo_description_plus_V47_authoritative_normative_markdown_plus_V48_policy_to_taskpack_and_worker_enforcement_plus_V49A_semantic_forms_core_contracts_plus_V49B_semantic_forms_recovery_on_main_plus_V49C_semantic_forms_lowering_on_main",
  "governing_stack_consumption_mode": "anchor_and_downstream_consumer_context_only_not_reopened_description_semantics_not_reopened_normative_semantics_not_reopened_worker_enforcement_semantics_not_reopened_v49a_contract_semantics_not_reopened_v49b_recovery_semantics_not_reopened_v49c_lowering_semantics",
  "source_intake_bundle": "examples/external_prototypes/adeu-semantic-forms-v0-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "released_v49c_seed_required": true,
  "semantic_forms_bridge_v48_py_required": true,
  "single_seed_input_initially_required": true,
  "single_bridge_contract_input_initially_required": true,
  "single_binding_profile_output_initially_required": true,
  "starter_domain_singleton": "repo_policy_work",
  "released_seed_schema_singleton": "adeu_taskpack_binding_spec_seed@1",
  "bridge_contract_schema_singleton": "adeu_semantic_seed_v48_bridge_contract@1",
  "bridge_contract_schema_anchors_frozen": true,
  "bridge_consumes_released_v48a_builder_without_redefinition": true,
  "bridge_output_must_be_released_anm_taskpack_binding_profile": true,
  "bridge_output_must_be_admissible_as_released_v48b_binding_profile_ref_carrier": true,
  "raw_v45_v47_v49a_v49b_bypass_not_authorized": true,
  "seed_anchor_resolution_must_be_explicit_and_fail_closed": true,
  "seed_fixed_defaults_may_only_restate_released_v48a_postures": true,
  "bridge_contract_task_scope_and_prompt_inputs_must_be_explicit": true,
  "policy_authority_clause_ref_must_be_resolved_only_through_released_v48a_builder": true,
  "fixed_default_conflicts_fail_closed": true,
  "compile_invocation_wrapper_not_selected_here": true,
  "worker_runtime_surfaces_not_selected_here": true,
  "cli_api_web_consumers_not_selected_here": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS117.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS118.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS119.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49C_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49D_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md"
}
```

## Slice

- Arc label: `vNext+120`
- Family label: `V49-D`
- Scope label: bounded repo-owned semantic forms seed-to-`V48` bridge for
  `repo_policy_work`

## Objective

Release the bounded `V49-D` bridge lane by adding the first repo-owned helper that
consumes one released `adeu_taskpack_binding_spec_seed@1` plus one repo-owned bridge
contract and emits one released `anm_taskpack_binding_profile@1` admissible as the
released `binding_profile_ref` carrier for the released `V48-B` compile flow, with
the remaining released compiler inputs supplied separately.

This slice must make explicit:

- one released `adeu_taskpack_binding_spec_seed@1` input posture;
- one repo-owned `adeu_semantic_seed_v48_bridge_contract@1` input posture;
- one emitted released `anm_taskpack_binding_profile@1` output posture;
- one deterministic mapping law from released seed anchors plus bridge-contract refs
  into the released `V48-A` builder inputs;
- one fail-closed posture for:
  - unresolved seed-anchor mapping;
  - snapshot mismatch;
  - worker-subject mismatch;
  - missing task-scope or prompt projection inputs;
  - unresolved policy-authority clause lineage;
  - unsupported seed values;
  - fixed-default conflict with released `V48-A` posture;
- one explicit distinction between:
  - released `V49-C` lowering;
  - released `V48-A` binding semantics;
  - later consumer use of released `V48-B` compile semantics.

This slice is bridge-first and still bounded. It does not authorize a new compile
wrapper, worker runtime behavior, conformance, delegated topology, symbol audit
integration, paper semantic contract integration, simulation integration, or any CLI /
API / web consumer.

## Frozen Implementation Decisions

1. Package-ownership strategy:
   - `packages/adeu_semantic_forms` remains the sole implementation owner in this
     slice;
   - the imported intake pack remains shaping evidence only and may not be treated as
     the live bridge surface.
2. Input/output cardinality strategy:
   - one released seed only;
   - one repo-owned bridge contract only;
   - one emitted released binding profile only;
   - no batching and no multi-target bridge in this slice.
3. Bridge-authority strategy:
   - bridge code may consume only:
     - released `V49-C` seed payloads;
     - one repo-owned bridge contract;
     - the released `build_v48a_taskpack_binding_profile(...)` surface;
   - bridge code may not bypass through raw `V45`, raw `V47`, raw `V49-A`, or raw
     `V49-B` discovery outside the bridge contract plus the released `V48-A` builder
     expectations;
   - ambient repo search may not supply missing scope, policy, or worker authority.
4. Bridge-contract strategy:
   - the bridge contract must declare:
     - `schema`
     - `bridge_contract_id`
     - `profile_id`
     - `snapshot_id`
     - `snapshot_sha256`
     - `binding_profile_id`
     - `binding_subject_id`
     - `task_scope_summary`
     - `policy_source_ref`
     - `scope_source_ref`
     - `scope_binding_entry_ref`
     - `expected_scope_anchor_ref`
     - `expected_policy_anchor_ref`
     - `expected_worker_subject_ref`
     - `command_projection`
     - `evidence_slot_projection`
     - `prompt_projection_inputs`
     - `lineage_resolution_posture`
     - `prompt_projection_posture`
     - `unsupported_mapping_posture`
     - `semantic_hash`
   - the bridge contract may not redefine released `V48-A` projection semantics.
5. Mapping strategy:
   - `seed.scope_anchor_ref` must match the bridge-contract expected scope anchor;
   - `seed.policy_anchor_ref` must match the bridge-contract expected policy anchor;
   - `seed.worker_subject_ref` must match the bridge-contract expected worker subject;
   - `bridge_contract.task_scope_summary` must remain the sole source of
     `task_scope_summary` and may not be synthesized from seed prose;
   - `bridge_contract.prompt_projection_inputs` must remain the sole source of prompt
     projection inputs and may not be synthesized from prompt prose, chat memory, or
     prototype narrative text;
   - `seed.allow_paths -> allowlist_projection`;
   - `seed.forbid_paths` plus `seed.forbid_effects -> forbidden_projection`;
   - `seed.fixed_defaults.lineage_resolution_posture` must restate the released
     `V48-A` lineage posture exactly;
   - `seed.fixed_defaults.prompt_projection_posture` must restate the released
     `V48-A` prompt posture exactly;
   - `seed.fixed_defaults.unsupported_mapping_posture` must restate the released
     `V48-A` unsupported-mapping posture exactly;
   - bridge-contract fixed defaults may restate released `V48-A` postures only and
     may never override seed-derived anchor or projection content;
   - `seed.mutation_posture` remains starter-bounded to `read_only` only.
6. `V48`-compatibility strategy:
   - the emitted binding profile must be produced through released `V48-A` builder
     semantics, not a parallel local re-encoding;
   - the emitted binding profile must be admissible as the released
     `binding_profile_ref` carrier for `compile_v48b_taskpack_binding(...)`, with the
     remaining released compiler inputs supplied separately;
   - `policy_authority_clause_ref` may be resolved only through the released
     `build_v48a_taskpack_binding_profile(...)` lineage path and may never be
     synthesized or repaired locally;
   - `V49-D` does not ship a new compile wrapper and does not redefine released
     `V48-B` compile semantics.
7. Determinism strategy:
   - repeated bridge execution over the same released seed and same released bridge
     contract must produce byte-identical binding-profile output;
   - support-only notices or explanations may not affect emitted binding-profile
     identity.
8. Widening strategy:
   - no new `V48-A` semantics here;
   - no new `V48-B` compile wrapper here;
   - no worker runtime or conformance surface here;
   - no CLI / API / web consumer here.

## Bounded Bridge Inputs

The first `V49-D` release should stay bounded to:

- `seed`:
  - one released `adeu_taskpack_binding_spec_seed@1` only
- `bridge_contract`:
  - one repo-owned `adeu_semantic_seed_v48_bridge_contract@1` only
- `domain_kind`:
  - `repo_policy_work` only
- emitted output:
  - one released `anm_taskpack_binding_profile@1` only
- released downstream posture:
  - admissibility as the released `binding_profile_ref` carrier for
    `compile_v48b_taskpack_binding(...)` only

It should not attempt:

- raw `V45` or `V47` discovery outside declared bridge-contract refs;
- new binding semantics beyond released `V48-A`;
- a new compile wrapper beyond released `V48-B`;
- worker execution or harness runtime wiring;
- symbol audit integration;
- paper semantic contract integration;
- simulation integration;
- CLI, API, or web surfaces.

## Selected Schema Anchors

The first `V49-D` release should freeze the following bridge anchors.

1. Consumed `adeu_taskpack_binding_spec_seed@1`
   - `schema`
   - `seed_id`
   - `profile_id`
   - `source_normal_form_hash`
   - `transform_contract_id`
   - `transform_contract_hash`
   - `scope_anchor_ref`
   - `policy_anchor_ref`
   - `worker_subject_ref`
   - `mutation_posture`
   - `allow_paths`
   - `forbid_paths`
   - `forbid_effects`
   - `artifact_kinds`
   - `fixed_defaults`
   - `seed_hash`
2. Consumed `adeu_semantic_seed_v48_bridge_contract@1`
   - `schema`
   - `bridge_contract_id`
   - `profile_id`
   - `snapshot_id`
   - `snapshot_sha256`
   - `binding_profile_id`
   - `binding_subject_id`
   - `task_scope_summary`
   - `policy_source_ref`
   - `scope_source_ref`
   - `scope_binding_entry_ref`
   - `expected_scope_anchor_ref`
   - `expected_policy_anchor_ref`
   - `expected_worker_subject_ref`
   - `command_projection`
   - `evidence_slot_projection`
   - `prompt_projection_inputs`
   - `lineage_resolution_posture`
   - `prompt_projection_posture`
   - `unsupported_mapping_posture`
   - `semantic_hash`
3. Emitted `anm_taskpack_binding_profile@1`
   - exactly the released `V48-A` contract family only
   - no bridge-local top-level schema replacement is selected here

## Bridge Law

The first `V49-D` release should make bridge behavior explicit.

- bridge consumes one released seed and one bridge contract;
- bridge must validate:
  - profile id match;
  - snapshot id / sha match;
  - scope anchor match;
  - policy anchor match;
  - worker subject match;
  - exact restatement of released `V48-A` posture defaults only;
- bridge should accept only released seeds whose upstream lowering lineage was already
  admissible:
  - direct `V49-A` normal-form lineage only; or
  - `V49-B resolved_singleton` lineage only;
  - never `typed_alternatives`, `clarification_required`, or
    `rejected_unsupported`;
- bridge must fail closed if any required bridge-contract refs are missing, stale, or
  inconsistent with the seed;
- bridge must project:
  - `allow_paths -> allowlist_projection`
  - `forbid_paths` plus `forbid_effects -> forbidden_projection`
  - `bridge_contract.task_scope_summary -> task_scope_summary`
  - bridge-contract command and evidence projections unchanged into the released
    `V48-A` builder
  - bridge-contract prompt projection inputs unchanged into the released `V48-A`
    builder
- bridge may restate released `V48-A` postures only when the seed fixed defaults carry
  the exact released values;
- `artifact_kinds` must remain starter-bounded to
  `taskpack_binding_spec_seed` only in this slice;
- emitted binding-profile identity must be determined by the released `V48-A` binding
  profile payload only.

## Acceptance Criteria

- same released seed plus same released bridge contract must produce a byte-identical
  released binding profile on repeated bridge execution;
- bridge emits only released `anm_taskpack_binding_profile@1` through released
  `build_v48a_taskpack_binding_profile(...)` semantics;
- bridge fails closed on unresolved anchor mapping, snapshot mismatch, worker-subject
  mismatch, unsupported seed values, or fixed-default conflict;
- emitted binding profile revalidates under the released
  `AnmTaskpackBindingProfile` model and recomputed `semantic_hash` matches the
  emitted `semantic_hash`;
- emitted binding profile is admissible as the released `binding_profile_ref` carrier
  for `compile_v48b_taskpack_binding(...)`, with remaining released compiler inputs
  supplied separately;
- no new compile wrapper, worker runtime surface, or product consumer ships in the
  same slice.

## Required Deliverables

- `packages/adeu_semantic_forms/src/adeu_semantic_forms/bridge_v48.py`
- bounded `models.py` additions for `adeu_semantic_seed_v48_bridge_contract@1`
- deterministic reference fixtures proving:
  - successful bridge replay
  - seed-anchor mismatch rejection
  - snapshot mismatch rejection
  - fixed-default conflict rejection
  - byte-identical bridge replay
- targeted package tests for deterministic bridge behavior and reject posture

## Hard Constraints

- do not reopen released `V49-C` lowering semantics;
- do not recreate `V48-A` validation logic locally when the released builder already
  owns it;
- do not ship a new compile wrapper around released `V48-B`;
- do not widen into worker runtime, conformance, delegation, or product consumers;
- do not import prototype bridge code wholesale into live package paths.

## Local Gate

- run `make arc-start-check ARC=120`
