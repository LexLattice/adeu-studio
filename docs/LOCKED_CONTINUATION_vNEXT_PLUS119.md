# Locked Continuation vNext+119

Status: `V49-C` implementation contract.

## V119 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v49c_semantic_forms_lowering_contract@1",
  "target_arc": "vNext+119",
  "target_path": "V49-C",
  "target_scope": "bounded_repo_owned_semantic_forms_deterministic_lowering_for_repo_policy_work",
  "implementation_packages": [
    "adeu_semantic_forms"
  ],
  "governing_released_stack": "V45_repo_description_plus_V47_authoritative_normative_markdown_plus_V48_policy_to_taskpack_and_worker_enforcement_plus_V49A_semantic_forms_core_contracts_plus_V49B_semantic_forms_recovery_on_main",
  "governing_stack_consumption_mode": "anchor_and_downstream_consumer_context_only_not_reopened_description_semantics_not_reopened_normative_semantics_not_reopened_worker_enforcement_semantics_not_reopened_v49a_contract_semantics_not_reopened_v49b_recovery_semantics",
  "source_intake_bundle": "examples/external_prototypes/adeu-semantic-forms-v0-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "released_v49a_contracts_required": true,
  "released_v49b_recovery_outputs_required": true,
  "lowering_admits_only_direct_v49a_normal_forms_or_v49b_resolved_singleton_outputs": true,
  "typed_alternatives_clarification_and_rejected_outputs_not_admissible_for_lowering": true,
  "semantic_forms_transform_v48_seed_py_required": true,
  "single_normal_form_input_initially_required": true,
  "single_transform_contract_initially_required": true,
  "single_seed_output_initially_required": true,
  "starter_domain_singleton": "repo_policy_work",
  "released_transform_target_schema_singleton": "adeu_taskpack_binding_spec_seed@1",
  "consumed_normal_form_schema_anchors_frozen": true,
  "required_singleton_relation_projection_required": true,
  "supported_multi_relation_projection_required": true,
  "produce_artifact_kind_singleton_projection_required": true,
  "missing_required_relation_fails_closed": true,
  "singleton_multiplicity_conflict_fails_closed": true,
  "unsupported_relation_kind_fails_closed": true,
  "fixed_default_conflict_fails_closed": true,
  "deterministic_multi_relation_ordering_required": true,
  "seed_schema_anchors_frozen": true,
  "transform_contract_schema_anchors_consumed_without_redefinition": true,
  "lowering_output_must_remain_pre_v48_binding_profile_seed_only": true,
  "seed_not_admissible_as_v48a_binding_profile_without_v49d_bridge": true,
  "v48_binding_or_compile_helper_not_selected_here": true,
  "cli_api_web_consumers_not_selected_here": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS117.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS118.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49C_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md"
}
```

## Slice

- Arc label: `vNext+119`
- Family label: `V49-C`
- Scope label: bounded repo-owned semantic forms deterministic lowering for
  `repo_policy_work`

## Objective

Release the bounded `V49-C` lowering lane by adding the first repo-owned deterministic
`ADEU -> ADEU` lowering surface from one released semantic normal form plus one
released transform contract into one narrow downstream seed artifact.

This slice must make explicit:

- one released `adeu_semantic_normal_form@1` input posture;
- one released `adeu_semantic_transform_contract@1` input posture;
- one emitted `adeu_taskpack_binding_spec_seed@1` output posture;
- one deterministic projection law from required singleton relations and supported
  multi relations into the emitted seed;
- one fail-closed posture for:
  - missing required relations;
  - singleton multiplicity conflicts;
  - unsupported relation kinds;
  - transform-contract / domain mismatch;
- one explicit distinction between:
  - released `V49` lowering;
  - later `V48` bridge helpers that are not selected in this slice.

This slice is lowering-first and still bounded. It does not authorize `V48-A`
binding-profile emission, `V48-B` compiled boundary emission, worker runtime behavior,
symbol audit integration, paper semantic contract integration, simulation integration,
or any CLI / API / web consumer.

## Frozen Implementation Decisions

1. Package-ownership strategy:
   - `packages/adeu_semantic_forms` remains the sole implementation owner in this
     slice;
   - the imported intake pack remains shaping evidence only and may not be treated as
     the live lowering surface.
2. Input/output cardinality strategy:
   - one released semantic normal form only;
   - one released transform contract only;
   - one emitted seed artifact only;
   - no batching and no multi-target lowering in this slice.
3. Lowering-authority strategy:
   - lowering may consume only released `V49-A` normal-form contracts and released
     `V49-A` transform-contract contracts;
   - lowering may accept upstream normal forms only when they are either:
     - directly authored or fixture-authored under released `V49-A`; or
     - emitted from a released `V49-B` parse result whose `parse_status` is exactly
       `resolved_singleton`;
   - lowering may not silently choose one alternative out of
     `typed_alternatives`, may not lower `clarification_required`, and may not lower
     `rejected_unsupported`;
   - lowering may not invent new relation kinds, new downstream target schemas, or new
     domain semantics.
4. Transform-contract strategy:
   - `required_singleton_relations` must each resolve to exactly one statement core;
   - `supported_multi_relations` may resolve to zero or more statement cores;
   - `required_singleton_relations` and `supported_multi_relations` remain disjoint;
   - `fixed_defaults` may inject only contract-declared fixed values and may not be
     treated as parser or bridge heuristics;
   - if a contract-declared fixed default conflicts with a relation-derived emitted
     value, lowering must fail closed rather than silently prefer one side.
5. Seed-output strategy:
   - the only emitted top-level contract is `adeu_taskpack_binding_spec_seed@1`;
   - the emitted seed remains pre-bridge and pre-runtime;
   - the emitted seed must name the released profile lineage, source normal-form
     lineage, and transform-contract lineage explicitly;
   - the emitted seed may project only the released starter relation families into
     bounded seed fields;
   - the emitted seed is a pre-bridge semantic seed only and is not admissible as a
     released `V48-A` binding profile without the later `V49-D` bridge.
6. Determinism strategy:
   - repeated lowering of the same released normal form and released transform contract
     must produce byte-identical seed output;
   - multi-relation outputs must be sorted deterministically by canonical value before
     emission;
   - support-only notices or explanations may not affect seed identity.
7. Fail-closed strategy:
   - missing required singleton relations must fail closed;
   - duplicate singleton relations must fail closed;
   - unsupported relation kinds must fail closed;
   - transform-contract domain or source/target mismatch must fail closed.
8. Widening strategy:
   - no `V48-A` binding-profile helper here;
   - no `V48-B` compile helper here;
   - no worker runtime or conformance surface here;
   - no CLI / API / web consumer here.

## Bounded Lowering Inputs

The first `V49-C` release should stay bounded to:

- `normal_form`:
  - one released `adeu_semantic_normal_form@1` only
  - admitted only when directly authored under released `V49-A` or emitted from a
    released `V49-B` parse result with `parse_status = resolved_singleton`
- `transform_contract`:
  - one released `adeu_semantic_transform_contract@1` only
- `domain_kind`:
  - `repo_policy_work` only
- `target_schema`:
  - `adeu_taskpack_binding_spec_seed@1` only
- admitted relation families:
  - released `V49-A` starter relation vocabulary only
- emitted output:
  - one seed contract only

It should not attempt:

- multi-target lowering;
- generalized semantic transforms beyond the released starter calculus;
- natural-language recovery heuristics;
- direct emission of `V48-A` binding profiles or `V48-B` compiled boundaries;
- worker execution or harness runtime wiring;
- symbol audit integration;
- paper semantic contract integration;
- simulation integration;
- CLI, API, or web surfaces.

## Selected Schema Anchors

The first `V49-C` release should freeze the following lowering anchors.

1. Consumed `adeu_semantic_normal_form@1`
   - `schema`
   - `profile_id`
   - `domain_kind`
   - `statement_cores`
   - per statement core:
     - `relation_kind`
     - `object_value`
     - `lane_tag`
     - `object_kind`
   - `semantic_hash`
2. Consumed `adeu_semantic_transform_contract@1`
   - `schema`
   - `contract_id`
   - `source_schema`
   - `target_schema`
   - `profile_id`
   - `required_singleton_relations`
   - `supported_multi_relations`
   - `fixed_defaults`
   - `unsupported_relation_kinds`
   - `semantic_hash`
3. Emitted `adeu_taskpack_binding_spec_seed@1`
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
   - `artifact_kinds` must contain exactly one canonical value in the starter slice
4. Required singleton projection posture
   - `bind_scope_anchor -> scope_anchor_ref`
   - `bind_policy_anchor -> policy_anchor_ref`
   - `use_worker_subject -> worker_subject_ref`
   - `set_mutation_posture -> mutation_posture`
   - `produce_artifact_kind -> artifact_kinds` as one required emitted artifact family
     represented as a single-item deterministic set in the starter slice
5. Supported multi projection posture
   - `allow_path -> allow_paths`
   - `forbid_path -> forbid_paths`
   - `forbid_effect -> forbid_effects`

## Lowering Law

The first `V49-C` release should make deterministic lowering explicit.

- lowering consumes one released normal form and indexes statement cores by
  `relation_kind`;
- if the lowering input came from released `V49-B` recovery, that upstream recovery
  result must already have been `resolved_singleton`; no lowering may select one
  candidate out of `typed_alternatives`;
- each `required_singleton_relation` must resolve to exactly one statement core;
- each `supported_multi_relation` may resolve to zero or more statement cores;
- emitted path/effect/artifact collections must be deduped and sorted
  deterministically by canonical `object_value`;
- `produce_artifact_kind` remains singleton in the starter slice and must emit exactly
  one canonical artifact family as a single-item deterministic set;
- any fixed-default conflict with a relation-derived emitted value must fail closed;
- `seed_id` may be derived from profile id plus source normal-form hash plus
  transform-contract hash, but it may not override the deterministic seed payload;
- `seed_hash` must be computed from the emitted seed payload excluding `seed_hash`
  itself.

## Acceptance Criteria

- same released normal form plus same released transform contract must produce a
  byte-identical seed on repeated lowering;
- lowering is admissible only from a directly authored released `V49-A` normal form or
  from a released `V49-B` `resolved_singleton` output;
- no lowering may proceed from `typed_alternatives`, `clarification_required`, or
  `rejected_unsupported` recovery outputs;
- singleton relation multiplicity ambiguity must fail closed;
- the emitted seed must remain non-equivalent to a released `V48-A` binding profile
  unless and until `V49-D` ships the later bridge.

## Required Deliverables

- `packages/adeu_semantic_forms/src/adeu_semantic_forms/transform_v48_seed.py`
- bounded package export updates if required
- deterministic reference fixtures proving:
  - successful lowering
  - missing-required-relation rejection
  - singleton-conflict rejection
  - unsupported-relation rejection or mismatch rejection
- targeted package tests for deterministic lowering and reject posture

## Hard Constraints

- do not redefine released `V49-A` model semantics;
- do not redefine released `V49-B` recovery semantics;
- do not emit `V48-A` binding profiles in this slice;
- do not emit `V48-B` compiled boundaries in this slice;
- do not import the GPT Pro prototype tree wholesale into live package paths;
- do not add CLI, API, or web surfaces in this slice.

## Acceptance Fixture Set

The first `V49-C` release should carry at least:

- one accepted lowering replay fixture;
- one reject fixture for missing required singleton relation;
- one reject fixture for duplicate singleton relation;
- one reject fixture for unsupported transform mismatch;
- one deterministic replay assertion proving repeated lowering is byte-identical.

## PR Shape

- Keep the diff bounded to `packages/adeu_semantic_forms`, bounded tests/fixtures, and
  any required schema/export wiring for the new seed contract.
- Do not widen into symbol audit, paper semantics, simulation, or released `V48`
  helper code in the same slice.
