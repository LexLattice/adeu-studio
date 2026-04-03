# Locked Continuation vNext+117

Status: `V49-A` implementation contract.

## V117 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v49a_semantic_forms_core_contract@1",
  "target_arc": "vNext+117",
  "target_path": "V49-A",
  "target_scope": "bounded_repo_owned_semantic_forms_core_contracts_for_repo_policy_work",
  "implementation_packages": [
    "adeu_semantic_forms"
  ],
  "governing_released_stack": "V45_repo_description_plus_V47_authoritative_normative_markdown_plus_V48_policy_to_taskpack_and_worker_enforcement_on_main",
  "governing_stack_consumption_mode": "anchor_and_downstream_consumer_context_only_not_reopened_description_semantics_not_reopened_normative_semantics_not_reopened_worker_enforcement_semantics",
  "source_intake_bundle": "examples/external_prototypes/adeu-semantic-forms-v0-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "semantic_forms_package_scaffold_required": true,
  "selected_schema_ids": [
    "adeu_semantic_parse_profile@1",
    "adeu_semantic_statement_core@1",
    "adeu_semantic_normal_form@1",
    "adeu_semantic_parse_result@1",
    "adeu_semantic_transform_contract@1"
  ],
  "starter_domain_singleton": "repo_policy_work",
  "starter_statement_core_fields": [
    "relation_kind",
    "object_value",
    "lane_tag",
    "object_kind",
    "evidence"
  ],
  "starter_relation_kind_vocabulary_frozen": [
    "bind_scope_anchor",
    "bind_policy_anchor",
    "use_worker_subject",
    "set_mutation_posture",
    "allow_path",
    "forbid_path",
    "forbid_effect",
    "produce_artifact_kind"
  ],
  "starter_lane_tag_vocabulary_frozen": [
    "scope",
    "policy",
    "worker",
    "mutation",
    "constraint",
    "deliverable"
  ],
  "starter_object_kind_vocabulary_frozen": [
    "scope_anchor",
    "policy_anchor",
    "worker_subject",
    "mutation_posture",
    "repo_rel_path",
    "effect_tag",
    "artifact_kind"
  ],
  "starter_qualifier_posture": "support_only_evidence_list_no_nested_qualifier_objects",
  "canonical_semantic_identity_law_required": true,
  "canonical_hash_subject_required": true,
  "identity_fields_vs_projection_fields_split_required": true,
  "semantic_equivalence_posture_required": true,
  "ambiguity_posture_required": true,
  "unsupported_posture_required": true,
  "normal_form_identity_fields": [
    "relation_kind",
    "object_value"
  ],
  "normal_form_projection_or_support_only_fields": [
    "evidence",
    "confidence_band",
    "uncertainty_notes"
  ],
  "parse_result_outcome_vocabulary_frozen": [
    "resolved_singleton",
    "typed_alternatives",
    "clarification_required",
    "rejected_unsupported"
  ],
  "models_py_required": true,
  "parse_profile_py_required": true,
  "normalized_support_fixtures_required": true,
  "parser_behavior_not_selected_here": true,
  "nl_to_adeu_recovery_not_selected_here": true,
  "adeu_to_adeu_lowering_not_selected_here": true,
  "v48_bridge_not_selected_here": true,
  "cli_api_web_consumers_not_selected_here": true,
  "authoritative_and_mirrored_schema_export_parity_required_if_schema_files_committed": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v31.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md"
}
```

## Slice

- Arc label: `vNext+117`
- Family label: `V49-A`
- Scope label: bounded repo-owned semantic forms core contracts for `repo_policy_work`

## Objective

Release the bounded `V49-A` substrate-contract lane by creating the first repo-owned
`adeu_semantic_forms` package and freezing one canonical starter semantic contract set
rich enough to make later recovery and lowering possible without yet selecting either
of those later lanes.

This slice must make explicit:

- one starter ADEU statement / calculus shape;
- one operator / relation posture;
- one semantic-kind / lane-tag posture;
- one canonical semantic identity law and canonical hash subject;
- one explicit split between identity-participating fields and projection-only /
  support-only fields;
- one semantic equivalence posture;
- one ambiguity posture and one unsupported posture;
- one contract-only parse-result outcome vocabulary over the starter domain
  `repo_policy_work`.

This slice is contract-first and substrate-first. It does not authorize parser
behavior, `NL -> ADEU` recovery, `ADEU -> ADEU` lowering, `V48` bridge helpers, symbol
audit integration, paper semantic contract integration, simulation integration, or any
CLI / API / web consumer.

## Frozen Implementation Decisions

1. Package-ownership strategy:
   - `packages/adeu_semantic_forms` is the sole implementation owner in this slice;
   - the imported intake pack remains shaping evidence only and may not be treated as
     the live package surface.
2. Starter-domain strategy:
   - the first released domain is exactly `repo_policy_work`;
   - no broader semantic metalanguage is selected in this slice.
3. Schema-family strategy:
   - the first released schema family is selected now as:
     - `adeu_semantic_parse_profile@1`
     - `adeu_semantic_statement_core@1`
     - `adeu_semantic_normal_form@1`
     - `adeu_semantic_parse_result@1`
     - `adeu_semantic_transform_contract@1`
   - these are the actual lock-selected schema IDs for `V49-A`, not merely planning
     placeholders.
4. Starter-calculus strategy:
   - one starter semantic statement core is frozen to the fields:
     - `relation_kind`
     - `object_value`
     - `lane_tag`
     - `object_kind`
     - `evidence`
   - `relation_kind`, `lane_tag`, and `object_kind` remain bounded to one starter
     vocabulary only;
   - `evidence` is support-only and may not widen into nested qualifier objects,
     boolean composition, or authority-bearing semantics.
5. Identity-and-hash strategy:
   - canonical semantic identity for the starter statement calculus is carried only by:
     - `relation_kind`
     - `object_value`
   - `lane_tag` and `object_kind` must validate against `relation_kind` and remain
     redundant/derived for identity purposes in the starter slice;
   - `evidence`, `confidence_band`, and `uncertainty_notes` are projection-only or
     support-only and must not affect semantic identity;
   - canonical hash computation must be deterministic and based only on the selected
     hash subject for each released artifact.
6. Equivalence-and-outcome strategy:
   - semantic equivalence in the starter slice means the canonicalized set of starter
     statement cores is identical after sorting/dedup and after removing
     projection-only / support-only differences;
   - `typed_alternatives` means more than one distinct canonical semantic object is
     admitted by the contract while required anchor classes are still present;
   - `clarification_required` means required anchor classes are missing or unresolved
     such that no single canonical semantic object is licensed;
   - `rejected_unsupported` means the requested construct falls outside the starter
     calculus, starter domain, or frozen unsupported posture;
   - these doctrines are frozen at the contract level in `V49-A` and may not be
     deferred to parser behavior.

## Bounded Starter Vocabularies

The first `V49-A` release should freeze bounded starter vocabularies rather than leave
the semantic substrate open-ended.

The intended bounded starter vocabularies are:

- `semantic_domain_kind`:
  - `repo_policy_work`
- `relation_kind`:
  - `bind_scope_anchor`
  - `bind_policy_anchor`
  - `use_worker_subject`
  - `set_mutation_posture`
  - `allow_path`
  - `forbid_path`
  - `forbid_effect`
  - `produce_artifact_kind`
- `lane_tag`:
  - `scope`
  - `policy`
  - `worker`
  - `mutation`
  - `constraint`
  - `deliverable`
- `object_kind`:
  - `scope_anchor`
  - `policy_anchor`
  - `worker_subject`
  - `mutation_posture`
  - `repo_rel_path`
  - `effect_tag`
  - `artifact_kind`
- `parse_status`:
  - `resolved_singleton`
  - `typed_alternatives`
  - `clarification_required`
  - `rejected_unsupported`
- `ambiguity_kind`:
  - `multiple_scope_anchor_matches`
  - `multiple_policy_anchor_matches`
  - `missing_required_anchor`
- `confidence_band`:
  - `high`
  - `medium`
  - `low`
- starter qualifier posture:
  - `support_only_evidence_list_no_nested_qualifier_objects`

Out-of-scope constructs in this slice are:

- boolean conjunction / disjunction algebra beyond the frozen statement set;
- if/then or conditional semantics;
- quantifiers, counts, or cardinality operators;
- free-form operator extension;
- multi-domain or cross-domain semantic kinds;
- nested qualifier objects that change semantic identity.

## Selected Schema Anchors

The first `V49-A` release should freeze the following contract anchors.

1. `adeu_semantic_parse_profile@1`
   - `profile_id`
   - `domain_kind`
   - `snapshot_id`
   - `snapshot_sha256`
   - released scope / policy / worker anchors
   - starter lexicons
   - `unsupported_patterns`
   - `semantic_hash`
2. `adeu_semantic_statement_core@1`
   - `relation_kind`
   - `object_value`
   - `lane_tag`
   - `object_kind`
   - `evidence`
3. `adeu_semantic_normal_form@1`
   - `profile_id`
   - `domain_kind`
   - canonical statement-core payload
   - explicit identity-field list
   - explicit projection-field list
   - `semantic_hash`
4. `adeu_semantic_parse_result@1`
   - `profile_id`
   - `input_kind`
   - `input_text`
   - `input_text_hash`
   - `parse_status`
   - resolved form or typed alternatives
   - ambiguities
   - diagnostics / notices
5. `adeu_semantic_transform_contract@1`
   - `source_schema`
   - `target_schema`
   - `profile_id`
   - required singleton relations
   - supported multi relations
   - deterministic posture defaults
   - `semantic_hash`

## Required Deliverables

1. Repo-owned package scaffold:
   - `packages/adeu_semantic_forms/pyproject.toml`
   - `packages/adeu_semantic_forms/src/adeu_semantic_forms/__init__.py`
   - `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`
   - `packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py`
   - `packages/adeu_semantic_forms/tests/`
2. New typed contract surfaces sufficient to carry:
   - `adeu_semantic_parse_profile@1`
   - `adeu_semantic_statement_core@1`
   - `adeu_semantic_normal_form@1`
   - `adeu_semantic_parse_result@1`
   - `adeu_semantic_transform_contract@1`
   - starter ADEU statement / calculus
   - operator / relation posture
   - semantic-kind / lane-tag posture
   - canonical semantic identity and canonical hash subject
   - identity-field versus projection-field split
   - semantic equivalence, ambiguity, and unsupported posture
3. Committed normalized support fixtures derived from the intake bundle only as
   support evidence:
   - one parse-profile fixture
   - one semantic-normal-form fixture
   - one resolved-singleton parse-result fixture
   - one typed-alternatives parse-result fixture
   - one rejected-unsupported parse-result fixture
   - one transform-contract fixture
   - one reject fixture or mutation spec proving that projection/support-only field
     changes do not change semantic hash
   - one reject fixture or mutation spec proving that identity-field changes do change
     semantic hash
   - one reject fixture proving invalid outcome vocabulary fails closed
4. Repo-native validation coverage for:
   - model validation
   - canonical hash stability
   - contract-only outcome vocabulary validation
   - fixture replay / round-trip validation
   - identity-field versus projection-field hash behavior

## Hard Constraints

- No direct import of the external intake bundle into live repo package paths may
  substitute for repo-owned code.
- No parser behavior, heuristic recovery, or prompt-like interpretation is authorized
  in this slice.
- No lowering into `V48` seed artifacts is authorized in this slice.
- No broad multi-domain semantic language is authorized in this slice.
- No arbitrary boolean composition is authorized in this slice.
- No product surface, route, CLI, or API may be shipped from this slice.
- The starter domain must remain `repo_policy_work`.
- The first released schema family must remain exactly:
  - `adeu_semantic_parse_profile@1`
  - `adeu_semantic_statement_core@1`
  - `adeu_semantic_normal_form@1`
  - `adeu_semantic_parse_result@1`
  - `adeu_semantic_transform_contract@1`
- The starter parse-result outcome vocabulary must remain exactly:
  - `resolved_singleton`
  - `typed_alternatives`
  - `clarification_required`
  - `rejected_unsupported`
- Canonical semantic identity must be computed only from identity-participating fields;
  projection-only or support-only fields must not affect semantic identity.
- The starter normal-form semantic hash must be computed from one canonical basis only:
  - `schema`
  - `profile_id`
  - `domain_kind`
  - the canonicalized statement-core list using only:
    - `relation_kind`
    - `object_value`
- The starter normal-form semantic hash must explicitly exclude:
  - `normal_form_id`
  - `semantic_hash`
  - `evidence`
  - `confidence_band`
  - `uncertainty_notes`
- The starter statement calculus must remain one-relation / one-object only per core
  row and must not widen into nested qualifier objects, free-form operator extension,
  or boolean composition.
- The repo must continue to treat imported bundle notes and source trees as support
  evidence rather than as precedent-bearing authority.

## Acceptance-Fixture Set

The first `V49-A` release should prove the substrate law through committed fixtures even
before any recovery engine exists.

The minimum fixture set is:

- one accepted parse-profile fixture
- one accepted semantic-normal-form fixture
- one accepted parse-result fixture with `parse_status = resolved_singleton`
- one accepted parse-result fixture with `parse_status = typed_alternatives`
- one accepted parse-result fixture with `parse_status = rejected_unsupported`
- one accepted transform-contract fixture
- one reject or mutation fixture proving projection/support-only field changes do not
  change semantic hash
- one reject or mutation fixture proving identity-field changes do change semantic hash
- one reject fixture proving invalid parse-result outcome vocabulary fails closed

## Local Gate

- run `make arc-start-check ARC=117`

## PR Shape

- Single integrated PR.

Rationale:

- the package scaffold, contract models, normalized fixtures, and targeted tests are
  tightly coupled and would drift if reviewed as multiple temporary PRs before the
  substrate contract is frozen.
