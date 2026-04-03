# Locked Continuation vNext+118

Status: `V49-B` implementation contract.

## V118 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v49b_semantic_forms_recovery_contract@1",
  "target_arc": "vNext+118",
  "target_path": "V49-B",
  "target_scope": "bounded_repo_owned_semantic_forms_recovery_for_repo_policy_work",
  "implementation_packages": [
    "adeu_semantic_forms"
  ],
  "governing_released_stack": "V45_repo_description_plus_V47_authoritative_normative_markdown_plus_V48_policy_to_taskpack_and_worker_enforcement_plus_V49A_semantic_forms_core_contracts_on_main",
  "governing_stack_consumption_mode": "anchor_and_downstream_consumer_context_only_not_reopened_description_semantics_not_reopened_normative_semantics_not_reopened_worker_enforcement_semantics_not_reopened_v49a_contract_semantics",
  "source_intake_bundle": "examples/external_prototypes/adeu-semantic-forms-v0-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "released_v49a_contracts_required": true,
  "semantic_forms_parser_py_required": true,
  "single_input_text_initially_required": true,
  "single_parse_profile_initially_required": true,
  "single_parse_result_output_initially_required": true,
  "starter_domain_singleton": "repo_policy_work",
  "released_relation_kind_vocabulary_required": [
    "bind_scope_anchor",
    "bind_policy_anchor",
    "use_worker_subject",
    "set_mutation_posture",
    "allow_path",
    "forbid_path",
    "forbid_effect",
    "produce_artifact_kind"
  ],
  "released_parse_result_outcome_vocabulary_required": [
    "resolved_singleton",
    "typed_alternatives",
    "clarification_required",
    "rejected_unsupported"
  ],
  "parse_result_schema_anchors_frozen": true,
  "recovery_candidate_schema_anchors_frozen": true,
  "clarification_and_unsupported_diagnostic_schema_anchors_frozen": true,
  "candidate_distinctness_by_semantic_hash_required": true,
  "deterministic_candidate_ordering_by_semantic_hash_required": true,
  "clarification_required_zero_candidate_posture_required": true,
  "partial_candidate_shells_not_selected_here": true,
  "alias_anchor_resolution_precedence_required": true,
  "explicit_anchor_or_exact_phrase_precedence_required": true,
  "equal_strength_anchor_conflict_may_not_silently_choose": true,
  "conflicting_relation_cues_fail_closed_to_clarification_or_unsupported": true,
  "recovery_must_emit_v49a_contracts_only": true,
  "recovery_alias_and_unsupported_pattern_sources_profile_bound_only": true,
  "v49a_identity_vs_projection_split_reused_in_recovery_outputs": true,
  "free_form_semantic_extension_not_selected_here": true,
  "multi_profile_or_multi_domain_resolution_not_selected_here": true,
  "adeu_to_adeu_lowering_not_selected_here": true,
  "v48_bridge_not_selected_here": true,
  "cli_api_web_consumers_not_selected_here": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS117.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_FORMS_V49B_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md"
}
```

## Slice

- Arc label: `vNext+118`
- Family label: `V49-B`
- Scope label: bounded repo-owned semantic forms recovery for `repo_policy_work`

## Objective

Release the bounded `V49-B` recovery lane by adding the first repo-owned
`NL -> ADEU` recovery surface over the already released `V49-A` contracts.

This slice must make explicit:

- one natural-language input text posture;
- one released `adeu_semantic_parse_profile@1` input posture;
- one emitted `adeu_semantic_parse_result@1` output posture;
- one bounded recovery doctrine over released aliases, released anchors, and released
  unsupported-pattern posture only;
- one explicit schema anchor set for:
  - parse result;
  - resolved candidate;
  - typed alternatives;
  - clarification diagnostics;
  - unsupported diagnostics;
- one typed distinction between:
  - `resolved_singleton`
  - `typed_alternatives`
  - `clarification_required`
  - `rejected_unsupported`
- one candidate distinctness and deterministic ordering law;
- one alias/anchor precedence and conflict posture;
- one explicit reuse of the released `V49-A` identity-versus-projection split.

This slice is recovery-first but still contract-bound. It does not authorize
deterministic `ADEU -> ADEU` lowering, `V48` bridge helpers, schema-family widening,
multi-domain recovery, multi-profile recovery, or any CLI / API / web consumer.

## Frozen Implementation Decisions

1. Package-ownership strategy:
   - `packages/adeu_semantic_forms` remains the sole implementation owner in this
     slice;
   - the imported intake pack remains shaping evidence only and may not be treated as
     the live parser surface.
2. Input/output cardinality strategy:
   - one input text only;
   - one released parse profile only;
   - one emitted parse result only;
   - no batching and no profile union in this slice.
3. Recovery-authority strategy:
   - recovery may consult only released `V49-A` anchors, aliases, vocabularies, and
     unsupported patterns from the admitted parse profile;
   - recovery may not invent new relation kinds, lane tags, object kinds, or domains.
4. Emitted-structure strategy:
   - recovery must emit only released `V49-A` contracts;
   - `adeu_semantic_parse_result@1` remains the only top-level emitted result
     contract;
   - resolved or alternative candidates must carry only released
     `adeu_semantic_normal_form@1` payloads plus support-only evidence summaries;
   - clarification and unsupported postures may emit diagnostics and notices only;
   - partial candidate shells are not selected in this slice.
5. Candidate distinctness and ordering strategy:
   - two candidates are the same candidate if and only if their released
     `normal_form.semantic_hash` values are identical;
   - dedupe must happen by canonical semantic hash before outcome classification;
   - candidate ordering must be deterministic and must sort deduped candidates by
     canonical semantic hash before assigning `candidate_rank`;
   - `resolved_singleton` means exactly one distinct canonical candidate survives
     after dedupe;
   - `typed_alternatives` means more than one distinct canonical candidate survives
     after dedupe while required anchor classes remain present.
6. Outcome-boundary strategy:
   - `clarification_required` means required anchors or relation cues remain missing,
     unresolved, or conflicting such that no single canonical candidate is licensed;
   - `clarification_required` must emit zero candidates only, plus typed ambiguity
     entries and notices;
   - `rejected_unsupported` means the input falls outside the released starter
     domain, released starter calculus, or explicit unsupported-pattern posture;
   - `rejected_unsupported` must emit zero candidates, zero ambiguities, one or more
     rejected reason codes, and notices only.
7. Alias/anchor resolution strategy:
   - exact released `anchor_id` or exact-phrase alias match outranks normalized alias
     match;
   - within the same alias kind, a longer exact match outranks a shorter one;
   - partial anchor cues may support diagnostics but may not license candidate
     selection by themselves;
   - equal-strength distinct anchor matches may not be silently chosen between;
   - conflicting relation cues or unresolved anchor conflicts must fail closed to
     `typed_alternatives`, `clarification_required`, or `rejected_unsupported`
     according to the frozen outcome law above.
8. Identity-versus-projection strategy:
   - emitted normal forms must preserve the released `V49-A` identity law and the
     released `V49-A` canonical hash subject;
   - `evidence_summary`, notices, ambiguity notes, and other recovery explanations are
     support-only and may not affect semantic identity or candidate distinctness.
9. Widening strategy:
   - no deterministic lowering here;
   - no `V48` bridge helper here;
   - no CLI / API / web consumer here;
   - no multi-domain or generalized natural-language semantics here.

## Bounded Recovery Inputs

The first `V49-B` release should stay bounded to:

- `input_text`:
  - one natural-language string only
- `parse_profile`:
  - one released `adeu_semantic_parse_profile@1` only
- `domain_kind`:
  - `repo_policy_work` only
- admitted contract family:
  - released `V49-A` contracts only
- emitted outcome vocabulary:
  - `resolved_singleton`
  - `typed_alternatives`
  - `clarification_required`
  - `rejected_unsupported`

It should not attempt:

- cross-domain recovery;
- boolean composition beyond the released `V49-A` starter calculus;
- deterministic lowering into `adeu_taskpack_binding_spec_seed@1`;
- `V48` binding / compile helpers;
- worker execution or harness runtime wiring;
- symbol audit integration;
- paper semantic contract integration;
- simulation integration;
- CLI, API, or web surfaces.

## Selected Schema Anchors

The first `V49-B` release should freeze the following recovery anchors.

1. `adeu_semantic_parse_result@1`
   - `schema`
   - `parse_result_id`
   - `profile_id`
   - `input_kind`
   - `input_text`
   - `input_text_hash`
   - `parse_status`
   - `candidates`
   - `ambiguities`
   - `rejected_reason_codes`
   - `notices`
2. Resolved or alternative candidate payload
   - `candidate_id`
   - `candidate_rank`
   - `normal_form`
   - `evidence_summary`
   - distinctness carried only by `normal_form.semantic_hash`
3. Typed ambiguity payload
   - `ambiguity_id`
   - `ambiguity_kind`
   - `alternatives`
   - `notes`
4. Clarification diagnostic posture
   - zero candidates only
   - one or more ambiguity entries
   - notices allowed
   - no partial candidate shells
   - no rejected reason codes
5. Unsupported diagnostic posture
   - zero candidates only
   - zero ambiguities
   - one or more rejected reason codes
   - notices allowed

## Candidate Distinctness And Ordering

The first `V49-B` release should make candidate identity and ordering explicit.

- candidate dedupe happens by released `normal_form.semantic_hash` only;
- support-only fields such as `evidence_summary`, notices, ambiguity notes, or other
  parser explanations may not create or distinguish candidates;
- after dedupe, remaining candidates must be sorted deterministically by canonical
  semantic hash before `candidate_rank` assignment;
- emitted `candidate_id` values may be derived from rank and semantic hash, but they
  may not override semantic-hash distinctness;
- `resolved_singleton` versus `typed_alternatives` must be decided only after the
  dedupe and ordering law above has been applied.

## Alias / Anchor Resolution Precedence

The first `V49-B` release should freeze a bounded recovery precedence law rather than
leave it to parser taste.

- exact released `anchor_id` text outranks alias matches;
- exact-phrase alias matches outrank normalized-phrase alias matches;
- longer exact matches within the same alias class outrank shorter exact matches;
- partial anchor cues do not count as resolved matches;
- if more than one equal-strength required-anchor match survives, recovery may not
  silently choose one;
- if multiple distinct canonical candidates survive after applying the precedence law,
  the result is `typed_alternatives`;
- if required anchor classes remain missing or unresolved after applying the
  precedence law, the result is `clarification_required`;
- explicit unsupported-pattern hits or explicit out-of-domain constructs remain
  `rejected_unsupported`, not clarification.

## Acceptance And Non-Shipping Gate

This slice is acceptable only if all of the following are true:

- parser output reuses only released `V49-A` contracts and does not redefine them;
- committed fixtures prove:
  - resolved singleton replay;
  - typed alternatives replay;
  - clarification required replay with zero candidates;
  - rejected unsupported replay;
  - candidate dedupe by semantic hash;
  - deterministic alternative ordering;
  - projection/support-only differences do not change semantic identity;
- targeted Python tests cover parser behavior and deterministic fixture replay;
- alias and anchor conflicts fail closed rather than silently choosing a winner.

This slice must not ship if any of the following occur:

- parser behavior becomes the first place where `V49-A` identity law is redefined;
- candidate distinctness depends on support-only recovery fields;
- candidate ordering depends on incidental iteration order;
- clarification emits candidate shells or partial unresolved candidates;
- unsupported inputs are coerced into apparent success;
- lowering, `V48` bridge helpers, or product consumers appear in the same slice.

## Required Deliverables

- `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py`
- bounded parser tests under:
  - `packages/adeu_semantic_forms/tests/`
- deterministic accepted / reject fixtures for:
  - resolved singleton
  - typed alternatives
  - clarification required
  - rejected unsupported
  - candidate dedupe by semantic hash
  - deterministic candidate ordering

## Hard Constraints

- no new schema family may be introduced in this slice;
- no released `V49-A` contract may be redefined in this slice;
- no direct import of the prototype parser tree into live package paths is allowed;
- no lowering helper or `V48` seed artifact may be emitted in this slice;
- no product-consumer route or UI surface may be introduced in this slice.

## PR Shape

- one bounded PR touching:
  - `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py`
  - targeted package tests / fixtures
  - package exports if needed
- no unrelated workflow, governance, or product-surface edits in the same slice
