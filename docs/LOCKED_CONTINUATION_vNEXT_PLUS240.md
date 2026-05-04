# LOCKED_CONTINUATION_vNEXT_PLUS240

## Status

Bounded starter lock draft for `V85-B` (canonical meta lookup index, semantic
operator/class registry, obligation-family registry, and semantic pointer
lookup fixtures).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`V85-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `V85`
- slice: `V85-B`
- branch-local execution target: `arc/v85-r2`

## Purpose

Freeze the bounded `V85-B` starter slice so the repo can translate released
`V85-A` turn semantic declaration request, source-index, and non-authority
guardrail rows into review-only canonical lookup and registry substrate.

`vNext+240` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_repo_description` package. It does not authorize
`V85-C`, declaration review summaries, post-declaration handoffs, obligation
expansion, evidence contracts, edge probe plans, reviewer taskpacks, audit
reports, deterministic transition tables, implementation locks, work-packet
activation, code edits, command execution, tool invocation, target mutation,
runtime transition, Morphic UX runtime changes, direct OAI runtime behavior,
meta-orchestrator runtime transition, product authorization, graph-memory
authority, recursive policy amendment, or selection of `V86`.

Controlling invariant:

```text
V85-B may prove canonical pointer lookup and registry behavior for review, but
lookup success is not natural-language truth, registry presence is not runtime
behavior, and obligation-family lookup is not obligation expansion.
```

The active `V85-B` implementation may add schema, model, validator, fixture,
and test files for the four selected surfaces. It must not record that a
semantic declaration is authoritative, that obligations have been expanded,
that evidence has been accepted, that audit has run, or that a later family
has been selected.

## Instantiated Here

- `V85-B` instantiates one bounded canonical declaration lookup seam:
  - existing repo-owned package only:
    - `adeu_repo_description`
  - consumed released basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS239.md`
    - `docs/ASSESSMENT_vNEXT_PLUS239_EDGES.md`
    - `artifacts/agent_harness/v239/evidence_inputs/v85a_semantic_declaration_review_closeout_evidence_v239.json`
    - `artifacts/agent_harness/v239/evidence_inputs/metric_key_continuity_assertion_v239.json`
    - `artifacts/agent_harness/v239/evidence_inputs/runtime_observability_comparison_v239.json`
    - `apps/api/fixtures/repo_description/vnext_plus239/repo_turn_semantic_declaration_request_v239_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus239/repo_semantic_declaration_source_index_v239_reference.json`
    - `apps/api/fixtures/repo_description/vnext_plus239/repo_semantic_declaration_non_authority_guardrail_v239_reference.json`
  - consumed support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v75.md`
    - `docs/ARCHITECTURE_ADEU_SEMANTIC_DECLARATION_META_LOOP_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
  - consumed starter record shapes:
    - `repo_turn_semantic_declaration_request@1`
    - `repo_semantic_declaration_source_index@1`
    - `repo_semantic_declaration_non_authority_guardrail@1`
  - emitted second-slice record shapes:
    - `repo_canonical_meta_lookup_index@1`
    - `repo_semantic_operator_class_registry@1`
    - `repo_obligation_family_registry@1`
    - `repo_semantic_pointer_lookup_fixture@1`

## Required Starter Vocabulary

Minimum `repo_canonical_meta_lookup_index@1` fields:

- `lookup_ref`
- `semantic_declaration_session_ref`
- `candidate_ref`
- `declaration_request_refs`
- `source_refs`
- `semantic_pointer`
- `semantic_pointer_rows`
- `operator_registry_refs`
- `class_registry_refs`
- `obligation_family_refs`
- `lookup_input_kind`
- `lookup_posture`
- `canonical_lookup_status`
- `pointer_competency_kind`
- `competency_claim_horizon`
- `order_preservation_posture`
- `duplicate_preservation_posture`
- `unknown_pointer_posture`
- `conflict_posture`
- `obligation_expansion_posture`
- `non_authority_guardrail_refs`
- `limitation_note`

Minimum semantic pointer row fields:

- `pointer_ref`
- `semantic_declaration_session_ref`
- `raw_pointer`
- `parsed_operator`
- `parsed_class`
- `parsed_version`
- `pointer_parse_posture`
- `normalization_posture`
- `source_refs`
- `limitation_note`

Minimum pointer parse posture values include:

- `parsed_exact`
- `parsed_with_alias`
- `malformed_pointer`
- `unknown_operator`
- `unknown_class`
- `unknown_version`
- `ambiguous_parse`
- `abstain_required`

Minimum pointer competency kinds include:

- `opaque_pointer_obedience`
- `explicit_pointer_lookup`
- `natural_binding_candidate_lookup`
- `registry_gap_detection`
- `conflict_detection`
- `distractor_resistance`

Minimum competency claim horizons include:

- `pointer_obedience_only`
- `exact_lookup_only`
- `natural_binding_not_claimed`
- `obligation_expansion_not_claimed`
- `implementation_not_claimed`

Minimum `repo_semantic_operator_class_registry@1` fields:

- `registry_ref`
- `semantic_declaration_session_ref`
- `source_refs`
- `registry_entry_kind`
- `registry_domain`
- `canonical_id`
- `alias_rows`
- `entry_status`
- `entry_currentness`
- `entry_scope_posture`
- `operator_semantics_posture`
- `class_semantics_posture`
- `non_invention_guardrail`
- `limitation_note`

`registry_domain` must distinguish at least:

- `operator`
- `object_class`
- `source_class`
- `target_class`
- `modifier`
- `relation_class`
- `obligation_family`

Operator entries such as `GATE`, `ROUTE`, `TRANSITION`, `REVIEW`,
`RECONCILE`, and `CLOSEOUT` are declaration operators only. They must not mint
runtime behavior, local authority, worker dispatch, audit authority, or
transition authority inside `V85-B`.

Minimum `repo_obligation_family_registry@1` fields:

- `obligation_family_ref`
- `semantic_declaration_session_ref`
- `source_refs`
- `obligation_family_id`
- `obligation_family_label`
- `applies_to_operator_refs`
- `applies_to_class_refs`
- `obligation_family_relation_kind`
- `obligation_family_activation_posture`
- `required_future_surfaces`
- `future_expansion_posture`
- `evidence_contract_required_posture`
- `waiver_posture`
- `non_execution_guardrail`
- `limitation_note`

Minimum obligation-family relation kinds include:

- `applies_by_operator`
- `applies_by_object_class`
- `applies_by_target_context`
- `applies_by_modifier`
- `applies_by_negative_cue`
- `applies_by_authority_boundary`
- `conflict_or_exclusion`
- `requires_later_disambiguation`

Minimum obligation-family activation postures include:

- `lookup_result_only`
- `named_for_later_expansion_only`
- `expansion_requires_v86_or_later`
- `expansion_blocked_by_ambiguity`
- `expansion_blocked_by_registry_gap`
- `expansion_not_authorized_by_v85`

Minimum `repo_semantic_pointer_lookup_fixture@1` fields:

- `lookup_fixture_ref`
- `semantic_declaration_session_ref`
- `source_refs`
- `fixture_kind`
- `pointer_competency_kind`
- `competency_claim_horizon`
- `input_pointer_rows`
- `expected_lookup_rows`
- `expected_order_posture`
- `expected_duplicate_posture`
- `expected_unknown_posture`
- `expected_conflict_posture`
- `actual_result_refs`
- `fixture_posture`
- `non_authority_guardrail_refs`
- `limitation_note`

The first fixture set should include both:

- an opaque pointer sequence such as `M-42 -> A1 -> A9 -> C4 -> Z2`;
- an explicit semantic pointer such as `CREATE ui.menu@v1`.

Opaque success proves pointer obedience only. It does not prove natural
semantic binding correctness, obligation expansion, implementation readiness,
runtime behavior, or product truth.

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `repo_canonical_meta_lookup_index@1`
  - `repo_semantic_operator_class_registry@1`
  - `repo_obligation_family_registry@1`
  - `repo_semantic_pointer_lookup_fixture@1`
- deterministic reference and reject fixtures for the bounded `V85-B` starter
  family only;
- validators that prove:
  - every `V85-B` row references released `V85-A` request, source, and
    guardrail rows;
  - `semantic_declaration_session_ref` and `candidate_ref` stay coherent
    across lookup, registry, obligation-family, and fixture rows;
  - unknown pointers abstain or route to registry gap rather than being
    repaired into nearest classes;
  - duplicate refs and input order are preserved unless an explicit
    normalization rule exists;
  - aliases require alias rows and unknown versions cannot become latest
    versions by default;
  - `GATE` and other authority-adjacent operators remain declaration
    semantics, not authority minting;
  - obligation families are named for later expansion only and are not
    expanded into concrete obligations;
  - opaque pointer fixtures cannot prove natural semantic binding correctness;
  - no `V85-C`, obligation expansion, evidence contract, audit taskpack,
    deterministic transition table, implementation, runtime, product, graph,
    recursive-policy, or `V86` rows ship in this slice.

## Deferred To Later Family Or Later Slice

- `V85-C`:
  - declaration review summaries;
  - post-semantic-declaration-review handoffs;
  - family closeout alignment.
- `V86` or later:
  - obligation expansion;
  - evidence contracts;
  - edge probe plans;
  - reviewer / auditor taskpacks;
  - deterministic transition tables;
  - remand routing.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS240.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+240",
  "target_path": "V85-B",
  "slice": "V85-B",
  "family": "V85",
  "branch_local_execution_target": "arc/v85-r2",
  "target_scope": "one_bounded_canonical_lookup_and_registry_review_slice",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS239.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS239_EDGES.md"
  ],
  "planning_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v75.md",
    "docs/ARCHITECTURE_ADEU_SEMANTIC_DECLARATION_META_LOOP_FAMILY_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85B_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "consumed_record_shapes": [
    "repo_turn_semantic_declaration_request@1",
    "repo_semantic_declaration_source_index@1",
    "repo_semantic_declaration_non_authority_guardrail@1"
  ],
  "emitted_record_shapes": [
    "repo_canonical_meta_lookup_index@1",
    "repo_semantic_operator_class_registry@1",
    "repo_obligation_family_registry@1",
    "repo_semantic_pointer_lookup_fixture@1"
  ],
  "forbidden_claims": [
    "declaration_summary_created",
    "post_declaration_handoff_created",
    "obligation_expansion",
    "evidence_contract_created",
    "edge_probe_plan_created",
    "audit_taskpack_created",
    "deterministic_transition_table_created",
    "implementation_lock_created",
    "work_packet_activation",
    "implementation_execution",
    "command_execution",
    "tool_invocation",
    "target_mutation",
    "runtime_transition",
    "product_authorization",
    "graph_memory_authority",
    "recursive_policy_amendment",
    "v86_selection"
  ],
  "local_gate": "make arc-start-check ARC=240"
}
```
