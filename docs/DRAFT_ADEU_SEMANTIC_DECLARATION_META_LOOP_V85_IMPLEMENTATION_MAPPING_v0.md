# Draft ADEU Semantic Declaration Meta-Loop V85 Implementation Mapping v0

Status: support / implementation mapping record for planned `V85`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V85` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v75.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_DECLARATION_META_LOOP_FAMILY_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V84_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V85` should add semantic declaration and canonical meta-list review records
without turning them into:

- obligation expansion, evidence contracts, edge probe plans, reviewer
  taskpacks, audit reports, or deterministic closeout routing;
- implementation, file edits, target mutation, or work-packet activation;
- command execution, tool invocation, worker assignment, dispatch execution,
  controlled execution, runtime permission, or meta-orchestrator runtime
  transition;
- Morphic UX runtime changes or direct OAI runtime behavior;
- PR creation, commit, merge, release, product authorization, or released
  truth;
- corpus ingestion, connector activation, endpoint access, data transfer, or
  external branch activation;
- graph-memory authority, benchmark truth, generalized artifact authority, or
  recursive policy amendment;
- `V86` or later-family selection.

The implementation target is a typed semantic declaration family that can
represent:

- source-bound turn declaration requests;
- source indexes over released `V84-C` substrate, operator / repo context,
  support doctrine, canonical meta-loop sources, and absence posture;
- non-authority guardrails;
- canonical meta lookup records;
- semantic operator/class registry rows;
- obligation-family registry rows;
- opaque and explicit pointer lookup fixtures;
- semantic declaration summaries and post-declaration handoffs.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded semantic declaration review records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus239/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V85` still describes review metadata. If
a later family becomes a live semantic declaration office, resident-agent
harness, meta-orchestrator runtime, Morphic UX implementation, direct OAI
runtime harness, graph runtime, or release automation layer, that work should
split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/semantic_declaration_meta_loop.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_semantic_declaration_meta_loop_v85a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_turn_semantic_declaration_request.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_declaration_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_declaration_non_authority_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_canonical_meta_lookup_index.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_operator_class_registry.v1.json`
- `packages/adeu_repo_description/schema/repo_obligation_family_registry.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_pointer_lookup_fixture.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_declaration_review_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_semantic_declaration_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_declaration_family_closeout_alignment.v1.json`

Expected mirror schema files follow the same names under `spec/`.

## 3. Candidate `V85` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_turn_semantic_declaration_request@1` | `V85-A` | source-bound declaration-review request rows for natural task / repo context |
| `repo_semantic_declaration_source_index@1` | `V85-A` | source rows over released `V84-C` substrate, operator turns, support doctrine, canonical meta-loop notes, and absence posture |
| `repo_semantic_declaration_non_authority_guardrail@1` | `V85-A` | guardrails preventing declarations from becoming obligation expansion, implementation, runtime, product, graph, policy, or later-family authority |
| `repo_canonical_meta_lookup_index@1` | `V85-B` | canonical lookup rows connecting semantic pointers to operator/class/obligation registry rows for review only |
| `repo_semantic_operator_class_registry@1` | `V85-B` | reviewed registry rows for operators, object/function classes, aliases, and non-invention posture |
| `repo_obligation_family_registry@1` | `V85-B` | reviewed obligation-family rows that may be named by lookup but not expanded by `V85` |
| `repo_semantic_pointer_lookup_fixture@1` | `V85-B` | opaque and explicit pointer fixtures proving exact lookup, abstention, duplicate preservation, and fail-closed behavior |
| `repo_semantic_declaration_review_summary@1` | `V85-C` | declaration readiness summary without obligation expansion or implementation |
| `repo_post_semantic_declaration_review_handoff@1` | `V85-C` | later-review handoff without selecting `V86` |
| `repo_semantic_declaration_family_closeout_alignment@1` | `V85-C` | family closeout alignment without later-family selection |

`V85-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement canonical lookup indexes,
registries, pointer fixtures, summaries, handoffs, obligation expansion,
implementation, PR creation, commits, releases, or runtime changes.

## 4. Source Classes

The family should consume concrete source refs from:

- `V84` family closeout:
  - `docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v238/evidence_inputs/v84_family_closeout_alignment_v238.json`
  - `artifacts/agent_harness/v238/evidence_inputs/v84c_work_packet_activation_closeout_evidence_v238.json`
- `V84-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus238/repo_work_packet_activation_readiness_summary_v238_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus238/repo_post_work_packet_activation_review_handoff_v238_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus238/repo_work_packet_activation_family_closeout_alignment_v238_reference.json`
- combined support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.json`
- support doctrine:
  - `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V84_v0.md`
  - `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
  - `docs/support/morphic_ux. v2.md`
  - `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
  - `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
  - `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
  - `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
  - `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become source rows. Support docs may contextualize `V85`; they do
not become declaration eligibility by themselves.

## 5. Shared Row Vocabulary

Minimum declaration source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `semantic_declaration_source_role`
- `source_horizon`
- `source_currentness`
- `source_scope_posture`
- `source_import_posture`
- `declaration_authority_posture`
- `loop_authority_posture`
- `limitation_note`

Minimum `semantic_declaration_source_role` values:

- `v84_readiness_summary_source`
- `v84_handoff_source`
- `v84_closeout_source`
- `v83_projection_packet_context`
- `v83_quality_gate_context`
- `v83_semantic_edge_context`
- `combined_dogfood_context`
- `post_v84_roadmap_source`
- `canonical_meta_loop_support_source`
- `morphic_ux_support_context`
- `direct_oai_support_context`
- `meta_orchestrator_support_context`
- `operator_turn_source`
- `repo_task_context_source`
- `natural_task_context_source`
- `code_context_source`
- `canonical_pointer_context`
- `opaque_pointer_context`
- `generated_declaration_candidate_source`
- `model_or_agent_profile_source`
- `reviewer_amendment_source`
- `explicit_absence_marker`
- `support_process_context`

Minimum declaration request fields:

- `declaration_request_ref`
- `semantic_declaration_session_ref`
- `candidate_ref`
- `turn_ref`
- `source_refs`
- `source_witness_refs`
- `operator_turn_refs`
- `repo_context_refs`
- `declared_semantic_act_rows`
- `semantic_act_witness_rows`
- `negative_cue_rows`
- `resident_model_competency_rows`
- `declaration_horizon`
- `requested_declaration_review_horizon`
- `binding_posture`
- `binding_resolution_posture`
- `binding_basis_refs`
- `negative_cue_refs`
- `uncertainty_slot_refs`
- `canonical_lookup_required_posture`
- `declaration_candidate_status`
- `canonical_lookup_status`
- `declaration_selection_status`
- `declaration_recordability_posture`
- `declaration_review_eligibility_posture`
- `guardrail_refs`
- `non_authority_posture`
- `odeu_lane_refs`
- `limitation_note`

Minimum declared semantic act row fields:

- `semantic_act_ref`
- `semantic_declaration_session_ref`
- `operator`
- `object_class`
- `source_class`
- `target_class`
- `target_context_refs`
- `modifiers`
- `binding_basis_refs`
- `source_witness_refs`
- `ambiguity_posture`
- `registry_gap_posture`
- `declaration_candidate_status`
- `declaration_selection_status`
- `canonical_status`
- `limitation_note`

Minimum semantic act witness row fields:

- `witness_ref`
- `semantic_declaration_session_ref`
- `source_refs`
- `witnessed_element`
- `witness_strength`
- `witness_currentness`
- `limitation_note`

Minimum `witnessed_element` values:

- `operator`
- `object_class`
- `source_class`
- `target_class`
- `target_context`
- `modifier`
- `negative_cue`
- `uncertainty`

Minimum `witness_strength` values:

- `direct`
- `indirect`
- `contextual`
- `support_only`
- `absence_marker`
- `conflict_marker`

Minimum negative cue row fields:

- `negative_cue_ref`
- `semantic_declaration_session_ref`
- `source_refs`
- `cue_kind`
- `effect_on_declaration`
- `limitation_note`

Minimum resident model competency row fields:

- `competency_ref`
- `semantic_declaration_session_ref`
- `competency_kind`
- `required_posture`
- `evidence_or_fixture_refs`
- `failure_routing_posture`
- `non_authority_guardrail_refs`

Minimum `binding_posture` values:

- `selected`
- `ambiguous`
- `abstain`
- `registry_gap`
- `malformed`
- `blocked_by_missing_source`
- `future_family_only`
- `rejected_out_of_scope`

Minimum state-transition postures:

- `declaration_candidate_status`
  - `candidate_recorded_for_review`
  - `ambiguous_candidate`
  - `abstain_candidate`
  - `registry_gap_candidate`
  - `malformed_candidate`
  - `support_context_only_candidate`
- `canonical_lookup_status`
  - `lookup_not_selected_by_v85a`
  - `lookup_required_later`
  - `exact_match_for_review_only`
  - `ambiguous_match`
  - `unknown_pointer_abstained`
  - `registry_gap`
  - `conflict_requires_review`
- `declaration_selection_status`
  - `not_selected_by_v85a`
  - `selected_for_later_obligation_expansion_review`
  - `ambiguous_not_selected`
  - `abstained_not_selected`
  - `registry_gap_not_selected`
  - `blocked_not_selected`

`V85-A` can create declaration candidates only. `V85-B` can create lookup
results only. `V85-C` can mark a declaration selected for later review only
when lookup, registry, witness, session, and guardrail coverage exists.

Minimum non-authority guardrail fields:

- `guardrail_ref`
- `semantic_declaration_session_ref`
- `candidate_ref`
- `source_refs`
- `forbidden_declaration_actions`
- `forbidden_downstream_actions`
- `required_later_authority_refs`
- `declaration_non_authority_posture`
- `obligation_expansion_posture`
- `implementation_posture`
- `runtime_transition_posture`
- `future_family_selection_posture`
- `limitation_note`

## 6. Slice Ladder

### `V85-A`

Adds:

- semantic declaration request rows;
- declaration source index rows;
- non-authority guardrail rows;
- reference and reject fixtures showing selected, ambiguous, abstain,
  registry-gap, support-only, and generated-candidate cases.

Does not add:

- canonical lookup indexes;
- registries;
- pointer lookup fixtures;
- summaries;
- handoffs.

### `V85-B`

Adds:

- canonical meta lookup indexes;
- semantic operator/class registry rows;
- obligation-family registry rows;
- pointer lookup fixtures over opaque and explicit pointers.

Does not add:

- obligation expansion bundles;
- evidence contracts;
- audit taskpacks;
- summaries or handoffs.

### `V85-C`

Adds:

- declaration review summaries;
- post-semantic-declaration-review handoffs;
- family closeout alignment rows and artifacts.

Does not add:

- `V86` selection;
- obligation expansion;
- runtime transition or implementation authority.

## 7. Verification Expectations

Focused verification should include:

- export-schema coverage for all shipped `V85` schemas;
- positive fixtures for source-bound declaration rows and pointer lookup rows;
- reject fixtures for support-only eligibility, ambiguous binding marked
  selected, unknown class invention, registry-gap laundering, duplicate
  obligation collapse, obligation expansion inside `V85`, and `V86` selection;
- family closeout checks after `V85-C`;
- updated combined dogfood only after `V85` closes.

## 8. Future Seams

Mapped but not selected:

- `V86` obligation expansion / evidence contract / edge probe plan review;
- `V87` reviewer / auditor taskpack and audit artifact review;
- `V88` deterministic closeout transition table / remand routing;
- canonical implementation-lock review;
- Morphic UX implementation review;
- direct OAI harness implementation review;
- meta-orchestrator workflow activation review;
- product typed-adjudication reporting;
- graph memory / living decision graph;
- recursive policy amendment.
