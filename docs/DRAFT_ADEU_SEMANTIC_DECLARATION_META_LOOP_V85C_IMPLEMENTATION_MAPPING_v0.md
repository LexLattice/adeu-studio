# Draft ADEU Semantic Declaration Meta-Loop V85-C Implementation Mapping v0

Status: support / slice mapping for planned `V85-C`.

Authority layer: support.

This note is not a starter lock. `V85-C` should activate only after `V85-B`
closes on `main` and a canonical `vNext+<n>` starter trio selects this slice.

`V85-C` should summarize semantic declaration and canonical lookup review
substrate and hand off later pressure. It should not expand obligations,
create evidence contracts, create audit taskpacks, run closeout transition
tables, implement code, run commands, invoke tools, create product authority,
create graph authority, amend policy, or select `V86`.

## Selected Surfaces

- `repo_semantic_declaration_review_summary@1`
- `repo_post_semantic_declaration_review_handoff@1`
- `repo_semantic_declaration_family_closeout_alignment@1`

## Package Scope

Expected implementation continues in:

- `packages/adeu_repo_description/src/adeu_repo_description/semantic_declaration_meta_loop.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Expected schema files:

- `packages/adeu_repo_description/schema/repo_semantic_declaration_review_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_semantic_declaration_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_declaration_family_closeout_alignment.v1.json`
- mirrored `spec/repo_*.schema.json` files

Expected tests and fixtures:

- `packages/adeu_repo_description/tests/test_semantic_declaration_meta_loop_v85c.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus241/repo_semantic_declaration_review_summary_v241_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus241/repo_post_semantic_declaration_review_handoff_v241_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus241/repo_semantic_declaration_family_closeout_alignment_v241_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus241/repo_semantic_declaration_closeout_v241_reject_*.json`

`vNext+241` is a planning expectation only; use the next available arc number
when `V85-C` actually starts.

## Review Summary Shape

Minimum summary fields:

- `summary_ref`
- `semantic_declaration_session_ref`
- `candidate_ref`
- `source_refs`
- `declaration_request_refs`
- `source_index_refs`
- `guardrail_refs`
- `lookup_index_refs`
- `operator_class_registry_refs`
- `obligation_family_registry_refs`
- `lookup_fixture_refs`
- `selected_declaration_refs`
- `declaration_selection_status_refs`
- `ambiguous_declaration_refs`
- `abstain_declaration_refs`
- `registry_gap_refs`
- `carried_blocker_refs`
- `carried_warning_refs`
- `warning_rows`
- `summary_posture`
- `ready_basis_posture`
- `lookup_coverage_posture`
- `declaration_non_authority_posture`
- `obligation_expansion_posture`
- `implementation_posture`
- `runtime_transition_posture`
- `future_family_selection_posture`
- `limitation_note`

Minimum `summary_posture` values:

- `ready_for_later_obligation_expansion_review`
- `ready_with_nonblocking_warnings`
- `blocked_by_missing_declaration_source`
- `blocked_by_ambiguous_binding`
- `blocked_by_registry_gap`
- `blocked_by_missing_lookup`
- `blocked_by_lookup_conflict`
- `blocked_by_missing_guardrail`
- `blocked_by_support_only_source`
- `future_family_only`
- `rejected_out_of_scope`

Minimum `ready_basis_posture` values:

- `ready_no_blockers`
- `ready_with_nonblocking_warnings`
- `not_ready_blockers_remain`
- `registry_or_ambiguity_review_requested`
- `future_family_only`
- `rejected_out_of_scope`

Minimum lookup coverage posture values:

- `selected_declarations_have_lookup_rows`
- `missing_lookup_for_selected_declaration`
- `lookup_conflict_present`
- `only_opaque_lookup_proven`
- `lookup_not_applicable`

Readiness invariant:

```text
if summary_posture == ready_for_later_obligation_expansion_review:
  ready_basis_posture == ready_no_blockers
  all selected_declaration_refs resolve to the same semantic_declaration_session_ref and candidate_ref
  selected_declaration_refs are non-empty
  lookup_index_refs are non-empty
  operator_class_registry_refs are non-empty
  obligation_family_registry_refs are non-empty
  guardrail_refs are non-empty
  carried_blocker_refs is empty
  lookup_coverage_posture == selected_declarations_have_lookup_rows
```

Warning-ready summaries may carry warnings but must not carry ambiguity,
registry-gap, missing-source, missing-lookup, lookup-conflict, missing
guardrail, or support-only blockers.

Minimum warning row fields:

- `warning_ref`
- `semantic_declaration_session_ref`
- `source_refs`
- `warning_kind`
- `blocking_posture`
- `limitation_note`

Allowed nonblocking `warning_kind` values:

- `nonblocking_alias_warning`
- `duplicate_preserved_warning`
- `support_context_present_but_not_decisive`
- `optional_obligation_family_unmapped`
- `documentation_alignment_warning`

Disallowed warning-only blocker kinds:

- `ambiguous_binding`
- `registry_gap`
- `unknown_pointer`
- `missing_guardrail`
- `missing_source_witness`
- `lookup_conflict`
- `support_only_source`
- `invented_class`
- `obligation_expansion_attempt`

## Handoff Shape

Minimum handoff fields:

- `handoff_ref`
- `semantic_declaration_session_ref`
- `candidate_ref`
- `source_refs`
- `summary_refs`
- `selected_declaration_refs`
- `lookup_index_refs`
- `operator_class_registry_refs`
- `obligation_family_registry_refs`
- `carried_blocker_refs`
- `carried_warning_refs`
- `handoff_target`
- `handoff_subject_horizon`
- `handoff_posture`
- `handoff_sequence_posture`
- `handoff_authority_horizon`
- `required_later_authority_refs`
- `non_authority_guardrail_refs`
- `obligation_expansion_status`
- `implementation_status`
- `runtime_transition_status`
- `future_family_selection_status`
- `limitation_note`

Minimum `handoff_target` values:

- `future_obligation_expansion_review`
- `future_evidence_contract_review`
- `future_edge_probe_plan_review`
- `future_audit_taskpack_review`
- `future_deterministic_closeout_transition_review`
- `future_canonical_implementation_lock_review`
- `future_morphic_ux_implementation_review`
- `future_direct_oai_harness_review`
- `future_meta_orchestrator_workflow_review`
- `future_product_review`
- `future_graph_memory_review`
- `future_family_review`
- `deferred_no_selection`

Minimum `handoff_subject_horizon` values:

- `semantic_declaration_review_outcome`
- `canonical_lookup_review_outcome`
- `obligation_family_lookup_pressure`
- `evidence_contract_pressure`
- `audit_taskpack_pressure`
- `closeout_transition_pressure`
- `implementation_lock_pressure`
- `support_doctrine_pressure`
- `future_family_only`

Minimum `handoff_authority_horizon` values:

- `obligation_expansion_review`
- `evidence_contract_review`
- `edge_probe_plan_review`
- `audit_taskpack_review`
- `closeout_transition_review`
- `implementation_lock_review`
- `morphic_ux_runtime_ui_authority_review`
- `direct_oai_provider_runtime_authority_review`
- `meta_orchestrator_workflow_runtime_authority_review`
- `product_authority_review`
- `graph_memory_authority_review`
- `recursive_policy_authority_review`
- `future_family_review`

Minimum `handoff_sequence_posture` values:

- `immediate_next_pressure`
- `downstream_after_obligation_expansion`
- `downstream_after_evidence_contract`
- `downstream_after_audit`
- `lateral_support_pressure`
- `future_family_only`

Handoff invariant:

```text
if handoff_target == future_obligation_expansion_review:
  summary_refs include ready or warning-ready summary
  lookup_index_refs are non-empty
  obligation_family_registry_refs are non-empty
  obligation_expansion_status == no_obligation_expansion_performed_by_v85
  future_family_selection_status == no_future_family_selected_by_v85
```

Sequence invariant:

```text
if handoff_target in future_evidence_contract_review,
                    future_edge_probe_plan_review,
                    future_audit_taskpack_review,
                    future_deterministic_closeout_transition_review:
  handoff_sequence_posture must not be immediate_next_pressure
  unless future_obligation_expansion_review is also carried as prerequisite
```

Blocker invariant:

```text
if carried_blocker_refs is non-empty:
  handoff_posture must not be ready_for_later_review
  unless handoff_target is future_family_review
  and ready_basis_posture routes blocker settlement explicitly
```

## Family Closeout Alignment Shape

Minimum closeout alignment fields:

- `family_closeout_ref`
- `family`
- `closed_by_arc`
- `semantic_declaration_session_refs`
- `source_refs`
- `summary_refs`
- `handoff_refs`
- `closed_surface_refs`
- `unselected_surface_refs`
- `carried_future_pressure_refs`
- `family_alignment_posture`
- `non_authority_posture`
- `future_family_selection_status`
- `limitation_note`

Minimum closed surface refs:

- `repo_turn_semantic_declaration_request@1`
- `repo_semantic_declaration_source_index@1`
- `repo_semantic_declaration_non_authority_guardrail@1`
- `repo_canonical_meta_lookup_index@1`
- `repo_semantic_operator_class_registry@1`
- `repo_obligation_family_registry@1`
- `repo_semantic_pointer_lookup_fixture@1`
- `repo_semantic_declaration_review_summary@1`
- `repo_post_semantic_declaration_review_handoff@1`
- `repo_semantic_declaration_family_closeout_alignment@1`

The closeout may say `V85` closed semantic declaration and canonical lookup
review. It must not say obligations were expanded, evidence contracts were
emitted, audit taskpacks were executed, closeout transitions were run,
implementation locks were created, runtime transitioned, product authority was
granted, graph-memory authority was created, recursive policy was amended, or
`V86` was selected.

## Mandatory Reject Cases

Reject:

- summary marked ready with no selected declaration refs;
- summary rows stitching together different `semantic_declaration_session_ref`
  or `candidate_ref` lineages;
- summary marked ready with selected declaration refs but no lookup rows;
- summary marked ready while ambiguity or registry-gap blockers remain;
- warning-ready summary carrying authority, lookup, missing-source, or
  registry-gap blockers;
- warning-ready summary carrying ambiguity, unknown-pointer, support-only, or
  invented-class blockers as warnings;
- handoff to obligation expansion with no obligation-family registry refs;
- handoff directly to evidence, edge probe, audit, or closeout transition as
  immediate next pressure without obligation expansion prerequisite;
- handoff claiming obligation expansion has already happened;
- handoff claiming implementation lock or runtime transition authority;
- closeout selecting `V86`;
- closeout claiming the whole meta-loop is complete;
- closeout turning Morphic UX, direct OAI, or meta-orchestrator support
  pressure into runtime behavior.

## Verification

Recommended targeted checks for the future active slice:

```text
PYTHONPATH=packages/adeu_repo_description/src \
  pytest packages/adeu_repo_description/tests/test_semantic_declaration_meta_loop_v85c.py \
         packages/adeu_repo_description/tests/test_repo_description_export_schema.py
```

After `V85-C`, run the family closeout lint and then create a new combined
dogfood record only after the family has closed on `main`.
