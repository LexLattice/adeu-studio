# Draft ADEU Semantic Declaration Meta-Loop V85-B Implementation Mapping v0

Status: support / slice mapping for planned `V85-B`.

Authority layer: support.

This note is not a starter lock. `V85-B` should activate only after `V85-A`
closes on `main` and a canonical `vNext+<n>` starter trio selects this slice.

`V85-B` should add canonical lookup and registry review surfaces. It should
not expand obligations, emit evidence contracts, create reviewer taskpacks,
run audit, implement code, run commands, invoke tools, or select `V86`.

## Selected Surfaces

- `repo_canonical_meta_lookup_index@1`
- `repo_semantic_operator_class_registry@1`
- `repo_obligation_family_registry@1`
- `repo_semantic_pointer_lookup_fixture@1`

## Package Scope

Expected implementation continues in:

- `packages/adeu_repo_description/src/adeu_repo_description/semantic_declaration_meta_loop.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Expected schema files:

- `packages/adeu_repo_description/schema/repo_canonical_meta_lookup_index.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_operator_class_registry.v1.json`
- `packages/adeu_repo_description/schema/repo_obligation_family_registry.v1.json`
- `packages/adeu_repo_description/schema/repo_semantic_pointer_lookup_fixture.v1.json`
- mirrored `spec/repo_*.schema.json` files

Expected tests and fixtures:

- `packages/adeu_repo_description/tests/test_semantic_declaration_meta_loop_v85b.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus240/repo_canonical_meta_lookup_index_v240_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus240/repo_semantic_operator_class_registry_v240_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus240/repo_obligation_family_registry_v240_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus240/repo_semantic_pointer_lookup_fixture_v240_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus240/repo_semantic_declaration_lookup_v240_reject_*.json`

`vNext+240` is a planning expectation only; use the next available arc number
when `V85-B` actually starts.

## Canonical Lookup Index

Minimum lookup row fields:

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

Minimum `lookup_input_kind` values:

- `opaque_pointer`
- `explicit_semantic_pointer`
- `natural_binding_candidate`
- `registry_gap_candidate`
- `support_context_only`

Minimum `lookup_posture` values:

- `exact_match_for_review_only`
- `ambiguous_match`
- `unknown_pointer_abstained`
- `registry_gap`
- `conflict_requires_review`
- `blocked_by_missing_source`
- `future_family_only`

The lookup index may name obligation-family refs, but it must not expand those
families into concrete obligations. Expansion belongs to a later family.

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

Minimum `pointer_parse_posture` values:

- `parsed_exact`
- `parsed_with_alias`
- `malformed_pointer`
- `unknown_operator`
- `unknown_class`
- `unknown_version`
- `ambiguous_parse`
- `abstain_required`

Minimum `pointer_competency_kind` values:

- `opaque_pointer_obedience`
- `explicit_pointer_lookup`
- `natural_binding_candidate_lookup`
- `registry_gap_detection`
- `conflict_detection`
- `distractor_resistance`

Minimum `competency_claim_horizon` values:

- `pointer_obedience_only`
- `exact_lookup_only`
- `natural_binding_not_claimed`
- `obligation_expansion_not_claimed`
- `implementation_not_claimed`

## Operator And Class Registry

Minimum registry row fields:

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

Minimum `registry_domain` values:

- `operator`
- `object_class`
- `source_class`
- `target_class`
- `modifier`
- `relation_class`
- `obligation_family`

Minimum `operator_semantics_posture` values:

- `action_verb_for_declaration_only`
- `guard_or_route_for_later_authority_review`
- `not_runtime_behavior`

Minimum `class_semantics_posture` values:

- `semantic_class_for_lookup_only`
- `not_runtime_class_behavior`
- `not_implementation_target`

Minimum operator entries should include:

- `CREATE`
- `MODIFY`
- `REMOVE`
- `CONNECT`
- `PROJECT`
- `VALIDATE`
- `NORMALIZE`
- `ROUTE`
- `TRANSITION`
- `AGGREGATE`
- `CACHE`
- `SUBSCRIBE`
- `PERSIST`
- `MIGRATE`
- `GATE`
- `REVIEW`
- `RECONCILE`
- `CLOSEOUT`

`GATE` must be represented as constrain / guard / route for later authority
review only. It must not locally mint authority.

Minimum class entries should include:

- `ui.menu@v1`
- `ui.modal@v1`
- `ui.popover@v1`
- `ui.projection@v1`
- `ui.surface@v1`
- `semantic.validator@v1`
- `semantic.normalizer@v1`
- `semantic.classifier@v1`
- `semantic.summarizer@v1`
- `state.transition@v1`
- `capability.gate@v1`
- `router.dispatcher@v1`
- `cache.layer@v1`
- `event.subscription@v1`
- `resource.handle@v1`
- `persistence.store@v1`
- `migration.plan@v1`
- `evidence.bundle@v1`
- `readiness.summary@v1`
- `schema.binding@v1`
- `worker.taskpack@v1`
- `audit.report@v1`
- `closeout.artifact@v1`

## Obligation Family Registry

Minimum obligation-family row fields:

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

Minimum obligation families should include:

- `stateful_lifecycle@v1`
- `birth_continuation_death_algebra@v1`
- `absence_null_empty_distinction@v1`
- `branch_specific_witness@v1`
- `non_vacuous_validation@v1`
- `projection_source_integrity@v1`
- `source_witness_preservation@v1`
- `idempotence_reentry@v1`
- `rollback_cleanup_teardown@v1`
- `staleness_invalidation@v1`
- `enum_exhaustiveness@v1`
- `unknown_case_handling@v1`
- `capability_guard@v1`
- `partial_retry_reentry@v1`
- `evidence_sufficiency@v1`
- `waiver_explicitness@v1`
- `cross_field_consistency@v1`
- `failure_path_fail_closed@v1`

Minimum future expansion posture values:

- `named_for_later_expansion_only`
- `expansion_requires_future_family`
- `expansion_blocked_by_missing_registry`
- `expansion_not_authorized_by_v85`

Minimum `obligation_family_relation_kind` values:

- `applies_by_operator`
- `applies_by_object_class`
- `applies_by_target_context`
- `applies_by_modifier`
- `applies_by_negative_cue`
- `applies_by_authority_boundary`
- `conflict_or_exclusion`
- `requires_later_disambiguation`

Minimum `obligation_family_activation_posture` values:

- `lookup_result_only`
- `named_for_later_expansion_only`
- `expansion_requires_v86_or_later`
- `expansion_blocked_by_ambiguity`
- `expansion_blocked_by_registry_gap`
- `expansion_not_authorized_by_v85`

## Pointer Lookup Fixtures

Minimum fixture row fields:

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

Minimum `fixture_kind` values:

- `opaque_pointer_exact_lookup`
- `opaque_pointer_duplicate_preservation`
- `opaque_pointer_unknown_abstain`
- `explicit_semantic_pointer_lookup`
- `explicit_semantic_pointer_registry_gap`
- `distractor_ignored`
- `conflict_requires_review`

The first fixture set should include an opaque test such as:

```text
M-42 -> A1 -> A9 -> C4 -> Z2
```

and an explicit semantic pointer such as:

```text
CREATE ui.menu@v1
  -> stateful_lifecycle@v1
  -> birth_continuation_death_algebra@v1
  -> rollback_cleanup_teardown@v1
  -> failure_path_fail_closed@v1
```

Opaque success proves pointer obedience only. It does not prove natural
semantic binding correctness or implementation readiness.

## Mandatory Reject Cases

Reject:

- unknown pointer expanded into obligation refs;
- duplicate obligation refs collapsed without explicit duplicate posture;
- input order changed without declared normalization rule;
- distractor row changes the active pointer;
- operator/class invented from model prose without registry source;
- `GATE` treated as local authority minting;
- obligation family expanded into concrete obligations inside `V85-B`;
- support doc treated as runtime behavior;
- lookup fixture treated as semantic truth or implementation authority;
- opaque pointer exact lookup used to mark natural binding semantically
  correct;
- malformed pointer normalized into a known class without a declared
  normalization rule;
- unknown version treated as the latest version;
- alias accepted without an alias row;
- `V86` selection inside `V85-B`.

## Verification

Recommended targeted checks for the future active slice:

```text
PYTHONPATH=packages/adeu_repo_description/src \
  pytest packages/adeu_repo_description/tests/test_semantic_declaration_meta_loop_v85b.py \
         packages/adeu_repo_description/tests/test_repo_description_export_schema.py
```
