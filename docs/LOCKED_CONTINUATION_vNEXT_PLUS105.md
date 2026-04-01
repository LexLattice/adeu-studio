# Locked Continuation vNext+105

Status: `V45-F` implementation contract.

## V105 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v45f_repo_descriptive_normative_binding_frame_contract@1",
  "target_arc": "vNext+105",
  "target_path": "V45-F",
  "target_scope": "repo_descriptive_to_normative_binding_over_released_v45a_v45b_v45c_v45d_v45e_descriptive_baseline",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "governing_released_stack": "V41_to_V42_released_stack_plus_V45-A_V45-B_V45-C_V45-D_V45-E_released_descriptive_surfaces_on_main",
  "governing_stack_consumption_mode": "binding_doctrine_only_not_mutation_or_recursive_execution_authority_minting",
  "repo_descriptive_normative_binding_frame_schema": "repo_descriptive_normative_binding_frame@1",
  "repo_entity_catalog_schema": "repo_entity_catalog@1",
  "repo_schema_family_registry_schema": "repo_schema_family_registry@1",
  "repo_symbol_catalog_schema": "repo_symbol_catalog@1",
  "repo_dependency_graph_schema": "repo_dependency_graph@1",
  "repo_test_intent_matrix_schema": "repo_test_intent_matrix@1",
  "repo_optimization_register_schema": "repo_optimization_register@1",
  "descriptive_plane_first_required": true,
  "bounded_repo_visible_snapshot_scope_required": true,
  "explicit_stale_snapshot_semantics_required": true,
  "source_set_binding_required": true,
  "source_set_hash_required": true,
  "released_v45a_v45b_v45c_v45d_v45e_binding_required": true,
  "top_level_extraction_posture_required": true,
  "top_level_extraction_method_required": true,
  "typed_binding_entry_required": true,
  "descriptive_input_vs_binding_posture_vs_authority_source_distinction_required": true,
  "consumer_class_required": true,
  "bounded_consumer_class_vocabulary_required": true,
  "promotion_law_posture_required": true,
  "source_artifact_refs_required": true,
  "cross_artifact_snapshot_identity_and_source_scope_compatibility_required": true,
  "bounded_vocabulary_note_required": true,
  "diagnostic_to_normative_boundary_required": true,
  "descriptive_input_ref_resolution_against_bound_baseline_required": true,
  "separate_authority_source_required_for_normative_use": true,
  "authority_source_and_promotion_law_relation_required": true,
  "binding_frame_collapse_rejection_required": true,
  "non_executive_non_approving_posture_required": true,
  "automatic_mutation_permission_forbidden": true,
  "automatic_recursive_execution_forbidden": true,
  "automatic_priority_or_scheduling_authority_forbidden": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "source_architecture_doc": "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
  "decomposition_doc": "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"
}
```

## Slice

- Arc label: `vNext+105`
- Family label: `V45-F`
- Scope label: bounded descriptive-to-normative binding frame over released descriptive surfaces

## Objective

Release the bounded `V45-F` binding seam by materializing:

- one canonical `repo_descriptive_normative_binding_frame@1`;

while preserving one explicit operational snapshot identity for the bound `V45-B`,
`V45-D`, and `V45-E` descriptive baseline, explicit snapshot-validity and
source-scope-compatibility posture for the bound `V45-A` and `V45-C` artifacts,
explicit bounded source-set posture, explicit distinction between descriptive input,
binding posture, and authority source, explicit promotion-law requirements for any
later normative consumption, explicit binding back to the released `V45-A` through
`V45-E` descriptive baselines, and fail-closed rejection of recursive-governance
laundering, mutation laundering, or self-authorizing normative use.

This slice is binding doctrine only. It is not mutation permission, scheduler
authority, recursive execution, a mutation request, an execution plan, an approval
artifact, or constitutional override.

## Frozen Implementation Decisions

1. Binding-doctrine strategy:
   - `V45-F` emits typed binding doctrine only;
   - outputs may define admissibility and promotion-law constraints for later consumers
     but may not mint mutation, scheduling, release-gating, settlement, or recursive
     execution authority by themselves.
   - the frame is a binding/consumption object only:
     - not an execution plan;
     - not a mutation request;
     - not an approval artifact by itself.
2. Path-order strategy:
   - `V45-A` through `V45-E` remain authoritative released descriptive baselines on
     `main`;
   - this contract follows the current `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md` ladder and
     does not reopen older path assignments;
   - `V45-F` is the next widening because later recursive-governance or amendment
     lanes should bind to explicit typed doctrine rather than raw descriptive artifacts
     or ad hoc prose interpretation.
3. Source authority strategy:
   - the artifact must bind to one explicit operational snapshot identity for the
     bound `V45-B`, `V45-D`, and `V45-E` baseline, plus one explicit bounded source
     set over the consumed descriptive inputs and binding doctrine sources;
   - the artifact must also bind one explicit source-set hash and one explicit
     extraction posture/method pair;
   - stale-snapshot semantics must remain explicit rather than implied;
   - outputs are valid for the bound snapshot only and become historical evidence when
     stale.
4. Cross-artifact binding strategy:
   - `repo_descriptive_normative_binding_frame@1` must bind to one released or same-run
     `repo_entity_catalog@1`, `repo_schema_family_registry@1`, `repo_symbol_catalog@1`,
     `repo_dependency_graph@1`, `repo_arc_dependency_register@2`,
     `repo_test_intent_matrix@1`, and `repo_optimization_register@1` over one
     operational bound baseline with:
     - shared snapshot identity for the bound `V45-B`, `V45-D`, and `V45-E` artifacts;
     - shared snapshot-validity posture and explicit artifact-local source-scope
       compatibility for `V45-A` and `V45-C`;
   - any internal `descriptive_input_ref` must resolve against one of those bound
     released descriptive artifacts under that same bound-baseline compatibility
     posture;
   - the frame may consult descriptive diagnostics from `V45-E`, but it may not treat
     those diagnostics as self-authorizing normative output.
5. Binding-entry modeling strategy:
   - row granularity is frozen as one row per descriptive-input/consumer binding rule;
   - each row must therefore carry stable identity, one explicit descriptive input
     kind/ref pair, one explicit consumer class, one explicit binding posture, one
     explicit authority source kind, one explicit promotion-law posture, one bounded
     allowed-use summary, one bounded forbidden-use summary, explicit derivation
     posture/method, and explicit source artifact refs;
   - the first release stays bounded to repo-internal descriptive surfaces only.
6. Consumer-class strategy:
   - the first release must freeze one bounded consumer-class vocabulary rather than
     leaving consumption classes to implementation taste;
   - a binding row may describe one consumer class only, not a collapsed
     multi-consumer shortcut;
   - consumer classes describe who may consume the binding doctrine:
     - not who has already been granted execution authority.
7. Promotion-law strategy:
   - the binding frame must make explicit that descriptive artifacts alone are not
     sufficient for execution-grade normative promotion;
   - later consumers must remain gated by an explicit authority source and one explicit
     promotion-law posture rather than implicit “looks good enough” escalation;
   - `authority_source_kind` is necessary but not sufficient for normative promotion;
   - `promotion_law_posture` is necessary but not sufficient for normative promotion;
   - no row may let promotion-law posture elevate a merely advisory or descriptive-only
     authority source into execution-grade authority by itself.
8. Authority-source strategy:
   - descriptive surfaces may be advisory or eligibility inputs only;
   - any row that points at normative consumption beyond advisory use must name a
     separate authority source kind rather than laundering authority from the
     descriptive artifact itself;
   - advisory or eligibility-only authority sources may constrain later evaluation,
     but they may not approve execution by themselves.
9. Anti-collapse strategy:
   - a row may not collapse descriptive input, authority source, and promotion outcome
     into a direct normative shortcut;
   - the mediation structure itself must remain explicit and inspectable.
10. Anti-overreach strategy:
   - `V45-F` may not present released descriptive objects as automatic mutation
     entitlement;
   - `V45-F` may not present optimization findings as automatic scheduler authority;
   - `V45-F` may not emit recursive-governance execution permission;
   - `V45-F` may not widen into automatic repo mutation.

## Bounded Vocabulary Note

The first `V45-F` release should freeze bounded starter vocabularies for the new typed
fields rather than leaving them to implementation taste.

The intended bounded starter vocabularies are:

- `descriptive_input_kind`:
  - `repo_entity_catalog`
  - `repo_schema_family_registry`
  - `repo_symbol_catalog`
  - `repo_dependency_graph`
  - `repo_test_intent_matrix`
  - `repo_optimization_register`
- `consumer_class`:
  - `planning_consumer`
  - `adjudication_consumer`
  - `policy_consumer`
  - `recursive_governance_consumer`
- `binding_posture`:
  - `advisory_only`
  - `eligibility_signal_only`
  - `adjudication_required`
  - `separate_normative_authority_required`
- `authority_source_kind`:
  - `descriptive_artifact_only_forbidden`
  - `separate_lock_required`
  - `separate_decision_required`
  - `separate_normative_artifact_required`
- `promotion_law_posture`:
  - `inferred_not_sufficient`
  - `adjudication_required_before_normative_use`
  - `settled_authority_required_before_execution`
- `derivation_posture`:
  - `observed`
  - `derived_deterministically`
  - `inferred_heuristically`
  - `adjudicated`
  - `settled`
- `derivation_method`:
  - `descriptive_projection`
  - `cross_artifact_join`
  - `policy_binding_rule`
  - `adjudicated_policy`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent vocabulary creep.

These vocabularies are starter doctrine for consumption posture only.

They do not by themselves grant execution authority, approval posture, or mutation
permission.

## Required Deliverables

1. New typed binding surface:
   - canonical `repo_descriptive_normative_binding_frame@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic extraction entrypoint(s) that:
   - consume one explicit repo snapshot and one bounded source set over the released
     descriptive baselines;
   - bind to released `V45-A` through `V45-E` artifacts over the same bound-baseline
     compatibility posture;
   - derive typed binding rows with explicit descriptive input kind/ref, consumer
     class, binding posture, authority source kind, promotion-law posture,
     allowed-use summary, forbidden-use summary, derivation posture/method, and
     source artifact refs;
   - fail closed on missing bound references, missing authority-source doctrine,
     missing promotion-law posture, or normative laundering.
3. Top-level schema anchors for `repo_descriptive_normative_binding_frame@1`:
   - `schema`
   - `repo_descriptive_normative_binding_frame_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `source_set`
   - `source_set_hash`
   - `bound_entity_catalog_ref`
   - `bound_schema_family_registry_ref`
   - `bound_symbol_catalog_ref`
   - `bound_dependency_graph_ref`
   - `bound_arc_dependency_register_ref`
   - `bound_test_intent_matrix_ref`
   - `bound_optimization_register_ref`
   - `binding_scope`
   - `extraction_posture`
   - `extraction_method`
   - `binding_entries`
   - `evidence_refs`
   - per evidence ref anchors:
     - `evidence_ref`
     - `evidence_kind`
   - per binding entry anchors:
     - `entry_id`
     - `descriptive_input_kind`
     - `descriptive_input_ref`
     - `consumer_class`
     - `binding_posture`
     - `authority_source_kind`
     - `promotion_law_posture`
     - `allowed_use_summary`
     - `forbidden_use_summary`
     - `derivation_posture`
     - `derivation_method`
     - `source_artifact_refs`
     - `supporting_evidence_refs`
4. Deterministic laws that fail closed on at least:
   - missing snapshot identity/hash binding;
   - missing or empty bounded source set binding;
   - missing source-set hash;
   - missing any bound `V45-A` through `V45-E` reference or mismatched operational
     snapshot / snapshot-validity / source-scope compatibility posture between the
     frame and those bound descriptive artifacts;
   - missing top-level extraction posture or extraction method;
   - any entry missing required descriptive-input, consumer, posture, authority,
     promotion-law, summary, derivation, or source-artifact fields;
   - any `source_artifact_ref` that does not resolve inside the declared `source_set`;
   - duplicate entry IDs;
   - any `descriptive_input_ref` that does not resolve against one of the bound
     descriptive artifacts under the same bound-baseline compatibility posture;
   - any entry whose `binding_posture`, `authority_source_kind`, and
     `promotion_law_posture` jointly imply self-authorizing mutation, scheduler
     control, release gating, settlement, or recursive execution;
   - any entry treating a descriptive artifact as sufficient authority source for
     normative execution;
   - any entry whose `authority_source_kind` is weaker than the normative use implied
     by its `promotion_law_posture`;
   - any entry collapsing descriptive input, authority source, and promotion outcome
     into a direct normative shortcut;
   - any row presented as an execution plan, mutation request, or approval artifact by
     itself.
5. Accepted and reject fixtures that prove at least:
   - accepted canonical binding frame over one bounded snapshot and one bounded source
     set;
   - reject missing promotion-law posture;
   - reject missing bound optimization-register ref;
   - reject descriptive-input ref outside bound baseline;
   - reject source artifact ref outside declared source set;
   - reject authority laundering from descriptive artifact alone;
   - reject recursive-governance execution entitlement minted in this slice.
6. Tests covering at least:
   - schema/model validation;
   - deterministic replay over committed accepted and rejected fixtures;
   - authoritative/mirrored schema export parity;
   - cross-artifact binding against released `V45-A` through `V45-E` fixtures;
   - bounded vocabulary enforcement;
   - fail-closed authority-laundering rejection.

## Acceptance Gates

Accept this slice only if:

1. canonical `repo_descriptive_normative_binding_frame@1` compiles deterministically
   over one bounded snapshot and one bounded source set;
2. the artifact binds cleanly to released `V45-A` through `V45-E` descriptive
   surfaces over one explicit operational snapshot identity for `V45-B`, `V45-D`, and
   `V45-E`, plus explicit snapshot-validity and artifact-local source-scope
   compatibility for `V45-A` and `V45-C`;
3. every row preserves explicit distinction between descriptive input, binding posture,
   authority source, and promotion-law requirement;
4. bounded consumer-class doctrine remains explicit and one row maps to one consumer
   class only;
5. authority source is necessary but not sufficient for normative promotion, and
   promotion-law posture is necessary but not sufficient for normative promotion;
6. no row collapses descriptive input and authority into a direct normative shortcut;
7. the frame remains non-executive and non-approving by itself;
8. source artifact refs and descriptive input refs remain resolvable and fail closed
   when malformed;
9. schema export parity and committed fixture replay pass;
10. scoped Python tests cover the released extraction/model surface.

Do not accept this slice if:

- the frame collapses descriptive evidence and normative authority into one field;
- a row collapses descriptive input, authority source, and promotion outcome into a
  direct normative shortcut;
- optimization findings are treated as self-authorizing amendment entitlement;
- `authority_source_kind` and `promotion_law_posture` can jointly imply execution
  permission without a stronger separate authority source;
- descriptive artifacts are allowed to mint recursive execution or auto-mutation;
- bound descriptive references drift across operational snapshot identity,
  snapshot-validity posture, or source-scope compatibility posture;
- `descriptive_input_ref` does not resolve against one of the bound `V45-A` through
  `V45-E` artifacts under the same snapshot-compatible baseline;
- source artifact refs are textual only and not source-set-membership checked;
- the frame is treated as an execution plan, mutation request, or approval artifact by
  itself;
- the first release widens into automatic repo mutation.

## Local Gate

- run targeted repo-description checks for the changed Python surface;
- run `make arc-start-check ARC=105` while the bundle remains docs-only;
- do not treat this starter bundle as a substitute for the Python lane once source code
  changes begin.
