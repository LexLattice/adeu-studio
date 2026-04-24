# Architecture ADEU ARC Series Cartography Family v0

Status: architecture / decomposition record for planned `V68`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V68` downstream of the current closed `V67` baseline and the
support-layer mapping in `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`.

## 1. Family Thesis

`V68` is the whole-series cartography family.

It should make the repo able to describe its current ARC lineage across:

- family names such as `V45`, `V67`, and `V68`;
- global closeout arc names such as `vNext+187`;
- slice names such as `V67-C` and `V68-A`;
- branch-local execution targets such as `arc/v67-r3`;
- schema-family names;
- closeout evidence locations;
- support and review lineage;
- evidence surface indexes;
- deferred and conditional branches.

The map must be multi-layered but unitary: the same record should separate
namespace, evidence, source status, closure posture, branch posture, and
tool-applicability without collapsing them into one prose summary.

The family must remain descriptive and planning-supportive. It does not itself
schedule, ratify, implement, release, or adopt future self-improvement changes.

## 2. Relationship To Existing Repo Description

`V45` already gives the repo descriptive surfaces for schemas, entities,
dependencies, symbols, tests, optimization seams, and descriptive/normative binding.
`V68` should consume that descriptive lineage and extend it to whole-series ARC
cartography.

`V68` should not replace:

- `repo_schema_family_registry@1`
- `repo_entity_catalog@1`
- `repo_arc_dependency_register@1`
- `repo_arc_dependency_register@2`
- `repo_symbol_catalog@1`
- `repo_test_intent_matrix@1`
- `repo_optimization_register@1`
- `repo_descriptive_normative_binding_frame@1`

Instead, it should add the family/slice/arc layer that those surfaces do not fully
own: current whole-series topology, closure state, source-status posture, branch
posture, and tool-applicability boundaries.

## 3. Core Separations

The family must keep these lanes distinct.

| Lane | Question | Forbidden collapse |
|---|---|---|
| Namespace | Which family, slice, implementation arc, closeout arc, branch target, schema, fixture, or evidence surface is being referenced? | Treating `V67`, `vNext+187`, `vnext_plus187`, and `arc/v67-r3` as interchangeable |
| Source status | Was a source integrated, available, pending, rejected, or superseded? | Treating mentioned feedback as admitted evidence |
| Closure posture | Is the family/slice closed, open, deferred, superseded, not selected, or in need of review? | Inferring closure from stale prose |
| Evidence posture | What evidence supports which claim horizon? | Treating tests, closeout notes, support docs, or tool passes as global authority |
| Tool applicability | Which tool result applies to which namespace and claim? | Treating local tool success as all-family proof |
| Future seam posture | What is tracked but not selected or authorized? | Letting deferred seams disappear or become implicit authority |

## 4. Source-Status Law

The family must represent review and support inputs without laundering them.

Minimum source-status vocabulary:

- `integrated_shaping_source`
- `available_but_not_integrated`
- `review_pending_input`
- `rejected_or_superseded_source`

This is required even when review artifacts are present. The GPTPro feedback
artifacts are now captured as support-layer shaping evidence, while future review
inputs may still be available-but-not-integrated, pending, rejected, or superseded.
The correct architectural response is to make source-status posture first-class
rather than infer admission from conversation.

## 5. Family Surfaces

The family-level starter target set should be:

| Surface | Role |
|---|---|
| `repo_arc_series_cartography@1` | unitary top-level ARC map with source set, namespace rows, family rows, future seams, and evidence joins |
| `repo_arc_namespace_map@1` | explicit family / slice / implementation arc / closeout arc / fixture / branch / schema namespace disambiguation |
| `repo_family_closure_register@1` | closure and selection posture for family and slice rows |
| `repo_branch_posture_register@1` | connected, deferred, conditional, superseded, or not-selected branch posture |
| `repo_support_lineage_register@1` | support-doc, review-input, and shaping-source lineage with source-status posture |
| `repo_evidence_surface_index@1` | closeout, fixture, test, tool, and support evidence surfaces with claim horizons |
| `repo_arc_mapping_tool_applicability_report@1` | claims about which repo tools apply to which cartography checks |
| `repo_recursive_coordinate_emission_plan@1` | bounded plan for how later families may consume coordinates without treating map output as authority |

`V68-A` should ship these as schema/model/validator surfaces and bounded reference
fixtures, not as a complete automatic cartography engine.

## 6. Namespace Posture

The namespace map must use a tight namespace-kind vocabulary. Source kind and source
authority layer are source-row fields, not namespace kinds.

Minimum namespace kinds:

- `selector_version`
- `family_id`
- `family_slice_id`
- `implementation_arc_id`
- `closeout_arc_id`
- `evidence_arc_id`
- `branch_local_execution_target`
- `planning_doc_ref`
- `lock_doc_ref`
- `decision_doc_ref`
- `assessment_doc_ref`
- `architecture_doc_ref`
- `support_doc_ref`
- `schema_id`
- `fixture_dir_ref`
- `evidence_input_ref`
- `stop_gate_ref`

It should reject rows that depend only on string resemblance.

Examples:

- `V67` is a family.
- `V67-C` is a slice.
- `vNext+187` is a closeout / implementation arc lane, depending on the row's
  declared namespace kind.
- `vnext_plus187` is a fixture directory naming convention.
- `arc/v67-r3` is a branch-local execution target.

Those may be related, but they are not the same identity.

## 7. Closure And Branch Posture

Closure posture and branch posture are separate vocabularies.

Minimum closure posture:

- `closed_on_main`
- `open_in_progress`
- `planned_not_started`
- `deferred_to_later_family`
- `superseded_by_alternate_surface`
- `not_selected_yet`
- `unknown_needs_review`

Minimum branch posture:

- `connected_conditional_branch`
- `deferred_branch`
- `selected_branch`
- `superseded_branch`
- `not_selected_branch`
- `review_required_branch`

`V68` must represent `V43` as a connected conditional branch unless a later planning
draft selects external-world contest participation as immediate pressure.

## 7.1 Shared Row Vocabulary

`V68-A` should avoid eight independent object families with duplicated semantics.
The implementation should define one shared internal row vocabulary and expose the
schema surfaces as bounded views over that vocabulary.

Minimum source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `integration_note`

Minimum namespace row fields:

- `namespace_ref`
- `namespace_kind`
- `canonical_label`
- `source_refs`
- `equivalence_posture`

Minimum family row fields:

- `family_ref`
- `family_id`
- `family_slice_id`
- `closure_posture`
- `selected_by_refs`
- `closeout_evidence_refs`

Minimum branch row fields:

- `branch_ref`
- `branch_family_id`
- `branch_posture`
- `selection_condition`
- `source_refs`

Minimum evidence surface row fields:

- `evidence_ref`
- `evidence_kind`
- `claim_horizon`
- `source_refs`
- `limitation_note`

Minimum tool applicability row fields:

- `tool_id`
- `target_claim_id`
- `target_namespace_kind`
- `applicability_posture`
- `observed_result_ref`
- `limitation_note`

Minimum coordinate plan row fields:

- `coordinate_ref`
- `coordinate_posture`
- `target_refs`
- `non_authority_guardrail`

## 8. Tool-Applicability Posture

The family must record tool applicability as evidence about a tool result, not as
authority over the mapped object.

Minimum tool-result posture:

- `applicable_and_supporting`
- `applicable_with_warnings`
- `namespace_limited`
- `not_applicable_to_claim`
- `failed_or_inconclusive`
- `not_run`

The prior support pass exposed why this matters: `make arc-closeout-check ARC=67`
can validate a specific `ARC=67` closeout-tool namespace, while a human may be
asking about family `V67`. A cartography map that cannot record that mismatch is
unsafe.

## 9. Family Slices

### 9.1 `V68-A`

Bounded schema-and-validator starter only.

Owns:

- the eight starter surfaces above;
- source-status and namespace enums;
- closure and branch posture enums;
- tool-applicability posture enums;
- evidence surface and support lineage row shapes;
- source-ref validation and canonical row ordering;
- reference and reject fixtures for the current post-`V67` baseline.

Does not own:

- automatic derivation over the full repo;
- recursive candidate admission;
- conceptual-diff schema adoption;
- quality classification;
- ratification;
- commit / merge / release authority;
- product UI projection.

### 9.2 `V68-B`

Deterministic repo-derived cartography and gap scan.

May own:

- derivation from current planning, lock, decision, assessment, architecture,
  support, fixture, schema, and closeout artifact locations;
- gap rows for missing closure posture, stale refs, namespace ambiguity, and
  unresolved branch posture;
- human-review-required rows for ambiguous derivations.

Does not own ratification or adoption.

### 9.3 `V68-C`

Tool-applicability and recursive-coordinate emission planning.

May own:

- a populated applicability report for existing repo tools against cartography
  claims;
- a coordinate emission plan that future `V69` through `V75` families may consume.

Does not own future-family execution.

## 10. Negative Laws

`V68` must preserve these laws:

- map output is not scheduling authority;
- source mention is not source admission;
- feedback reference is not evidence when the artifact is absent;
- closeout evidence is not authority outside its closed target;
- tool success is not authority beyond declared applicability;
- support-layer synthesis is not lock-level authorization;
- branch posture is not selection;
- product projection is not product authorization;
- recursive-coordinate emission is not recursive candidate admission.
