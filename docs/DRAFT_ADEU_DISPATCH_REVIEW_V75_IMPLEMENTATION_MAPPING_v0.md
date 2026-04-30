# Draft ADEU Dispatch Review V75 Implementation Mapping v0

Status: support / implementation mapping record for planned `V75`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V75` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is drafted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v65.md`
- `docs/ARCHITECTURE_ADEU_DISPATCH_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75C_IMPLEMENTATION_MAPPING_v0.md`

## 1. Family Intent

`V75` should add dispatch-review and multi-worker orchestration-posture records
without turning them into:

- worker assignment or dispatch;
- command execution;
- runtime permission;
- PR, commit, merge, release, or released truth;
- product authorization;
- external contest participation;
- benchmark truth or model selection;
- recursive policy amendment.

The implementation target is a typed dispatch-review family that can represent:

- source-bound dispatch-review requests over released `V74-C` substrate;
- dispatch source rows and explicit source absence posture;
- non-execution guardrails for review requests;
- worker role capacity profiles;
- multi-worker assignment plans without execution;
- worker IO contracts and output authority posture;
- worker tool-applicability matrices;
- dispatch exception registers;
- worker-output reconciliation plans;
- dispatch reconciliation contracts;
- post-dispatch-review handoff rows;
- dispatch-review family closeout alignment without selecting runtime,
  product, external, release, or recursive-policy authority.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded dispatch-review records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus209/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative: `V75` still describes repo/corpus metadata
and dispatch-review state. If a later slice tries to become live command
execution, runtime permissioning, worker dispatch, product UI, external contest
automation, or release automation, that work should split away instead of
expanding `adeu_repo_description` by implication.

The proposed `repo_*` schemas are repo-description dispatch-review surfaces,
not live runtime, product, worker-execution, release, or ARC challenge
artifacts.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/dispatch_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_dispatch_review_v75a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_dispatch_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_dispatch_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_dispatch_non_execution_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_worker_role_capacity_profile.v1.json`
- `packages/adeu_repo_description/schema/repo_multi_worker_assignment_plan.v1.json`
- `packages/adeu_repo_description/schema/repo_worker_io_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_worker_tool_applicability_matrix.v1.json`
- `packages/adeu_repo_description/schema/repo_dispatch_exception_register.v1.json`
- `packages/adeu_repo_description/schema/repo_worker_output_reconciliation_plan.v1.json`
- `packages/adeu_repo_description/schema/repo_dispatch_reconciliation_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_post_dispatch_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_dispatch_review_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_dispatch_review_request.schema.json`
- `spec/repo_dispatch_source_index.schema.json`
- `spec/repo_dispatch_non_execution_guardrail.schema.json`
- `spec/repo_worker_role_capacity_profile.schema.json`
- `spec/repo_multi_worker_assignment_plan.schema.json`
- `spec/repo_worker_io_contract.schema.json`
- `spec/repo_worker_tool_applicability_matrix.schema.json`
- `spec/repo_dispatch_exception_register.schema.json`
- `spec/repo_worker_output_reconciliation_plan.schema.json`
- `spec/repo_dispatch_reconciliation_contract.schema.json`
- `spec/repo_post_dispatch_review_handoff.schema.json`
- `spec/repo_dispatch_review_family_closeout_alignment.schema.json`

## 3. Candidate `V75` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_dispatch_review_request@1` | `V75-A` | top-level dispatch-review request rows over released `V74-C` substrate |
| `repo_dispatch_source_index@1` | `V75-A` | source rows for dispatch review, absence posture, and source roles |
| `repo_dispatch_non_execution_guardrail@1` | `V75-A` | non-assignment, non-command, non-runtime, non-product, non-release, and non-external guardrails |
| `repo_worker_role_capacity_profile@1` | `V75-B` | worker role / capability posture without authority grant |
| `repo_multi_worker_assignment_plan@1` | `V75-B` | assignment planning without dispatch or execution |
| `repo_worker_io_contract@1` | `V75-B` | worker input / output contract and output authority posture |
| `repo_worker_tool_applicability_matrix@1` | `V75-B` | target-bound and horizon-bound tool applicability |
| `repo_dispatch_exception_register@1` | `V75-B` | orchestration blockers, authority gaps, and source gaps |
| `repo_worker_output_reconciliation_plan@1` | `V75-C` | projected or observed worker-output reconciliation posture |
| `repo_dispatch_reconciliation_contract@1` | `V75-C` | required reconciliation roles, authority refs, and forbidden inferences |
| `repo_post_dispatch_review_handoff@1` | `V75-C` | later-review handoff after dispatch review, without claiming dispatch execution |
| `repo_dispatch_review_family_closeout_alignment@1` | `V75-C` | family closeout alignment without runtime, product, external, or release authority |

`V75-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement dispatch, worker execution,
runtime permission, or product workbenching.

## 4. Source Classes

The family should consume concrete source refs from:

- `V68` through `V73` family closeouts and family alignment artifacts as
  upstream context;
- `V74` operator projection family closeout:
  - `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v208/evidence_inputs/v74_family_closeout_alignment_v208.json`
  - `artifacts/agent_harness/v208/evidence_inputs/v74c_operator_projection_closeout_evidence_v208.json`
- `V74-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus208/repo_decision_visibility_contract_v208_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus208/repo_ratification_review_workbench_projection_v208_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus208/repo_post_projection_handoff_v208_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus208/repo_operator_projection_family_closeout_alignment_v208_reference.json`
- support lineage:
- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_POST_V74_MULTI_ARC_ROADMAP_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_DISPATCH_REVIEW_V75_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become dispatch source rows.

If any expected source is missing when the active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct dispatch-review state from planning prose.

## 5. Shared Row Vocabulary

Minimum dispatch source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `dispatch_source_role`
- `source_horizon`
- `limitation_note`

Minimum dispatch-review request row fields:

- `dispatch_request_ref`
- `candidate_ref`
- `case_view_refs`
- `visibility_contract_refs`
- `workbench_projection_refs`
- `post_projection_handoff_refs`
- `required_later_authority_refs`
- `required_later_authority_rows`
- `carried_upstream_exception_refs`
- `carried_exception_origin`
- `dispatch_review_posture`
- `requested_orchestration_horizon`
- `odeu_lanes`
- `guardrail_refs`
- `limitation_note`

Eligibility rows must distinguish context from eligibility. Support docs,
roadmaps, and review notes may appear in the source index, but
`eligible_for_dispatch_review` requires concrete released `V74-C` handoff,
visibility-contract, and workbench-projection sources.

Minimum required later-authority row fields:

- `authority_requirement_ref`
- `candidate_ref`
- `authority_kind`
- `required_before_surface`
- `source_refs`
- `source_presence_posture`
- `authority_gap_posture`
- `limitation_note`

Minimum carried exception origin:

- `v74_exception_visibility`
- `v74_visibility_contract`
- `v74_post_projection_handoff`
- `absence_marker`

Minimum non-execution guardrail row fields:

- `guardrail_ref`
- `candidate_ref`
- `dispatch_request_refs`
- `forbidden_action_kinds`
- `allowed_next_review_surfaces`
- `non_execution_guardrail`
- `limitation_note`

Minimum worker planning row families:

- worker role capacity rows;
- assignment plan rows;
- worker IO contract rows;
- worker tool applicability rows;
- dispatch exception rows.

Minimum reconciliation row families:

- worker output reconciliation plan rows;
- output relation rows;
- dispatch reconciliation contract rows;
- post-dispatch-review handoff rows;
- family closeout alignment rows.

## 6. Validation Themes

Expected validators should enforce:

- all request, plan, IO, tool, exception, reconciliation, and handoff refs
  resolve locally or through explicit source rows;
- absence is represented as source posture, not prose memory;
- `odeu_lanes` are sorted and non-empty where required;
- `V75-A` cannot assign workers, run commands, or select runtime / product /
  release / external authority;
- `V75-B` cannot treat role, assignment, IO, or tool rows as execution;
- `V75-C` cannot claim dispatch execution occurred;
- worker output cannot be truth without later reconciliation and authority;
- product, runtime, external, and release pressure remain blocked or
  future-family-only unless later families select them.

Name hygiene: `V75` intentionally supersedes earlier roadmap placeholder names
that could imply execution or observed outputs. Use
`repo_worker_output_reconciliation_plan@1` and
`repo_post_dispatch_review_handoff@1` in locks and schemas.

## 7. First Fixture Strategy

The first `V75-A` reference fixture should be deliberately narrow:

- one source index over released `V74-C` visibility, workbench, handoff, closeout,
  dogfood, and family closeout sources;
- one eligible dispatch-review request for the self-evidencing workflow-type
  emergence candidate carried by the `V74-C` handoff;
- one blocked or future-family-only product-pressure row if needed to prove
  product pressure does not become dispatch;
- one non-execution guardrail with all forbidden action kinds represented;
- zero worker assignment rows, runtime command rows, product authorization rows,
  external contest rows, PR / merge / release rows, or recursive policy
  amendment rows.

## 8. Future Closeout Expectation

At `V75` family closeout, the repo should be able to say:

- dispatch-review requests are source-bound and non-executing;
- worker orchestration planning is typed but did not execute;
- worker-output reconciliation is represented without making outputs truth;
- later runtime, product, external, experiment, graph, or cross-corpus pressure
  is handed forward as review pressure only;
- `V75` closed without granting dispatch, runtime, product, release, external,
  benchmark, model-selection, or recursive-policy authority.
