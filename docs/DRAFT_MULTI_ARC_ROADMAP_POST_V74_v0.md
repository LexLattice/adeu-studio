# Draft Multi-Arc Roadmap Post V74 v0

Status: planning roadmap after `V74` closed on `main` through `vNext+208`,
after the combined `V68` through `V74` dogfood probe, and before any
`DRAFT_NEXT_ARC_OPTIONS_v65.md` selector has been drafted.

Authority layer: planning.

This roadmap records the current best anticipated post-`V74` territory. It is a
supporting sequence note for the next family selector, not a selector, lock,
starter bundle, implementation authority, runtime authority, product authority,
or release authority.

Interpretive doctrine for this planning surface:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`, `deferred`,
  and `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and
  absence-of-authorization statements for this roadmap, not lock-equivalent
  permanent prohibitions by themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`;
- internal family sequencing should follow
  `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`: one family-level
  `DRAFT_NEXT_ARC_OPTIONS_v*` selector per family, then per-slice
  `vNext+<n>` starter bundles.

## Current Frontier

- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- `V73` is closed on `main` as the candidate outcome-review family.
- `V74` is closed on `main` as the operator-projection family.
- latest closed implementation arc: `vNext+208`
- latest family-level selector: `docs/DRAFT_NEXT_ARC_OPTIONS_v64.md`
- no `docs/DRAFT_NEXT_ARC_OPTIONS_v65.md` is present at this roadmap point.

The current combined dogfood probe is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.json`

The probe says the closed families compose in this direction:

```text
V68 map substrate
  -> V69 source-bound candidate pressure
  -> V70 evidence / adversarial / gap classification
  -> V70 pre-ratification handoff
  -> V71 request / settlement / ratification-review / handoff
  -> V72 containment plan / trial / effect / rollback / authority posture
  -> V73 outcome entry / observation / regression / tool-fitness / ledger
  -> V74 operator projection / typed case view / comparison / visibility / handoff
  -> V75 dispatch / orchestration pressure
```

The `V74` family closeout explicitly leaves `V75` as later review pressure. It
does not select dispatch, worker assignment, runtime permission, product
authorization, release, external contest participation, model selection,
benchmark truth, or recursive policy amendment.

## Roadmap Thesis

The post-`V74` territory should be mapped as a widening cone from operator
projection into governed action review.

The immediate pressure is not "turn on agents." The immediate pressure is:

```text
source-bound projected case state
  -> dispatch-review request
  -> worker / tool / assignment / exception posture
  -> reconciliation contract
  -> later runtime, product, external, or experiment authority review
```

`V75` should therefore be framed as dispatch-review and multi-worker
orchestration posture. It should type the conditions under which dispatch could
be reviewed, planned, constrained, and reconciled later. It should not perform
runtime dispatch or worker execution.

Beyond `V75`, the roadmap should stay banded rather than pre-authorizing a long
chain of exact family numbers. The likely bands are:

- worker-output reconciliation and arbiter hardening;
- runtime permission and action-effect envelopes;
- productized typed-adjudication reporting / workbench posture;
- controlled self-improvement experiment design;
- external-world / `V43` branch activation;
- cross-corpus governance;
- living decision graph / queryable case memory.

Those bands can receive candidate labels below so reviewers can reason about
sequence, but this roadmap does not select them.

## Roadmap Operating Model: Territory Graph, Not Queue

This roadmap should be read as a territory graph, not a pre-authorized queue.

`V75` is the recommended next selector target because `V74-C` leaves
dispatch-review pressure as the nearest untyped handoff. Candidate labels after
`V75` are planning handles only. They may be merged, split, reordered, deferred,
or renamed after `V75` emits concrete source-bound rows.

A future band becomes selector-ready only when at least one released upstream
surface emits all of the following:

- a concrete source-bound pressure row;
- a named missing or blocked authority surface;
- a carried-forward exception, gap, handoff, or recommendation;
- an explicit non-authority guardrail;
- a reason why the pressure cannot be handled inside the already selected
  family.

Minimum band posture values:

- `mapped_not_selected`
- `selector_ready_candidate`
- `blocked_pending_source`
- `blocked_pending_authority`
- `conditional_branch`
- `merge_candidate`
- `split_candidate`
- `superseded_by_later_evidence`

The roadmap may recommend a likely next family, but only a future
`DRAFT_NEXT_ARC_OPTIONS_v*` selector may select it.

## Cross-Family Anti-Drift Rules

These rules are the main reasons to keep `V75` review-only and to split later
territories:

- a dispatch-review request is not dispatch;
- an assignment plan is not worker execution;
- a worker role profile is not a worker authority grant;
- worker output is not truth;
- model output is not benchmark truth or global model selection;
- a tool pass is not scope expansion;
- tool applicability remains target-bound and horizon-bound;
- an operator click or workbench affordance is not authorization;
- runtime permission requires a later authority surface;
- commit, PR update, merge, release, and released truth require their own
  authority posture;
- product pressure and product legibility are not product authorization;
- external contest participation remains a connected conditional branch, not a
  side effect of orchestration planning;
- self-improvement outcome and promotion recommendation are not self-approval;
- living memory or graph traversal is not authority by itself.

## Anticipated Family And Band Shape

| Candidate | Theme | Likely lane ladder | Current posture |
|---|---|---|---|
| `V75` | dispatch-review / multi-worker orchestration posture | `V75-A` dispatch-review request / source index / non-execution guardrail; `V75-B` worker role, assignment-plan, IO, tool-applicability, and dispatch-exception posture; `V75-C` worker-output reconciliation plan, dispatch reconciliation contract, post-dispatch-review handoff, and family closeout alignment | recommended next family candidate, not selected until `DRAFT_NEXT_ARC_OPTIONS_v65.md` |
| `V76` candidate band | reconciliation / arbiter hardening beyond starter dispatch posture | worker-output claim mapping; arbiter relation register; dissent / complementarity preservation; model-output comparison continuation | prepared band, not selected |
| `V77` candidate band | runtime permission and action-effect envelopes | runtime permission request; command preflight contract; action effect envelope; telemetry and rollback contract | prepared band, not selected |
| `V78` candidate band | productized typed adjudication and read-only report surfaces | typed adjudication report export; fixed-substrate model comparison report; authority-risk / exception report; product workbench review boundary | product band, not selected |
| `V79` candidate band | controlled self-improvement experiments | experiment design; longitudinal outcome comparison; recursive policy amendment request; experiment-to-review handoff | experiment band, not selected |
| `V80` candidate band | external-world / `V43` branch activation | external contest eligibility; data/tool/submission authority; result provenance; withdrawal posture | connected conditional branch band, not selected |
| `V81` candidate band | cross-corpus governance | corpus cartography; imported-substrate candidate intake; cross-repo / paper / benchmark result adjudication | generalization band, not selected |
| `V82` candidate band | living decision graph / queryable case memory | candidate graph; source graph; authority graph; evidence graph; exception graph; handoff graph; outcome graph; projection graph | memory / traversal band, not selected |

The candidate labels after `V75` are planning placeholders. A later selector may
merge, split, reorder, or rename them after `V75` produces concrete evidence.

## Band Dependency And Reordering Logic

The roadmap should not assume `V76` through `V82` must occur in numeric order.
The labels are handles for reasoning about territory.

| Evidence emitted upstream | Selector-ready candidate | Reason |
|---|---|---|
| `V74-C` post-projection handoff carries `v75_dispatch_review` | `V75` | dispatch review is the nearest untyped handoff after operator projection |
| `V75-C` carries unresolved worker-output relation gaps | `V76` reconciliation / arbiter band | worker outputs or projected output slots need claim-level reconciliation |
| `V75` or `V76` emits a bounded command / action need with authority blockers | `V77` runtime permission band | execution requires permission, preflight, telemetry, and rollback envelopes |
| `V74` or `V75` preserves product-pressure cases without product authority | `V78` product typed-adjudication band | read-only product reports can be typed before live product authority |
| `V73` or `V75` emits recurring improvement claims needing longitudinal proof | `V79` experiment band | self-improvement claims need experiment design and comparison |
| A concrete external contest / external-world objective appears | `V80` or `V43` branch band | external participation requires data, tool, submission, provenance, and withdrawal authority |
| Non-repo corpora become first-class inputs | `V81` cross-corpus band | imported substrates need their own cartography and authority boundaries |
| Row volume / case reuse makes manual traversal brittle | `V82` living decision graph band | memory and query layers become useful, but remain non-authority |

`V78` read-only report surfaces may become selector-ready before `V77` runtime
permission if the pressure is product legibility rather than execution.

`V82` graph / memory work may become selector-ready earlier than its label if
the repo needs navigation over already emitted rows before runtime or product
widening.

## Immediate `V75` Candidate Shape

Recommended family name for the next selector:

```text
V75: dispatch-review, multi-worker orchestration posture,
worker-output reconciliation, and non-execution guardrails
```

Recommended family thesis:

`V75` may review dispatch and multi-worker orchestration pressure emitted by
`V74`, but it must not perform runtime dispatch, worker execution, product
authorization, release, external contest participation, or recursive
self-approval.

### `V75` Entry Criteria

`V75` is selector-ready when the future `DRAFT_NEXT_ARC_OPTIONS_v65.md` can
cite concrete released `V74-C` rows showing:

- at least one `repo_post_projection_handoff@1` row carrying
  `v75_dispatch_review` or equivalent later-dispatch-review pressure;
- a decision visibility contract for the case;
- a ratification-review workbench projection row that permits review-only
  operator action;
- visible carried exceptions, or an explicit checked absence of carried
  exceptions;
- required later authority rows for any runtime, product, release, external, or
  dispatch-sensitive action;
- non-dispatch / non-execution guardrails.

Roadmap and support-review sources may contextualize `V75`, but they cannot by
themselves make a dispatch-review request eligible. Eligibility requires
concrete released `V74-C` handoff, visibility-contract, workbench-projection,
exception / checked-absence, later-authority, and non-dispatch guardrail
substrate.

`V75` is not selector-ready if the only evidence is:

- operator desire to "turn on agents";
- a model suggestion without source-bound `V74-C` handoff;
- an unresolved product-authority gap being smuggled in as dispatch pressure;
- an external contest objective without `V43` / external-world branch posture;
- a runtime command request without a later runtime permission surface;
- a worker-output comparison that lacks model-output provenance or
  benchmark-truth guardrails.

### `V75` Non-Entry Criteria

`V75` must not be used to select:

- runtime command execution;
- actual worker assignment;
- product launch or product authorization;
- external contest participation;
- PR creation, commit, merge, release, or released truth;
- recursive policy amendment;
- global model selection;
- benchmark truth.

Recommended `V75-A` starter surfaces:

- `repo_dispatch_review_request@1`
- `repo_dispatch_source_index@1`
- `repo_dispatch_non_execution_guardrail@1`

`V75-A` should consume released `V74-C` post-projection handoff rows,
visibility contracts, ratification-review workbench projection rows, carried
exceptions, required later authority rows, and non-dispatch guardrails. It
should create dispatch-review request rows only.

`V75-A` should not assign workers, run commands, grant runtime permission,
open PRs, merge, release, productize, participate in external contests, or
claim a recursive policy amendment.

Recommended `V75-B` surfaces:

- `repo_worker_role_capacity_profile@1`
- `repo_multi_worker_assignment_plan@1`
- `repo_worker_io_contract@1`
- `repo_worker_tool_applicability_matrix@1`
- `repo_dispatch_exception_register@1`

`V75-B` should describe role / capacity / assignment / IO / tool-applicability
and exception posture without executing the plan. It may say which worker roles
would be needed, which inputs and outputs are required, which tools apply to
which claim horizons, and which exceptions block orchestration.

`V75-B` should not treat an assignment plan as dispatch, a role profile as
permission, a tool as globally applicable, or an operator-facing projection as
worker authority.

Recommended `V75-C` surfaces:

- `repo_worker_output_reconciliation_plan@1`
- `repo_dispatch_reconciliation_contract@1`
- `repo_post_dispatch_review_handoff@1`
- `repo_dispatch_review_family_closeout_alignment@1`

`V75-C` should define how worker outputs or projected worker-output slots would
be reconciled if a later family or active runtime authority executes dispatch.
It may request later outcome review, runtime permission review, product review,
external branch review, or future-family review. It should not treat worker
output as truth or declare that dispatch execution occurred.

### `V75-A` Deeper Starter Shape

`V75-A` should create dispatch-review request posture only.

Suggested embedded row sets:

- dispatch source rows:
  - `source_ref`
  - `source_kind`
  - `authority_layer`
  - `source_status`
  - `source_presence_posture`
  - `dispatch_source_role`
  - `source_horizon`
  - `limitation_note`
- dispatch-review request rows:
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
- non-execution guardrail rows:
  - `guardrail_ref`
  - `candidate_ref`
  - `dispatch_request_refs`
  - `forbidden_action_kinds`
  - `allowed_next_review_surfaces`
  - `non_execution_guardrail`
  - `limitation_note`

Minimum `dispatch_source_role` values:

- `v74_post_projection_handoff_source`
- `visibility_contract_source`
- `workbench_projection_source`
- `exception_visibility_source`
- `required_later_authority_source`
- `non_dispatch_guardrail_source`
- `combined_dogfood_source`
- `family_closeout_source`
- `absence_marker`

Minimum `carried_exception_origin` values:

- `v74_exception_visibility`
- `v74_visibility_contract`
- `v74_post_projection_handoff`
- `absence_marker`

Minimum `dispatch_review_posture` values:

- `eligible_for_dispatch_review`
- `blocked_by_missing_projection_source`
- `blocked_by_unresolved_exception`
- `blocked_by_required_later_authority`
- `blocked_by_product_authority_gap`
- `blocked_by_runtime_authority_gap`
- `blocked_by_external_branch_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Minimum `forbidden_action_kinds` values:

- `assign_worker_now`
- `run_command_now`
- `open_pr_now`
- `commit_now`
- `merge_now`
- `release_now`
- `authorize_product_now`
- `grant_runtime_permission_now`
- `enter_external_contest_now`
- `self_approve_now`

Mandatory `V75-A` rejects:

- dispatch request without concrete source refs or explicit absence rows;
- request that assigns workers in `V75-A`;
- request that carries a command to run;
- request that treats a workbench action as authorization;
- request that routes product pressure into dispatch without product-authority
  blocker;
- request that routes external contest pressure into dispatch without `V43`
  branch posture;
- request with empty non-execution guardrails.

### `V75-B` Deeper Orchestration-Planning Shape

`V75-B` should plan worker / role / tool / IO posture without executing it.

Suggested row sets:

- worker role capacity profile:
  - `worker_role_ref`
  - `role_kind`
  - `capability_horizon`
  - `allowed_input_kinds`
  - `expected_output_kinds`
  - `allowed_tool_ids`
  - `tool_use_posture`
  - `forbidden_action_kinds`
  - `authority_boundary_refs`
  - `limitation_note`
- assignment plan:
  - `assignment_plan_ref`
  - `dispatch_request_refs`
  - `worker_role_refs`
  - `io_contract_refs`
  - `tool_applicability_refs`
  - `exception_refs`
  - `assignment_plan_posture`
  - `assignment_execution_posture`
  - `non_execution_guardrail_refs`
  - `limitation_note`
- worker IO contract:
  - `io_contract_ref`
  - `worker_role_refs`
  - `input_source_refs`
  - `input_claim_horizon`
  - `expected_output_kind`
  - `output_schema_ref`
  - `output_authority_posture`
  - `non_truth_guardrail`
  - `limitation_note`
- worker tool applicability matrix:
  - `tool_matrix_ref`
  - `worker_role_refs`
  - `tool_id`
  - `target_claim_refs`
  - `target_namespace_kind`
  - `claim_horizon`
  - `applicability_posture`
  - `observed_or_required_result_refs`
  - `limitation_note`

A worker role is a capability profile, not a worker authority grant.

Minimum `role_kind` values:

- `source_index_worker`
- `evidence_review_worker`
- `adversarial_review_worker`
- `schema_validation_worker`
- `tool_run_worker`
- `reconciliation_worker`
- `operator_projection_worker`
- `external_branch_review_worker`

Minimum `assignment_plan_posture` values:

- `plan_ready_for_review`
- `blocked_by_missing_role_profile`
- `blocked_by_missing_io_contract`
- `blocked_by_tool_applicability_gap`
- `blocked_by_unresolved_exception`
- `blocked_by_later_authority`
- `future_family_only`
- `rejected_out_of_scope`

Minimum `assignment_execution_posture` values:

- `no_execution_authorized`
- `review_plan_only`
- `blocked_pending_later_authority`

Minimum `output_authority_posture` values:

- `output_for_review_only`
- `output_requires_reconciliation`
- `output_requires_adversarial_review`
- `output_requires_human_ratification`
- `output_not_truth`

Minimum `tool_use_posture` values:

- `applicability_record_only`
- `tool_use_requires_later_runtime_permission`
- `tool_use_not_authorized_by_v75`

Mandatory `V75-B` rejects:

- assignment plan treated as execution;
- role profile treated as permission;
- IO output treated as truth;
- tool applicability treated as global;
- plan missing exception refs when upstream exceptions exist;
- plan missing required later authority refs;
- plan that assigns external contest work without `V43` branch posture.

### `V75-C` Deeper Reconciliation-Contract Shape

`V75-C` should define reconciliation posture for worker outputs or projected
worker-output slots. It should not require that dispatch execution happened.

Suggested row sets:

- worker output reconciliation plan:
  - `reconciliation_plan_ref`
  - `dispatch_request_refs`
  - `assignment_plan_refs`
  - `io_contract_refs`
  - `projected_output_slot_refs`
  - `observed_worker_output_refs`
  - `output_presence_posture`
  - `dispatch_execution_posture`
  - `relation_rows`
  - `exception_refs`
  - `non_truth_guardrail`
  - `limitation_note`
- relation rows:
  - `relation_ref`
  - `left_output_ref`
  - `right_output_ref`
  - `claim_horizon`
  - `relation_kind`
  - `source_refs`
  - `authority_boundary_posture`
  - `required_next_review_surface`
  - `limitation_note`
- dispatch reconciliation contract:
  - `contract_ref`
  - `reconciliation_plan_refs`
  - `required_review_roles`
  - `required_authority_refs`
  - `allowed_settlement_postures`
  - `forbidden_inferences`
  - `handoff_refs`
  - `limitation_note`

Minimum `output_presence_posture` values:

- `projected_not_observed`
- `observed_from_authorized_prior_run`
- `observed_from_support_artifact`
- `missing_expected_output`
- `not_applicable`

Minimum `dispatch_execution_posture` value:

- `no_dispatch_executed_by_v75`

Minimum `relation_kind` values:

- `conflict`
- `complementarity`
- `duplicate`
- `orthogonal`
- `unclear_relation`
- `single_output_no_relation`

Minimum `forbidden_inferences` values:

- `worker_output_as_truth`
- `model_output_as_benchmark_truth`
- `tool_pass_as_scope_expansion`
- `assignment_plan_as_execution`
- `dispatch_review_as_runtime_permission`

Mandatory `V75-C` rejects:

- reconciliation row that treats worker output as truth;
- relation row without source refs or explicit absence posture;
- post-dispatch-review handoff that claims dispatch execution occurred;
- handoff to runtime execution while blocking exceptions remain;
- handoff to product authorization without product authority;
- handoff to external contest participation without `V43` branch activation.

## Post-`V75` Band Notes

### Reconciliation And Arbiter Band

If `V75-C` can only define starter reconciliation contracts, a follow-on band
may need to harden arbitration over actual worker / model outputs. That band
would ask:

- what claim horizon each output addresses;
- which source rows each output cites;
- which authority boundary each output preserves or violates;
- which differences are conflicts, complementarity, duplication, or orthogonal
  work;
- which outputs need adversarial review;
- which outputs are useful but non-authoritative.

This band should reuse `V70` review machinery and `V74` model-output comparison
projection without turning comparison into benchmark truth.

Trigger:

- `V75-C` emits worker-output or projected-output relation rows that cannot be
  settled by a simple dispatch-review contract;
- model-output comparison, worker-output comparison, or adversarial review
  produces unresolved conflict / complementarity / duplication / orthogonality
  posture;
- a later selector needs arbiter roles without treating arbiter output as
  truth.

Possible starter surfaces:

- `repo_worker_output_claim_map@1`
- `repo_arbiter_relation_register@1`
- `repo_reconciliation_dissent_register@1`

Later surfaces:

- `repo_arbiter_authority_profile@1`
- `repo_reconciliation_settlement_request@1`
- `repo_reconciliation_to_review_handoff@1`

Negative laws:

- arbiter output is not truth;
- reconciliation is not ratification unless a later authority surface says so;
- model-output comparison is not benchmark truth;
- majority worker agreement is not correctness;
- dissent preservation is not failure by itself.

### Runtime And Effect-Envelope Band

After dispatch review and reconciliation are typed, the repo can consider
controlled runtime / action envelopes:

- what command may run;
- under which lock or authority source;
- with which target boundary;
- with which rollback posture;
- with which effect telemetry;
- with which human or maintainer authority;
- with which failure containment.

This band should start with permission requests and preflight contracts, not
autonomous execution. It should consume `V72` contained-integration
distinctions: plan, trial, effect, rollback, commit intent, merge truth, and
released truth are separate.

Trigger:

- `V75` or the reconciliation band emits a concrete need for command execution,
  tool execution, or runtime action;
- the action has a bounded target, rollback posture, expected telemetry, and
  human / maintainer authority requirement;
- execution cannot be represented as dispatch review alone.

Possible starter surfaces:

- `repo_runtime_permission_request@1`
- `repo_runtime_source_index@1`
- `repo_runtime_non_execution_guardrail@1`

Later surfaces:

- `repo_command_preflight_contract@1`
- `repo_action_effect_envelope@1`
- `repo_effect_telemetry_record@1`
- `repo_runtime_rollback_contract@1`
- `repo_runtime_to_outcome_review_handoff@1`

Negative laws:

- runtime permission request is not execution;
- preflight pass is not release truth;
- command success is not merge or product authority;
- telemetry is not outcome success without review;
- rollback prose is not rollback verification.

### Product And Typed-Adjudication Band

`V74` made the typed-adjudication product wedge visible without authorizing
productization. A later product band should be read-only first:

- typed adjudication report export;
- fixed-substrate model-output comparison report;
- authority-risk / exception report;
- next-slice recommendation report;
- operator-facing review workbench boundary.

Only a later authority surface should consider live UI, customer substrate
ingestion, paid product workflows, product-market validation, or product
authorization.

Trigger:

- `V74` or `V75` keeps surfacing product-pressure cases;
- the operator needs exportable, read-only typed adjudication reports;
- cross-model or cross-artifact comparison is valuable, but product authority is
  still absent.

Possible starter surfaces:

- `repo_typed_adjudication_report_export_plan@1`
- `repo_product_projection_source_index@1`
- `repo_product_non_authority_guardrail@1`

Later surfaces:

- `repo_fixed_substrate_model_comparison_report@1`
- `repo_authority_risk_exception_report@1`
- `repo_next_slice_recommendation_report@1`
- `repo_product_workbench_review_boundary@1`

Negative laws:

- product legibility is not product authorization;
- report export is not customer substrate ingestion;
- fixed-substrate comparison is not global model selection;
- a read-only workbench is not operator command authority.

### Self-Improvement Experiment Band

`V73` created outcome-review and recommendation machinery, but did not prove
self-improvement or grant recursive policy authority. A later experiment band
could define:

- self-improvement experiment design;
- longitudinal outcome comparison;
- recursive policy amendment request;
- experiment-to-ratification or experiment-to-outcome-review handoff.

An outcome ledger remains evidence, not self-approval. A promotion
recommendation remains a recommendation, not adoption.

Trigger:

- `V73` or `V75` emits recurring self-improvement recommendations;
- outcome ledgers show a claim worth testing longitudinally;
- recursive policy amendment pressure appears, but adoption authority is
  absent.

Possible starter surfaces:

- `repo_self_improvement_experiment_design@1`
- `repo_experiment_source_index@1`
- `repo_experiment_non_adoption_guardrail@1`

Later surfaces:

- `repo_longitudinal_outcome_comparison@1`
- `repo_experiment_regression_register@1`
- `repo_recursive_policy_amendment_request@1`
- `repo_experiment_to_ratification_handoff@1`

Negative laws:

- outcome ledger is not self-approval;
- promotion recommendation is not adoption;
- experiment success is not recursive policy amendment;
- benchmark improvement is not authority without ratification.

### External-World / `V43` Branch Band

`V43` remains a connected conditional branch. It should activate only when the
repo has explicit surfaces for:

- external contest eligibility;
- data boundary;
- tool boundary;
- submission authority;
- human / maintainer authority;
- runtime permission;
- result provenance;
- rollback or withdrawal posture.

Neither `V75` nor any dispatch-review surface should accidentally select
external contest participation.

Trigger:

- a concrete external-world objective appears;
- the repo has explicit data, tool, submission, maintainer, runtime,
  provenance, and withdrawal boundaries;
- the objective cannot remain a repo-local review or product-report case.

Possible starter surfaces:

- `repo_external_contest_eligibility_record@1`
- `repo_external_data_boundary@1`
- `repo_external_non_submission_guardrail@1`

Later surfaces:

- `repo_external_tool_boundary@1`
- `repo_submission_authority_profile@1`
- `repo_external_result_provenance@1`
- `repo_external_withdrawal_or_rollback_posture@1`

Negative laws:

- external eligibility is not submission authority;
- dispatch planning is not external participation;
- runtime permission is not submission permission;
- external result is not released truth without provenance and review.

### Cross-Corpus Governance Band

The `V68` through `V74` spine was built inside this repo, but the same typed
adjudication pattern can generalize to:

- multiple repos;
- PR diffs;
- design forks;
- papers;
- benchmark result sets;
- model-output bundles;
- agent-run traces;
- customer-provided corpora.

The cross-corpus band should preserve the same progression:

```text
cartograph corpus
  -> admit candidates
  -> classify evidence
  -> ratify review posture
  -> bound integration or recommendation
  -> observe outcome
  -> project case
  -> optionally review dispatch
```

Cross-corpus generalization should not weaken source, authority, evidence,
ratification, integration, outcome, projection, or dispatch boundaries.

Trigger:

- the same typed adjudication spine needs to operate over repos, PRs, design
  forks, papers, benchmark result sets, model-output bundles, agent traces, or
  customer-provided corpora;
- imported substrates need source, authority, and evidence boundaries distinct
  from the local repo.

Possible starter surfaces:

- `repo_or_external_corpus_cartography@1`
- `repo_imported_substrate_source_index@1`
- `repo_cross_corpus_non_authority_guardrail@1`

Later surfaces:

- `repo_imported_candidate_intake_record@1`
- `repo_cross_corpus_review_classification@1`
- `repo_cross_corpus_case_projection@1`
- `repo_cross_corpus_dispatch_review_handoff@1`

Negative laws:

- imported corpus visibility is not authority;
- customer-provided source is not automatically trusted evidence;
- cross-corpus comparison is not benchmark truth;
- product usefulness is not product authorization.

### Living Decision Graph Band

The `V68` through `V74` run produced many rows, fixtures, schemas, and closeout
artifacts. A later memory band could make those traversable through:

- candidate graph;
- source graph;
- authority graph;
- evidence graph;
- exception graph;
- handoff graph;
- outcome graph;
- operator-projection graph;
- dispatch-review graph.

Useful query examples:

- show all product-pressure candidates blocked by authority gaps;
- show all dispatch-review handoffs carrying unresolved exceptions;
- show all model-output comparisons with benchmark-truth guardrails;
- show all candidates that reached outcome review but not projection;
- show all candidates whose rollback posture blocked later handoff.

The graph should be a query and navigation substrate, not authority by itself.

Trigger:

- the emitted row volume from `V68` through `V75+` makes manual traversal
  brittle;
- repeated queries over candidates, sources, authority gaps, exceptions,
  handoffs, outcomes, and projections become review-critical;
- the repo needs navigable memory without turning memory into authority.

Possible starter surfaces:

- `repo_decision_graph_index@1`
- `repo_case_memory_source_index@1`
- `repo_graph_non_authority_guardrail@1`

Later surfaces:

- `repo_candidate_graph_view@1`
- `repo_source_authority_graph_view@1`
- `repo_exception_handoff_graph_view@1`
- `repo_outcome_projection_graph_view@1`
- `repo_dispatch_review_graph_view@1`
- `repo_graph_query_contract@1`

Negative laws:

- graph traversal is not authority;
- path existence is not causality;
- query result is not ratification;
- centrality or visibility is not priority;
- memory is not a standing operator profile.

## Roadmap Risk Register

| Risk | Why it matters | Mitigation |
|---|---|---|
| Numeric label anchoring | `V76` through `V82` may be mistaken for selected future locks | Keep `band_posture` explicit and repeat that labels are planning handles |
| `V75-C` naming implies dispatch happened | `post_dispatch` wording can weaken non-execution doctrine | Use `post_dispatch_review` naming and require `no_dispatch_executed_by_v75` |
| Assignment plan becomes execution | Worker planning can look like permission | Require non-execution guardrails and reject actual worker assignment |
| Worker output becomes truth | Multi-worker outputs can be overread as native correctness | Require reconciliation, source refs, dissent, and truth-forbidden guardrails |
| Product report becomes product authorization | Typed adjudication is commercially legible | Keep read-only report first and source-bind product authority gaps |
| Runtime preflight becomes permission | Tool / command preflight can be overread as safe execution | Separate permission request, command preflight, effect telemetry, and rollback |
| External branch sneaks in through dispatch | Orchestration language can accidentally include contest participation | Keep `V43` / external-world branch as conditional and explicit |
| Decision graph becomes authority | Graph visibility can look like governance priority | Treat graph as navigation only; authority remains in source-bound rows |

## Selection Status

- selected by this roadmap: none
- recommended next selector target: `V75`
- recommended next selector file: `docs/DRAFT_NEXT_ARC_OPTIONS_v65.md`
- recommended next implementation starter after selector / review:
  `vNext+209` for `V75-A`, assuming no intervening arc has claimed that number
- prepared but not selected bands: `V76` through `V82` candidate labels above
- connected conditional branch: `V43` external-world / contest participation
- explicitly not selected: runtime execution, product authorization, release,
  external contest participation, global model selection, benchmark truth,
  recursive policy amendment, and autonomous dispatch

## Relationship To Canonical Arc Docs

This roadmap should be read together with:

- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v64.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_POST_V74_MULTI_ARC_ROADMAP_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.json`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`

The normal concretization path remains:

1. roadmap-level anticipated sequence;
2. canonical next-family selector;
3. family architecture / implementation mapping / slice implementation specs;
4. external or joint review of the family and slice ladder;
5. per-slice canonical starter bundle;
6. implementation PR;
7. lean slice closeout after merge;
8. full family closeout after the final slice.

So this roadmap clarifies sequence and likely post-`V74` territory, but the
next authoritative planning boundary should still be set by a future
`docs/DRAFT_NEXT_ARC_OPTIONS_v65.md`.

## Machine-Readable Planning Seed

```json
{
  "schema": "post_v74_multi_arc_roadmap@1",
  "authority_layer": "planning",
  "selected_by_this_doc": [],
  "band_operating_model": {
    "roadmap_is_queue": false,
    "roadmap_is_territory_graph": true,
    "future_labels_are_placeholders": true,
    "selector_required_for_family_selection": true
  },
  "current_frontier": {
    "latest_family_selector": "docs/DRAFT_NEXT_ARC_OPTIONS_v64.md",
    "latest_closed_arc": "vNext+208",
    "closed_families": [
      "V68",
      "V69",
      "V70",
      "V71",
      "V72",
      "V73",
      "V74"
    ],
    "combined_dogfood": [
      "docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.md",
      "docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.json"
    ],
    "next_selector_present": false
  },
  "recommended_next_selector": "docs/DRAFT_NEXT_ARC_OPTIONS_v65.md",
  "v75_entry_criteria": [
    "released_v74c_post_projection_handoff_present",
    "visibility_contract_present",
    "workbench_projection_present",
    "carried_exceptions_visible_or_checked_absent",
    "required_later_authority_rows_present",
    "non_dispatch_guardrails_present"
  ],
  "v75_non_entry_criteria": [
    "operator_desire_without_source_bound_handoff",
    "runtime_command_request_without_runtime_permission_surface",
    "product_authority_gap_smuggled_as_dispatch",
    "external_contest_objective_without_v43_branch_posture",
    "model_output_without_provenance_or_non_benchmark_guardrail"
  ],
  "naming_warnings_integrated": [
    {
      "old_surface": "repo_post_dispatch_outcome_review_handoff@1",
      "risk": "can imply dispatch execution occurred",
      "integrated_alternative": "repo_post_dispatch_review_handoff@1"
    },
    {
      "old_surface": "repo_worker_output_reconciliation_record@1",
      "risk": "can imply observed worker output exists",
      "integrated_alternative": "repo_worker_output_reconciliation_plan@1"
    }
  ],
  "recommended_next_family": {
    "family_id": "V75",
    "family_name": "dispatch-review, multi-worker orchestration posture, worker-output reconciliation, and non-execution guardrails",
    "selection_posture": "recommended_next_candidate_not_selected_here",
    "negative_laws": [
      "dispatch_review_request_is_not_dispatch",
      "assignment_plan_is_not_worker_execution",
      "worker_output_is_not_truth",
      "tool_applicability_is_not_scope_expansion",
      "operator_click_is_not_authorization",
      "runtime_permission_requires_later_authority",
      "product_projection_is_not_product_authorization",
      "external_contest_participation_not_selected"
    ],
    "slice_plan": [
      {
        "slice_id": "V75-A",
        "posture": "starter_candidate_after_selector_and_review",
        "surfaces": [
          "repo_dispatch_review_request@1",
          "repo_dispatch_source_index@1",
          "repo_dispatch_non_execution_guardrail@1"
        ]
      },
      {
        "slice_id": "V75-B",
        "posture": "future_slice_candidate_not_selected_here",
        "surfaces": [
          "repo_worker_role_capacity_profile@1",
          "repo_multi_worker_assignment_plan@1",
          "repo_worker_io_contract@1",
          "repo_worker_tool_applicability_matrix@1",
          "repo_dispatch_exception_register@1"
        ]
      },
      {
        "slice_id": "V75-C",
        "posture": "future_slice_candidate_not_selected_here",
        "surfaces": [
          "repo_worker_output_reconciliation_plan@1",
          "repo_dispatch_reconciliation_contract@1",
          "repo_post_dispatch_review_handoff@1",
          "repo_dispatch_review_family_closeout_alignment@1"
        ]
      }
    ]
  },
  "candidate_future_bands": [
    {
      "candidate_label": "V76",
      "theme": "reconciliation / arbiter hardening",
      "selection_posture": "not_selected"
    },
    {
      "candidate_label": "V77",
      "theme": "runtime permission and action-effect envelopes",
      "selection_posture": "not_selected"
    },
    {
      "candidate_label": "V78",
      "theme": "productized typed adjudication and read-only report surfaces",
      "selection_posture": "not_selected"
    },
    {
      "candidate_label": "V79",
      "theme": "controlled self-improvement experiments",
      "selection_posture": "not_selected"
    },
    {
      "candidate_label": "V80",
      "theme": "external-world / V43 branch activation",
      "selection_posture": "not_selected_connected_conditional"
    },
    {
      "candidate_label": "V81",
      "theme": "cross-corpus governance",
      "selection_posture": "not_selected"
    },
    {
      "candidate_label": "V82",
      "theme": "living decision graph / queryable case memory",
      "selection_posture": "not_selected"
    }
  ],
  "band_transition_rules": [
    {
      "from": "V75-C",
      "condition": "unresolved_worker_output_relation_gaps",
      "candidate_band": "V76"
    },
    {
      "from": "V75_OR_V76",
      "condition": "bounded_command_or_runtime_action_need",
      "candidate_band": "V77"
    },
    {
      "from": "V74_OR_V75",
      "condition": "product_pressure_visible_but_not_authorized",
      "candidate_band": "V78"
    },
    {
      "from": "V73_OR_V75",
      "condition": "longitudinal_self_improvement_claim_needs_experiment",
      "candidate_band": "V79"
    },
    {
      "from": "V75_OR_V77",
      "condition": "external_world_objective_with_submission_pressure",
      "candidate_band": "V80_OR_V43"
    },
    {
      "from": "ANY",
      "condition": "non_repo_corpus_becomes_first_class_input",
      "candidate_band": "V81"
    },
    {
      "from": "ANY",
      "condition": "row_graph_navigation_needed_for_review",
      "candidate_band": "V82"
    }
  ]
}
```
