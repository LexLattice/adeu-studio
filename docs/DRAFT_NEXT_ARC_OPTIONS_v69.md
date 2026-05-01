# Draft Next Arc Options v69

Status: planning handoff after `vNext+220` / `V78-C` merged on `main`, after
the `V78` family closeout pass, and after the combined `V68` through `V78`
dogfood probe.

Authority layer: planning.

This draft records the post-`V78` frontier. It does not authorize command
execution, tool invocation, worker assignment, dispatch execution, product
authorization, external branch activation, PR creation, commit, merge,
release, benchmark truth, global model selection, living-memory authority,
recursive policy amendment, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v68.md`, which selected the `V78` runtime execution
authority review and tool-use permission envelope family. `vNext+218`,
`vNext+219`, and `vNext+220` then closed `V78-A`, `V78-B`, and `V78-C`
without creating additional family selector versions.

## Current Frontier

- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- `V73` is closed on `main` as the candidate outcome-review family.
- `V74` is closed on `main` as the operator-projection family.
- `V75` is closed on `main` as the dispatch-review family.
- `V76` is closed on `main` as the reconciliation / arbiter review family.
- `V77` is closed on `main` as the runtime-permission review family.
- `V78` is closed on `main` as the runtime execution authority review family.
- latest closed implementation arc: `vNext+220`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v68.md`
- next planning obligation: select and review `V79` as the next family outside
  closed `V78`.

The combined `V68` through `V78` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V78` closed runtime execution authority review without executing commands,
invoking tools, dispatching workers, authorizing products, activating external
branches, or selecting `V79`. It also records two carry-forward findings:

- `V78` closes runtime execution authority review and tool-use permission
  envelope posture without executing commands or invoking tools;
- `V78-C` carries runtime execution review pressure and product review
  pressure forward as later-review requests, but it does not select `V79` or
  grant downstream authority.

## Next Planning Question

Now that `V78` can make runtime authority requests, authority decisions,
tool-use permission envelopes, command-scope boundaries, exceptions,
readiness summaries, and pre-execution-authority-review handoffs reviewable
without executing commands or invoking tools, should the next family be `V79`:
controlled execution review, execution run-plan readiness, tool-invocation
planning, effect-monitoring contracts, and post-review handoff?

## Recommended Next Pressure

- family: `V79`
- proposed family name:
  - `V79: controlled execution review, execution run-plan readiness,
    tool-invocation planning, effect-monitoring contracts, and
    post-review handoff`
- recommended planning posture:
  - select `V79` as the next family;
  - select `V79-A` as the next default candidate for `vNext+221`;
  - consume `V78-C` readiness summaries, pre-execution-authority-review
    handoffs, and family closeout alignment as immediate source substrate;
  - consume `V78-B` decisions, tool-use permission envelopes, command-scope
    boundaries, and exception registers as review substrate;
  - define source-bound controlled-execution review requests, source indexing,
    and non-execution guardrails before any run-plan or tool-invocation plan
    is represented.

`V79` should type the question "what would need to be true before a later
family may review a bounded command or tool-invocation run plan?" It must not
run commands, invoke tools, assign workers, dispatch, productize, activate
external branches, or claim release authority.

`V79-A` should not create refs to future `V79-B` surfaces. The starter request
shape should use requested horizons and required postures for run-plan,
tool-invocation, monitoring, telemetry, rollback, and operator-confirmation
pressure, plus `controlled_execution_action_posture =
no_controlled_execution_performed_by_v79`.

## Proposed Family Decomposition

`V79` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V79-A` | controlled execution review request, controlled execution source index, and non-execution guardrail over released `V78-C` handoff / closeout substrate |
| `V79-B` | execution run plan, tool-invocation plan, effect-monitoring contract, and controlled execution exception register |
| `V79-C` | controlled execution review summary, post-controlled-execution-review handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V79-A` should be the first active slice. Candidate starter surfaces:

- `repo_controlled_execution_review_request@1`
- `repo_controlled_execution_source_index@1`
- `repo_controlled_execution_non_execution_guardrail@1`

Recommendation: select `V79-A` as the next default candidate after this
selector, with `vNext+221` as the canonical starter bundle if no intervening
arc claims that number.

Later `V79` surfaces should remain planning-layer until their own starter
locks:

- `repo_execution_run_plan@1`
- `repo_tool_invocation_plan@1`
- `repo_execution_effect_monitoring_contract@1`
- `repo_controlled_execution_exception_register@1`
- `repo_controlled_execution_review_summary@1`
- `repo_post_controlled_execution_review_handoff@1`
- `repo_controlled_execution_review_family_closeout_alignment@1`

Post-`V79-A` continuation posture: after `vNext+221` closes on `main`, select
`V79-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V79` family and does not
create a new next-arc-options selector version.

Post-`V79-B` continuation posture: after the `V79-B` slice closes on `main`,
select `V79-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V79` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- command execution;
- actual tool invocation;
- runtime worker dispatch;
- worker assignment;
- dispatch execution;
- product launch, product-market validation, or product authorization;
- external branch activation or `V43` contest participation;
- PR creation, commit, merge, release, or released-truth authority;
- relation settlement, claim truth, or benchmark truth;
- global model selection;
- living decision graph authority;
- recursive policy amendment;
- self-improvement experiment authority.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`V79` is selector-ready because the post-`V78` substrate can cite concrete
released rows showing:

- `V78-C` handoff and closeout records preserve runtime execution review and
  product review pressure without executing commands or invoking tools;
- `V78-C` keeps product pressure blocked by later authority and
  self-evidencing pressure warning-ready only for later runtime execution
  review;
- `V78-B` decisions, tool-use permission envelopes, command-scope boundaries,
  and exception rows separate later-review authority from execution;
- the combined dogfood confirms that no command execution or tool invocation
  has occurred and no downstream family has been selected.

`V79` must not be used if the only evidence is:

- an operator desire to run a command;
- a model suggestion that a command would be useful;
- a passing local tool run being treated as authority;
- a `V78` decision posture being treated as execution authorization;
- a tool-use permission envelope being treated as actual tool invocation;
- a command-scope boundary being treated as target mutation authority;
- a product-pressure case being treated as execution review readiness;
- an unbounded glob target being treated as a run-plan boundary;
- an effect-monitoring requirement being treated as observed effect evidence.

## Inputs For Starter Drafting

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v68.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_CONTROLLED_EXECUTION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v220/evidence_inputs/v78_family_closeout_alignment_v220.json`
- `artifacts/agent_harness/v220/evidence_inputs/v78c_runtime_execution_authority_closeout_evidence_v220.json`
- `apps/api/fixtures/repo_description/vnext_plus220/repo_runtime_authority_readiness_summary_v220_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus220/repo_pre_execution_authority_review_handoff_v220_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus220/repo_runtime_execution_authority_family_closeout_alignment_v220_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus219/repo_runtime_execution_authority_decision_v219_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus219/repo_tool_use_permission_envelope_v219_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus219/repo_command_scope_authorization_boundary_v219_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus219/repo_runtime_authority_exception_register_v219_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

## Lock Readiness Note

The future `vNext+221` starter lock should consume committed `V68` through
`V78` closeouts, the combined dogfood artifacts, `vNext+220` evidence inputs,
and released `V78-C` readiness / handoff / closeout fixtures as concrete
source rows. If any expected source is missing at lock time, the `V79-A`
controlled execution review surface should record that absence explicitly with
source-presence or source-status posture.

The starter source index should distinguish eligibility source roles from
support context roles. `eligible_for_controlled_execution_review` must cite a
released `V78-C` readiness-summary or pre-execution-authority-review handoff
source role; combined dogfood and support-process rows may contextualize the
request but cannot be the only eligibility source.

`V79-A` should include one eligible controlled-execution review row and one
product-pressure row that remains product-blocked or future-family-only. It
should include zero run plans, zero tool-invocation plans, zero command
executions, zero tool invocations, zero observed effects, zero telemetry
success, zero rollback verification, zero dispatch rows, zero product /
external / release rows, and zero `V80` selection rows.
