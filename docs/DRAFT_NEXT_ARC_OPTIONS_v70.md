# Draft Next Arc Options v70

Status: planning handoff after `vNext+223` / `V79-C` merged on `main`, after
the `V79` family closeout pass, and after the combined `V68` through `V79`
dogfood probe.

Authority layer: planning.

This draft records the post-`V79` frontier. It does not authorize command
execution, tool invocation, target mutation, worker assignment, dispatch
execution, product authorization, external branch activation, external contest
participation, external submission, PR creation, commit, merge, release,
benchmark truth, global model selection, living-memory authority, recursive
policy amendment, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v69.md`, which selected the `V79` controlled execution
review family. `vNext+221`, `vNext+222`, and `vNext+223` then closed `V79-A`,
`V79-B`, and `V79-C` without creating additional family selector versions.

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
- `V79` is closed on `main` as the controlled execution review family.
- latest closed implementation arc: `vNext+223`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v69.md`
- next planning obligation: select and review `V80` as the next family outside
  closed `V79`.

The combined `V68` through `V79` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V79` closed controlled execution review without executing commands, invoking
tools, mutating targets, dispatching workers, authorizing products, activating
external branches, or selecting `V80`. It also records two carry-forward
findings:

- `V79` closes controlled execution review with review-only run-plan,
  tool-invocation-plan, monitoring, telemetry, rollback, and operator
  confirmation posture, but without command execution or tool invocation;
- `V79-C` carries controlled execution trial review pressure and product review
  pressure forward as later-review requests, but it does not select `V80` or
  grant downstream authority.

## Next Planning Question

The post-`V74` multi-arc roadmap named `V80` as the external-world / `V43`
branch activation band. Now that `V79` has closed without external activation,
should the next family be `V80`: external branch activation review, `V43`
conditional branch posture, external data / tool / submission / result
provenance boundaries, withdrawal posture, and non-activation guardrails?

This selector intentionally treats `V80` as external branch **review**, not
external branch activation. The current source basis carries external branch
activation as unselected future territory and requires concrete branch posture
before any eligibility claim can be made. If no concrete `V43` / external
branch posture source exists at starter time, `V80-A` must represent that
absence explicitly.

## Recommended Next Pressure

- family: `V80`
- proposed family name:
  - `V80: external branch activation review, V43 conditional branch posture,
    external data / tool / submission / result provenance boundaries, and
    non-activation guardrails`
- recommended planning posture:
  - select `V80` as the next family under the named multi-arc roadmap;
  - select `V80-A` as the next default candidate for `vNext+224`;
  - consume `V79-C` controlled execution summaries, post-controlled-execution
    handoffs, and family closeout alignment as immediate source substrate;
  - consume the combined `V68` through `V79` dogfood as support context;
  - distinguish concrete external branch posture from roadmap context and
    explicit absence markers;
  - define source-bound external branch review requests, source indexing, and
    non-activation guardrails before any data boundary, tool boundary,
    submission authority, result provenance, or withdrawal contract is
    represented.

`V80` should type the question "what would need to be true before a later
family may review external branch activation or external contest participation
for a bounded branch horizon?" It must not activate `V43`, submit to an
external system, run external tools for effect, widen runtime execution,
productize, release, or claim external-world results.

## Proposed Family Decomposition

`V80` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V80-A` | external branch review request, external branch source index, and non-activation guardrail over released `V79-C` closeout / handoff substrate plus explicit `V43` posture or absence rows |
| `V80-B` | external data boundary, external tool boundary, external submission authority review, external result provenance / withdrawal contract, and external branch exception register |
| `V80-C` | external branch readiness summary, post-external-branch-review handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V80-A` should be the first active slice. Candidate starter surfaces:

- `repo_external_branch_review_request@1`
- `repo_external_branch_source_index@1`
- `repo_external_branch_non_activation_guardrail@1`

Recommendation: select `V80-A` as the next default candidate after this
selector, with `vNext+224` as the canonical starter bundle if no intervening
arc claims that number.

Later `V80` surfaces should remain planning-layer until their own starter
locks:

- `repo_external_data_boundary@1`
- `repo_external_tool_boundary@1`
- `repo_external_submission_authority_review@1`
- `repo_external_result_provenance_contract@1`
- `repo_external_branch_exception_register@1`
- `repo_external_branch_readiness_summary@1`
- `repo_post_external_branch_review_handoff@1`
- `repo_external_branch_review_family_closeout_alignment@1`

Post-`V80-A` continuation posture: after `vNext+224` closes on `main`, select `V80-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V80` family and does not
create a new next-arc-options selector version.

Post-`V80-B` continuation posture: after the `V80-B` slice closes on `main`,
select `V80-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V80` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- external branch activation;
- `V43` contest participation;
- external submission;
- external tool invocation for effect;
- external endpoint mutation;
- command execution;
- actual tool invocation;
- runtime worker dispatch;
- worker assignment;
- dispatch execution;
- product launch, product-market validation, or product authorization;
- PR creation, commit, merge, release, or released-truth authority;
- relation settlement, claim truth, benchmark truth, or external result truth;
- global model selection;
- living decision graph authority;
- recursive policy amendment;
- controlled execution trial execution.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`V80` is planning-ready because the post-`V79` substrate can cite concrete
released rows showing:

- `V79-C` closeout keeps `external_branch_activation` unselected;
- earlier families repeatedly preserve external branch pressure as blocked or
  future-family-only without activating it;
- the combined dogfood confirms no command execution, no tool invocation, no
  target mutation, no external branch activation, no external submission, and
  no downstream family selection;
- the post-`V74` multi-arc roadmap already named external-world / `V43`
  branch activation as the next remaining branch band after `V75` through
  `V79`.

`V80-A` eligibility must be stricter than selector readiness. An external
objective source may support request existence and objective-only review, but
it must not by itself make a request eligible for external branch review. A
request may be `eligible_for_external_branch_review` only if it cites concrete
released `V79-C` substrate and a current `V43` / external branch posture
source. If no such source exists, the request must remain
`request_recorded_objective_only`, `blocked_by_missing_v43_branch_posture`,
`blocked_by_missing_external_objective`, `future_family_only`, or
`rejected_out_of_scope`.

Starter rows should carry `branch_posture_currentness` so historical branch
planning context cannot be read as current branch posture:

- `current_branch_posture`
- `historical_branch_planning_context`
- `explicit_absence_marker`
- `stale_or_superseded`
- `unknown_needs_review`

`V80` must not be used if the only evidence is:

- an operator desire to enter an external contest;
- a model suggestion that external participation would be useful;
- a roadmap label without concrete branch posture;
- a historical `DRAFT_NEXT_ARC_OPTIONS_v43.md` planning file treated as
  external activation authority;
- an external objective source treated as current branch posture;
- a passing local command or tool result treated as submission authority;
- a product-pressure case treated as external activation readiness;
- a controlled execution review package treated as external execution
  authority;
- an external URL or endpoint string treated as permission to access or mutate
  an external system.

## Inputs For Starter Drafting

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v69.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v223/evidence_inputs/v79_family_closeout_alignment_v223.json`
- `artifacts/agent_harness/v223/evidence_inputs/v79c_controlled_execution_review_closeout_evidence_v223.json`
- `apps/api/fixtures/repo_description/vnext_plus223/repo_controlled_execution_review_summary_v223_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus223/repo_post_controlled_execution_review_handoff_v223_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus223/repo_controlled_execution_review_family_closeout_alignment_v223_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

Potential branch-history context, not activation authority by itself:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`

## Lock Readiness Note

The future `vNext+224` starter lock should consume committed `V68` through
`V79` closeouts, the combined dogfood artifacts, `vNext+223` evidence inputs,
and released `V79-C` summary / handoff / closeout fixtures as concrete source
rows. If any expected `V43` or external branch posture source is missing, the
`V80-A` external branch review surface should record that absence explicitly
with source-presence or source-status posture.

The starter source index should distinguish eligibility source roles from
support context roles. Roadmap and dogfood rows may contextualize the request
but cannot be the only eligibility basis. A historical branch planning doc may
contextualize `V43` lineage, but cannot become external activation authority
without a concrete current branch posture row.

`V80-A` may include one explicitly blocked external-branch review row if no
concrete `V43` posture exists, plus one row preserving product or execution
pressure as out-of-scope for external activation. It should include zero
external submissions, zero external tool invocations, zero external endpoint
mutations, zero result claims, zero withdrawal actions, zero product /
external / release authority rows, and zero `V81` selection rows.
