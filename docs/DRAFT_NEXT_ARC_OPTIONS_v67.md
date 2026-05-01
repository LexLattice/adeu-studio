# Draft Next Arc Options v67

Status: planning handoff after `vNext+214` / `V76-C` merged on `main`, after
the `V76` family closeout pass, and after the combined `V68` through `V76`
dogfood probe.

Authority layer: planning.

This draft records the post-`V76` frontier. It does not authorize runtime
permission, command execution, worker assignment, dispatch execution, product
authorization, external branch activation, PR creation, commit, merge, release,
benchmark truth, global model selection, living-memory authority, recursive
policy amendment, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v66.md`, which selected the `V76` reconciliation /
arbiter review family. `vNext+212`, `vNext+213`, and `vNext+214` then closed
`V76-A`, `V76-B`, and `V76-C` without creating additional family selector
versions.

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
- latest closed implementation arc: `vNext+214`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v66.md`
- next planning obligation: select and review `V77` as the next family outside
  closed `V76`.

The combined `V68` through `V76` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V76` closed reconciliation / arbiter review without relation settlement,
claim truth, runtime permission, product authorization, external authority, or
`V77` selection. It also records two carry-forward findings:

- `V76` closes reconciliation / arbiter review over projected-output and
  relation-review pressure without settling relations or declaring claim truth;
- `V76-C` carries product pressure to future product review and
  self-evidencing pressure to future reconciliation / arbiter review, but it
  does not select `V77` or runtime / product / external authority.

## Next Planning Question

Now that `V76` can make reconciliation claims, relation posture, dissent,
review-only authority profiles, settlement requests, adversarial review, gap
scans, summaries, and handoffs reviewable without settling truth, should the
next family be `V77`: runtime-permission review, command preflight posture,
action-effect envelopes, telemetry / rollback requirements, and non-execution
guardrails?

## Recommended Next Pressure

- family: `V77`
- proposed family name:
  - `V77: runtime-permission review, command preflight posture, action-effect
    envelopes, telemetry / rollback requirements, and non-execution guardrails`
- recommended planning posture:
  - select `V77` as the next family;
  - select `V77-A` as the next default candidate for `vNext+215`;
  - consume `V76-C` reconciliation summaries, post-reconciliation handoffs, and
    family closeout alignment as immediate source substrate;
  - consume `V72` contained integration trial / effect / rollback distinctions
    as historical source substrate for effect-envelope vocabulary;
  - consume `V75` dispatch-review and `V76` reconciliation / arbiter boundaries
    as non-execution and non-truth guardrails;
  - define runtime permission review requests, source indexing, and
    non-execution guardrails before any command preflight or effect envelope is
    represented.

`V77` should type the question "what would have to be true before a command or
runtime action could be reviewed later?" It must not run the command, grant
runtime permission, assign a worker, perform dispatch, productize, activate an
external branch, or claim release authority.

## Why `V77` Now

`V68` through `V76` repeatedly preserve an important negative law: visibility,
review, ratification, containment, outcome, projection, dispatch review, and
reconciliation are not runtime permission. That repeated boundary is now
useful enough to become a typed positive substrate.

The next bottleneck is not "execute commands." It is making runtime-action
pressure reviewable before any future execution family can exist:

- what candidate or handoff is asking for runtime review;
- what concrete sources or absence markers justify that request;
- what command intent is being discussed, if any;
- what target boundary and effect surface would be in scope;
- what telemetry and rollback evidence would be required;
- what human or maintainer authority would be needed first;
- what must remain forbidden no matter how visible the request is.

`V77` is therefore a runtime-permission review family, not a runtime execution
family.

## Proposed Family Decomposition

`V77` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V77-A` | runtime permission review request, runtime source index, and non-execution guardrail over released `V76-C` handoff / closeout substrate |
| `V77-B` | command preflight contract, action-effect envelope, telemetry requirement, and runtime rollback contract |
| `V77-C` | runtime permission authority posture, runtime review summary, post-runtime-review handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V77-A` should be the first active slice. Candidate starter surfaces:

- `repo_runtime_permission_review_request@1`
- `repo_runtime_permission_source_index@1`
- `repo_runtime_non_execution_guardrail@1`

Recommendation: select `V77-A` as the next default candidate after this
selector, with `vNext+215` as the canonical starter bundle if no intervening
arc claims that number.

Later `V77` surfaces should remain planning-layer until their own starter
locks:

- `repo_command_preflight_contract@1`
- `repo_action_effect_envelope@1`
- `repo_runtime_telemetry_requirement@1`
- `repo_runtime_rollback_contract@1`
- `repo_runtime_permission_authority_posture@1`
- `repo_runtime_permission_review_summary@1`
- `repo_post_runtime_permission_review_handoff@1`
- `repo_runtime_permission_family_closeout_alignment@1`

Post-`V77-A` continuation posture: after `vNext+215` closes on `main`, select
`V77-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V77` family and does not
create a new next-arc-options selector version.

Post-`V77-B` continuation posture: after the `V77-B` slice closes on `main`,
select `V77-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V77` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- command execution;
- runtime permission grant;
- runtime worker dispatch;
- worker assignment;
- dispatch execution;
- actual tool invocation permission;
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

`V77` is selector-ready because the post-`V76` substrate can cite concrete
released rows showing:

- `V76-C` handoff and closeout records preserve future pressure without
  granting runtime, product, external, or release authority;
- `V76-C` keeps product pressure blocked by later authority and
  self-evidencing pressure in later review posture;
- `V75` and `V76` both preserve non-execution and non-truth guardrails;
- `V72` already introduced target-boundary, trial, effect, rollback, and
  commit / release distinctions that can inform effect-envelope vocabulary;
- the combined dogfood confirms that no runtime permission has been granted
  and no downstream family has been selected.

`V77` must not be used if the only evidence is:

- an operator desire to run a command;
- a model suggestion that a command would be useful;
- a passing local tool run being treated as future runtime permission;
- a dispatch-review request being treated as dispatch execution;
- a reconciliation handoff being treated as relation settlement;
- a product-pressure case being treated as runtime authority;
- an unbounded glob target being treated as a command target boundary;
- a rollback claim without source-bound rollback posture.

## Inputs For Starter Drafting

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v66.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RUNTIME_PERMISSION_V77_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v214/evidence_inputs/v76_family_closeout_alignment_v214.json`
- `artifacts/agent_harness/v214/evidence_inputs/v76c_reconciliation_arbiter_closeout_evidence_v214.json`
- `apps/api/fixtures/repo_description/vnext_plus214/repo_reconciliation_review_summary_v214_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus214/repo_post_reconciliation_handoff_v214_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus214/repo_reconciliation_family_closeout_alignment_v214_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_contained_integration_trial_record_v201_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_effect_surface_register_v201_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_rollback_readiness_v201_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

## Lock Readiness Note

The future `vNext+215` starter lock should consume committed `V68` through
`V76` closeouts, the combined dogfood artifacts, `vNext+214` evidence inputs,
and released `V76-C` summary / handoff / closeout fixtures as concrete source
rows. If any expected source is missing at lock time, the `V77-A` runtime
permission review surface should record that absence explicitly with
source-presence or source-status posture.

The lock should not reconstruct runtime permission state from prose memory,
model preference, operator vibe, worker-majority intuition, uncommitted
transcript, or a local command that happened outside the lock.
