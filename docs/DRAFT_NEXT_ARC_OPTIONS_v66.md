# Draft Next Arc Options v66

Status: planning handoff after `vNext+211` / `V75-C` merged on `main`, after
the `V75` family closeout pass, and after the combined `V68` through `V75`
dogfood probe.

Authority layer: planning.

This draft records the post-`V75` frontier. It does not authorize arbiter
truth, worker-output truth, dispatch execution, worker assignment, command
execution, runtime permission, product authorization, external contest
participation, commit, PR update, merge, release, benchmark truth, global model
selection, living-memory authority, or recursive self-approval by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v65.md`, which selected the `V75` dispatch-review
family. `vNext+209`, `vNext+210`, and `vNext+211` then closed `V75-A`,
`V75-B`, and `V75-C` without creating additional family selector versions.

## Current Frontier

- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- `V73` is closed on `main` as the candidate outcome-review family.
- `V74` is closed on `main` as the operator-projection family.
- `V75` is closed on `main` as the dispatch-review family.
- latest closed implementation arc: `vNext+211`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v65.md`
- next planning obligation: select and review `V76` as the next family outside
  closed `V75`.

The combined `V68` through `V75` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that `V75`
closed dispatch review without dispatch execution. It also records two
carry-forward findings:

- runtime permission and action-effect envelopes remain future territory;
- `V75-C` emitted reconciliation / arbiter pressure over projected output
  slots and contracts, but observed no worker output.

## Next Planning Question

Now that `V75` can carry dispatch-review requests, worker-role / assignment /
IO / tool-applicability plans, exceptions, projected output slots, relation
rows, reconciliation contracts, and post-dispatch-review handoffs without
executing dispatch, should the next family be `V76`: reconciliation / arbiter
hardening over projected or later-observed output claims, relation posture,
dissent preservation, and non-truth guardrails?

## Recommended Next Pressure

- family: `V76`
- proposed family name:
  - `V76: reconciliation / arbiter hardening, output-claim mapping, relation
    review posture, dissent preservation, and non-truth guardrails`
- recommended planning posture:
  - select `V76` as the next family;
  - select `V76-A` as the next default candidate for `vNext+212`;
  - consume `V75-C` reconciliation plans, relation rows, reconciliation
    contracts, post-dispatch-review handoffs, and family closeout alignment as
    the immediate source substrate;
  - consume `V68` through `V74` as upstream source, candidate, evidence,
    ratification, integration, outcome, and projection substrate;
- map projected and later-observed output claims without treating any output,
  relation, arbiter note, model output, or worker majority as truth;
- distinguish projected output-slot existence / relation-review need from
  observed output-content claims;
  - preserve dissent and relation uncertainty instead of smoothing it into
    settlement;
  - defer runtime permission, action execution, product authorization, external
    branch activation, release authority, benchmark truth, global model
    selection, living-memory authority, and recursive policy amendment.

## Why `V76` Now

`V75-C` shipped `repo_worker_output_reconciliation_plan@1`,
`repo_dispatch_reconciliation_contract@1`, and
`repo_post_dispatch_review_handoff@1` rows. Those surfaces deliberately stop
short of arbiter hardening:

- projected output slots are distinct from observed worker output refs;
- relation rows are source-bound and plan-scoped;
- relation rows can require `future_reconciliation_or_arbiter_review`;
- contracts preserve forbidden inferences, including worker output as truth and
  model output as benchmark truth;
- post-dispatch-review handoffs can carry blocked product pressure or request
  future outcome review of the dispatch-review process;
- family closeout records reconciliation / arbiter review as future pressure
  without selecting it.

The next bottleneck is therefore not runtime permission. It is making
reconciliation and arbiter pressure itself typed: what claim horizon is under
relation review, whether the claim is only projected-slot existence or an
observed output-content claim, which projected or observed output ref bears on
it, which relation posture is visible, which dissent is preserved, and which
later authority would be needed before settlement.

## Proposed Family Decomposition

`V76` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V76-A` | reconciliation claim map, arbiter relation register, and reconciliation dissent register over released `V75-C` reconciliation / relation / handoff substrate |
| `V76-B` | arbiter authority profile, reconciliation settlement request, adversarial relation review, and relation gap scan |
| `V76-C` | reconciliation review summary, post-reconciliation handoff, and family closeout alignment without ratification, runtime execution, product authorization, or release |

## Selected Surfaces For Starter Drafting

`V76-A` should be the first active slice. Candidate starter surfaces:

- `repo_reconciliation_claim_map@1`
- `repo_arbiter_relation_register@1`
- `repo_reconciliation_dissent_register@1`

Recommendation: select `V76-A` as the next default candidate after this
selector, with `vNext+212` as the canonical starter bundle if no intervening
arc claims that number.

Later `V76` surfaces should remain planning-layer until their own starter
locks:

- `repo_arbiter_authority_profile@1`
- `repo_reconciliation_settlement_request@1`
- `repo_adversarial_relation_review@1`
- `repo_reconciliation_gap_scan@1`
- `repo_reconciliation_review_summary@1`
- `repo_post_reconciliation_handoff@1`
- `repo_reconciliation_family_closeout_alignment@1`

Post-`V76-A` continuation posture: after `vNext+212` closes on `main`, select `V76-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V76` family and does not
create a new next-arc-options selector version.

Post-`V76-B` continuation posture: after the `V76-B` slice closes on `main`,
select `V76-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V76` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- arbiter output as truth;
- worker output as truth;
- majority agreement as correctness;
- model-output comparison as benchmark truth or global model selection;
- relation settlement as ratification;
- reconciliation as product authorization;
- runtime command execution;
- actual worker assignment or dispatch;
- product launch, product-market validation, or product authorization;
- external contest participation or `V43` activation;
- commit, PR update, merge, release, or released-truth authority;
- recursive policy amendment;
- runtime permission or command preflight authority;
- living memory / graph authority.

Those remain mapped future seams only until their own planning and lock
surfaces select them.

## Entry And Non-Entry Criteria

`V76` is selector-ready because the post-`V75` substrate can cite concrete
released `V75-C` rows showing:

- at least one `repo_worker_output_reconciliation_plan@1` row with projected
  output slots and source-bound relation refs;
- at least one relation row whose `required_next_review_surface` is
  `future_reconciliation_or_arbiter_review`;
- a dispatch reconciliation contract carrying forbidden inferences;
- a post-dispatch-review handoff that carries either blocked authority pressure
  or ready later-review pressure without dispatch execution;
- family closeout alignment that explicitly leaves reconciliation / arbiter
  hardening as future territory;
- combined dogfood evidence that no worker output was observed by `V75`.

`V76` must not be used if the only evidence is:

- a desire to settle model or worker outputs by taste;
- a majority of model / worker outputs without source-bound relation rows;
- a projected output slot being treated as observed output;
- a projected output slot being treated as an observed output-content claim;
- a relation row without source refs or explicit absence posture;
- a product-pressure case being smuggled in as arbiter authority;
- a runtime command request without a later runtime permission surface;
- a model comparison that lacks benchmark-truth guardrails.

## Inputs For Starter Drafting

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v65.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/ARCHITECTURE_ADEU_RECONCILIATION_ARBITER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_POST_V74_MULTI_ARC_ROADMAP_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECONCILIATION_ARBITER_V76_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v211/evidence_inputs/v75_family_closeout_alignment_v211.json`
- `artifacts/agent_harness/v211/evidence_inputs/v75c_dispatch_review_closeout_evidence_v211.json`
- `apps/api/fixtures/repo_description/vnext_plus211/repo_worker_output_reconciliation_plan_v211_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus211/repo_dispatch_reconciliation_contract_v211_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus211/repo_post_dispatch_review_handoff_v211_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus211/repo_dispatch_review_family_closeout_alignment_v211_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

## Lock Readiness Note

The future `vNext+212` starter lock should consume committed `V68` through
`V75` closeouts, the combined dogfood artifacts, `vNext+211` evidence inputs,
and released `V75-C` reconciliation / contract / handoff / closeout fixtures as
concrete source rows. If any expected source is missing at lock time, the
`V76-A` reconciliation surface should record that absence explicitly with
source-presence or source-status posture.

The lock should not reconstruct reconciliation state from prose memory, model
preference, operator vibe, worker-majority intuition, or uncommitted
transcript.
