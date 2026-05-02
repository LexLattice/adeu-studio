# Draft Next Arc Options v71

Status: planning handoff after `vNext+226` / `V80-C` merged on `main`, after
the `V80` family closeout pass, and after the combined `V68` through `V80`
dogfood probe.

Authority layer: planning.

This draft records the post-`V80` frontier. It does not authorize external
data ingestion, cross-corpus import, connector activation, customer substrate
handling, external submission, endpoint access, command execution, tool
invocation, worker dispatch, product authorization, PR creation, commit,
merge, release, benchmark truth, global model selection, living-memory
authority, recursive policy amendment, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v70.md`, which selected the `V80` external branch
activation review family. `vNext+224`, `vNext+225`, and `vNext+226` then
closed `V80-A`, `V80-B`, and `V80-C` without creating additional family
selector versions.

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
- `V80` is closed on `main` as the external branch activation review family.
- latest closed implementation arc: `vNext+226`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v70.md`
- next planning obligation: select and review `V81` as the next family outside
  closed `V80`.

The combined `V68` through `V80` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V80` closed external branch activation review without external activation,
`V43` contest participation, external submission, external tool invocation,
endpoint mutation, external data transfer, external result truth, withdrawal
action, product authorization, release, or `V81` selection. It also records
two carry-forward findings:

- `V80` closes external branch activation review with source-bound request,
  data/tool/submission/result boundary, exception, summary, and handoff
  posture, but without external activation, submission, tool invocation, data
  transfer, endpoint mutation, or result truth;
- `V80-C` carries external-branch authority review pressure and product review
  pressure forward as later-review requests, but it does not select `V81` or
  grant downstream authority.

## Next Planning Question

The post-`V74` multi-arc roadmap named `V81` as the cross-corpus governance
band. Now that `V80` has closed external branch activation review and still
records missing current `V43` posture, should the next family be `V81`:
cross-corpus / imported-substrate governance review, corpus boundary posture,
imported source provenance, authority and privacy gaps, and non-ingestion
guardrails?

This selector intentionally treats `V81` as cross-corpus **governance review**,
not cross-corpus ingestion or adjudication execution. The current source basis
shows that external-world pressure exists, but the repo still needs a typed
review layer for non-repo substrate boundaries before any later product,
external participation, customer corpus, benchmark-result, or connector
workflow can be safely considered.

## Recommended Next Pressure

- family: `V81`
- proposed family name:
  - `V81: cross-corpus governance review, imported-substrate source posture,
    corpus boundary contracts, authority / privacy gap visibility, and
    non-ingestion guardrails`
- recommended planning posture:
  - select `V81` as the next family under the named multi-arc roadmap;
  - select `V81-A` as the next default candidate for `vNext+227`;
  - consume `V80-C` external branch readiness summaries,
    post-external-branch-review handoffs, and family closeout alignment as
    immediate source substrate;
  - consume the combined `V68` through `V80` dogfood as support context;
  - define source-bound cross-corpus governance review requests, corpus source
    indexing, and non-ingestion guardrails before any corpus-boundary contract,
    imported-substrate provenance register, authority gap register, or
    cross-corpus summary is represented.

`V81` should type the question "what would need to be true before a later
family may review a non-repo or imported corpus as a bounded adjudication
substrate?" It must not ingest external data, connect to customer systems,
claim imported data truth, run cross-corpus adjudication, productize, activate
external branches, submit externally, or release.

## Proposed Family Decomposition

`V81` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V81-A` | cross-corpus governance review request, corpus source index, and non-ingestion guardrail over released `V80-C` closeout / handoff substrate plus explicit imported-corpus source or absence rows |
| `V81-B` | corpus boundary contract, imported-substrate provenance register, cross-corpus authority gap register, and cross-corpus exception register |
| `V81-C` | cross-corpus governance summary, post-cross-corpus-review handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V81-A` should be the first active slice. Candidate starter surfaces:

- `repo_cross_corpus_governance_request@1`
- `repo_cross_corpus_source_index@1`
- `repo_cross_corpus_non_ingestion_guardrail@1`

Recommendation: select `V81-A` as the next default candidate after this
selector, with `vNext+227` as the canonical starter bundle if no intervening
arc claims that number.

Later `V81` surfaces should remain planning-layer until their own starter
locks:

- `repo_corpus_boundary_contract@1`
- `repo_imported_substrate_provenance_register@1`
- `repo_cross_corpus_authority_gap_register@1`
- `repo_cross_corpus_exception_register@1`
- `repo_cross_corpus_governance_summary@1`
- `repo_post_cross_corpus_review_handoff@1`
- `repo_cross_corpus_governance_family_closeout_alignment@1`

Post-`V81-A` continuation posture: after `vNext+227` closes on `main`, select `V81-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V81` family and does not
create a new next-arc-options selector version.

Post-`V81-B` continuation posture: after the `V81-B` slice closes on `main`,
select `V81-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V81` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- external data ingestion;
- cross-corpus import execution;
- customer substrate handling;
- connector activation;
- external endpoint access or mutation;
- external branch activation or `V43` contest participation;
- external submission;
- command execution or actual tool invocation;
- runtime worker dispatch or worker assignment;
- product launch, product-market validation, or product authorization;
- PR creation, commit, merge, release, or released-truth authority;
- relation settlement, claim truth, benchmark truth, imported-result truth, or
  external result truth;
- global model selection;
- living decision graph authority;
- recursive policy amendment;
- cross-corpus adjudication execution.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`V81` is planning-ready because the post-`V80` substrate can cite concrete
released rows showing:

- `V80-C` closeout keeps external branch activation, external submission,
  external tool invocation, endpoint mutation, external data transfer, result
  truth, product authorization, and `V81` selection unselected;
- external branch and product pressure remain visible as later-review requests
  rather than actions;
- the combined dogfood confirms no command execution, no tool invocation, no
  target mutation, no external activation, no external submission, no
  cross-corpus ingestion, and no downstream family selection;
- the post-`V74` multi-arc roadmap already named cross-corpus governance as a
  generalization band after external-world review.

`V81-A` request recordability must be stricter than selector readiness, and
eligibility must be stricter than request recordability. A cross-corpus review
request may be recorded when a concrete imported-corpus source,
benchmark-result source, customer-provided-corpus source, paper/design/repo
source, or explicit absence row exists. Explicit absence rows support
`request_recorded_absence_only` or `blocked_by_missing_corpus_source`; they do
not by themselves support `eligible_for_cross_corpus_governance_review`.

An eligible row must cite released `V80-C` substrate and at least one current
concrete corpus source. Support and dogfood sources may contextualize
`V81-A`; they cannot be the only eligibility source.

`V81` must not be used if the only evidence is:

- an operator desire to ingest a corpus;
- a model suggestion that cross-corpus evaluation would be useful;
- a roadmap label without concrete current corpus source or explicit absence
  posture;
- an external objective treated as permission to ingest data;
- an external endpoint string treated as connector access permission;
- a benchmark result treated as benchmark truth without provenance;
- customer data mentioned in transcript without authority or privacy posture;
- product-pressure visibility treated as product authorization;
- external branch review handoff treated as external activation.

## Inputs For Starter Drafting

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v70.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_CROSS_CORPUS_GOVERNANCE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v226/evidence_inputs/v80_family_closeout_alignment_v226.json`
- `artifacts/agent_harness/v226/evidence_inputs/v80c_external_branch_review_closeout_evidence_v226.json`
- `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_readiness_summary_v226_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus226/repo_post_external_branch_review_handoff_v226_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_review_family_closeout_alignment_v226_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

Potential corpus-history context, not ingestion authority by itself:

- prior external branch and product-pressure docs that mention non-repo
  corpora or external objectives.

## Lock Readiness Note

The future `vNext+227` starter lock should consume committed `V68` through
`V80` closeouts, the combined dogfood artifacts, `vNext+226` evidence inputs,
and released `V80-C` summary / handoff / closeout fixtures as concrete source
rows. If any expected imported-corpus source, benchmark source, external
corpus source, customer corpus source, or authority source is missing, the
`V81-A` cross-corpus governance surface should record that absence explicitly
with source-presence or source-status posture.
