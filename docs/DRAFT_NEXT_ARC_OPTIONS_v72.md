# Draft Next Arc Options v72

Status: planning handoff after `vNext+229` / `V81-C` merged on `main`, after
the `V81` family closeout pass, and after the combined `V68` through `V81`
dogfood probe.

Authority layer: planning.

This draft records the post-`V81` frontier. It does not authorize corpus
ingestion, external data import/export, customer-data handling, connector
activation, endpoint access, cross-corpus adjudication execution, command
execution, tool invocation, worker dispatch, product authorization, PR
creation, commit, merge, release, benchmark truth, imported-result truth,
global model selection, living-memory authority, recursive policy amendment,
or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v71.md`, which selected the `V81` cross-corpus
governance family. `vNext+227`, `vNext+228`, and `vNext+229` then closed
`V81-A`, `V81-B`, and `V81-C` without creating additional family selector
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
- `V77` is closed on `main` as the runtime-permission review family.
- `V78` is closed on `main` as the runtime execution authority review family.
- `V79` is closed on `main` as the controlled execution review family.
- `V80` is closed on `main` as the external branch activation review family.
- `V81` is closed on `main` as the cross-corpus governance family.
- latest closed implementation arc: `vNext+229`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v71.md`
- next planning obligation: select and review `V82` as the next family outside
  closed `V81`.

The combined `V68` through `V81` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V81` closed cross-corpus governance review without corpus ingestion,
customer-data handling, connector activation, endpoint access, cross-corpus
adjudication execution, benchmark truth, imported-result truth, product
authorization, release, graph-memory authority, or `V82` selection. It also
records two carry-forward findings:

- `V81` closes cross-corpus governance review with source-bound request,
  source-index, boundary, provenance, authority-gap, exception, summary, and
  handoff posture, but without corpus ingestion, customer-data handling,
  connector activation, endpoint access, cross-corpus adjudication execution,
  benchmark truth, imported-result truth, product authorization, release, or
  graph-memory authority;
- `V81-C` carries corpus-ingestion review pressure and product review pressure
  forward as later-review requests, but it does not select `V82` or grant
  downstream authority.

## Next Planning Question

The post-`V74` roadmap used `V82` as a placeholder for living decision graph /
queryable case memory. The released `V81-C` substrate now emits a nearer
source-bound pressure: corpus-ingestion review with privacy, license, source,
connector, and authority blockers. This selector therefore narrows `V82` to
the next concrete pressure and leaves graph memory as mapped but unselected
future territory.

Should the next family be `V82`: corpus-ingestion authority review, connector
access review posture, data-handling clearance requirements, transfer
boundaries, and non-transfer guardrails?

This selector intentionally treats `V82` as corpus-ingestion **review**, not
corpus ingestion. It may type what would be required before a later family
reviews ingestion or connector access for a bounded corpus horizon. It must
not ingest corpora, transfer data, handle customer data, activate connectors,
access endpoints, execute cross-corpus adjudication, productize, release, or
claim imported truth.

## Recommended Next Pressure

- family: `V82`
- proposed family name:
  - `V82: corpus-ingestion authority review, connector access posture,
    data-handling clearance requirements, and non-transfer guardrails`
- recommended planning posture:
  - select `V82` as the next family based on concrete `V81-C`
    `future_corpus_ingestion_review` handoff pressure;
  - select `V82-A` as the next default candidate for `vNext+230`;
  - consume `V81-C` cross-corpus governance summaries,
    post-cross-corpus-review handoffs, and family closeout alignment as
    immediate source substrate;
  - consume released `V81-B` corpus boundary, provenance, authority-gap, and
    exception rows as context;
  - consume the combined `V68` through `V81` dogfood as support context;
  - define source-bound corpus-ingestion review requests, source indexes, and
    non-transfer guardrails before any preflight contract, connector boundary,
    data-handling authority review, exception register, summary, or handoff is
    represented.

`V82` should type the question "what would need to be true before a later
family may review bounded corpus ingestion or connector access?" It must not
perform ingestion, activate a connector, access an endpoint, transfer data, or
turn a request into clearance.

## Proposed Family Decomposition

`V82` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V82-A` | corpus-ingestion review request, source index, and non-transfer guardrail over released `V81-C` handoff / closeout substrate plus explicit corpus source or absence rows |
| `V82-B` | corpus-ingestion preflight contract, connector access review boundary, data-handling authority review, and corpus-ingestion exception register |
| `V82-C` | corpus-ingestion review summary, post-corpus-ingestion-review handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V82-A` should be the first active slice. Candidate starter surfaces:

- `repo_corpus_ingestion_review_request@1`
- `repo_corpus_ingestion_source_index@1`
- `repo_corpus_ingestion_non_transfer_guardrail@1`

Recommendation: select `V82-A` as the next default candidate after this
selector, with `vNext+230` as the canonical starter bundle if no intervening
arc claims that number.

Later `V82` surfaces should remain planning-layer until their own starter
locks:

- `repo_corpus_ingestion_preflight_contract@1`
- `repo_connector_access_review_boundary@1`
- `repo_corpus_data_handling_authority_review@1`
- `repo_corpus_ingestion_exception_register@1`
- `repo_corpus_ingestion_review_summary@1`
- `repo_post_corpus_ingestion_review_handoff@1`
- `repo_corpus_ingestion_review_family_closeout_alignment@1`

Post-`V82-A` continuation posture: after `vNext+230` closes on `main`, select
`V82-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V82` family and does not
create a new next-arc-options selector version.

Post-`V82-B` continuation posture: after the `V82-B` slice closes on `main`,
select `V82-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V82` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- corpus ingestion or external data import/export;
- customer data handling;
- connector activation;
- endpoint access or mutation;
- cross-corpus adjudication execution;
- benchmark truth, imported-result truth, or external result truth;
- product launch, product-market validation, or product authorization;
- external branch activation, `V43` contest participation, or external
  submission;
- command execution, tool invocation, worker assignment, or dispatch
  execution;
- PR creation, commit, merge, release, or released-truth authority;
- global model selection;
- living decision graph authority;
- recursive policy amendment;
- `V83` or any later family.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`V82` is planning-ready because the post-`V81` substrate can cite concrete
released rows showing:

- `V81-C` emits a `future_corpus_ingestion_review` handoff for the
  self-evidencing workflow case while preserving missing corpus source,
  privacy, license, and connector blockers;
- `V81-C` emits product review pressure separately for the product wedge
  instead of converting product pressure into ingestion readiness;
- `V81` closeout keeps corpus ingestion, customer-data handling, connector
  activation, endpoint access, cross-corpus adjudication execution,
  benchmark truth, imported-result truth, graph-memory authority, and `V82`
  selection unselected;
- the combined dogfood confirms no corpus ingestion, no connector activation,
  no endpoint access, no cross-corpus adjudication execution, no product
  authorization, and no downstream family selection.

`V82-A` request recordability must be stricter than selector readiness, and
eligibility must be stricter than request recordability. A corpus-ingestion
review request may be recorded when released `V81-C` handoff pressure exists
and either a current concrete corpus source or explicit corpus-source absence
row exists. Explicit absence rows support
`request_recorded_absence_only` or `blocked_by_missing_corpus_source`; they do
not by themselves support `eligible_for_corpus_ingestion_review`.

An eligible row must cite released `V81-C` handoff or summary substrate, at
least one current concrete corpus or customer corpus source, privacy / license
/ consent posture, and non-transfer guardrail rows. Corpus descriptors,
benchmark descriptors, connector identifiers, endpoint identifiers, and
absence rows may support recordability or blockers; they cannot be the only
eligibility source. Support and dogfood sources may contextualize `V82-A`;
they cannot be the only eligibility source.

`V82` must not be used if the only evidence is:

- an operator desire to ingest data;
- a model suggestion that ingestion would be useful;
- a roadmap label without concrete current corpus source or explicit absence
  posture;
- a public URL treated as permission to import;
- customer data mentioned in transcript without privacy, license, consent, or
  customer authority posture;
- a connector name treated as activation authority;
- an endpoint string treated as access permission;
- a benchmark result treated as benchmark truth;
- product-pressure visibility treated as product authorization;
- graph-memory interest treated as living-memory authority.

## Inputs For Starter Drafting

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v71.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v229/evidence_inputs/v81_family_closeout_alignment_v229.json`
- `artifacts/agent_harness/v229/evidence_inputs/v81c_cross_corpus_governance_closeout_evidence_v229.json`
- `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_summary_v229_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus229/repo_post_cross_corpus_review_handoff_v229_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_family_closeout_alignment_v229_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

## Lock Readiness Note

The future `vNext+230` starter lock should consume committed `V68` through
`V81` closeouts, the combined dogfood artifacts, `vNext+229` evidence inputs,
and released `V81-C` summary / handoff / closeout fixtures as concrete source
rows. If any expected corpus source, privacy source, license/consent source,
customer authority source, connector authority source, or endpoint authority
source is missing, the `V82-A` corpus-ingestion review surface should record
that absence explicitly with source-presence or source-status posture.
