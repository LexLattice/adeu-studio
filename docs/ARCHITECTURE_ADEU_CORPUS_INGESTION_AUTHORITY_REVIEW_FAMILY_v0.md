# Architecture ADEU Corpus Ingestion Authority Review Family v0

Status: architecture / decomposition note for planned `V82`.

Authority layer: architecture / decomposition.

This architecture note does not authorize implementation by itself. It defines
the intended family boundary for `V82` so starter locks can select bounded
implementation slices without turning corpus-ingestion review into corpus
ingestion, customer-data handling, connector activation, endpoint access,
cross-corpus adjudication execution, product authorization, benchmark truth,
release authority, or recursive policy amendment.

## Family Thesis

`V82` should make corpus-ingestion and connector-access authority review
legible before any later family considers importing corpus contents, accessing
external endpoints, activating connectors, handling customer data, running
cross-corpus adjudication, or productizing external-substrate workflows. It
consumes the `V81` cross-corpus governance substrate and emits review records
about whether a bounded corpus-ingestion horizon has source, privacy, license,
consent, data-handling, connector, endpoint, transfer, rollback, and exception
posture.

`V82` may say:

- a corpus-ingestion review request exists;
- a request is source-bound to released `V81-C` handoff or summary rows;
- a request is recordable because a missing corpus source, privacy source, or
  connector source is explicit, without being eligible for ingestion review;
- a current concrete corpus source, customer corpus source, benchmark
  descriptor, connector identifier, or endpoint identifier exists;
- later review would need data-handling authority, privacy / license /
  consent posture, connector authority, endpoint access authority, transfer
  boundaries, monitoring, rollback, and exception visibility;
- a summary can hand off pressure to a later family.

`V82` must not say:

- a corpus was ingested or imported;
- customer or third-party data was handled;
- a connector was activated;
- an endpoint was accessed or mutated;
- external data was transferred;
- imported data, benchmark results, or external results are true;
- cross-corpus adjudication was performed;
- product authorization, runtime authority, release authority, or external
  branch activation exists;
- living-memory authority exists;
- `V83` or any later family is selected.

## Source Stack Consumed

`V82` consumes:

- `V68` source / authority / namespace cartography;
- `V69` source-bound candidate identity;
- `V70` review classification and gap posture;
- `V71` ratification-review and authority-profile posture;
- `V72` containment, effect, rollback, and commit/release boundary posture;
- `V73` outcome and recommendation posture;
- `V74` operator projection and visibility posture;
- `V75` dispatch-review and worker-planning posture;
- `V76` reconciliation / arbiter and dissent posture;
- `V77` runtime-permission review, command preflight, telemetry, rollback, and
  authority posture;
- `V78` runtime execution authority review, tool-use permission envelope,
  command-scope boundary, exception, readiness, and handoff posture;
- `V79` controlled execution review, run-plan review, tool-invocation-plan
  review, effect-monitoring, exception, summary, and handoff posture;
- `V80` external branch activation review, data/tool/submission/result
  boundary posture, exceptions, summary, and handoff posture;
- `V81` cross-corpus governance request, source, boundary, provenance,
  authority-gap, exception, summary, and handoff posture.

No upstream stage becomes corpus-ingestion authority by being consumed.

## Family Slices

### `V82-A`: Corpus-Ingestion Review Intake

Starter surfaces:

- `repo_corpus_ingestion_review_request@1`
- `repo_corpus_ingestion_source_index@1`
- `repo_corpus_ingestion_non_transfer_guardrail@1`

Purpose:

- admit source-bound corpus-ingestion review requests over released `V81-C`
  summary / handoff / closeout substrate;
- distinguish current concrete corpus / privacy / license / connector /
  endpoint sources from support context and explicit absence rows;
- preserve product, external, release, benchmark, graph-memory, and recursive
  policy gaps;
- make non-transfer guardrails explicit before preflight, connector, authority,
  exception, summary, or handoff vocabulary exists.

Forbidden:

- corpus-ingestion preflight contracts;
- connector access review boundaries;
- data-handling authority review rows;
- corpus-ingestion exception registers;
- summaries;
- handoffs;
- corpus ingestion, data transfer, customer data handling, connector
  activation, endpoint access, cross-corpus adjudication, product
  authorization, release, graph-memory authority, or external branch
  activation.

### `V82-B`: Preflight, Connector Boundary, And Authority Review

Later surfaces:

- `repo_corpus_ingestion_preflight_contract@1`
- `repo_connector_access_review_boundary@1`
- `repo_corpus_data_handling_authority_review@1`
- `repo_corpus_ingestion_exception_register@1`

Purpose:

- represent corpus-ingestion preflight posture without importing or copying
  corpus contents;
- represent connector and endpoint access boundaries without activation or
  access;
- represent privacy, license, consent, retention, deletion, customer-data, and
  maintainer authority review requirements without clearance claims;
- keep blocking exceptions visible.

Forbidden:

- data ingestion, export, or transfer;
- customer data handling;
- connector activation;
- endpoint access for effect;
- ingestion permission grants;
- imported truth, benchmark truth, or cross-corpus adjudication execution;
- resolving blockers by prose.

### `V82-C`: Corpus-Ingestion Review Summary And Handoff

Later surfaces:

- `repo_corpus_ingestion_review_summary@1`
- `repo_post_corpus_ingestion_review_handoff@1`
- `repo_corpus_ingestion_review_family_closeout_alignment@1`

Purpose:

- summarize released `V82-A` request / source / guardrail rows and released
  `V82-B` preflight / connector / authority / exception rows;
- preserve blockers and nonblocking warnings;
- hand off later pressure without performing the target family;
- close `V82` as corpus-ingestion authority review only.

Forbidden:

- corpus-ingestion completion;
- connector activation completion;
- endpoint access completion;
- cross-corpus adjudication completion;
- product, release, runtime, external activation, benchmark, imported-result,
  or living-memory authority;
- selecting `V83` or any later family.

## Required Boundary Distinctions

`V82` must keep these distinctions machine-checkable:

- corpus-ingestion review request is not corpus ingestion;
- corpus source is not permission to import corpus contents;
- corpus descriptor, benchmark descriptor, connector identifier, and endpoint
  identifier rows are not corpus-content permission;
- explicit corpus-source absence is not ingestion readiness;
- source permission posture must remain explicit: permission not claimed,
  absent, requiring later authority, present for review only, or not
  applicable;
- privacy / license / consent posture is not clearance unless a later
  authority source says so;
- customer-provided source is not customer-data handling authority;
- connector identifier is not connector activation;
- endpoint identifier is not endpoint access;
- preflight contract is not ingestion permission;
- data-handling authority review is not data-handling authority grant;
- transfer boundary is not data transfer;
- monitoring requirement is not observed monitoring;
- rollback requirement is not rollback verification;
- provenance is not truth;
- benchmark descriptor is not benchmark truth;
- product pressure is not product authorization;
- graph-memory pressure is not living-memory authority;
- support / dogfood context is not ingestion eligibility by itself;
- handoff is not target-family completion.

## Negative Laws

- A roadmap label is not ingestion authority.
- A model suggestion is not ingestion authority.
- Operator desire is not ingestion authority.
- A public URL is not import permission.
- A customer mention is not customer-data permission.
- A connector name is not activation authority.
- An endpoint string is not access permission.
- A benchmark result is not benchmark truth.
- A preflight pass is not ingestion permission.
- A closeout is not next-family selection.

## Package Boundary

Primary implementation should remain in `packages/adeu_repo_description`
because `V82` is still repo/corpus review metadata, not a connector runtime,
external corpus ingestion layer, customer data processing system, product UI,
release automation layer, cross-corpus adjudication executor, or graph-query
runtime.

If later work becomes live connector access, external corpus ingestion,
customer data handling, external endpoint interaction, product UI,
cross-corpus adjudication execution, or graph query runtime, it should split
away rather than expanding repo-description by implication.
