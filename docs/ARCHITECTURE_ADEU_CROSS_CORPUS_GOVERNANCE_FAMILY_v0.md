# Architecture ADEU Cross-Corpus Governance Family v0

Status: architecture / decomposition note for planned `V81`.

Authority layer: architecture / decomposition.

This architecture note does not authorize implementation by itself. It defines
the intended family boundary for `V81` so starter locks can select bounded
implementation slices without turning cross-corpus governance review into
external data ingestion, customer substrate handling, connector activation,
product authorization, benchmark truth, release authority, or recursive policy
amendment.

## Family Thesis

`V81` should make non-repo / imported-substrate governance review legible
before any later family considers cross-corpus adjudication, customer corpus
ingestion, benchmark-result comparison, external corpus reports, connector
workflows, or productized typed-adjudication over external material. It
consumes the `V80` external branch activation review substrate and emits
review records about whether a bounded external or imported corpus horizon has
source, provenance, authority, privacy, license, boundary, and exception
posture.

`V81` may say:

- a cross-corpus governance review request exists;
- a corpus source or absence posture supports that request;
- a request is recordable because absence is explicit, without being eligible
  for cross-corpus governance readiness;
- a candidate corpus horizon is repo-local, external public, customer-provided,
  benchmark-result, paper/design/repo bundle, synthetic, or unknown;
- later review would need corpus boundary contracts, imported-substrate
  provenance, authority grants, privacy review, license review, data-handling
  posture, and exception visibility;
- a summary can hand off pressure to a later family.

`V81` must not say:

- an external corpus was ingested;
- customer or third-party data was imported;
- a connector was activated;
- an external endpoint was accessed;
- imported data is true;
- benchmark results are benchmark truth;
- cross-corpus adjudication was performed;
- product authorization, runtime authority, release authority, or external
  branch activation exists;
- `V82` or any later family is selected.

## Source Stack Consumed

`V81` consumes:

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
  boundary posture, exceptions, summary, and handoff posture.

No upstream stage becomes cross-corpus ingestion authority by being consumed.

## Family Slices

### `V81-A`: Cross-Corpus Governance Intake

Starter surfaces:

- `repo_cross_corpus_governance_request@1`
- `repo_cross_corpus_source_index@1`
- `repo_cross_corpus_non_ingestion_guardrail@1`

Purpose:

- admit source-bound cross-corpus governance review requests over released
  `V80-C` summary / handoff / closeout substrate;
- distinguish concrete corpus sources from support context and explicit
  absence rows;
- preserve product, runtime, release, external activation, privacy, license,
  and recursive-policy gaps;
- make non-ingestion guardrails explicit before corpus-boundary,
  imported-provenance, authority-gap, or exception vocabulary exists.

Forbidden:

- corpus boundary contracts;
- imported-substrate provenance registers;
- authority gap registers;
- exception registers;
- summaries;
- handoffs;
- external data ingestion, connector activation, customer data handling,
  external endpoint access, cross-corpus adjudication, product authorization,
  release, or external branch activation.

### `V81-B`: Corpus Boundary, Provenance, And Authority Gaps

Later surfaces:

- `repo_corpus_boundary_contract@1`
- `repo_imported_substrate_provenance_register@1`
- `repo_cross_corpus_authority_gap_register@1`
- `repo_cross_corpus_exception_register@1`

Purpose:

- represent corpus boundary posture without importing or copying corpus
  contents;
- represent imported-substrate provenance without claiming imported truth;
- represent privacy, license, consent, maintainer, product, and external
  authority gaps;
- keep blocking exceptions visible.

Forbidden:

- data ingestion or export;
- customer data handling;
- connector activation;
- endpoint access for effect;
- corpus truth or benchmark truth;
- cross-corpus adjudication execution;
- resolving blockers by prose.

### `V81-C`: Cross-Corpus Governance Summary And Handoff

Later surfaces:

- `repo_cross_corpus_governance_summary@1`
- `repo_post_cross_corpus_review_handoff@1`
- `repo_cross_corpus_governance_family_closeout_alignment@1`

Purpose:

- summarize released `V81-A` request / source / guardrail rows and released
  `V81-B` boundary / provenance / authority / exception rows;
- preserve blockers and nonblocking warnings;
- hand off later pressure without performing the target family;
- close `V81` as cross-corpus governance review only.

Forbidden:

- cross-corpus ingestion completion;
- cross-corpus adjudication completion;
- product, release, runtime, external activation, connector, or living-memory
  authority;
- selecting `V82` or any later family.

## Required Boundary Distinctions

`V81` must keep these distinctions machine-checkable:

- cross-corpus governance request is not corpus ingestion;
- corpus source is not permission to import corpus contents;
- explicit corpus-source absence is not cross-corpus readiness;
- historical or stale corpus context is not a current concrete corpus source;
- corpus boundary is not data handling authority;
- provenance register is not truth;
- benchmark result source is not benchmark truth;
- customer-provided source is not customer-data handling authority;
- connector identifier is not connector activation;
- external endpoint string is not access permission;
- privacy / license posture is not privacy / license clearance unless an
  explicit later authority source says so;
- product pressure is not product authorization;
- external branch handoff is not external branch activation;
- support / dogfood context is not cross-corpus eligibility by itself;
- handoff is not target-family completion.

## Negative Laws

- A roadmap label is not corpus authority.
- A model suggestion is not corpus authority.
- Operator desire is not corpus authority.
- A public URL is not ingestion permission.
- A customer mention is not customer-data permission.
- A benchmark result is not benchmark truth.
- A connector name is not connector activation.
- A corpus boundary is not corpus transfer.
- A provenance register is not truth.
- A closeout is not next-family selection.

## Package Boundary

Primary implementation should remain in `packages/adeu_repo_description`
because `V81` is still repo/corpus review metadata, not a connector runtime,
external corpus ingestion layer, customer data processing system,
product-facing report renderer, release automation layer, or graph-query
runtime.

If later work becomes live connector access, external corpus ingestion,
customer data handling, persistent graph storage, product UI, or release
automation, it should split away rather than expanding repo-description by
implication.
