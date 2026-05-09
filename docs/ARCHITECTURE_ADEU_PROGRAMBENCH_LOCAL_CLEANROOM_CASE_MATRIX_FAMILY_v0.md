# Architecture ADEU ProgramBench Local Cleanroom Case Matrix Family v0

Status: architecture / decomposition note for planned `PB-MATRIX-0`.

Authority layer: architecture / decomposition.

This architecture note does not authorize official ProgramBench participation,
official task execution, official runner integration, official evaluator
integration, hidden-test handling, hidden-test inference, hidden-test
equivalence, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, model ranking, leaderboard standing,
generated official submissions, official submission authority, second retry
authority, retry-chain authority, batch command execution, target mutation
outside a released local sandbox/write scope, runtime transition, product
authority, graph-memory authority, recursive policy amendment, PR creation,
commit, merge, release, or future-family selection by itself.

## Family Thesis

`PB-RETRY-0` created the typed lifecycle for one bounded local cleanroom retry:

```text
released local trial remand decision
  -> retry request and retry lineage registry
  -> local-only remand source index
  -> retry eligibility review
  -> unchanged-boundary retry scope contract
  -> one local retry dispatch specimen
  -> retry execution capture
  -> candidate delta snapshot
  -> lifecycle projection
  -> sandbox application trace
  -> local retry outcome audit
  -> same-lineage delta observation summary
  -> local remand settlement
  -> family closeout alignment
```

The next bottleneck is not official benchmark participation. It is lawful
scaling from one governed case lineage to a small local matrix of case
lineages:

```text
released local case lineage(s)
  -> case matrix request
  -> inclusion manifest
  -> lineage eligibility review
  -> shared control contract
  -> later per-case result projection
  -> later matrix observation ledger
  -> later matrix coverage / contamination registers
  -> later matrix summary and handoff
```

Controlling invariant:

```text
PB-MATRIX-0 may govern a local cleanroom case matrix over released local
case lineages. It may not turn matrix inclusion, aggregate counts, local
coverage, per-case posture, retry settlement, or observation summaries into
benchmark truth, hidden-test equivalence, model ranking, leaderboard standing,
official submission authority, batch execution authority, or future-family
selection.
```

## Relationship To `PB-RETRY-0`

`PB-MATRIX-0` consumes `PB-RETRY-0` as optional retry-settlement substrate:

- `programbench_local_retry_request@1`
- `programbench_local_retry_lineage_registry@1`
- `programbench_trial_remand_source_index@1`
- `programbench_local_retry_eligibility_review@1`
- `programbench_local_retry_scope_contract@1`
- `programbench_local_retry_non_authority_guardrail@1`
- `programbench_local_retry_dispatch_record@1`
- `programbench_local_retry_execution_capture@1`
- `programbench_local_retry_candidate_delta_snapshot@1`
- `programbench_local_retry_lifecycle_projection@1`
- `programbench_local_retry_sandbox_application_trace@1`
- `programbench_local_retry_outcome_audit@1`
- `programbench_local_retry_delta_observation_summary@1`
- `programbench_local_retry_remand_settlement@1`
- `programbench_local_retry_family_closeout_alignment@1`

The retry lifecycle remains the authority boundary for retry evidence.
`PB-MATRIX-0` may include released retry settlement as local case posture. It
may not create a second retry, compare unrelated workers or models, rewrite
the retry outcome, erase unresolved remand pressure, or claim official
ProgramBench standing.

## Relationship To Earlier ProgramBench Families

`PB-MATRIX-0` inherits:

- cleanroom fixture and concept/realization substrate from `PB-PY-0`;
- task intake, visibility, probe observation, and case-packet law from
  `PB-ADAPTER-0`;
- workbench and local evidence law from `PB-RECON-0`;
- attempt lifecycle law from `PB-ATTEMPT-0`;
- single-trial specimen law from `PB-TRIAL-0`;
- retry governance law from `PB-RETRY-0`.

These inputs constrain matrix inclusion. They do not grant official benchmark
authority, hidden-test inference authority, wider source visibility, model
ranking, official submission authority, or batch execution authority.

## Family Slices

### `PB-MATRIX-0-A`: Matrix Intake And Inclusion Controls

Starter surfaces:

- `programbench_local_case_matrix_request@1`
- `programbench_local_case_inclusion_manifest@1`
- `programbench_local_case_lineage_eligibility_review@1`
- `programbench_local_case_matrix_control_contract@1`
- `programbench_local_case_matrix_non_authority_guardrail@1`

Purpose:

- record a request to assemble a local cleanroom case matrix;
- identify candidate case lineages and their released source families;
- decide whether each case lineage is eligible for matrix inclusion;
- define shared controls for worker profile, tool policy, probe basis,
  cleanroom visibility, sandbox/write-scope posture, and non-ranking posture;
- preserve that slice A does not project per-case results, compute aggregate
  summaries, run commands, execute cases, materialize candidates, score
  benchmarks, rank models, or select a future family.

Forbidden:

- official ProgramBench participation;
- official task execution;
- benchmark score or model ranking;
- hidden-test handling;
- per-case result projection;
- matrix summary;
- batch execution;
- second retry or retry-chain authority.

### `PB-MATRIX-0-B`: Per-Case Projection And Matrix Observation Ledger

Later surfaces:

- `programbench_local_case_matrix_result_projection@1`
- `programbench_local_case_matrix_observation_ledger@1`
- `programbench_local_case_matrix_coverage_register@1`
- `programbench_local_case_matrix_contamination_register@1`

Purpose:

- project released per-case trial/retry/attempt/workbench postures into a
  common local matrix row vocabulary;
- preserve one current matrix result projection per included case lineage;
- record local observation rows, coverage rows, blocker rows, and
  contamination rows without ranking models or claiming benchmark standing;
- preserve hidden/forbidden evidence exclusions, source lineage, and local-only
  benchmark-not-truth posture.

`PB-MATRIX-0-B` should not execute cases directly. If later work wants batch
dispatch or suite execution, that requires a separate family or a later lock
that explicitly grants batch execution authority.

### `PB-MATRIX-0-C`: Matrix Summary And Closeout

Later surfaces:

- `programbench_local_case_matrix_summary@1`
- `programbench_post_case_matrix_handoff@1`
- `programbench_local_case_matrix_family_closeout_alignment@1`

Purpose:

- summarize the local matrix as a set of local case postures, coverage status,
  blockers, and non-authority limitations;
- carry handoff pressure for later local case expansion, official
  participation review, hidden-evaluator governance, model-comparison
  governance, or batch execution review without selecting any of them;
- close only `PB-MATRIX-0`.

Forbidden:

- benchmark score;
- official success claim;
- model ranking;
- leaderboard standing;
- official submission authority;
- hidden-test equivalence;
- future-family selection.

## Matrix Phase Law

```text
matrix_request_phase:
  record local matrix request
  no per-case result projection

case_inclusion_phase:
  list candidate case lineages and released source refs
  reject unreleased, contaminated, hidden/evaluator/source-derived cases

lineage_eligibility_phase:
  decide which cases are eligible for local matrix inclusion
  no benchmark scoring

control_contract_phase:
  define shared matrix controls and non-ranking posture
  no execution

result_projection_phase:
  later slice may project released per-case local results
  no new trial/retry execution

observation_ledger_phase:
  later slice may record local matrix observations and blockers
  no model ranking or official score

matrix_summary_phase:
  later slice may summarize local matrix posture and handoff pressure
  no future-family selection
```

## Cleanroom Matrix Law

A matrix cannot widen source visibility. Included case rows may cite only
released local cleanroom refs or non-content-bearing exclusion categories.

Forbidden, hidden, postmortem-only, original-source, decompilation, internet,
external-repository, host-secret, Docker-socket, official-evaluator, and
hidden-test refs must remain excluded. They must not be exposed directly or
through derived summaries in inclusion manifests, result projections,
observation ledgers, coverage registers, contamination registers, matrix
summaries, or handoffs.

## Non-Ranking Law

Local matrix aggregation may answer:

```text
Which local case lineages are included?
Which local postures are present?
Which local blockers remain?
Which local evidence categories are covered or missing?
Which future review pressures exist?
```

It must not answer:

```text
Which model is better?
What is the benchmark score?
Was ProgramBench solved?
Should this be submitted officially?
What hidden tests would pass?
Should another retry run automatically?
```

## Aggregate Count Law

Local matrix counts are inventory and accounting only. They may describe:

```text
included case count
projected local posture count
local remand count
local blocker count
local coverage-gap count
contamination-blocked count
```

They must not become:

```text
pass rate
solve rate
success rate
benchmark score
official success rate
leaderboard metric
model score
```

Allowed aggregate count postures:

- `local_inventory_count_only`
- `local_case_posture_count_only`
- `coverage_accounting_only`
- `not_benchmark_score`

Any denominator used by `PB-MATRIX-0` is the declared local matrix denominator,
not the official ProgramBench task count, hidden-test count, benchmark sample
count, or model-evaluation denominator.

## Case Selection Law

Case selection must be explicit and non-representative unless a later
benchmark-result governance family says otherwise. Matrix intake should carry:

- per-case candidate rows with released lineage refs and boundary hashes;
- matrix selection rationale rows;
- matrix horizon;
- matrix maximum case count;
- representativeness posture.

Allowed local matrix horizons:

- `local_smoke_matrix`
- `local_regression_matrix`
- `local_coverage_probe_matrix`
- `local_research_matrix`
- `not_representative_benchmark_sample`

The default matrix control posture is one worker profile, one model/profile
posture, one tool policy, one probe basis, and one sandbox/write-scope
posture. Multi-profile matrices are allowed only as comparability accounting
with `multi_profile_matrix_posture =
comparability_accounting_only_no_ranking`; they are not model-comparison
authority.

## Negative Laws

`PB-MATRIX-0` must keep these distinctions machine-checkable:

- case matrix is not official benchmark suite;
- case inclusion is not benchmark participation;
- per-case local result is not hidden-test truth;
- aggregate count is not benchmark score;
- local coverage is not hidden-test equivalence;
- observation summary is not model ranking;
- representative-looking local selection is not benchmark representativeness;
- contamination register is not postmortem evidence admission;
- handoff pressure is not future-family selection;
- unresolved remand pressure is not retry-chain authority.

## Deferred Seams

The following seams remain future-family-only unless separately selected:

- official ProgramBench participation;
- official runner/evaluator integration;
- hidden evaluator result governance;
- benchmark-result and benchmark-score governance;
- model-ranking or leaderboard governance;
- batch execution over a matrix;
- second retry or retry-chain governance;
- generated official submission review;
- larger fixture generation beyond released local case lineage law;
- natural task-to-program-profile inference;
- generalized conceptual broker implementation;
- multi-language realization overlays;
- `V86`, `V87`, and `V88` continuations;
- product, graph-memory, release, or recursive-policy work.
