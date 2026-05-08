# Architecture ADEU ProgramBench Local Cleanroom Retry Governance Family v0

Status: architecture / decomposition note for planned `PB-RETRY-0`.

Authority layer: architecture / decomposition.

This architecture note does not authorize official ProgramBench participation,
official task execution, official runner integration, official evaluator
integration, hidden-test handling, hidden-test inference, hidden-test
equivalence, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, model ranking, generated official
submissions, official submission authority, retry dispatch authority,
multi-attempt comparison, arbitrary command execution outside a released local
sandbox, target mutation outside a released local sandbox/write scope,
runtime transition, product authority, graph-memory authority, recursive
policy amendment, PR creation, commit, merge, release, or future-family
selection by itself.

## Family Thesis

`PB-TRIAL-0` created the typed lifecycle for one local cleanroom
reconstruction trial:

```text
released local cleanroom attempt lifecycle package
  -> trial docket
  -> execution runbook
  -> sandbox readiness review
  -> one local worker dispatch specimen
  -> execution capture
  -> candidate artifact snapshot
  -> lifecycle projection
  -> local outcome audit
  -> single-trial observation summary
  -> local-only remand decision
  -> family closeout alignment
```

The next bottleneck is not official benchmark participation. It is lawful
re-entry after a local trial emits remand pressure:

```text
released trial remand decision
  -> retry request intake
  -> remand source index
  -> retry eligibility review
  -> retry scope contract
  -> later retry dispatch specimen
  -> later retry execution capture
  -> later retry candidate delta snapshot
  -> later retry outcome audit
  -> remand settlement / closeout
```

Controlling invariant:

```text
PB-RETRY-0 may govern one bounded local cleanroom retry lifecycle for a
released PB-TRIAL-0 lineage. It may not treat remand pressure as dispatch
authority, widen worker-visible evidence, use hidden or forbidden sources,
rank models, create benchmark truth, submit officially, or create unbounded
retry authority.
```

Loop-control invariant:

```text
One bounded retry means one eligible retry request for one released trial
lineage and one released remand decision. Repeating "single" retry requests
for the same remand is not allowed inside PB-RETRY-0.
```

## Relationship To `PB-TRIAL-0`

`PB-RETRY-0` consumes `PB-TRIAL-0` as the controlling trial substrate:

- `programbench_local_reconstruction_trial_docket@1`
- `programbench_local_trial_execution_runbook@1`
- `programbench_local_trial_sandbox_readiness_review@1`
- `programbench_local_trial_non_authority_guardrail@1`
- `programbench_local_trial_worker_dispatch_record@1`
- `programbench_local_trial_execution_capture@1`
- `programbench_local_trial_candidate_artifact_snapshot@1`
- `programbench_local_trial_lifecycle_projection@1`
- `programbench_local_trial_outcome_audit@1`
- `programbench_local_trial_observation_summary@1`
- `programbench_local_trial_remand_decision@1`
- `programbench_local_trial_family_closeout_alignment@1`

The trial lifecycle remains the authority boundary for the prior local
specimen. `PB-RETRY-0` may inspect its released local remand decision and
same-lineage evidence to determine whether one retry candidate is eligible.
It may not mutate the prior trial, erase its outcome, convert remand pressure
into dispatch authority, compare unrelated attempts, or claim benchmark
standing.

## Relationship To Earlier ProgramBench Families

`PB-RETRY-0` inherits:

- workbench law from `PB-RECON-0`;
- cleanroom visibility law from `PB-ADAPTER-0`;
- advisory concept and Python realization substrate from `PB-PY-0`;
- attempt lifecycle law from `PB-ATTEMPT-0`;
- single-trial evidence and local remand source from `PB-TRIAL-0`.

These inputs constrain retry. They do not grant official benchmark authority,
hidden-test inference authority, wider source visibility, model ranking, or
unbounded iteration.

## Family Slices

### `PB-RETRY-0-A`: Retry Intake And Eligibility

Starter surfaces:

- `programbench_local_retry_request@1`
- `programbench_local_retry_lineage_registry@1`
- `programbench_trial_remand_source_index@1`
- `programbench_local_retry_eligibility_review@1`
- `programbench_local_retry_scope_contract@1`
- `programbench_local_retry_non_authority_guardrail@1`

Purpose:

- record a request to consider one retry for one released `PB-TRIAL-0`
  lineage;
- bind that request to a retry lineage registry so the same trial remand
  cannot become many separately eligible single retries;
- index the local remand source rows and distinguish retryable local gaps from
  non-retryable blockers;
- require local-only remand source, clean contamination posture, and released
  trial family closeout before eligibility;
- define the retry scope delta, retry depth limit, worker-visible context
  continuity, unchanged forbidden-evidence posture, and no-dispatch posture;
- preserve that slice A does not run the worker, execute commands, create
  candidate files, dispatch a retry, run probes, score results, create
  official submissions, rank models, or grant second-retry authority.

Forbidden:

- retry dispatch;
- local command execution;
- generated retry candidate files;
- retry execution capture;
- retry outcome audit;
- retry delta observation summary;
- official ProgramBench participation;
- hidden-test handling;
- benchmark score or model ranking.

### `PB-RETRY-0-B`: Local Retry Dispatch Capture

Later surfaces:

- `programbench_local_retry_dispatch_record@1`
- `programbench_local_retry_execution_capture@1`
- `programbench_local_retry_candidate_delta_snapshot@1`
- `programbench_local_retry_lifecycle_projection@1`
- `programbench_local_retry_sandbox_application_trace@1`

Purpose:

- record one local retry dispatch specimen under released A eligibility and
  scope refs;
- bind retry dispatch to the original trial lineage, retry request,
  retry depth limit, worker-visible input hash, retry scope delta, sandbox
  policy, run budget, tool manifest, and a later B lock authority ref;
- capture retry execution with bounded transcript excerpts, output hashes,
  tool manifests, sandbox witnesses, and forbidden-content screening;
- snapshot retry candidate deltas only inside the released write scope;
- project retry evidence back onto released `PB-TRIAL-0` and `PB-ATTEMPT-0`
  lifecycle rows without inventing new evidence law.

`PB-RETRY-0-B` is the execution-adjacent retry slice. It must remain one
bounded local retry specimen. It must not create official runner/evaluator
contact, hidden-test access, benchmark scoring, model ranking, or another
retry chain.

### `PB-RETRY-0-C`: Retry Outcome And Settlement

Later surfaces:

- `programbench_local_retry_outcome_audit@1`
- `programbench_local_retry_delta_observation_summary@1`
- `programbench_local_retry_remand_settlement@1`
- `programbench_local_retry_family_closeout_alignment@1`

Purpose:

- audit the retry outcome against released A/B rows, local evidence, sandbox
  law, and lifecycle projection only;
- summarize same-lineage before/after local observations without ranking
  models, comparing unrelated attempts, or claiming benchmark truth;
- settle remand as locally resolved, locally unresolved, inconclusive,
  blocked, or deferred without granting another retry by itself;
- close only `PB-RETRY-0`.

Forbidden:

- official ProgramBench scoring;
- hidden-test equivalence;
- model leaderboard ranking;
- benchmark truth claims;
- official submissions;
- automatic second retries;
- selecting the next family.

## Retry Phase Law

```text
retry_request_phase:
  consume released local trial closeout and remand refs
  no execution

remand_source_index_phase:
  classify local remand source rows
  reject hidden/evaluator/source/internet/decompilation origins

retry_eligibility_phase:
  decide whether the remand can become one bounded retry candidate
  no dispatch

retry_scope_contract_phase:
  define retry scope delta, unchanged evidence boundary, and retry depth
  no candidate materialization

retry_dispatch_phase:
  later slice may dispatch one local retry specimen if lock authority exists
  no official ProgramBench contact or hidden-test access

retry_capture_phase:
  later slice may capture retry output and sandbox evidence
  no benchmark scoring

retry_delta_snapshot_phase:
  later slice may snapshot candidate deltas inside write scope
  no official submission

retry_outcome_phase:
  later slice may audit local retry result and settle remand
  no automatic next retry
```

## Cleanroom Continuity Law

Retry cannot widen the evidence boundary. The worker-visible context for a
retry may include only released cleanroom-visible material, allowed local
trial artifacts, and retry-scope deltas that are themselves cleanroom-visible.

Forbidden, hidden, postmortem-only, original-source, decompilation, internet,
external-repository, host-secret, Docker-socket, official-evaluator, and
hidden-test refs must remain excluded. They must not be exposed directly or
through derived summaries in retry request, worker-visible context, retry
scope, execution capture, delta observation summary, or remand settlement
rows.

Remand source rows may describe local failure or gap categories. They must not
include hidden or forbidden source names, paths, excerpts, semantic summaries,
test names, original-source clues, or derived facts.

## Retry Rationale Law

Allowed retry rationale kinds:

- `local_probe_failure`
- `local_output_capture_gap`
- `local_candidate_snapshot_gap`
- `lifecycle_projection_gap`
- `runbook_satisfaction_gap`
- `worker_declared_uncertainty`
- `local_evidence_inconclusive`

Forbidden retry rationale kinds:

- `hidden_test_failure`
- `official_evaluator_feedback`
- `source_lookup_fact`
- `decompilation_fact`
- `internet_lookup_fact`
- `external_repo_fact`
- `benchmark_score_pressure`
- `model_ranking_pressure`

Retry rationale can explain why a local retry candidate is being considered.
It cannot grant dispatch authority, widen the cleanroom boundary, or create a
second retry.

## Same-Lineage Delta Law

`PB-RETRY-0-C` may compare the original local trial and the retry only inside
one released retry lineage:

```text
same trial lineage
same cleanroom case
same worker-visible evidence boundary
same declared local probe basis
same local-only benchmark-not-truth posture
```

It may not compare models, workers, unrelated attempts, benchmark tasks,
official scores, hidden-test outcomes, or leaderboard standing.

## Family Non-Goals

`PB-RETRY-0` does not select:

- official ProgramBench participation;
- hidden-test handling or hidden-test repair;
- official runner/evaluator integration;
- benchmark scoring or benchmark truth;
- model ranking or leaderboard reporting;
- generated official submission review;
- unbounded retry loops or second retries by default;
- multi-attempt comparison across unrelated lineages;
- larger fixture matrices;
- natural task-to-program-profile inference;
- broader conceptual broker implementation;
- product, graph-memory, release, or recursive-policy authority.
