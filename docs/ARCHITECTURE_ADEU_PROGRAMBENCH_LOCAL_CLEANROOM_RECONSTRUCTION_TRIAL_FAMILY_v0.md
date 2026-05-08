# Architecture ADEU ProgramBench Local Cleanroom Reconstruction Trial Family v0

Status: architecture / decomposition note for planned `PB-TRIAL-0`.

Authority layer: architecture / decomposition.

This architecture note does not authorize official ProgramBench participation,
official task execution, official runner integration, official evaluator
integration, hidden-test handling, hidden-test inference, hidden-test
equivalence, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, model ranking, generated official
submissions, retry dispatch authority, multi-attempt comparison, arbitrary
command execution outside a released local sandbox, target mutation outside a
released local sandbox, runtime transition, product authority, graph-memory
authority, recursive policy amendment, PR creation, commit, merge, release, or
future-family selection by itself.

## Family Thesis

`PB-ATTEMPT-0` created the typed lifecycle for one local cleanroom
reconstruction attempt:

```text
released local cleanroom workbench
  -> attempt request and worker-visible input packet
  -> eligibility-only dispatch preflight
  -> one bounded local worker invocation
  -> bounded output capture and screened candidate materialization
  -> sandbox application trace
  -> workbench evidence export
  -> local attempt result review
  -> pressure-only remand queue
  -> family closeout alignment
```

The next bottleneck is not adding more schema surfaces. It is running one
local trial through that lifecycle while keeping the cleanroom and authority
boundaries explicit:

```text
released attempt lifecycle package
  -> trial docket
  -> execution runbook
  -> sandbox readiness review
  -> local worker dispatch specimen
  -> execution capture
  -> candidate artifact snapshot
  -> lifecycle projection
  -> local outcome audit
  -> remand decision / closeout
```

Controlling invariant:

```text
PB-TRIAL-0 may instantiate one local cleanroom reconstruction trial under
released PB-ATTEMPT-0 lifecycle law. It may not become official ProgramBench
participation, benchmark truth, hidden-test inference, retry authority,
model ranking, or official submission authority.
```

## Relationship To `PB-ATTEMPT-0`

`PB-TRIAL-0` consumes `PB-ATTEMPT-0` as the controlling lifecycle substrate:

- `programbench_reconstruction_attempt_request@1`
- `programbench_reconstruction_attempt_worker_input_packet@1`
- `programbench_reconstruction_attempt_dispatch_preflight@1`
- `programbench_reconstruction_attempt_non_authority_guardrail@1`
- `programbench_reconstruction_attempt_worker_invocation_record@1`
- `programbench_reconstruction_attempt_output_capture@1`
- `programbench_reconstruction_attempt_candidate_materialization@1`
- `programbench_reconstruction_attempt_sandbox_application_trace@1`
- `programbench_reconstruction_attempt_workbench_evidence_export@1`
- `programbench_reconstruction_attempt_result_review@1`
- `programbench_reconstruction_attempt_remand_queue@1`
- `programbench_reconstruction_attempt_family_closeout_alignment@1`

The attempt lifecycle remains the authority boundary. `PB-TRIAL-0` may select
one released attempt package for a local trial, execute inside that released
boundary in a later slice, and record the resulting specimen. It may not widen
worker visibility, exceed sandbox or budget law, dispatch retries, aggregate
multiple attempts, or convert local results into benchmark truth.

## Relationship To `PB-RECON-0`, `PB-ADAPTER-0`, And `PB-PY-0`

`PB-TRIAL-0` inherits workbench law from `PB-RECON-0`, cleanroom visibility
law from `PB-ADAPTER-0`, and advisory concept/realization substrate from
`PB-PY-0`.

These inputs constrain the trial; they do not grant official benchmark
authority. A Python realization overlay is advisory worker context, not source
truth. A cleanroom case packet is local reconstruction evidence, not official
ProgramBench truth. A local workbench result is local-only, not hidden-test
equivalence.

## Family Slices

### `PB-TRIAL-0-A`: Trial Docket And Runbook

Starter surfaces:

- `programbench_local_reconstruction_trial_docket@1`
- `programbench_local_trial_execution_runbook@1`
- `programbench_local_trial_sandbox_readiness_review@1`
- `programbench_local_trial_non_authority_guardrail@1`

Purpose:

- select exactly one released local attempt lifecycle package as a trial
  candidate;
- bind the trial to one worker profile, one worker-visible input packet hash,
  one sandbox policy, one run budget, and one cleanroom case lineage;
- create a runbook that names allowed local steps, expected input/output
  boundaries, timeout/budget law, write-scope law, and observation capture
  obligations;
- review sandbox readiness before execution;
- consume prior `PB-ATTEMPT-0` result-review rows only as lifecycle context,
  not as evidence of this new trial outcome;
- bind runbook hash, input materialization policy, and sandbox witness
  requirements so B has explicit proof obligations;
- preserve that slice A does not run the worker, execute commands, create
  candidate files, run probes, score results, dispatch retries, or create
  official submissions.

Forbidden:

- worker dispatch;
- local command execution;
- generated candidate files;
- candidate artifact snapshots;
- local execution capture;
- local outcome audit;
- retry authority;
- official ProgramBench participation;
- hidden-test handling;
- benchmark score or model ranking.

### `PB-TRIAL-0-B`: Local Trial Execution Capture

Later surfaces:

- `programbench_local_trial_worker_dispatch_record@1`
- `programbench_local_trial_execution_capture@1`
- `programbench_local_trial_candidate_artifact_snapshot@1`
- `programbench_local_trial_lifecycle_projection@1`

Purpose:

- record one local worker dispatch specimen under released A docket/runbook
  refs;
- capture execution with input packet hash, worker-visible context hash,
  tool manifest hashes, bounded transcript excerpts, output hashes, and
  sandbox witness refs;
- bind dispatch to a later B lock authority ref and sandbox attestation
  bundle before execution-shaped records can validate;
- snapshot candidate artifacts inside the released write scope;
- project the trial specimen back onto released `PB-ATTEMPT-0` lifecycle rows
  without inventing new evidence law.

`PB-TRIAL-0-B` is the active execution slice. It must remain single-trial and
local-only. It should not introduce retry dispatch, multi-attempt comparison,
official runner/evaluator contact, hidden-test access, or benchmark scoring.

### `PB-TRIAL-0-C`: Outcome Audit And Trial Closeout

Later surfaces:

- `programbench_local_trial_outcome_audit@1`
- `programbench_local_trial_observation_summary@1`
- `programbench_local_trial_remand_decision@1`
- `programbench_local_trial_family_closeout_alignment@1`

Purpose:

- audit the local trial outcome against released runbook, sandbox readiness,
  attempt lifecycle projection, and local workbench evidence only;
- summarize observations as local trial evidence, not benchmark truth;
- decide whether local remand pressure exists without granting retry
  authority;
- require local acceptance to have a candidate snapshot inside released write
  scope and a lifecycle projection that passed released `PB-ATTEMPT-0`
  validator bindings;
- close only `PB-TRIAL-0`.

Forbidden:

- official ProgramBench scoring;
- hidden-test equivalence;
- model leaderboard ranking;
- benchmark truth claims;
- official submissions;
- retry dispatch authority;
- selecting the next family.

## Trial Phase Law

```text
trial_docket_phase:
  consume released local attempt lifecycle refs
  select exactly one local trial candidate
  no execution

trial_runbook_phase:
  define allowed local steps and capture obligations
  no worker dispatch

sandbox_readiness_phase:
  prove sandbox/budget/readiness closure
  no local command execution yet

local_dispatch_phase:
  later slice may dispatch exactly one local worker specimen
  no official ProgramBench contact or hidden-test access

execution_capture_phase:
  later slice may capture local transcript/output/artifact hashes
  no benchmark scoring

lifecycle_projection_phase:
  later slice may map specimen evidence to released PB-ATTEMPT rows
  no new evidence law

outcome_audit_phase:
  later slice may audit local-only outcome
  no hidden-test equivalence

remand_decision_phase:
  later slice may record remand pressure
  no retry authority by itself
```

## Required Boundary Distinctions

`PB-TRIAL-0` must keep these distinctions machine-checkable:

- trial docket is not execution authority;
- runbook is not worker dispatch;
- sandbox readiness is not official runner contact;
- worker-visible packet hash is not permission to add new context;
- local dispatch specimen is not official ProgramBench task execution;
- candidate snapshot is not official submission;
- lifecycle projection is not new evidence law;
- local outcome audit is not benchmark truth;
- remand decision is not retry authority;
- local trial closeout is not future-family selection.
