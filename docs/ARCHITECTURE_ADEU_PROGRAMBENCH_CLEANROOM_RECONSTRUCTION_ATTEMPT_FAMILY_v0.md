# Architecture ADEU ProgramBench Cleanroom Reconstruction Attempt Family v0

Status: architecture / decomposition note for planned `PB-ATTEMPT-0`.

Authority layer: architecture / decomposition.

This architecture note does not authorize official ProgramBench participation,
official task execution, official runner integration, official evaluator
integration, hidden-test handling, hidden-test inference, hidden-test
equivalence, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, model ranking, generated official
submissions, arbitrary command execution outside a later selected local
sandbox, target mutation outside a later selected local sandbox, runtime
transition, product authority, graph-memory authority, recursive policy
amendment, PR creation, commit, merge, release, or future-family selection by
itself.

## Family Thesis

`PB-RECON-0` created a local cleanroom reconstruction workbench: work orders,
worker-visible context, auditor-only exclusions, sandbox policy, run budget,
candidate artifact manifests, local run traces, probe result logs,
remand/correction records, local equivalence audits, result summaries,
handoffs, and family closeout alignment.

The next bottleneck is not official benchmark solving. It is making the
worker-attempt lifecycle itself reviewable:

```text
released local workbench
  -> attempt request
  -> worker-visible input packet
  -> dispatch eligibility / sandbox preflight
  -> local worker invocation record
  -> worker output capture
  -> candidate materialization boundary
  -> exported local workbench evidence
  -> attempt result review / remand queue / closeout
```

Controlling invariant:

```text
PB-ATTEMPT-0 may orchestrate and record a local cleanroom reconstruction
attempt only under released PB-RECON-0 workbench law. It may not become
official ProgramBench participation, benchmark truth, hidden-test inference,
model ranking, or official submission authority.
```

## Relationship To `PB-RECON-0`

`PB-ATTEMPT-0` consumes `PB-RECON-0` as the controlling workbench substrate:

- `programbench_reconstruction_work_order@1`
- `programbench_reconstruction_worker_context_packet@1`
- `programbench_reconstruction_context_exclusion_manifest@1`
- `programbench_reconstruction_sandbox_policy@1`
- `programbench_reconstruction_run_budget@1`
- `programbench_reconstruction_workbench_non_authority_guardrail@1`
- `programbench_reconstruction_candidate_artifact_manifest@1`
- `programbench_reconstruction_local_run_trace@1`
- `programbench_reconstruction_probe_result_log@1`
- `programbench_reconstruction_remand_correction_record@1`
- `programbench_reconstruction_equivalence_audit@1`
- `programbench_reconstruction_result_summary@1`
- `programbench_reconstruction_handoff@1`
- `programbench_reconstruction_workbench_family_closeout_alignment@1`

The workbench remains the authority boundary. `PB-ATTEMPT-0` may package
worker input and record an attempt under that boundary; it may not widen
worker visibility, ignore auditor-only exclusions, exceed the sandbox, exceed
the run budget, or convert local evidence into benchmark truth.

## Relationship To `PB-ADAPTER-0`

`PB-ATTEMPT-0` inherits the cleanroom membrane from `PB-ADAPTER-0` through the
released case packet and access law. Hidden, forbidden, postmortem-only, and
excluded-derived evidence stays non-worker-visible. Visibility posture remains
source-bound and artifact-identity-bound.

## Relationship To `PB-PY-0`

`PB-ATTEMPT-0` may consume `PB-PY-0` Python realization rows as advisory
worker-input context only. A concept profile or Python realization overlay is
not a program source, not implementation authority, not an official
submission, and not proof of equivalence.

## Family Slices

### `PB-ATTEMPT-0-A`: Attempt Request And Worker Input

Starter surfaces:

- `programbench_reconstruction_attempt_request@1`
- `programbench_reconstruction_attempt_worker_input_packet@1`
- `programbench_reconstruction_attempt_dispatch_preflight@1`
- `programbench_reconstruction_attempt_non_authority_guardrail@1`

Purpose:

- select a released local workbench row set as a candidate attempt substrate;
- assemble the exact worker-visible input packet from released worker context,
  advisory realization refs, probe expectations, sandbox summary, and budget
  summary;
- represent auditor-only exclusions by ref without exposing excluded material;
- make worker-input manifest hashing, worker-visible ref counts, and
  forbidden-ref exposure check hashes reviewable before any dispatch;
- prove dispatch eligibility and sandbox preflight as reviewable posture;
- preserve that no worker invocation, generated candidate, command execution,
  local probe run, score, official evaluation, or model ranking is authorized
  by slice A.

Forbidden:

- worker invocation;
- worker transcript capture;
- generated candidate files;
- candidate materialization;
- local execution traces;
- probe result logs;
- workbench evidence export;
- official task execution;
- hidden-test handling;
- benchmark scores or model rankings.

### `PB-ATTEMPT-0-B`: Worker Invocation And Candidate Materialization

Later surfaces:

- `programbench_reconstruction_attempt_worker_invocation_record@1`
- `programbench_reconstruction_attempt_output_capture@1`
- `programbench_reconstruction_attempt_candidate_materialization@1`
- `programbench_reconstruction_attempt_sandbox_application_trace@1`

Purpose:

- record one bounded local worker invocation under a released attempt request
  and dispatch preflight;
- capture worker output with hashes, bounded excerpts, declared uncertainty,
  and forbidden-content screening;
- materialize candidate artifacts only inside the released sandbox write
  scope;
- record sandbox application traces without open command authority or
  official submission posture.

`PB-ATTEMPT-0-B` is the first execution-adjacent slice. It should carry a
single-attempt invocation contract unless a later lock explicitly introduces
retry parent and retry authority rows. Invocation records should bind to input
packet hash, worker-visible context hash, allowed tool manifest hash, and
forbidden tool manifest hash. Candidate materialization should be impossible
unless forbidden-content screening passes, and materialization should carry
input and output manifest hashes.

Forbidden:

- official ProgramBench evaluator execution;
- hidden-test repair loops;
- original source, decompilation, internet, or external repo lookup;
- unbounded command authority;
- benchmark scoring;
- model ranking;
- official submission authority.

### `PB-ATTEMPT-0-C`: Evidence Export, Review, And Remand Queue

Later surfaces:

- `programbench_reconstruction_attempt_workbench_evidence_export@1`
- `programbench_reconstruction_attempt_result_review@1`
- `programbench_reconstruction_attempt_remand_queue@1`
- `programbench_reconstruction_attempt_family_closeout_alignment@1`

Purpose:

- export attempt capture into released `PB-RECON-0` workbench evidence shapes
  without redefining those shapes;
- review local attempt posture against local workbench evidence only;
- queue remand/retry pressure without hidden-test diagnosis or source lookup;
- close only `PB-ATTEMPT-0`.

Exports must include released `PB-RECON-0` validator binding and validator
result refs. A positive attempt review must depend on those validator results,
not on the attempt family inventing a parallel evidence law.

Forbidden:

- official ProgramBench scoring;
- hidden-test equivalence;
- model leaderboard ranking;
- benchmark truth claims;
- official submissions;
- selecting the next family.

## Attempt Phase Law

```text
attempt_request_phase:
  consume released local workbench refs only
  no worker invocation or code generation

worker_input_phase:
  assemble worker-visible input from released cleanroom-visible refs
  no hidden, forbidden, postmortem-only, or excluded-derived evidence

dispatch_preflight_phase:
  prove local-only eligibility and sandbox/budget closure
  no execution yet in slice A

local_worker_invocation_phase:
  later slice may record one bounded worker invocation
  no official ProgramBench contact or hidden-test access

candidate_materialization_phase:
  later slice may materialize worker output inside released write scope
  candidate is not an official submission

evidence_export_phase:
  later slice may export local attempt evidence to workbench evidence rows
  local evidence is not benchmark truth

remand_phase:
  queue local remand/retry pressure only
  no hidden-test diagnosis or source lookup
```

## Required Boundary Distinctions

`PB-ATTEMPT-0` must keep these distinctions machine-checkable:

- released workbench is not automatic worker dispatch;
- attempt request is not execution authority;
- worker input packet is not permission to include hidden or forbidden rows;
- dispatch preflight is not official benchmark participation;
- worker invocation record is not model ranking;
- worker output is not candidate materialization until sandbox-bound;
- candidate materialization is not official submission;
- local evidence export is not benchmark truth;
- remand queue is not permission to use hidden tests;
- remand queue is not retry authority by itself;
- handoff pressure is not future-family selection.

## Negative Laws

- "The workbench exists" is not "the worker may run now."
- "Dispatch preflight passed" is not "official ProgramBench may be contacted."
- "A worker emitted code" is not "the code may be submitted."
- "A local candidate was materialized" is not "hidden tests pass."
- "A local probe passed" is not "benchmark truth exists."
- "A remand is queued" is not "hidden tests may diagnose the failure."
- "A worker profile is recorded" is not "a model ranking exists."
- "An attempt closes" is not "the next family is selected."
