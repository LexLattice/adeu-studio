# Architecture ADEU ProgramBench Cleanroom Reconstruction Workbench Family v0

Status: architecture / decomposition note for planned `PB-RECON-0`.

Authority layer: architecture / decomposition.

This architecture note does not authorize official ProgramBench participation,
official task execution, official runner integration, official evaluator
integration, hidden-test handling, hidden-test inference, original source
lookup, decompilation, internet lookup inside ProgramBench tasks, external
repository lookup, benchmark submission, benchmark scoring, benchmark truth,
model ranking, generated official submissions, arbitrary command execution
outside a later selected local sandbox, target mutation outside a later
selected local sandbox, runtime transition, product authority, graph-memory
authority, recursive policy amendment, PR creation, commit, merge, release, or
future-family selection by itself.

## Family Thesis

`PB-ADAPTER-0` created a cleanroom adapter membrane: task intake, artifact
identity, visibility/access law, local probe observations, reconstruction case
packets, readiness summaries, and handoff pressure. The next bottleneck is not
official ProgramBench solving. It is making a local reconstruction attempt
reviewable under that membrane:

```text
released reconstruction case packet
  -> work order
  -> worker context packet
  -> sandbox and budget policy
  -> candidate artifact capture
  -> local probe run observations
  -> local equivalence audit
  -> result summary / remand / handoff
```

Controlling invariant:

```text
PB-RECON-0 may run only as a local cleanroom reconstruction workbench under
released case-packet and sandbox law. It may not become official ProgramBench
participation, benchmark truth, hidden-test inference, model ranking, or
official submission authority.
```

## Relationship To `PB-ADAPTER-0`

`PB-RECON-0` consumes `PB-ADAPTER-0` as adapter substrate:

- `programbench_cleanroom_task_intake@1`
- `programbench_task_artifact_manifest@1`
- `programbench_task_visibility_manifest@1`
- `programbench_adapter_worker_access_contract@1`
- `programbench_adapter_non_authority_guardrail@1`
- `programbench_adapter_probe_plan@1`
- `programbench_probe_observation_log@1`
- `programbench_io_artifact_observation_index@1`
- `programbench_filesystem_side_effect_observation@1`
- `programbench_reconstruction_case_packet@1`
- `programbench_adapter_readiness_summary@1`
- `programbench_adapter_handoff@1`
- `programbench_cleanroom_adapter_family_closeout_alignment@1`

Only case packets with ready posture and no contamination blockers may become
workbench candidates. A case packet remains evidence substrate; it does not by
itself authorize worker dispatch, code generation, command execution, official
evaluation, or submission.

## Relationship To `PB-PY-0`

`PB-RECON-0` may consume `PB-PY-0` Python realization records as advisory
reconstruction substrate:

- cleanroom reconstruction profiles;
- program ODEU concept boundary seeds;
- Python realization packs;
- Python reconstruction plans;
- Python witness templates;
- local fixture and comparison/audit records.

Those records remain advisory and local. A Python realization row is not a
canonical program concept definition, not source code, not an executable
command, and not proof of equivalence.

## Family Slices

### `PB-RECON-0-A`: Work Order And Worker Context

Starter surfaces:

- `programbench_reconstruction_work_order@1`
- `programbench_reconstruction_worker_context_packet@1`
- `programbench_reconstruction_context_exclusion_manifest@1`
- `programbench_reconstruction_sandbox_policy@1`
- `programbench_reconstruction_run_budget@1`
- `programbench_reconstruction_workbench_non_authority_guardrail@1`

Purpose:

- select a released, ready, uncontaminated case packet for later local
  reconstruction review;
- bind the exact worker-visible context packet derived from released adapter
  and realization rows;
- bind an auditor-only exclusion manifest for hidden, forbidden,
  postmortem-only, and excluded derived-summary refs without serving those
  refs to the worker;
- define sandbox, network, filesystem, dependency, timeout, and artifact
  output policy;
- define local run budget and repetition limits;
- preserve that no worker dispatch, code generation, command execution, probe
  run, score, official evaluation, or model ranking is authorized by slice A.

Forbidden:

- candidate source files;
- generated submissions;
- local execution traces;
- probe result logs;
- equivalence audits;
- official task execution;
- hidden-test handling;
- benchmark scores or model rankings.

### `PB-RECON-0-B`: Candidate Artifact And Local Run Capture

Later surfaces:

- `programbench_reconstruction_candidate_artifact_manifest@1`
- `programbench_reconstruction_local_run_trace@1`
- `programbench_reconstruction_probe_result_log@1`
- `programbench_reconstruction_remand_correction_record@1`

Purpose:

- capture worker-generated candidate artifacts under a released work order and
  sandbox policy;
- record local sandbox command traces with argv-shaped commands, bounded
  output, hashes, exit codes, durations, and filesystem diffs;
- record local probe result logs without claiming benchmark truth or
  hidden-test equivalence;
- represent remand/correction attempts without laundering hidden evidence,
  repairing unknown behavior silently, or mutating the original case packet.

Forbidden:

- official evaluator execution;
- hidden-test repair loops;
- original source or decompilation lookup;
- unbounded command authority;
- benchmark scoring;
- model ranking;
- official submission authority.

### `PB-RECON-0-C`: Local Audit, Summary, And Handoff

Later surfaces:

- `programbench_reconstruction_equivalence_audit@1`
- `programbench_reconstruction_result_summary@1`
- `programbench_reconstruction_handoff@1`
- `programbench_reconstruction_workbench_family_closeout_alignment@1`

Purpose:

- audit local probe outcomes against the case-packet evidence and witness
  expectations;
- distinguish accepted-local, remand-required, blocked, contaminated,
  inconclusive, and future-family-only states;
- summarize limitations and evidence boundaries;
- hand off pressure to larger local fixture matrices, official participation
  governance, benchmark-result governance, or conceptual broker work without
  selecting those families;
- close only `PB-RECON-0`.

Forbidden:

- official ProgramBench scoring;
- hidden-test equivalence;
- model leaderboard ranking;
- benchmark truth claims;
- official submissions;
- selecting the next family.

## Workbench Phase Law

```text
work_order_phase:
  consume released case packet and readiness refs only
  no worker dispatch or code generation

worker_context_phase:
  assemble worker-visible context from released cleanroom-visible refs
  no forbidden, hidden, postmortem-only, or derived-forbidden evidence

local_reconstruction_phase:
  later slice may capture worker-generated candidate artifacts under sandbox
  no official submission or hidden-test access

local_probe_phase:
  later slice may run or record allowed local/reference probes only
  local probes are not benchmark truth

audit_phase:
  interpret local evidence against case-packet obligations
  pass/remand/block locally without claiming hidden-test equivalence

postmortem_phase:
  record limitations and downstream pressure only
  no retroactive inference from forbidden evidence
```

## Required Boundary Distinctions

`PB-RECON-0` must keep these distinctions machine-checkable:

- ready case packet is not worker dispatch authority;
- worker context packet is not permission to include hidden or forbidden rows;
- auditor-only exclusion manifest is not worker-visible context;
- sandbox policy is not open command authority;
- run budget is not permission to exceed local cleanroom scope;
- candidate artifact is not official submission;
- local probe pass is not hidden-test equivalence;
- local result summary is not benchmark score;
- worker/model profile is context, not ranking;
- remand is not permission to use hidden tests or original source;
- handoff pressure is not future-family selection.

## Negative Laws

- "The case packet is ready" is not "the worker may execute now."
- "The worker generated code" is not "the code is an official submission."
- "An exclusion ref is recorded for audit" is not "the worker may see it."
- "A local probe passed" is not "the ProgramBench hidden tests pass."
- "A candidate outperformed another locally" is not "the model is ranked."
- "A remand was issued" is not "hidden tests may diagnose the failure."
- "A sandbox command is allowed" is not "arbitrary commands are allowed."
- "A workbench result exists" is not "benchmark truth exists."
