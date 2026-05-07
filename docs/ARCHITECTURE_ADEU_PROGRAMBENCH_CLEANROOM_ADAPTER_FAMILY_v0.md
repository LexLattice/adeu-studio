# Architecture ADEU ProgramBench Cleanroom Adapter Family v0

Status: architecture / decomposition note for planned `PB-ADAPTER-0`.

Authority layer: architecture / decomposition.

This architecture note does not authorize official ProgramBench participation,
official task execution, official runner integration, hidden-test handling,
hidden-test inference, original source lookup, decompilation, internet lookup
inside ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, model ranking, generated official
submissions, implementation generation, command execution, tool invocation,
target mutation, runtime transition, product authority, graph-memory
authority, recursive policy amendment, PR creation, commit, merge, release, or
future-family selection by itself.

## Family Thesis

`PB-PY-0` created a local cleanroom reconstruction substrate: cleanroom
profiles, concept seeds, evidence source indexes, Python realization overlays,
one local fixture, comparison packets, and local probe audits. The next
practical bottleneck is not official ProgramBench solving. It is adapting
task-visible evidence into a cleanroom case shape that later reconstruction
workers can consume without seeing forbidden evidence or receiving benchmark
authority.

The `PB-ADAPTER-0` circuit is:

```text
ProgramBench-style task-visible material
  -> cleanroom task intake
  -> source visibility manifest
  -> worker access contract
  -> allowed probe / observation adapter
  -> reconstruction case packet
  -> later reconstruction or evaluation review
```

Controlling invariant:

```text
PB-ADAPTER-0 may make task-visible material and local observation evidence
reviewable, but it may not turn that material into official benchmark
participation, hidden-test inference, benchmark scoring, model ranking,
implementation authority, or submission authority.
```

## Relationship To `PB-PY-0`

`PB-ADAPTER-0` consumes `PB-PY-0` as local reconstruction substrate:

- `programbench_cleanroom_reconstruction_profile@1`
- `program_odeu_concept_boundary_seed@1`
- `programbench_cleanroom_evidence_source_index@1`
- `programbench_reconstruction_non_authority_guardrail@1`
- `programbench_local_cleanroom_fixture_contract@1`
- `concept_realization_record@1`
- `python_reconstruction_realization_pack@1`
- `python_reconstruction_plan@1`
- `python_realization_witness_template@1`
- `programbench_local_cleanroom_fixture@1`
- `programbench_reconstruction_comparison_packet@1`
- `programbench_probe_equivalence_audit@1`
- `programbench_realization_family_closeout_alignment@1`

Those records remain local cleanroom research substrate. Consuming them does
not authorize official ProgramBench runs, hidden-test access, original source
access, official submissions, benchmark scores, or model rankings.

## Family Slices

### `PB-ADAPTER-0-A`: Task Intake And Visibility Contract

Starter surfaces:

- `programbench_cleanroom_task_intake@1`
- `programbench_task_artifact_manifest@1`
- `programbench_task_visibility_manifest@1`
- `programbench_adapter_worker_access_contract@1`
- `programbench_adapter_non_authority_guardrail@1`

Purpose:

- record a ProgramBench-style task intake without running or solving it;
- bind the exact task-visible artifact set with hashes, snapshot refs,
  ingestion method, and origin posture;
- classify visible, hidden, forbidden, support-only, and postmortem-only
  evidence stores;
- define which files and source rows a worker may see during inference;
- define network, source lookup, decompilation, external repo, Docker socket,
  and host-secret prohibitions;
- preserve that public descriptors and task labels are context, not task truth;
- reject any intake that exposes forbidden inference stores to a worker.

Forbidden:

- probe execution;
- probe observation logs;
- reconstruction case packets;
- official task execution;
- hidden-test handling;
- generated submissions;
- benchmark scores or model rankings.

### `PB-ADAPTER-0-B`: Probe And Observation Adapter

Later surfaces:

- `programbench_adapter_probe_plan@1`
- `programbench_probe_observation_log@1`
- `programbench_io_artifact_observation_index@1`
- `programbench_filesystem_side_effect_observation@1`

Purpose:

- represent local, allowed probe plans and observations under the access
  contract selected by `PB-ADAPTER-0-A`;
- adapt CLI/help/stdin/stdout/stderr/exit-code/generated-file/directory
  side-effect evidence into typed rows;
- distinguish reference-executable observations, worker-generated probe
  observations, generated submission observations, and postmortem-only
  observations;
- preserve local probe results as reconstruction evidence, not hidden-test
  equivalence.

Forbidden:

- official hidden evaluator execution;
- official runner integration;
- hidden-test repair loops;
- treating probe passes as benchmark truth;
- mutating benchmark task sources or hidden stores.

### `PB-ADAPTER-0-C`: Reconstruction Case Packet And Handoff

Later surfaces:

- `programbench_reconstruction_case_packet@1`
- `programbench_adapter_readiness_summary@1`
- `programbench_adapter_handoff@1`
- `programbench_cleanroom_adapter_family_closeout_alignment@1`

Purpose:

- bundle task intake, visibility manifest, access contract, guardrail, and
  probe observation refs into one reviewable reconstruction case packet;
- summarize whether the case is ready for a later reconstruction experiment,
  blocked by evidence exposure, blocked by missing observation coverage, or
  future-family-only;
- hand off pressure to a later reconstruction execution or evaluation family
  without selecting it;
- close only `PB-ADAPTER-0`.

Forbidden:

- generating code or submissions;
- invoking an official evaluator;
- ranking models;
- claiming benchmark truth;
- selecting official ProgramBench participation or implementation-lock review.

## Evidence Visibility Law

The adapter must preserve these visibility classes:

```text
cleanroom_visible
worker_generated_probe
worker_generated_submission
reference_executable_observation
public_descriptor_context
support_context_only
postmortem_only
evaluation_oracle_hidden
forbidden_original_source
forbidden_decompilation
forbidden_internet_lookup
forbidden_external_repo
forbidden_host_secret
forbidden_docker_socket
```

Forbidden inference stores must not be mounted, registered as worker-visible
sources, queried, summarized for inference, or exposed through derived rows
during inference. It is not enough to label a leaked source as forbidden after
the worker has seen it.

Visibility rows should distinguish:

```text
known_visible
known_hidden
known_forbidden
known_support_only
unknown_not_indexed
declared_absent
```

Derived summaries inherit the strictest source visibility they summarize.
Hidden or forbidden material must not be converted into cleanroom-visible
advisory text for worker inference.

## Phase Law

```text
intake_phase:
  record task-visible source posture and visibility manifest only

inference_phase:
  expose only cleanroom-visible sources authorized by the access contract

probe_observation_phase:
  record allowed local/reference observations under the access contract

evaluation_phase:
  hidden tests may judge only if a later family authorizes that posture
  hidden tests remain external court, not inference evidence

postmortem_phase:
  postmortem observations may inform harness research only
  they do not retroactively become inference evidence
```

## Required Boundary Distinctions

`PB-ADAPTER-0` must keep these distinctions machine-checkable:

- task intake is not task solving;
- artifact manifest hash identity is not permission to expose every artifact;
- visibility manifest is not permission to expose every listed store;
- worker access contract constrains exposure but does not authorize execution;
- reference-executable observation is not source-code visibility;
- allowed probe observation is not hidden-test equivalence;
- generated submission observation is not official submission authority;
- evaluation oracle hidden means external court, not inference evidence;
- public ProgramBench descriptor is context, not benchmark truth;
- reconstruction case packet is not implementation or submission authority;
- adapter readiness summary is not a benchmark result.

## Negative Laws

- "This looks like a ProgramBench task" is not "official ProgramBench
  participation is authorized."
- "A hidden test exists" is not "the worker may infer from it."
- "A task source exists in the repo" is not "the worker may read original
  source during inference."
- "A forbidden source was summarized" is not "the summary may become
  cleanroom-visible worker evidence."
- "A probe passed locally" is not "the official hidden evaluator will pass."
- "A case packet is ready" is not "code generation or submission is allowed."
- "A worker access contract exists" is not "commands may be executed."
