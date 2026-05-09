# Architecture ADEU ProgramBench Local Cleanroom Single Case Run Family v0

Status: architecture / decomposition note for planned
`PB-SINGLE-CASE-RUN-0`.

Authority layer: architecture / decomposition.

This note decomposes the local single-case run family after
`PB-MATRIX-INCLUSION-0`. It does not authorize implementation, local
execution, official ProgramBench participation, hidden-test handling,
benchmark scoring, baseline comparison, model ranking, submission, commit,
merge, release, or future-family selection by itself.

## Family Thesis

The prior ProgramBench families established the local cleanroom substrate:

```text
Python realization substrate
  -> cleanroom adapter membrane
  -> reconstruction workbench
  -> attempt lifecycle
  -> trial lifecycle
  -> bounded retry governance
  -> matrix accounting
  -> case expansion
  -> matrix inclusion
```

`PB-SINGLE-CASE-RUN-0` asks the next bounded question:

```text
Can the repo run one selected local cleanroom case specimen and capture the
resulting evidence, without treating that evidence as official benchmark
truth or model performance?
```

The family exists because an actual run is a distinct authority step. A
ready case lineage or matrix member is not automatically executable, and a
local execution specimen is not automatically a benchmark score, official
result, baseline comparison, or model-ranking datum.

`PB-SINGLE-CASE-RUN-0` is not a replacement for `PB-TRIAL-0`. It is a
matrix/case-lineage selected run wrapper that binds one selected released case
lineage to the already-established adapter, workbench, attempt, trial, and
optional retry evidence vocabulary.

## Relationship To Prior Families

`PB-SINGLE-CASE-RUN-0` consumes prior families only as released lineage and
constraints:

- `PB-PY-0`: concept / Python realization substrate;
- `PB-ADAPTER-0`: task-visible evidence and access membrane;
- `PB-RECON-0`: reconstruction workbench law;
- `PB-ATTEMPT-0`: attempt lifecycle and worker input packet law;
- `PB-TRIAL-0`: single local trial specimen law;
- `PB-RETRY-0`: optional one-retry lineage law;
- `PB-MATRIX-0`: local matrix accounting doctrine;
- `PB-CASE-EXPANSION-0`: local case lineage supply;
- `PB-MATRIX-INCLUSION-0`: local matrix membership revision governance.

It may use those rows to constrain one local run. It may not mint official
benchmark truth, hidden-test authority, model ranking, baseline comparison,
batch execution, or future-family authority.

## Authority Boundary

`PB-SINGLE-CASE-RUN-0` may govern:

- selection of exactly one local cleanroom target case lineage;
- one local run request;
- worker-visible packet and runbook identity binding;
- sandbox, tool, budget, write-scope, and probe-basis preflight;
- one later local worker dispatch specimen;
- local execution capture;
- local probe observation capture;
- local candidate artifact capture inside released write scope;
- lifecycle projection back into released attempt/trial/workbench law;
- local-only outcome audit;
- pressure-only remand / handoff after the specimen.

`PB-SINGLE-CASE-RUN-0` may not govern:

- official ProgramBench task execution;
- official runner/evaluator integration;
- hidden-test access, inference, or equivalence;
- original source lookup;
- decompilation;
- internet or external repository lookup for task inference;
- batch execution;
- matrix-wide execution;
- benchmark score, pass rate, solve rate, success rate, official success rate,
  or leaderboard standing;
- baseline comparison;
- model ranking;
- official submission authority;
- retry-chain authority;
- future-family selection.

## Core Circuit

```text
released local cleanroom case lineage
  -> single-case run request
  -> target selection
  -> execution preflight
  -> run control contract
  -> one local worker dispatch specimen
  -> execution capture
  -> local probe observation bundle
  -> candidate artifact capture
  -> lifecycle projection
  -> local outcome audit
  -> observation summary
  -> remand / acceptance decision
  -> pressure-only handoff
  -> family closeout alignment
```

## Slice A: Request, Target, And Preflight

`PB-SINGLE-CASE-RUN-0-A` should make the single-case run candidate reviewable
without executing it.

Selected surfaces:

- `programbench_single_case_run_request@1`
- `programbench_single_case_target_selection@1`
- `programbench_single_case_execution_preflight@1`
- `programbench_single_case_run_control_contract@1`
- `programbench_single_case_run_non_authority_guardrail@1`

The slice should answer:

```text
Which one released local cleanroom case lineage is selected for later local
run review, under what sandbox, tool, budget, write-scope, and probe-basis
constraints?
```

It should not answer:

```text
Did the worker run?
What did the worker produce?
Did the program pass?
What benchmark score did we get?
How does this compare to a baseline?
```

Target-origin routes:

- `matrix_member`:
  default route; selected case must be included in a released local matrix
  revision.
- `ready_expanded_case_lineage`:
  exception route; selected case must have released readiness and no
  contamination blockers.
- `direct_adapter_case_exception`:
  exceptional route; selected case must carry explicit exception posture and
  non-matrix-lineage warning.

## Slice B: One Local Execution Specimen

`PB-SINGLE-CASE-RUN-0-B` should perform or record exactly one local cleanroom
execution specimen under released A controls.

Selected surfaces:

- `programbench_single_case_worker_dispatch_specimen@1`
- `programbench_single_case_execution_trace@1`
- `programbench_single_case_probe_observation_bundle@1`
- `programbench_single_case_candidate_artifact_capture@1`
- `programbench_single_case_lifecycle_projection@1`

The slice is action-adjacent. It should require explicit dispatch authority
from the B lock, sandbox attestations, command allowlist matching, network /
source / secret / Docker-socket absence witnesses, output hashes, bounded
excerpts, and write-scope-constrained artifact capture.

## Slice C: Local Outcome Audit And Closeout

`PB-SINGLE-CASE-RUN-0-C` should audit the one local specimen and close the
family.

Selected surfaces:

- `programbench_single_case_local_outcome_audit@1`
- `programbench_single_case_run_observation_summary@1`
- `programbench_single_case_remand_or_acceptance_decision@1`
- `programbench_single_case_run_handoff@1`
- `programbench_single_case_run_family_closeout_alignment@1`

The slice should emit a local-only outcome posture such as accepted, remand
required, blocked, or inconclusive. It should not score ProgramBench, compare
baselines, rank models, infer hidden tests, or authorize another run by
itself.

## Invariants

- Exactly one target case lineage may be selected per run request.
- `PB-SINGLE-CASE-RUN-0` is a selected case-lineage run wrapper under prior
  lifecycle law, not a parallel trial semantics family.
- `target_origin_route = matrix_member` is the default target-origin route.
- Matrix-origin targets must bind source matrix ref, source matrix revision
  ref/hash, matrix membership row ref, and `matrix_membership_status =
  included`.
- Deferred or rejected matrix-inclusion candidates may not be selected as
  run targets.
- Exactly one local worker dispatch specimen may be associated with a selected
  run request unless a later retry family explicitly grants retry authority.
- A preflight pass is eligibility for later execution review, not dispatch
  authority.
- B dispatch authority must come from the B lock, not A preflight.
- The worker-visible packet hash, runbook hash, sandbox policy hash, tool
  manifest hash, write-scope hash, and probe-basis hash must remain stable
  from A into B.
- Local output capture must record stdout/stderr hashes, bounded excerpts,
  exit code, duration, timeout status, and filesystem side-effect evidence.
- Candidate artifact capture is valid only inside released write scope and
  after forbidden-content screening passes.
- Local outcome audit is not official ProgramBench evaluation.
- Local acceptance is local-only and limited to the declared probe/oracle
  basis.
- Remand pressure is not retry authority.
- Observation summaries must not include pass rate, solve rate, success rate,
  model comparison, baseline comparison, or leaderboard language.

## Execution Safety Discipline

Before any B specimen is valid, the family should require witnesses for:

- network disabled;
- Docker socket absent;
- host secrets absent;
- original source lookup disabled;
- decompilation disabled;
- external repository lookup disabled;
- command allowlist matched;
- tool manifest closed;
- bounded write scope enforced;
- worker input packet hash matched;
- sandbox policy and run budget matched;
- stdout/stderr and generated artifacts captured by hash.

These witnesses are local run evidence only. They do not become official
benchmark evaluation evidence.

## Deferred Seams

The following remain future-family-only:

- running more than one case;
- batch execution over a matrix;
- official ProgramBench participation;
- official runner/evaluator integration;
- hidden-test inference or equivalence;
- benchmark score governance;
- baseline comparison governance;
- model comparison or ranking;
- retry-chain governance;
- publishing official submissions;
- converting local observations into baseline-relative claims.
