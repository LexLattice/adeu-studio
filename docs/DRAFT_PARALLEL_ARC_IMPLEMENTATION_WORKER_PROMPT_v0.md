# Draft Parallel Arc Implementation Worker Prompt v0

Status: support-only pilot prompt scaffold.

Authority layer: support only.

This prompt scaffold does not authorize runtime changes by itself. It records the
minimum finish-line posture an implementation worker should receive during the
parallel-family pilot.

## Purpose

- prevent implementation workers from stopping at exploratory partial diffs
- keep implementation ownership bounded to one slice
- make completion auditable through exact required outputs and exact targeted checks
- preserve retry fidelity when a prior attempt left partial state behind
- force one materialized semantic-IR bridge between starter contract and live code
  rather than leaving that bridge implicit inside hidden model reasoning

## Required Prompt Sections

Every implementation-worker launch for the pilot should state explicitly:

1. assigned family and slice
2. exact branch and worktree path
3. exact allowed write scope
4. exact controlling lock and slice-mapping refs
5. exact implementation stage currently authorized
6. exact finish line
7. exact targeted checks to run
8. exact stage-report artifact to emit
9. exact baton artifact to emit when the final stage completes
10. explicit prohibition on claiming completion while red, partial, or baton-less

For strict diagnostic runs, the launch should also state:

11. exact execution-template ref
12. exact currently authorized template step id/order
13. explicit instruction to stop after that step and wait for orchestrator continuation

## Three-Stage Law

The prompt should define the implementation phase as:

1. semantic-IR bridge
2. code transposition
3. verification and attestation

### Semantic-IR Bridge

The worker should first materialize one code-facing semantic-IR artifact that names:

- the exact contract names or schema ids being introduced
- the planned package/file ownership
- the planned schema export and root `spec/` mirror surfaces
- the planned deterministic fixtures/tests
- the exact non-goals and deferred seams that must remain out of scope

This stage may include pseudocode or function/class skeletons, but it should not
pretend the live code already exists.

### Code Transposition

The worker should then transpose that semantic-IR into live code surfaces.

### Verification And Attestation

The worker should finally run the bounded targeted checks and emit the final
implementation baton.

## Finish-Line Law

The prompt should define completion as all of the following:

- the semantic-IR bridge artifact exists
- required live package surfaces exist and are coherent
- required schema exports exist under the package schema directory
- required root `spec/` mirrors exist
- required deterministic fixtures/tests for the slice exist
- the bounded targeted checks for the owned package lane pass
- the worker emits one implementation baton with:
  - changed files
  - checks run
  - checks skipped
  - blockers
  - readiness judgment

The prompt should explicitly say that these do **not** count as completion:

- reasoning about the code only in hidden model thought
- only writing models without export surfaces
- only writing helpers without fixtures/tests
- only writing tests without contract surfaces
- red targeted checks
- a prose status message without the baton

## Stage-End Reporting Law

At the end of each implementation stage, the worker should emit one machine-checkable
stage report using:

- `docs/PARALLEL_ARC_IMPLEMENTATION_STAGE_REPORT_TEMPLATE_v0.json`

The stage report should map:

- contract item
- implementation status
- evidence ref
- remaining gap if any

This is the durable semantic bridge between the starter contract and the final code
diff.

## Strict Step-Checkpoint Law

If the orchestrator has enabled strict step-checkpoint mode, the prompt should say:

- follow `docs/PARALLEL_ARC_IMPLEMENTATION_EXECUTION_TEMPLATE_v0.json` exactly
- execute only the currently authorized template step
- after completing that step:
  - emit the required stage report carrying the template ref plus step id/order
  - set `claimed_step_complete = true`
  - set `continuation_required_before_next_step = true`
  - stop and wait for explicit orchestrator continuation
- do not self-advance to the next step even if it looks routine

This mode is intentionally slower and is used to inspect procedural compliance rather
than maximize throughput.

For non-diagnostic runs, the same stage structure still applies, but the worker may
complete the full implementation phase without routine orchestrator interruption as
long as each stage-end artifact is produced.

## Retry Law

If the worker is relaunching after a failed attempt, the prompt should say:

- the previous partial state is preserved as evidence
- the worker should finish from the current assigned retry branch state
- the worker must address the concrete misses named by the orchestrator, not just
  restate them

Typical concrete misses to name:

- missing semantic-IR contract bridge
- missing schema files or root mirrors
- tests still bound to obsolete released field names
- missing package wiring
- missing fixtures
- missing implementation baton

## Targeted-Check Law

The worker may run only targeted checks during implementation.

The prompt should still require enough targeted checks to cover the owned package lane,
typically:

- package-local lint
- package-local pytest
- any slice-local export-schema or fixture replay tests required by the new contract

The prompt should also require the worker to state clearly that broader `make check`
was not run.
