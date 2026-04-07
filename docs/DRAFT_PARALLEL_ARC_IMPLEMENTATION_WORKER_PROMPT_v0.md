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

## Required Prompt Sections

Every implementation-worker launch for the pilot should state explicitly:

1. assigned family and slice
2. exact branch and worktree path
3. exact allowed write scope
4. exact controlling lock and slice-mapping refs
5. exact finish line
6. exact targeted checks to run
7. exact baton artifact to emit
8. explicit prohibition on claiming completion while red, partial, or baton-less

## Finish-Line Law

The prompt should define completion as all of the following:

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

- only writing models without export surfaces
- only writing helpers without fixtures/tests
- only writing tests without contract surfaces
- red targeted checks
- a prose status message without the baton

## Retry Law

If the worker is relaunching after a failed attempt, the prompt should say:

- the previous partial state is preserved as evidence
- the worker should finish from the current assigned retry branch state
- the worker must address the concrete misses named by the orchestrator, not just
  restate them

Typical concrete misses to name:

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
