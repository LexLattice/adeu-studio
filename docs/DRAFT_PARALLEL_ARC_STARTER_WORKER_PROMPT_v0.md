# Draft Parallel Arc Starter Worker Prompt v0

Status: support-only pilot prompt scaffold.

Authority layer: support only.

This prompt scaffold does not authorize runtime changes by itself. It records the
starter-worker posture for strict step-checkpoint runs in the parallel-family pilot.

## Purpose

- stop starter workers from drifting into repeated convention lookup
- make starter drafting auditable one material step at a time
- separate checkpoint writing from starter-doc drafting
- make doc mismatches recordable without turning the worker into a reviewer

## Required Prompt Sections

Every strict starter-worker launch should state explicitly:

1. assigned family and slice
2. exact branch and worktree path
3. exact execution-template ref
4. exact currently authorized template step id/order
5. exact files the step is allowed to create or update
6. exact controlling refs the step may read
7. exact baton artifact to emit
8. explicit instruction to stop after that step and wait for orchestrator continuation

## Fresh-Worker Law

For strict diagnostic runs, use a fresh worker per material starter step by default.

This is especially important for:

- step 1 checkpointing
- step 2 stub creation
- step 3 draft filling

The pilot evidence shows that reusing the same worker across those boundaries carries
too much `read more before writing` inertia.

## Patch-First Law

For starter drafting steps that are supposed to create files:

- the first next write action should be `apply_patch`
- the orchestrator may pre-materialize the exact target files as minimal stubs, in
  which case the worker should fill those stubs rather than spending the step creating
  filenames or searching for examples
- the worker should not perform exploratory `rg`, `find`, `git`, or broad `sed`/`cat`
  calls after the step is authorized unless the prompt explicitly names one bounded
  read as allowed

If the worker cannot proceed from the current authorized context:

- write only the step baton
- set `claimed_step_complete = false`
- state one exact blocker

## Contradiction Law

If the worker encounters a real doc mismatch during a step that does not own that
repair yet:

- record the mismatch in the required step artifact
- do not turn the step into extra repo research
- do not repair the mismatch unless that repair is explicitly authorized in the step

## Step-2 Specific Law

Starter drafting should be split into:

1. stub creation
2. draft filling

The worker should not try to do both if the strict template has authorized only one of
them.

## Completion Law

The worker does not count as complete for a strict starter step unless:

- the exact required files for that step exist
- the baton names the template ref and step id/order
- `continuation_required_before_next_step = true`
- `next_allowed_actions = ["wait_for_orchestrator_continuation"]`

A prose status message without the files and baton is not completion.
