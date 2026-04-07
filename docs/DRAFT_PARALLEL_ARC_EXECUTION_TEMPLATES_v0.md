# Draft Parallel Arc Execution Templates v0

Status: support-only diagnostic scaffold.

Authority layer: support only.

This document does not authorize runtime changes by itself. It records the
machine-checkable step templates that may be used when the parallel-family pilot is run
in strict step-checkpoint mode.

## Purpose

- convert “finish the slice” prompts into explicit ordered execution steps
- make worker compliance auditable at the step level
- let the meta-orchestrator ratify one completed step at a time
- preserve procedural failures as evidence instead of collapsing them into one final
  success/failure narrative

## Current Template Set

- `docs/PARALLEL_ARC_STARTER_BUNDLE_EXECUTION_TEMPLATE_v0.json`
- `docs/PARALLEL_ARC_IMPLEMENTATION_EXECUTION_TEMPLATE_v0.json`
- `docs/PARALLEL_ARC_REVIEW_FIX_EXECUTION_TEMPLATE_v0.json`
- `docs/PARALLEL_ARC_CLOSEOUT_EXECUTION_TEMPLATE_v0.json`

## Shared Step Contract

Every step in every template should carry:

- `step_id`
- `step_order`
- `required_inputs`
- `required_outputs`
- `success_predicate`
- `required_checks`
- `forbidden_shortcuts`
- `next_step_if_pass`
- `escalate_if_fail`

## Diagnostic Use

When strict step-checkpoint mode is enabled:

- the worker receives one template ref
- the worker receives one currently authorized step
- the worker may execute only that step
- after that step the worker must stop and wait for orchestrator continuation

This is intentionally slower than the normal pilot path. The purpose is to identify:

- where workers drift procedurally
- which steps are robust
- which steps are fragile under copy-forward or partial-completion pressure

## Not Frozen Yet

This first template set does not yet freeze:

- a universal template schema validator
- mandatory per-step baton filenames
- automatic orchestrator ratification tooling
- reviewer-side step templates

Those can be added later if the strict step-checkpoint mode proves useful.
