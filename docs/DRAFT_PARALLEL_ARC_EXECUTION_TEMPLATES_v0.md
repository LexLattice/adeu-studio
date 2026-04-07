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
- `docs/PARALLEL_ARC_IMPLEMENTATION_STAGE_REPORT_TEMPLATE_v0.json`
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

Current observed hardening direction:

- use a fresh worker per material step
- split drafting into `stub -> fill` rather than one broad draft step
- require `apply_patch` as the first next write action for file-creation steps
- record contradictions inside the current step artifact rather than letting them
  trigger extra repo research
- for code, prefer semantic-IR stage artifacts over pre-materialized live code stubs
- keep self-report at implementation stage boundaries rather than during live coding
- use the semantic-IR stage as the durable bridge from starter contract to final code
  rather than relying on hidden model reasoning alone
- treat the semantic-IR stage as the authoritative implementation-lowering artifact
  unless a later stage records an explicit justified mapping change
- require stage-2 and stage-3 reports to compare against both the starter contract and
  the semantic-IR bridge rather than only asserting final code presence

## Not Frozen Yet

This first template set does not yet freeze:

- a universal template schema validator
- mandatory per-step baton filenames
- automatic orchestrator ratification tooling
- reviewer-side step templates

Those can be added later if the strict step-checkpoint mode proves useful.
