# Draft Stop-Gate Decision (Pre vNext+163)

This note records the starter decision scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS163.md`

Status: draft starter decision note (pre-start scaffold, April 15, 2026 UTC).

Authority layer: starter planning + lock draft only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS163.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_start_bundle": true,
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This document records pre-start bundle readiness only. It must be superseded by post-closeout evidence if V59-C is implemented."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+163` starter readiness only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS163.md`.
- This note does not by itself authorize implementation, runtime behavior, schema
  release, continuity admission-law change, occupancy-law change, continuity
  reintegration-law change, continuity restoration-law change, replay/resume-law
  change, ticket-law change, broader `local_write` semantics, broader continuity-root
  authority, execute rollout, dispatch rollout, product/UI authority, or
  hidden-cognition governance.

## Starter Preconditions

- `V59-B` is merged and closed on `main` through `v162`.
- the family remains:
  - `V59`
  - step-3 continuation over the shipped `V59-A` / `V59-B` continuity-bound path
- the starter slice remains exactly:
  - one current URM copilot session path
  - one exact `V56-B` `local_write` ticket lineage
  - one exact `V59-A` continuity region / admission / occupancy / reintegration
    lineage
  - one exact `V59-B` continuity restoration handoff / restoration / reintegration
    lineage
  - one exact target under the declared continuity root
- the slice owns only:
  - one advisory continuity hardening register
- the slice does not own:
  - new checkpoint or ticket semantics
  - new continuity admission, occupancy, or reintegration semantics
  - new continuity-safe restoration semantics
  - new replay or resume semantics
  - broader `local_write` or broader region-family law
  - execute or dispatch widening
  - product/UI authority
  - migration or rollout law
- admitted shaping inputs are frozen to the lock-listed set
- committed lane evidence from `V56`, `V57`, `V58`, `V59-A`, and `V59-B` is required
  as machine input or drift guard

## Planned Exit Criteria (vNext+163)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `V59-C` stays inside the `V59` family and does not reopen `V56` / `V57` / `V58` / `V59-A` / `V59-B` law | required | lock contract + family mapping + slice mapping |
| Existing URM copilot session path remains the only selected live harness path | required | implementation diff + tests |
| Declared continuity root remains the only selected persistent region | required | fixtures + focused tests |
| Exact live path remains `local_write/create_new` centered on `runtime/reference_patch_candidate.diff` | required | fixtures + focused tests |
| Selected hardening target remains the shipped continuity-bound observed-and-restored exemplar only | required | schema/fixture + tests |
| Recommendation depends on occupancy / boundedness / reintegration verdicts, not refs alone | required | schema/fixture + tests |
| Recommendation remains extensional and replayable for the same evidence basis and frozen policy anchor | required | checker semantics + tests |
| Hardening register carries one explicit frozen-policy anchor | required | schema/fixture + tests |
| Common lineage roots remain non-independent at the advisory layer | required | schema/fixture + tests |
| Evidence basis remains distinct from recommendation outcome | required | schema/fixture + tests |
| Restoration freshness and baseline verdicts carry through explicitly at the advisory layer | required | schema/fixture + tests |
| Positive advisory outcomes remain candidate-only and non-entitling | required | schema/fixture + tests |
| No live behavior mutation, continuity entitlement widening, restoration-law widening, replay/resume widening, execute widening, dispatch widening, or product/UI widening lands | required | diff review + tests |
| Repo-native starter gate passes | required | `make arc-start-check ARC=163` |

## Starter Summary

```json
{
  "schema": "v163_start_decision_summary@1",
  "arc": "vNext+163",
  "target_path": "V59-C",
  "family": "V59",
  "starter_kind": "continuity_hardening_starter",
  "selected_live_path": "urm_copilot_turn_plus_v59a_v59b_continuity_bound_lineage_only",
  "selected_continuity_root": "artifacts/agentic_de/v59/workspace_continuity/",
  "live_behavior_mutation_selected": false,
  "ready_for_implementation_after_review": true
}
```

## Recommendation (Pre v163)

- starter decision:
  - `V59C_CONTINUITY_HARDENING_STARTER_RECOMMENDED`
- rationale:
  - `V59-A` and `V59-B` closed one exact continuity-bound observed-and-restored path
    on `main`.
  - the practical remaining gap is not broader continuity authority but one bounded
    advisory hardening / drift surface over that same exact lineage.
  - one advisory continuity hardening register is the smallest lawful next
    continuation:
    - same continuity root
    - same target
    - same `create_new` exemplar
    - same observed-and-restored lineage
    - verdict-driven evidence chain
    - explicit frozen-policy anchor
    - extensional and replayable recommendation function
    - explicit restoration freshness / baseline / scope-match verdict carry-through
    - lineage-root non-independence at the advisory layer
    - evidence basis distinct from recommendation outcome
    - candidate-only non-entitling outcomes
    - no live mutation or broader authority widening
