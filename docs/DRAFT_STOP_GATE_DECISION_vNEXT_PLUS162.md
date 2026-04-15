# Draft Stop-Gate Decision (Pre vNext+162)

This note records the starter decision scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS162.md`

Status: draft starter decision note (pre-start scaffold, April 15, 2026 UTC).

Authority layer: starter planning + lock draft only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS162.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_start_bundle": true,
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This document records pre-start bundle readiness only. It must be superseded by post-closeout evidence if V59-B is implemented."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+162` starter readiness only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS162.md`.
- This note does not by itself authorize implementation, runtime behavior, schema
  release, continuity-admission-law change, occupancy-law change, continuity
  reintegration-law change, replay-law change, ticket-law change, broader
  `local_write` semantics, broader continuity-safe restoration, continuity hardening,
  execute rollout, dispatch rollout, product/UI authority, or hidden-cognition
  governance.

## Starter Preconditions

- `V59-A` is merged and closed on `main` through `v161`.
- the family remains:
  - `V59`
  - step-2 continuation over the shipped `V59-A` continuity-bound path
- the starter slice remains exactly:
  - one current URM copilot session path
  - one exact `V56-B` `local_write` ticket lineage
  - one exact `V59-A` continuity region / admission / occupancy / reintegration
    lineage
  - one exact `V57-B` / `V58-B` restoration baseline reused as shaping and bounded
    derivation only
  - one exact target under the declared continuity root
- the slice owns only:
  - one continuity restoration handoff surface
  - one continuity restoration reintegration surface
- the slice does not own:
  - new checkpoint or ticket semantics
  - new continuity admission or occupancy semantics
  - new replay or resume semantics
  - append-only, overwrite, or destructive continuity restoration
  - broader `local_write` or broader region-family law
  - execute or dispatch widening
  - product/UI authority
  - migration or rollout law
- admitted shaping inputs are frozen to the lock-listed set
- committed lane evidence from `V56`, `V57`, `V58`, and `V59-A` is required as
  machine input or drift guard

## Planned Exit Criteria (vNext+162)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `V59-B` stays inside the `V59` family and does not reopen `V56` / `V57` / `V58` / `V59-A` law | required | lock contract + family mapping + slice mapping |
| Existing URM copilot session path remains the only selected live harness path | required | implementation diff + tests |
| Declared continuity root remains the only selected persistent region | required | fixtures + focused tests |
| Exact live path remains `local_write/create_new` centered on `runtime/reference_patch_candidate.diff` | required | fixtures + focused tests |
| Continuity-safe restoration remains a new live act, not standing continuity authority | required | checker semantics + tests |
| Restoration-time capability / approval posture is re-snapshotted and mismatch fails closed | required | runner semantics + tests |
| Restoration-time continuation verdict is typed, witness-bearing, and replayable | required | schema/fixture + tests |
| Historical lineage refs remain lineage-only and do not by themselves mint restoration entitlement | required | schema/fixture + tests |
| Explicit prior governed-state baseline and bounded compensating-scope match remain required | required | schema/fixture + tests |
| Explicit baseline-match verdict and restoration-time target/region state summary remain first-class | required | schema/fixture + tests |
| Positive continuity restoration reintegration requires explicit witness basis or certificate ref | required | schema/fixture + tests |
| Replay stays bounded to recomputation / re-evaluation of the exact continuity-safe restoration event only | required | schema/fixture + tests |
| No append-only, overwrite, destructive cleanup, continuity hardening, execute widening, dispatch widening, or product/UI widening lands | required | diff review + tests |
| Repo-native starter gate passes | required | `make arc-start-check ARC=162` |

## Starter Summary

```json
{
  "schema": "v162_start_decision_summary@1",
  "arc": "vNext+162",
  "target_path": "V59-B",
  "family": "V59",
  "starter_kind": "continuity_safe_restoration_starter",
  "selected_live_path": "urm_copilot_turn_plus_v56b_ticket_plus_v59a_continuity_bound_lineage_only",
  "selected_continuity_root": "artifacts/agentic_de/v59/workspace_continuity/",
  "live_behavior_mutation_selected": false,
  "ready_for_implementation_after_review": true
}
```

## Recommendation (Pre v162)

- starter decision:
  - `V59B_CONTINUITY_SAFE_RESTORATION_STARTER_RECOMMENDED`
- rationale:
  - `V59-A` closed the declared continuity region / admission / occupancy /
    reintegration starter on `main`.
  - the practical remaining gap is not broader workspace authority but one explicit
    continuity-safe compensating restore over that same exact lineage.
  - one explicit restoration handoff plus one explicit restoration reintegration is the
    smallest lawful next continuation:
    - same continuity root
    - same target
    - same `create_new` exemplar
    - restoration as new live act
    - typed replayable restoration-time continuation verdict
    - explicit prior governed-state baseline
    - explicit baseline-match verdict and restoration-time state summary
    - explicit bounded compensating-scope match
    - explicit restoration-time resnapshot
    - no replay/resume widening
    - no hardening or broader cleanup widening
