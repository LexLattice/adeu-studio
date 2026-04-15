# Draft Stop-Gate Decision (Pre vNext+161)

This note records the starter decision scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS161.md`

Status: draft starter decision note (pre-start scaffold, April 15, 2026 UTC).

Authority layer: starter planning + lock draft only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS161.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_start_bundle": true,
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This document records pre-start bundle readiness only. It must be superseded by post-closeout evidence if V59-A is implemented."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+161` starter readiness only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS161.md`.
- This note does not by itself authorize implementation, runtime behavior, schema
  release, continuity admission-law change, occupancy-law change, continuity
  reintegration-law change, replay-law change, ticket-law change, broader
  `local_write` semantics, continuity-safe restoration, broader continuity-region
  semantics, execute rollout, dispatch rollout, product/UI authority, or
  hidden-cognition governance.

## Starter Preconditions

- `V58-C` is merged and closed on `main` through `v160`.
- the next slice moves to a new family:
  - `V59`
  - step-1 continuation over the shipped `V56` / `V57` / `V58` governed live path
- the starter slice remains exactly:
  - one declared persistent continuity region
  - one exact `V56-B` `local_write` ticket lineage
  - one exact `V57-A` observed `create_new` path
  - one exact `V58` live admission / handoff / reintegration lineage
  - one exact target under the declared continuity root
- the slice owns only:
  - one continuity-region declaration
  - one typed continuity admission surface
  - one typed occupancy / prior-presence surface
  - one continuity reintegration surface
- the slice does not own:
  - new checkpoint or ticket semantics
  - new live-turn admission, handoff, or reintegration semantics
  - new restoration-state semantics
  - new replay or resume semantics
  - broader `local_write` or region-family law
  - execute or dispatch widening
  - product/UI authority
  - migration or rollout law
- admitted shaping inputs are frozen to the lock-listed set
- committed lane evidence from `V56`, `V57`, and `V58` is required as machine input or
  drift guard

## Planned Exit Criteria (vNext+161)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `V59-A` stays a new family and does not reopen `V56` / `V57` / `V58` law | required | lock contract + family mapping + slice mapping |
| Existing URM copilot session path remains the only selected live harness path | required | implementation diff + tests |
| Declared continuity root remains the only selected persistent region | required | fixtures + focused tests |
| Exact live path remains `local_write/create_new` centered on `runtime/reference_patch_candidate.diff` | required | fixtures + focused tests |
| Continuity admission stays typed and replayable | required | schema/fixture + tests |
| Occupancy verdict stays witness-bearing and replayable | required | schema/fixture + tests |
| `create_new` remains admissible only for `unoccupied` target state | required | checker semantics + tests |
| Non-target occupants remain contextual only and do not become ambient admissibility | required | runner semantics + tests |
| Positive continuity reintegration requires explicit witness basis or certificate ref | required | schema/fixture + tests |
| Prior workspace state remains context at most, never standing authority | required | checker semantics + tests |
| No continuity-safe restoration, replay/resume widening, execute widening, dispatch widening, or product/UI widening lands | required | diff review + tests |
| Repo-native starter gate passes | required | `make arc-start-check ARC=161` |

## Starter Summary

```json
{
  "schema": "v161_start_decision_summary@1",
  "arc": "vNext+161",
  "target_path": "V59-A",
  "family": "V59",
  "starter_kind": "persistent_workspace_continuity_starter",
  "selected_live_path": "urm_copilot_turn_plus_v56b_ticket_plus_v57a_observed_effect_plus_v58_live_lineage_only",
  "selected_continuity_root": "artifacts/agentic_de/v59/workspace_continuity/",
  "live_behavior_mutation_selected": false,
  "ready_for_implementation_after_review": true
}
```

## Recommendation (Pre v161)

- starter decision:
  - `V59A_PERSISTENT_WORKSPACE_CONTINUITY_STARTER_RECOMMENDED`
- rationale:
  - `V58` now makes one exact governed live path operational on `main`.
  - the practical remaining gap is not more live authority but bounded continuity over
    that exact path.
  - one declared persistent continuity region with typed continuity admission,
    explicit occupancy law, and witness-bearing continuity reintegration is the
    smallest lawful next continuation:
    - context-only prior state
    - exact `create_new` occupancy law
    - no restoration widening
    - no replay or resume widening
    - no broader region authority
  - breadth widening should stay deferred until that one exact continuity starter path
    is operationally real and constitutionally stable.
