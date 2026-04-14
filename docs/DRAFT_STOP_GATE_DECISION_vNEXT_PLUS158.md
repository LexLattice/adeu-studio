# Draft Stop-Gate Decision (Pre vNext+158)

This note records the starter decision scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS158.md`

Status: draft starter decision note (pre-start scaffold, April 14, 2026 UTC).

Authority layer: starter planning + lock draft only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS158.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_start_bundle": true,
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This document records pre-start bundle readiness only. It must be superseded by post-closeout evidence if V58-A is implemented."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+158` starter readiness only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS158.md`.
- This note does not by itself authorize implementation, runtime behavior, schema
  release, checkpoint-law change, ticket-law change, `local_write` widening,
  restoration-state integration, execute rollout, dispatch rollout, product/UI
  authority, or hidden-cognition governance.

## Starter Preconditions

- `V57` is fully closed on `main` through `v157`.
- the next family is treated as a new family:
  - `V58`
  - not `V57-D`
- the starter slice remains exactly:
  - one real URM copilot turn
  - one exact `V56-B` `local_write` ticket lineage
  - one exact `V57-A` observed `create_new` effect
  - no auto-restoration
- the new family owns only:
  - live-turn admission
  - explicit ticket-to-effect handoff
  - reintegration closeout
- the family does not own:
  - new checkpoint or ticket semantics
  - new `local_write` semantics
  - broader repo-write authority
  - execute or dispatch widening
- admitted shaping inputs are frozen to the lock-listed set
- committed lane evidence from `V56` / `V57` is required as machine input or drift
  guard

## Planned Exit Criteria (vNext+158)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `V58-A` stays a new family and does not reopen `V56` / `V57` law | required | lock contract + family architecture + slice mapping |
| Existing URM copilot session path remains the only selected live harness path | required | implementation diff + tests |
| Exact live path remains `local_write/create_new` under the designated `V57` sandbox root | required | fixtures + focused tests |
| Outer harness capability remains necessary at most, never sufficient | required | admission/handoff/reintegration surfaces + tests |
| `writes_allowed` and approval posture do not count as ticket equivalents | required | tests + runner enforcement |
| Current-turn admission remains explicit | required | `agentic_de_live_turn_admission_record@1` |
| Ticket-to-effect handoff remains explicit | required | `agentic_de_live_turn_handoff_record@1` |
| Reintegration closes over current-turn artifacts, not ambient state | required | `agentic_de_live_turn_reintegration_report@1` + tests |
| Transcript / event stream remain observability only | required | schema / runner / tests |
| No auto-restoration, broader write, execute, dispatch, or product/UI widening lands | required | diff review + focused tests |
| Repo-native starter gate passes | required | `make arc-start-check ARC=158` |

## Starter Summary

```json
{
  "schema": "v158_start_decision_summary@1",
  "arc": "vNext+158",
  "target_path": "V58-A",
  "family": "V58",
  "starter_kind": "live_harness_bind",
  "selected_live_path": "urm_copilot_turn_plus_v56b_ticket_plus_v57a_create_new_observation_only",
  "restoration_selected": false,
  "ready_for_implementation_after_review": true
}
```

## Recommendation (Pre v158)

- starter decision:
  - `V58A_LIVE_HARNESS_BIND_STARTER_RECOMMENDED`
- rationale:
  - `V55`, `V56`, and `V57` are already closed and runnable on `main`.
  - the practical gap is now composition, not representation.
  - one bounded live harness bind is the smallest lawful next family:
    - live-turn admission
    - explicit ticket-to-effect handoff
    - reintegration closeout
  - breadth widening should stay deferred until that one exact path is operationally
    real and constitutionally stable.
