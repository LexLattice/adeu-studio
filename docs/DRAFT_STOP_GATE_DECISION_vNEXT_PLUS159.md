# Draft Stop-Gate Decision (Pre vNext+159)

This note records the starter decision scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS159.md`

Status: draft starter decision note (pre-start scaffold, April 15, 2026 UTC).

Authority layer: starter planning + lock draft only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS159.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_start_bundle": true,
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This document records pre-start bundle readiness only. It must be superseded by post-closeout evidence if V58-B is implemented."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+159` starter readiness only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS159.md`.
- This note does not by itself authorize implementation, runtime behavior, schema
  release, packet-law change, checkpoint-law change, ticket-law change, broader
  `local_write` semantics, restoration-family widening, broader cleanup semantics,
  harness replay hardening, execute rollout, dispatch rollout, product/UI authority,
  or hidden-cognition governance.

## Starter Preconditions

- `V58-A` is merged and closed on `main` through `v158`.
- the next slice remains inside the same family:
  - `V58`
  - step-2 continuation over the shipped `V58-A` bind path
- the starter slice remains exactly:
  - one real URM copilot restoration-state path
  - one exact `V56-B` `local_write` ticket lineage
  - one exact `V57-B` compensating-restore exemplar over the shipped `V57-A`
    `create_new` path
  - no append-only restore integration
- the slice owns only:
  - live restoration handoff
  - live restoration reintegration closeout
  - explicit restoration-state harness binding
- the slice does not own:
  - new checkpoint or ticket semantics
  - new `local_write` semantics
  - broader replay semantics
  - broader repo cleanup semantics
  - execute or dispatch widening
  - hardening or migration decision outputs
- admitted shaping inputs are frozen to the lock-listed set
- committed lane evidence from `V56`, `V57`, and `V58-A` is required as machine input
  or drift guard

## Planned Exit Criteria (vNext+159)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `V58-B` stays a continuation of `V58` and does not reopen `V56` / `V57` / `V58-A` law | required | lock contract + family mapping + slice mapping |
| Existing URM copilot session path remains the only selected live harness path | required | implementation diff + tests |
| Exact live path remains `local_write/create_new` under the designated `V57` sandbox root and target | required | fixtures + focused tests |
| Restoration remains explicit harness state, not hidden cleanup | required | new handoff/reintegration surfaces + tests |
| Outer harness capability remains necessary at most, never sufficient | required | runner enforcement + tests |
| `writes_allowed` and approval posture do not count as restoration entitlement | required | tests + runner enforcement |
| Original ticket does not become ambient ongoing restoration authority | required | handoff/reintegration surfaces + tests |
| Restoration-time capability/approval posture is re-snapshotted and mismatch fails closed | required | handoff/reintegration surfaces + tests |
| `action_ticket_ref` and prior reintegration refs stay historical lineage inputs only | required | schema/runner semantics + tests |
| Live restoration handoff remains explicit | required | `agentic_de_live_restoration_handoff_record@1` |
| Live restoration reintegration closes over current-turn restoration artifacts, not ambient state | required | `agentic_de_live_restoration_reintegration_report@1` + tests |
| Transcript / event stream remain observability only | required | schema / runner / tests |
| Replay remains bounded to the exact restoration event and the proof lives inside reintegration | required | helper/runner path + report/tests |
| No append-only restore integration, broader cleanup, hardening, execute, dispatch, or product/UI widening lands | required | diff review + focused tests |
| Repo-native starter gate passes | required | `make arc-start-check ARC=159` |

## Starter Summary

```json
{
  "schema": "v159_start_decision_summary@1",
  "arc": "vNext+159",
  "target_path": "V58-B",
  "family": "V58",
  "starter_kind": "live_restoration_state_integration",
  "selected_live_path": "urm_copilot_turn_plus_v56b_ticket_plus_v57b_create_new_compensating_restore_only",
  "hardening_selected": false,
  "ready_for_implementation_after_review": true
}
```

## Recommendation (Pre v159)

- starter decision:
  - `V58B_LIVE_RESTORATION_STATE_STARTER_RECOMMENDED`
- rationale:
  - `V58-A` is now closed and runnable on `main`.
  - the practical remaining gap in the family is explicit restoration-state
    integration, not broader class widening.
  - one bounded live restoration path is the smallest lawful next continuation:
    - live restoration handoff
    - live restoration reintegration closeout
    - explicit non-equivalence between harness capability and restoration authority
  - breadth widening and hardening should stay deferred until that one exact
    restoration-state path is operationally real and constitutionally stable.
