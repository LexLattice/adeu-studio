# Draft Stop-Gate Decision (Pre vNext+160)

This note records the starter decision scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS160.md`

Status: draft starter decision note (pre-start scaffold, April 15, 2026 UTC).

Authority layer: starter planning + lock draft only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS160.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_start_bundle": true,
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This document records pre-start bundle readiness only. It must be superseded by post-closeout evidence if V58-C is implemented."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+160` starter readiness only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS160.md`.
- This note does not by itself authorize implementation, runtime behavior, schema
  release, live-turn admission-law change, handoff-law change, reintegration-law
  change, replay-law change, ticket-law change, broader `local_write` semantics,
  restoration-family widening, broader replay-family widening, execute rollout,
  dispatch rollout, product/UI authority, or hidden-cognition governance.

## Starter Preconditions

- `V58-B` is merged and closed on `main` through `v159`.
- the next slice remains inside the same family:
  - `V58`
  - step-3 continuation over the shipped `V58-A` / `V58-B` live harness path
- the starter slice remains exactly:
  - one real URM copilot hardening-decision path
  - one exact `V56-B` `local_write` ticket lineage
  - one exact `V57-A` observed `create_new` path
  - one exact `V57-B` compensating-restore exemplar
  - one exact `V58-A` bind lineage
  - one exact `V58-B` restoration-state lineage
- the slice owns only:
  - one advisory live harness hardening register
  - one bounded evidence-consumption path over the shipped lineage
  - one path-level recommendation surface over the exact exemplar
- the slice does not own:
  - new checkpoint or ticket semantics
  - new live-turn admission, handoff, or reintegration semantics
  - new restoration-state semantics
  - new replay semantics
  - broader `local_write` or restoration-family law
  - execute or dispatch widening
  - product/UI authority
  - migration or rollout law
- admitted shaping inputs are frozen to the lock-listed set
- committed lane evidence from `V56`, `V57`, `V58-A`, and `V58-B` is required as
  machine input or drift guard

## Planned Exit Criteria (vNext+160)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `V58-C` stays a continuation of `V58` and does not reopen `V56` / `V57` / `V58-A` / `V58-B` law | required | lock contract + family mapping + slice mapping |
| Existing URM copilot session path remains the only selected live harness path | required | implementation diff + tests |
| Exact live path remains `local_write/create_new` under the designated `V57` sandbox root and target | required | fixtures + focused tests |
| Hardening target remains the shipped observed-and-restored live harness-bound exemplar only | required | register fixture + tests |
| Hardening remains advisory-only, candidate-only, and path-level-only | required | register schema/fixture + tests |
| Exemplar evidence remains non-generalizing by default | required | lock-aligned fields + tests |
| Recommendation depends on shipped boundedness / reintegration verdicts, not on refs alone | required | runner/register semantics + tests |
| Recommendation is extensional and replayable for the selected evidence chain and frozen policy | required | checker semantics + tests |
| Common lineage roots are deduplicated and do not count as independent escalation support by repetition alone | required | register semantics + tests |
| Evidence basis remains distinct from recommendation outcome | required | register schema + tests |
| Allowed outcomes retain their bounded non-entitling meanings | required | schema/fixture semantics + tests |
| Live behavior remains unchanged by default | required | advisory flags + tests |
| No live-turn admission / handoff / reintegration mutation lands | required | diff review + tests |
| No replay widening, execute widening, dispatch widening, or product/UI widening lands | required | diff review + tests |
| Repo-native starter gate passes | required | `make arc-start-check ARC=160` |

## Starter Summary

```json
{
  "schema": "v160_start_decision_summary@1",
  "arc": "vNext+160",
  "target_path": "V58-C",
  "family": "V58",
  "starter_kind": "live_harness_hardening_decision",
  "selected_live_path": "urm_copilot_turn_plus_v56b_ticket_plus_v58a_v58b_bound_create_new_lineage_only",
  "live_behavior_mutation_selected": false,
  "ready_for_implementation_after_review": true
}
```

## Recommendation (Pre v160)

- starter decision:
  - `V58C_LIVE_HARNESS_HARDENING_STARTER_RECOMMENDED`
- rationale:
  - `V58-A` and `V58-B` now make one exact live harness-bound observed/restored path
    operational on `main`.
  - the practical remaining gap in the family is advisory hardening over that exact
    path, not more live authority.
  - one bounded live harness hardening register is the smallest lawful next
    continuation:
    - path-level only
    - advisory-only only
    - exemplar-bound only
    - non-generalizing by default
  - breadth widening and migration should stay deferred until that one exact
    hardening-decision path is operationally real and constitutionally stable.
