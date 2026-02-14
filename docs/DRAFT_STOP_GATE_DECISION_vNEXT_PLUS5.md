# Draft Stop-Gate Decision (Post vNext+5)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS5.md`

Status: draft decision note.

## Decision Guardrail (Frozen)

- This draft cannot pre-commit `vNext+6` implementation scope before all `vNext+5` thresholds are measured and evidenced.
- Any `vNext+6` recommendation in this document is non-binding until `all_passed = true` for the `vNext+5` exit criteria.

## Evidence Source

- CI workflow: `ci` on `main`
- Run ID: `22009799001`
- Head SHA: `a4f753268bf99d2ea924f63d80919518d2e36368`
- CI result timestamp window: merge on February 14, 2026 (UTC)
- Key artifacts:
  - queue determinism/idempotency fixtures:
    - `apps/api/tests/test_urm_copilot_routes.py`
  - budget snapshot/exhaustion fixtures:
    - `apps/api/tests/test_urm_copilot_routes.py`
  - connector snapshot replay fixtures:
    - `apps/api/tests/test_urm_copilot_routes.py`
  - steer target resolution/denial fixtures:
    - `apps/api/tests/test_urm_copilot_routes.py`
  - Merge PRs:
    - `#99` (B1), `#100` (B2), `#101` (B3), `#102` (B4)

## Exit-Criteria Check (vNext+5)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| B1-B4 merged with green CI | required | `pass` | CI run `22009799001` (`python=success`, `web=success`) |
| multi-child queue replay determinism | `100%` | `pass` | `test_agent_spawn_queue_mode_v2_enforces_fifo_and_queue_limit`; `test_agent_spawn_queue_mode_v2_cancel_running_dispatches_next`; `test_agent_spawn_queue_mode_v2_idempotency_conflict_includes_payload_hashes` |
| budget exhaustion code/event stability | `100%` | `pass` | `test_agent_spawn_budget_snapshot_v1_immutable_after_profile_switch`; `test_agent_spawn_budget_breach_solver_calls_is_deterministic` |
| connector snapshot replay determinism | `100%` | `pass` | `test_connector_snapshot_create_get_and_idempotency`; `test_connector_snapshot_get_stale_and_not_found`; `test_connector_snapshot_create_replay_mode_blocks_live_discovery` |
| steer target resolution replay determinism | `100%` | `pass` | `test_copilot_steer_endpoint_is_idempotent_and_rate_limited`; `test_copilot_steer_last_turn_after_seq_unresolved_emits_denied_event` |
| no solver semantics delta | required | `pass` | Arc diff `3ce29ed..a4f7532` is confined to URM runtime/API/docs; no ADEU solver semantics contract changes |
| no trust-lane regression | required | `pass` | no trust-lane taxonomy/model changes in B1-B4 patches |
| follow-on lock draft ready | required | `pass` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS6.md` (draft lock) |

Summary:

- `valid = true`
- `all_passed = true`
- `issues = []`

## B-Track Result Summary

- B1 multi-child queueing hardening:
  - status: `done`
  - evidence: merged in `#99`; deterministic queue/idempotency/cancel fixtures in `apps/api/tests/test_urm_copilot_routes.py`
- B2 budget inheritance/exhaustion hardening:
  - status: `done`
  - evidence: merged in `#100`; deterministic budget snapshot/breach fixtures in `apps/api/tests/test_urm_copilot_routes.py`
- B3 connector snapshot replay hardening:
  - status: `done`
  - evidence: merged in `#101`; deterministic replay/stale/live-block fixtures in `apps/api/tests/test_urm_copilot_routes.py`
- B4 steer diagnostics hardening:
  - status: `done`
  - evidence: merged in `#102`; deterministic steer target/denial fixtures in `apps/api/tests/test_urm_copilot_routes.py`

## Open Issues / Residual Risks

- none blocking `vNext+5` closeout.
- residual process risk:
  - severity: low
  - owner: runtime/governance maintainers
  - mitigation: keep `vNext+6` scope thin, additive, and replay-first.

## Recommendation (`vNext+6` Gate)

- gate decision:
  - `GO_VNEXT_PLUS6_DRAFT`
- rationale:
  - all `vNext+5` frozen scope items (B1-B4) are merged.
  - merge CI is green on `main` for the closeout commit.
  - follow-on `vNext+6` draft lock is prepared.
- explicit guard:
  - if `all_passed != true`, decision is `HOLD_VNEXT_PLUS6`.
  - no implementation scope for `vNext+6` is authorized from this note while held.

## Suggested Next Artifacts

1. Merge the frozen `docs/LOCKED_CONTINUATION_vNEXT_PLUS5.md` update on `main`.
2. Approve `docs/LOCKED_CONTINUATION_vNEXT_PLUS6.md` draft lock scope.
3. Start `vNext+6` implementation PR1 once `vNext+6` lock is approved.
