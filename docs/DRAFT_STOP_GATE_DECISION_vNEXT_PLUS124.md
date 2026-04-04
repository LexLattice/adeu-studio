# Draft Stop-Gate Decision (Post vNext+124)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS124.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS124.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v124_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+124` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS124.md`.
- This note captures bounded `V51-A` kernel evidence only; it does not authorize the
  later `V51-B` API seam, the later `V51-C` UI seam, persistent storage, product
  surfaces, worker orchestration, or imported-bundle precedent by itself.
- Canonical `V51-A` release in `v124` is carried by the shipped `adeu_odeu_sim`
  package source, committed deterministic `v51a` fixtures, package tests, and the
  canonical `v51a_odeu_sim_kernel_evidence@1` evidence input under
  `artifacts/agent_harness/v124/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` now marks `V51-A`
  closed on `main` and advances the branch-local default next path to `V51-B`; it
  does not select the `V51-B` API contract by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#346` (`feat(v124): add ODEU simulation kernel`)
- arc-completion merge commit: `9d172a9307e492d5f74bd75944fabad86442f0b3`
- merged-at timestamp: `2026-04-04T11:58:15Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v124_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v124_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v124_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v124/evidence_inputs/metric_key_continuity_assertion_v124.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v124/evidence_inputs/runtime_observability_comparison_v124.json`
  - `V51-A` release evidence input:
    `artifacts/agent_harness/v124/evidence_inputs/v51a_odeu_sim_kernel_evidence_v124.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v124/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS124_EDGES.md`

## Exit-Criteria Check (vNext+124)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V51-A` merged with green CI | required | `pass` | PR `#346`, merge commit `9d172a9307e492d5f74bd75944fabad86442f0b3`, checks `python/web/lean-formal = pass` |
| Repo-owned `adeu_odeu_sim` package remains the only live owner of the shipped `V51-A` code | required | `pass` | `packages/adeu_odeu_sim/pyproject.toml`, `packages/adeu_odeu_sim/src/adeu_odeu_sim/*.py`, and absence of live API/UI package promotion in this slice |
| The first release freezes the typed kernel submodels and explicit lane-crossing contract surface instead of a broad implicit world-state blob | required | `pass` | `Agent`, `ResourcePool`, `Institution`, `LaneCrossingContract`, `EventRecord`, and `WorldState` in `models.py`, plus package exports in `__init__.py` |
| The released kernel replays deterministically over exactly `healthy_baseline` and `weak_d` with canonical seed `7` and horizon `25` | required | `pass` | `CANONICAL_REPLAY_SEED`, `CANONICAL_REPLAY_HORIZON`, `run_canonical_scenario(...)`, and committed `v51a` fixtures |
| Deterministic agent iteration and sanction-target tie-break law are explicit and regression-tested | required | `pass` | `plan_actions(...)` ordering, `_select_sanction_target(...)`, and `test_agent_iteration_order_is_frozen_by_agent_id` plus `test_sanction_target_tiebreak_is_deterministic` |
| Replay-state bookkeeping is correct on reset and verify actions | required | `pass` | initialization-event attachment in `_build_world(...)`, `actor.last_action` update in `_apply_action(...)`, and the `test_reset_records_initialization_event_on_new_world_only` plus `test_verify_action_updates_last_action_for_epistemic_follow_on` regressions |
| Invalid kernel state fails closed on malformed scenario shares and empty agent sets | required | `pass` | `ScenarioConfig` validation, `WorldState` validation, `summarize_lane_state(...)`, `compute_metrics(...)`, and fail-closed tests |
| Regime outputs stay heuristic diagnostics only, not control authority or optimization targets | required | `pass` | `regimes.py`, `MetricPoint.regime_label`, and the absence of any decision/control interface in the shipped package |
| The package bootstraps into the repo Python environment so merged CI can import it without ad hoc path hacks | required | `pass` | `Makefile` editable-install wiring for `packages/adeu_odeu_sim[dev]` and green merged `python` CI on PR `#346` |
| No FastAPI route, browser UI, persistent storage, or product-surface entitlement ships in this slice | required | `pass` | shipped scope limited to `packages/adeu_odeu_sim`, tests, fixtures, bootstrap wiring, and closeout artifacts only |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v124_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v124/evidence_inputs/metric_key_continuity_assertion_v124.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v124/evidence_inputs/runtime_observability_comparison_v124.json` |

## Stop-Gate Summary

```json
{
  "schema": "v124_closeout_stop_gate_summary@1",
  "arc": "vNext+124",
  "target_path": "V51-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v123": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 143,
  "runtime_observability_delta_ms": 7
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v123_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v124_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+123","current_arc":"vNext+124","baseline_source":"artifacts/stop_gate/report_v123_closeout.md","current_source":"artifacts/stop_gate/report_v124_closeout.md","baseline_elapsed_ms":136,"current_elapsed_ms":143,"delta_ms":7,"notes":"v124 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V51-A ODEU simulation kernel lane: one repo-owned adeu_odeu_sim package, one deterministic kernel over the bounded one-region/one-commons/one-institution/one-archive starter domain, exact healthy_baseline and weak_d scenario replay with canonical seed 7 and horizon 25, first-class typed nested kernel models plus typed lane-crossing contracts and typed event records, deterministic agent-order and sanction-target tie-break behavior, fail-closed share-allocation and empty-agent validation, bootstrap wiring for editable package installation, and no API, UI, persistent-storage, or product-surface widening."}
```

## V51A ODEU Sim Kernel Evidence

```json
{"schema":"v51a_odeu_sim_kernel_evidence@1","evidence_input_path":"artifacts/agent_harness/v124/evidence_inputs/v51a_odeu_sim_kernel_evidence_v124.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS124.md#v124-continuation-contract-machine-checkable","merged_pr":"#346","merge_commit":"9d172a9307e492d5f74bd75944fabad86442f0b3","implementation_packages":["adeu_odeu_sim"],"odeu_sim_package_root":"packages/adeu_odeu_sim","odeu_sim_pyproject_path":"packages/adeu_odeu_sim/pyproject.toml","odeu_sim_models_source_path":"packages/adeu_odeu_sim/src/adeu_odeu_sim/models.py","odeu_sim_actions_source_path":"packages/adeu_odeu_sim/src/adeu_odeu_sim/actions.py","odeu_sim_scenarios_source_path":"packages/adeu_odeu_sim/src/adeu_odeu_sim/scenarios.py","odeu_sim_regimes_source_path":"packages/adeu_odeu_sim/src/adeu_odeu_sim/regimes.py","odeu_sim_metrics_source_path":"packages/adeu_odeu_sim/src/adeu_odeu_sim/metrics.py","odeu_sim_engine_source_path":"packages/adeu_odeu_sim/src/adeu_odeu_sim/engine.py","odeu_sim_package_init_source_path":"packages/adeu_odeu_sim/src/adeu_odeu_sim/__init__.py","repo_bootstrap_makefile_path":"Makefile","canonical_replay_seed":7,"canonical_replay_horizon":25,"test_reference_paths":["packages/adeu_odeu_sim/tests/test_odeu_sim_models.py","packages/adeu_odeu_sim/tests/test_odeu_sim_actions.py","packages/adeu_odeu_sim/tests/test_odeu_sim_scenarios.py","packages/adeu_odeu_sim/tests/test_odeu_sim_engine.py"],"reference_healthy_baseline_fixture_path":"packages/adeu_odeu_sim/tests/fixtures/v51a/reference_healthy_baseline_summary.json","reference_weak_d_fixture_path":"packages/adeu_odeu_sim/tests/fixtures/v51a/reference_weak_d_summary.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v124/evidence_inputs/metric_key_continuity_assertion_v124.json","runtime_observability_comparison_path":"artifacts/agent_harness/v124/evidence_inputs/runtime_observability_comparison_v124.json","runtime_event_stream_path":"artifacts/agent_harness/v124/runtime/evidence/local/urm_events.ndjson","notes":"v124 evidence pins the released V51-A ODEU simulation kernel lane on main: one repo-owned adeu_odeu_sim package, one deterministic starter kernel over healthy_baseline and weak_d, canonical replay seed 7 and horizon 25, first-class typed lane-state/agent/institution/resource/norm/action/lane-crossing/event/world-state models, deterministic agent-order and sanction-target tie-break law, typed event records instead of loose string-only logs, fail-closed scenario share validation, fail-closed empty-agent validation, review-hardened initialization-event and last_action replay-state bookkeeping, bootstrap wiring for editable package installation, deterministic v51a replay fixtures, and no API, browser UI, persistent-storage, or product-surface widening."}
```

## Recommendation (Post v124)

- gate decision:
  - `V51A_ODEU_SIM_KERNEL_COMPLETE_ON_MAIN`
  - `V51_ODEU_SIM_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v124` closes the bounded `V51-A` kernel seam on `main` by shipping the first
    repo-owned `adeu_odeu_sim` package over the imported sandbox prototype’s kernel
    decomposition, without promoting the prototype API or UI as live authority.
  - the shipped slice remains properly narrow: one package, one bounded
    one-region/one-commons/one-institution/one-archive starter domain, exact
    `healthy_baseline` and `weak_d` scenarios, deterministic replay with canonical
    seed `7` and horizon `25`, typed lane-crossing contracts, typed event records,
    heuristic regime diagnostics, and no API/UI or persistent storage.
  - review hardening landed in the release rather than staying in commentary:
    initialization events now attach to the current world, verify actions update
    `last_action`, and empty-agent kernel states fail closed instead of silently
    degrading metrics or summaries.
  - the repo bootstrap flow now installs the package, so full-suite CI can import the
    released kernel without local path hacks.
  - the imported sandbox bundle remains support-only and non-precedent; the release
    re-authors live code in repo-owned package paths rather than importing the
    prototype tree wholesale.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+7 ms` vs `v123` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` should now be read with `V51-A` closed on
    `main` and the branch-local default next path advanced to `V51-B` / `vNext+125`.
