# Future Cleanups Tracker

This note tracks small follow-up cleanups that are intentionally out of scope for the
current milestone PR sequence.

## Pending

- `cleanup-policy-cli-strictness-defaults`:
  align `policy validate`, `policy eval`, and `policy diff` strictness defaults and
  preserve explicit compatibility flags. This is the separate cleanup PR noted during N2 planning.
- `cleanup-copilot-child-queue-method-extraction`:
  refactor large `URMCopilotManager` methods in
  `packages/urm_runtime/src/urm_runtime/copilot.py` into smaller helpers without behavior
  changes:
  - `_run_child_workflow_v2`
  - `_spawn_child_v2`
  - `_recover_stale_child_runs`
  This was deferred from PR3/PR4 as maintainability-only follow-up work.
- `cleanup-vnext-plus16-schema-consolidation-evaluation`:
  evaluate whether `adeu_integrity_dangling_reference@0.1`,
  `adeu_integrity_cycle_policy@0.1`, and `adeu_integrity_deontic_conflict@0.1`
  should remain separate or move to a unified `adeu_integrity@0.1` family with a
  deterministic discriminator, after v16 stability evidence is available.
- `cleanup-vnext-plus16-drift-error-granularity`:
  evaluate splitting shared `URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT` into
  per-diagnostic-family drift codes if debugging signal is insufficient in production.
- `cleanup-vnext-plus16-stop-gate-ci-budget`:
  assess CI/runtime budget impact from cumulative stop-gate metric growth (30+ metrics),
  and propose bounded runtime strategies (fixture scheduling, selective lanes, or
  deterministic parallelization) without reducing gate guarantees.
- `cleanup-vnext-plus16-d2-d-lane-cycle-expansion`:
  evaluate whether integrity cycle diagnostics should expand beyond `E`-layer
  `depends_on` edges to include `D`-lane policy/exception cyclic structures in a follow-on arc.
- `cleanup-vnext-plus16-d3-condition-alias-policy`:
  revisit whether normalized condition aliases beyond current baseline should include or
  exclude additional semantic tokens; confirm long-term handling of `"always"`/`"none"` style
  condition encodings against real fixture distributions.
- `cleanup-vnext-plus16-hostile-fixture-generation`:
  evaluate adding deterministic procedural hostile fixture generation for integrity diagnostics
  (malformed/dangling/cyclic payload families) to improve defense-in-depth coverage while
  preserving replay determinism.
- `cleanup-vnext-plus16-diagnostic-delta-tracking`:
  evaluate additive baseline-to-baseline diagnostic delta tracking (deterministic hash or
  counts diff) in transfer-report tooling for faster regression triage across arcs.
- `cleanup-vnext-plus16-shared-validation-module`:
  extract duplicated v16 manifest/artifact validation logic currently mirrored between
  `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` and
  `apps/api/src/adeu_api/integrity_transfer_report_vnext_plus16.py` into shared helpers
  (runtime-owned) to reduce maintenance drift risk without changing validation behavior.
- `cleanup-vnext-plus25-extraction-fidelity-ui-render-keys`:
  for the planned v25 diff-viewer surface, add an explicit UI-safe render key contract
  (derived key field or constrained `match_id` profile) so frontend key props do not rely
  on opaque `match_id` content assumptions from v24.
- `cleanup-stop-gate-metrics-input-model`:
  replace the wide argument list for
  `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:build_stop_gate_metrics`
  with a typed request model (for example Pydantic/dataclass) to reduce call-site drift
  and improve maintainability without changing metric behavior.
