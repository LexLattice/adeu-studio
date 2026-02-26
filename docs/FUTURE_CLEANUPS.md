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
- `cleanup-vnext-plus24-x4-catalog-helper-cache`:
  apply a tiny read-path optimization in
  `apps/api/tests/test_extraction_fidelity_x4_guards.py` by caching `_catalog_payload`
  (and clearing that cache in the autouse fixture) to avoid repeated fixture file I/O
  when test case count grows.
- `cleanup-vnext-plus24-transfer-report-builder`:
  add a dedicated v24 extraction-fidelity transfer-report builder module/script/test
  (parity with prior arcs) so `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md`
  is generated mechanically from manifests/captured fixtures instead of manual updates.
- `cleanup-read-surface-guard-harness-consolidation`:
  consolidate repeated guard-test scaffolding across read-surface families
  (`*_c4_guards.py`, `*_n4_guards.py`, `*_t4_guards.py`, `*_v4_guards.py`,
  `test_extraction_fidelity_x4_guards.py`) into shared helper utilities for
  materialization-target lists, fixture-surface hashing, and non-enforcement key scans.
- `cleanup-next-arc-options-rollover-discipline`:
  reduce stale planning-state drift in `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` by
  introducing a lightweight update checklist/script that is run whenever an arc
  closeout decision doc is merged (execution checkpoint + proposed freeze candidate
  sections must be advanced in the same follow-up commit).
- `cleanup-vnext-plus25-s3b-metric-key-finalization`:
  before freezing `docs/LOCKED_CONTINUATION_vNEXT_PLUS25.md`, validate and align
  proposed v25 S3b stop-gate metric key names against runtime conventions to avoid
  lock/doc naming drift during implementation.
- `cleanup-vnext-plus25-provider-telemetry-capture`:
  evaluate adding optional proposer provider telemetry capture for S3b follow-on arcs
  (`remote_latency_ms`, token counters, and capture-time provider metadata) with
  deterministic replay-safe exclusion rules so observability can improve without
  destabilizing lock-level determinism contracts.
