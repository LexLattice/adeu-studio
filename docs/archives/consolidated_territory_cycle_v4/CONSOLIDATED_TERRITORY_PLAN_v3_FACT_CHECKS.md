# Consolidated Territory Plan v3 Fact Checks

This appendix carries forward v2 checks and records any additional claim checks used in `docs/CONSOLIDATED_TERRITORY_PLAN_v3.md`.

Status tags:
- `VERIFIED`
- `MISSING`
- `MISMATCH`

## VERIFIED

1. v26 lock baseline and closeout artifacts exist.
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
- `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
- `artifacts/stop_gate/metrics_v26_closeout.json`
- `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`

2. Active evidence `/urm` routes are present in API.
- `apps/api/src/adeu_api/main.py` includes:
  - `/urm/core-ir/propose`
  - `/urm/core-ir/artifacts/*`
  - `/urm/normative-advice/*`
  - `/urm/proof-trust/*`
  - `/urm/semantics-v4/*`
  - `/urm/extraction-fidelity/*`

3. v26 lock explicitly freezes deterministic env and host-path normalization allowlist.
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` contains:
  - deterministic env lock (`TZ=UTC`, `LC_ALL=C`)
  - allowlist-only path normalization keys (`baseline_path`, `candidate_path`, `report_path`, `manifest_path`)

4. v26 normalization implementation currently applies broad suffix behavior.
- `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`:
  - `_normalize_vnext_plus26_parity_paths`
  - suffix checks for `endswith("_path")` / `endswith("_paths")`

5. Hotspot LOC anchors are accurate at check time.
- `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`: ~15179 LOC.
- `apps/api/src/adeu_api/main.py`: ~7424 LOC.

6. Canonical JSON/hash helpers are duplicated across layers.
- `apps/api/src/adeu_api/hashing.py`
- `packages/urm_runtime/src/urm_runtime/hashing.py`
- `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`
- `packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py`
- `packages/adeu_explain/src/adeu_explain/explain_diff.py`
- `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py`

7. Lean ODEU prep and runner facts.
- `packages/adeu_lean/AdeuODEU/Artifacts.lean` exists.
- `packages/adeu_lean/AdeuODEU/Invariants.lean` exists.
- `packages/adeu_lean/src/adeu_lean/runner.py` uses `NamedTemporaryFile`.

8. Proposer idempotency cache is process-local.
- `apps/api/src/adeu_api/main.py` (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`).

9. Worker-run endpoint path differs from capability-gated tool-call path.
- `apps/api/src/adeu_api/urm_routes.py`:
  - `urm_worker_run_endpoint` does not call `authorize_action`.
  - tool/spawn/cancel paths call `authorize_action`.

10. Active-manifest declarations are duplicated between script and runtime tooling.
- `apps/api/scripts/build_stop_gate_metrics.py` (`_ACTIVE_MANIFEST_VERSIONS`).
- `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (manifest defaults/constants).

11. v24/v25 dedicated transfer-report builder modules exist.
- `packages/urm_runtime/src/urm_runtime/extraction_fidelity_transfer_report_vnext_plus24.py`
- `packages/urm_runtime/src/urm_runtime/core_ir_proposer_transfer_report_vnext_plus25.py`

## MISSING

1. S9 trigger checker script.
- Missing: `apps/api/scripts/check_s9_triggers.py`.
- Remediation: add deterministic fail-closed script + tests.

2. v27 lock artifacts (planning-stage expected missing, still factual gaps).
- Missing:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
  - `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`

3. Dedicated v26 transfer-report builder module/script counterpart.
- No dedicated `*vnext_plus26*` builder module/script under:
  - `packages/urm_runtime/src/urm_runtime/`
  - `apps/api/scripts/`
- Remediation: add deterministic builder path + parity tests.

## MISMATCH

1. v0 consolidated plan filename reference mismatch in earlier prompt chain.
- Referenced: `docs/CONSOLIDATED_TERRITORY_PLAN_v0.md`.
- Present: `docs/DRAFT_CONSOLIDATED_TERRITORY_PLAN_v0.md`.
- Remediation: use the actual path consistently until/if renamed.
