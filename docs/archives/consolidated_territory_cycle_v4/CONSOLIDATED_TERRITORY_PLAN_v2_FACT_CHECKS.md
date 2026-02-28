# Consolidated Territory Plan v2 Fact Checks

This appendix records factual verification used to build `docs/CONSOLIDATED_TERRITORY_PLAN_v2.md`.

Status tags:
- `VERIFIED`: claim matches repo state.
- `MISMATCH`: claim wording/content does not match repo as stated.
- `MISSING`: required file/artifact does not exist.

## VERIFIED

1. v26 baseline lock and closeout artifacts exist.
- Evidence:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
  - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
  - `artifacts/stop_gate/metrics_v26_closeout.json`
  - `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`

2. Active `/urm` read/projection/proposer surfaces are present in API code.
- Evidence: `apps/api/src/adeu_api/main.py` route declarations for:
  - `/urm/core-ir/propose`
  - `/urm/core-ir/artifacts/*`
  - `/urm/normative-advice/*`
  - `/urm/proof-trust/*`
  - `/urm/semantics-v4/*`
  - `/urm/extraction-fidelity/*`

3. v26 lock explicitly freezes deterministic env and host-path allowlist rules.
- Evidence: `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` lines around:
  - deterministic env lock (`TZ=UTC`, `LC_ALL=C`)
  - host-path normalization allowlist (`baseline_path`, `candidate_path`, `report_path`, `manifest_path`)

4. Implementation currently normalizes broad `*_path/*_paths` keys in v26 parity projection.
- Evidence: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (`_normalize_vnext_plus26_parity_paths`).

5. Core risk hotspots by file size/centrality are real.
- Evidence:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` ~15179 LOC.
  - `apps/api/src/adeu_api/main.py` ~7424 LOC.

6. Lean ODEU prep files are present.
- Evidence:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`

7. Lean runner uses `NamedTemporaryFile`.
- Evidence: `packages/adeu_lean/src/adeu_lean/runner.py`.

8. Proposer idempotency cache is process-local in API memory.
- Evidence: `apps/api/src/adeu_api/main.py` (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`).

9. Worker-run route does not use `authorize_action` in its endpoint path.
- Evidence: `apps/api/src/adeu_api/urm_routes.py` (`urm_worker_run_endpoint`) contrasted with `authorize_action(...)` in tool/spawn/cancel endpoints.

10. Active stop-gate manifest version declarations are duplicated.
- Evidence:
  - `apps/api/scripts/build_stop_gate_metrics.py` (`_ACTIVE_MANIFEST_VERSIONS`)
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (default/path constants for vNext manifests)

## MISSING

1. S9 executable trigger checker script.
- Missing path: `apps/api/scripts/check_s9_triggers.py`
- Why this matters: v26 lock marks this as executable precondition, currently not enforceable as code.
- Remediation: add deterministic script reading the designated closeout artifact and fail-closed on missing/below-threshold trigger metrics.

2. v27 lock artifacts (expected to be absent at planning time, but still factual gaps).
- Missing paths:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
  - `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`
- Why this matters: confirms v2 must remain planning-only; no freeze claims for v27.
- Remediation: produce after selecting and freezing the next arc.

3. Dedicated v26 tooling transfer-report builder module/script counterpart.
- Evidence present for v24/v25:
  - `packages/urm_runtime/src/urm_runtime/extraction_fidelity_transfer_report_vnext_plus24.py`
  - `packages/urm_runtime/src/urm_runtime/core_ir_proposer_transfer_report_vnext_plus25.py`
- Missing dedicated `*vnext_plus26*` builder module/script.
- Why this matters: report regeneration path is less explicit than v24/v25 families.
- Remediation: add deterministic v26 builder module/script and parity tests against locked report payload.

## MISMATCH

1. Source filename mismatch from previous planning input naming.
- Claimed input filename in prompt chain: `docs/CONSOLIDATED_TERRITORY_PLAN_v0.md`.
- Actual repo file present: `docs/DRAFT_CONSOLIDATED_TERRITORY_PLAN_v0.md`.
- Why this matters: avoid stale path references in subsequent planning docs.
- Remediation: standardize references on the actual file path until renamed.
