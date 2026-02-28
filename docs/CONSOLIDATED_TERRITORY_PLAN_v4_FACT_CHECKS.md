# Consolidated Territory Plan v4 Fact Checks

This appendix carries forward v3 checks and records additional verification used in `docs/CONSOLIDATED_TERRITORY_PLAN_v4.md`.

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

2. Active evidence routes exist in API (`apps/api/src/adeu_api/main.py`).
- Includes:
  - `/urm/core-ir/propose`
  - `/urm/core-ir/artifacts/*`
  - `/urm/normative-advice/*`
  - `/urm/proof-trust/*`
  - `/urm/semantics-v4/*`
  - `/urm/extraction-fidelity/*`

3. v26 lock includes deterministic env lock and path-normalization allowlist lock.
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` sections covering:
  - `TZ=UTC`, `LC_ALL=C`
  - allowlist keys: `baseline_path`, `candidate_path`, `report_path`, `manifest_path`

4. v26 lock binds S9 precondition to v25 closeout evidence reference.
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` includes S9 trigger precondition section referencing:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md`

5. v26 parity normalization implementation currently applies suffix-based path handling.
- `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`:
  - `_normalize_vnext_plus26_parity_paths`
  - `endswith("_path")` / `endswith("_paths")`

6. Hotspot LOC anchors at check time.
- `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`: ~15179 LOC.
- `apps/api/src/adeu_api/main.py`: ~7424 LOC.

7. Canonical JSON helper duplication is present across layers.
- `apps/api/src/adeu_api/hashing.py`
- `packages/urm_runtime/src/urm_runtime/hashing.py`
- `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`
- `packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py`
- `packages/adeu_explain/src/adeu_explain/explain_diff.py`
- `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py`

8. Lean lane facts.
- `packages/adeu_lean/AdeuODEU/Artifacts.lean` exists.
- `packages/adeu_lean/AdeuODEU/Invariants.lean` exists.
- `packages/adeu_lean/src/adeu_lean/runner.py` uses `NamedTemporaryFile`.

9. Governance and idempotency risk facts.
- `apps/api/src/adeu_api/urm_routes.py`:
  - `urm_worker_run_endpoint` path does not call `authorize_action`.
  - other tool lifecycle endpoints do call `authorize_action`.
- `apps/api/src/adeu_api/main.py`:
  - `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` exists and is process-local.

10. Transfer-report module coverage fact.
- dedicated modules exist:
  - `packages/urm_runtime/src/urm_runtime/extraction_fidelity_transfer_report_vnext_plus24.py`
  - `packages/urm_runtime/src/urm_runtime/core_ir_proposer_transfer_report_vnext_plus25.py`
- no dedicated `*vnext_plus26*` transfer-report module exists under `packages/urm_runtime/src/urm_runtime/`.

## MISSING

1. `apps/api/scripts/check_s9_triggers.py`.
- Impact: executable precondition declared in v26 lock is not implemented as script.
- Remediation: deterministic fail-closed script + tests.

2. v27 lock artifacts (expected planning-stage gaps).
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
- `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`

3. dedicated v26 transfer-report builder entrypoint counterpart.
- no `*vnext_plus26*` script in `apps/api/scripts/`.
- remediation: add deterministic runtime builder + script entrypoint + parity tests.

## MISMATCH

1. v0 plan filename reference mismatch in earlier chain.
- referenced: `docs/CONSOLIDATED_TERRITORY_PLAN_v0.md`
- present: `docs/DRAFT_CONSOLIDATED_TERRITORY_PLAN_v0.md`
- remediation: use actual path consistently unless renamed.
