# Consolidated Territory Plan v2 (Draft Planning, Not Frozen)

Inputs:

- `docs/reviewv2.md`
- `docs/leanv2.md`
- `docs/next arcv2.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v1.md`
- Repo fact checks captured in `docs/CONSOLIDATED_TERRITORY_PLAN_v2_FACT_CHECKS.md`

This document is planning-only. It is not a lock doc and does not authorize behavior changes.

## 1) Repo Truth Snapshot (Mechanically Verified)

### 1.1 Verification status summary

- `VERIFIED` current v26 lock baseline exists:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
  - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
  - `artifacts/stop_gate/metrics_v26_closeout.json`
  - `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`
- `VERIFIED` active evidence routes are present in:
  - `apps/api/src/adeu_api/main.py`
- `VERIFIED` ODEU Lean prep files are present:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`
- `MISSING` `apps/api/scripts/check_s9_triggers.py`
- `MISSING` v27 lock artifacts (expected for planning stage):
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
  - `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`

### 1.2 Pre-v27 fix list (hard preconditions to start next lock arc)

1. Missing S9 executable precondition script.
- Gap: `apps/api/scripts/check_s9_triggers.py` is absent.
- Why it matters: v26 lock declares it as executable precondition, but current enforcement is documentation-only.
- Lowest-lock fix: `L1` (lock-alignment correction).
- Acceptance check: script exists, reads v25 closeout artifact, fails closed on missing keys or `< 100.0` threshold values.

2. v26 parity normalization behavior is broader than frozen allowlist.
- Gap: implementation normalizes any `*_path`/`*_paths` key.
- Lock text freezes allowlist-only normalization (`baseline_path`, `candidate_path`, `report_path`, `manifest_path`).
- Lowest-lock fix: `L1`.
- Acceptance check: parity projection tests prove non-allowlist path fields are not normalized.

3. Deterministic env lock is not enforced by tooling entrypoints.
- Gap: tooling scripts do not enforce `TZ=UTC`/`LC_ALL=C` internally.
- Lowest-lock fix: `L0`.
- Acceptance check: entrypoint helper enforces/fails closed deterministically; existing fixture outputs unchanged.

4. No dedicated v26 tooling transfer-report builder module/script.
- Gap: v24/v25 have dedicated runtime builder modules, v26 report exists as doc but no dedicated builder module/script.
- Evidence:
  - `packages/urm_runtime/src/urm_runtime/extraction_fidelity_transfer_report_vnext_plus24.py`
  - `packages/urm_runtime/src/urm_runtime/core_ir_proposer_transfer_report_vnext_plus25.py`
  - no corresponding `*vnext_plus26*` builder module/script.
- Lowest-lock fix: `L0`.
- Acceptance check: deterministic v26 builder path added and parity-tested against current locked report payload.

## 2) Ranked Risk Register (Evidence + Lock Classification)

Lock classes:
- `L0`: behavior-preserving under current locks.
- `L1`: lock-alignment correction (should be fixed before expansion).
- `L2`: requires explicit lock release due to runtime policy/authority boundary change.

| Rank | Risk | Evidence | Lock class | Operational impact |
|---|---|---|---|---|
| 1 | v26 path normalization lock mismatch | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md:230-239`, `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:6680-6711` | `L1` | Can hide parity drift by over-normalizing hash inputs. |
| 2 | Missing S9 executable trigger checker | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md:73-75`, missing `apps/api/scripts/check_s9_triggers.py` | `L1` | Trigger gate is not mechanically enforced. |
| 3 | Deterministic env constraints not enforced at tooling entrypoints | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md:55-56`, `apps/api/scripts/build_stop_gate_metrics.py`, `apps/api/scripts/build_quality_dashboard.py` | `L0` | Determinism depends on caller shell discipline. |
| 4 | Canonical JSON/hashing helper duplication | `apps/api/src/adeu_api/hashing.py`, `packages/urm_runtime/src/urm_runtime/hashing.py`, `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`, `packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py`, `packages/adeu_explain/src/adeu_explain/explain_diff.py`, `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py` | `L0` | Drift risk in deterministic hash pipelines. |
| 5 | Stop-gate tooling complexity concentration | `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (~15179 LOC) | `L0` | High regression blast radius and slower lock-aligned changes. |
| 6 | API surface complexity concentration | `apps/api/src/adeu_api/main.py` (~7424 LOC) | `L0` | Coupling risk for route/contract maintenance. |
| 7 | Manifest version wiring duplication | `apps/api/scripts/build_stop_gate_metrics.py` (`_ACTIVE_MANIFEST_VERSIONS`), `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (vnext manifest constants) | `L0` | Arc-rollover drift risk. |
| 8 | `/urm/worker/run` bypasses capability-policy path | `apps/api/src/adeu_api/urm_routes.py` (`urm_worker_run_endpoint` vs `authorize_action(...)` usage in tool endpoints) | `L2` | Governance consistency gap; default change alters runtime behavior. |
| 9 | Proposer idempotency cache is process-local | `apps/api/src/adeu_api/main.py` (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`) | `L2` | Multi-process correctness gap; persistent semantics requires release. |
| 10 | Lean runner temp filename nondeterminism | `packages/adeu_lean/src/adeu_lean/runner.py` (`NamedTemporaryFile`) | `L0` | Potential nondeterministic noise in proof evidence paths. |
| 11 | v26 tooling transfer-report builder path not explicit | present v24/v25 builders in `packages/urm_runtime/src/urm_runtime/*transfer_report_vnext_plus24.py` and `*vnext_plus25.py`; no dedicated v26 counterpart | `L0` | Manual/report drift risk for v26 family regeneration. |

## 3) Cross-stream Shared Primitives (Non-negotiable)

1. Deterministic env enforcement helper used by tooling entrypoints.
2. Canonical JSON conformance tests across API/runtime/kernel helper implementations.
3. Single reusable recursive `created_at` stripping helper for parity hash projections.
4. Shared active-manifest registry consumed by runtime/scripts/tests.
5. Lock-conformant v26 path normalization allowlist behavior.
6. Deterministic executable S9 trigger checker (fail-closed).
7. Formal-lane oracle boundary declaration (structural proofs hard, hashing/canonical-json oracle-bounded unless explicitly released).

## 4) Workstreams + Thin-slice Arcs (Normalized vNext numbering)

## Workstream W1: Determinism and Lock Alignment Baseline

### Arc vNext+27 (Path A)

Readiness: **Draft lock candidate**.

Scope:
- Implement missing deterministic S9 trigger checker.
- Enforce deterministic env in tooling entrypoints.
- Align v26 path normalization with allowlist in lock text.
- Add canonical-json conformance tests.

Locks:
- No schema changes.
- No metric-key additions.
- Preserve `stop_gate_parity.v1` behavior on locked fixtures.

Acceptance:
- Existing v26 closeout outputs remain reproducible on locked fixtures.
- S9 checker is executable and fail-closed.
- Conformance tests pass across helper implementations.

Stop-gate impact:
- None.

## Workstream W2: Stop-gate Tooling Sustainability

### Arc vNext+28 (Path A)

Readiness: **Draft lock candidate**.

Scope:
- Modularize `stop_gate_tools.py` internals while preserving compatibility façade.
- Introduce shared manifest registry and remove duplicated version declarations.
- Add deterministic builder path for v26 tooling transfer report parity regeneration.

Locks:
- Preserve output payload shapes and deterministic ordering.
- Preserve existing metric definitions.

Acceptance:
- Baseline vs candidate parity is hash-identical for locked fixture suites.
- Existing stop-gate tests remain green.

Stop-gate impact:
- None.

## Workstream W3: Product Read-only Evidence UX

### Arc vNext+29 (Path B)

Readiness: **Draft lock candidate**.

Scope:
- Add deterministic catalog/list endpoints over existing evidence families.
- Add read-only evidence explorer UI.
- Present trust-lane labels and explicit non-enforcement boundaries.

Locks:
- No provider expansion.
- No enforcement behavior.
- Fixture-first authority remains unchanged for evidence families.

Acceptance:
- Sorted deterministic list outputs.
- No-provider/no-mutation guard coverage for new read surfaces.
- Non-enforcement semantics explicit in UI.

Stop-gate impact:
- None.

## Workstream W4: Formal ODEU Additive Lane

### Arc vNext+30 (Path C)

Readiness: **Planning-only research arc** (needs toolchain/fixture agreement evidence finalized before lock drafting).

Scope:
- Stabilize `AdeuCore.ODEU.*` compile path.
- Prove first structural invariants aligned with current validators.
- Add deterministic fixture-backed agreement checks (Python canonicalization -> Lean typed constants).

Locks:
- `SEMANTICS_v3` remains runtime authority.
- No enforcement derived from Lean outputs.
- Oracle boundary for hashing/canonical-json remains explicit.

Acceptance:
- Deterministic compile and agreement-check runs on selected fixtures.
- No runtime API/kernel behavior changes.

Stop-gate impact:
- None by default.
- Metric additions only if a new evidence family is explicitly introduced and justified in a future lock.

## 5) Deferred L2 Bucket (Explicit lock release required)

These are not next-arc defaults; they require explicit continuation lock release:

1. Default capability-policy enforcement for `/urm/worker/run`.
2. Persistent/shared proposer idempotency storage replacing process-local cache.

## 6) Recommended Sequence + Dependency Edges

Recommended sequence:

1. `vNext+27` Path A (W1)
2. `vNext+28` Path A (W2)
3. `vNext+29` Path B (W3)
4. `vNext+30` Path C (W4, research-to-lock transition)

Explicit dependency edges:

- `vNext+28 Path A` depends on `vNext+27 Path A`.
  - Needs lock-aligned normalization and deterministic env/conformance baseline first.
- `vNext+29 Path B` depends on `vNext+27 Path A`.
  - Needs deterministic and lock-compliant data plumbing before UX surfacing.
- `vNext+30 Path C` depends on `vNext+27 Path A` and partially on `vNext+28 Path A`.
  - Needs stable canonicalization and fixture/tooling modularity for agreement checks.
- `L2` items depend on a separate explicit lock release and are excluded from the recommended sequence.

## 7) Planning Boundaries

- This document is planning-only and not contract-freezing.
- This document does not implement code.
- This document does not add metric keys.
- New metric keys are only in scope when a new evidence family is explicitly justified and locked.
