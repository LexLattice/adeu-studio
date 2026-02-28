# Consolidated Territory Plan v1 (Draft Planning, Not Frozen)

Inputs used:

- `docs/reviewv2.md`
- `docs/leanv2.md`
- `docs/next arcv2.md`
- `docs/DRAFT_CONSOLIDATED_TERRITORY_PLAN_v0.md`
- Current repo state (code, fixtures, closeout artifacts)

This is a planning document only. It is not a lock doc and does not authorize behavior changes by itself.

## 1) Repo Truth Snapshot (Grounded)

### 1.1 Current locked baseline and evidence

- Latest continuation lock in repo:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
- Latest closeout draft and artifacts:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
  - `artifacts/stop_gate/metrics_v26_closeout.json`
  - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
- v26 fixture manifest is present:
  - `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`

### 1.2 Active evidence surfaces present in code

- Proposer surface:
  - `apps/api/src/adeu_api/main.py` (`POST /urm/core-ir/propose`)
- Read/evidence surfaces:
  - `apps/api/src/adeu_api/main.py`:
    - `/urm/core-ir/artifacts/{artifact_id}`
    - `/urm/core-ir/artifacts/{artifact_id}/lane-projection`
    - `/urm/core-ir/artifacts/{artifact_id}/lane-report`
    - `/urm/core-ir/artifacts/{artifact_id}/integrity/{family}`
    - `/urm/normative-advice/pairs/...`
    - `/urm/normative-advice/projection`
    - `/urm/proof-trust/pairs/...`
    - `/urm/proof-trust/projection`
    - `/urm/semantics-v4/pairs/...`
    - `/urm/semantics-v4/projection`
    - `/urm/extraction-fidelity/sources/{source_text_hash}`
    - `/urm/extraction-fidelity/projection`
- Stop-gate fixtures up through v26 exist:
  - `apps/api/fixtures/stop_gate/vnext_plus21...vnext_plus26*`

### 1.3 Immediate factual gaps

- No v27 lock artifacts yet:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md` (missing)
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md` (missing)
  - `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json` (missing)
- v26 lock references an executable S9 precondition script, but file is absent:
  - `apps/api/scripts/check_s9_triggers.py` (missing)

### 1.4 Lean formal lane baseline

- Existing Lean library wiring:
  - `packages/adeu_lean/lakefile.lean`
  - `packages/adeu_lean/AdeuCore.lean`
- Existing ODEU prep files:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`
- Lean runner currently uses random temp filenames:
  - `packages/adeu_lean/src/adeu_lean/runner.py` (`NamedTemporaryFile`)

## 2) Ranked Risk Register (Evidence + Lock Classification)

Lock classification legend:
- `L0`: behavior-preserving change allowed under current locks.
- `L1`: lock-alignment correction (doc/code mismatch; should be fixed before expansion).
- `L2`: requires explicit lock release because default runtime behavior/authority boundary changes.

| Rank | Risk | Evidence paths | Lock class | Why it matters |
|---|---|---|---|---|
| 1 | v26 parity-path normalization is broader than lock allowlist | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`, `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (`_normalize_vnext_plus26_parity_paths`) | `L1` | Can mask parity drift by normalizing fields outside frozen scope. |
| 2 | S9 executable precondition script missing | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`, `apps/api/scripts/check_s9_triggers.py` (missing) | `L1` | Trigger gate remains policy-only instead of mechanically enforced. |
| 3 | Deterministic env lock not enforced in tooling entrypoints | `apps/api/scripts/build_stop_gate_metrics.py`, `apps/api/scripts/build_quality_dashboard.py` | `L0` | Relies on operator shell discipline instead of fail-closed tooling behavior. |
| 4 | Canonical JSON/hashing logic duplicated across layers | `apps/api/src/adeu_api/hashing.py`, `packages/urm_runtime/src/urm_runtime/hashing.py`, `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`, `packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py`, `packages/adeu_explain/src/adeu_explain/explain_diff.py`, `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py` | `L0` | High drift risk for determinism and replay integrity. |
| 5 | Stop-gate tooling is still a monolith (complexity concentration) | `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (~15179 LOC) | `L0` | Raises regression risk and slows lock-compliant changes. |
| 6 | API main surface is still a monolith (coupling concentration) | `apps/api/src/adeu_api/main.py` (~7424 LOC) | `L0` | Increases blast radius for route/contract changes. |
| 7 | Active stop-gate manifest version wiring is duplicated | `apps/api/scripts/build_stop_gate_metrics.py`, `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` | `L0` | Version drift risk on future arc rollover. |
| 8 | `/urm/worker/run` bypasses capability policy path used by tool calls | `apps/api/src/adeu_api/urm_routes.py` (`urm_worker_run_endpoint`, `authorize_action` usage elsewhere) | `L2` | Governance inconsistency; changing default behavior affects runtime policy semantics. |
| 9 | Core-ir proposer idempotency cache is process-local and unbounded | `apps/api/src/adeu_api/main.py` (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`) | `L2` | Multi-worker/multi-instance correctness gap; persistent semantics change needs explicit release. |
| 10 | Lean runner random temp filename can leak nondeterminism into evidence paths | `packages/adeu_lean/src/adeu_lean/runner.py` | `L0` | Undermines deterministic proof-lane evidence reproducibility when enabled. |

## 3) Cross-stream Shared Primitives (Non-negotiable Prerequisites)

1. Deterministic environment enforcement helper.
- Must be invoked by tooling entrypoints, not only CI shell wrappers.
- Initial targets: `apps/api/scripts/build_stop_gate_metrics.py`, `apps/api/scripts/build_quality_dashboard.py`.

2. Canonical JSON conformance test suite across API/runtime/kernel implementations.
- Validates identical canonicalization/hash behavior for frozen profile.
- Guards against silent drift across duplicate helpers.

3. Single shared `created_at` stripping primitive for parity hash projections.
- No ad hoc recursive stripping variants in feature-specific code.

4. Single source of truth for active stop-gate manifest versions.
- Shared registry consumed by scripts/tests/runtime tooling.

5. Lock-conformant v26 path normalization allowlist behavior.
- Normalize only fields frozen in lock text.

6. Executable S9 trigger check contract.
- Deterministic parser over closeout artifact source.
- Fail-closed on missing keys or thresholds below required values.

7. Formal-lane oracle boundary declaration.
- Lean proofs can hard-prove structural invariants.
- sha256/canonical-json equivalence remains oracle-bounded unless separately released.

## 4) Workstreams and Thin-slice Arcs

## Workstream 1: Tooling Determinism + Lock Alignment

### Arc vNext+27 (Path A: Determinism hardening baseline)

Scope:
- Add deterministic env enforcement in tooling entrypoints.
- Implement missing `check_s9_triggers.py` precondition script.
- Add canonical-json conformance tests across key helper implementations.
- Align v26 path normalization implementation with frozen allowlist.

Locks:
- No schema changes.
- No stop-gate metric key additions.
- Keep `stop_gate_parity.v1` semantics unchanged for locked fixtures.

Acceptance:
- Existing v26 closeout metrics remain reproducible and unchanged for locked fixtures.
- Script-level trigger check is executable and fail-closed.
- Conformance tests pass across API/runtime/kernel canonical-json helpers.

Stop-gate impact:
- None (behavior-preserving hardening only).

### Arc vNext+28 (Path A: Stop-gate modularization)

Scope:
- Split stop-gate tooling internals into smaller modules with compatibility façade.
- Introduce shared manifest version registry and remove duplicated version tuples.

Locks:
- Preserve public entrypoints and output payloads.
- Preserve deterministic ordering and hashing behavior.

Acceptance:
- Golden parity: baseline vs candidate stop-gate outputs remain hash-identical under current projection rules.
- Existing stop-gate test suite remains green.

Stop-gate impact:
- None.

## Workstream 2: Runtime Governance Hardening

### Arc vNext+29 (Path B: Governance prep with compatibility defaults)

Scope:
- Add explicit worker-run governance observability and optional policy-gate path behind config flag.
- Add explicit idempotency cache observability/limits for proposer path (no default storage-model change yet).

Locks:
- Default runtime behavior must remain compatible unless lock release is approved.
- No provider surface expansion.

Acceptance:
- With defaults, behavior remains unchanged.
- Optional stricter modes are deterministic and fully tested.

Stop-gate impact:
- None.

Notes:
- Enforcing policy by default for `/urm/worker/run` or moving proposer idempotency to persistent storage is `L2` and requires explicit continuation lock release in a later arc.

## Workstream 3: Product Read-only Evidence UX

### Arc vNext+30 (Path C: Evidence Explorer v1)

Scope:
- Add deterministic catalog/list endpoints over existing evidence families.
- Add web read-only evidence explorer pages for packet/projection browsing.
- Surface trust-lane and non-enforcement labels explicitly in UI.

Locks:
- No new enforcement behaviors.
- No provider calls in evidence browsing paths.
- Fixture-first authority for cross-IR/coherence remains unchanged.

Acceptance:
- Deterministic sorted list outputs.
- No-provider/no-mutation guard coverage on new read endpoints.
- UI labels clearly distinguish advisory/candidate outputs as non-enforcing.

Stop-gate impact:
- None (UI and read-only endpoint layer).

## Workstream 4: Formal ODEU Lane (Additive)

### Arc vNext+31 (Path D: Lean ODEU skeleton + agreement checks)

Scope:
- Stabilize `AdeuCore.ODEU.*` module scaffolding.
- Prove first structural invariants aligned with existing Python validators.
- Add deterministic fixture-backed agreement checks via Python->Lean typed constant path.

Locks:
- No runtime semantic authority shift (`SEMANTICS_v3` remains default).
- No new enforcement logic from Lean outputs.
- Keep canonical-json/sha256 oracle boundary explicit.

Acceptance:
- Lean scaffold compiles reproducibly.
- Agreement tests pass on selected fixture-backed artifacts.
- No runtime behavior changes on API/kernel code paths.

Stop-gate impact:
- None by default.
- Metric additions only if a new evidence family is introduced and explicitly locked.

## 5) Recommended Sequence + Explicit Dependency Edges

Recommended sequence:

1. `vNext+27` Path A (Tooling determinism hardening baseline)
2. `vNext+28` Path A (Stop-gate modularization)
3. `vNext+30` Path C (Read-only Evidence Explorer)
4. `vNext+31` Path D (Lean ODEU skeleton + agreement)
5. `vNext+29` Path B (Governance prep), with `L2` changes deferred until explicit release

Rationale:
- Resolves lock-alignment and determinism risks first.
- Preserves stop-gate continuity before adding product UX surface area.
- Keeps formal lane additive and low-risk.
- Defers governance changes that require lock release to avoid accidental semantic shifts.

Dependency edges:

- `vNext+28 Path A` depends on `vNext+27 Path A`:
  - requires deterministic env/conformance baseline and lock-aligned parity behavior first.
- `vNext+30 Path C` depends on `vNext+27 Path A`:
  - requires stable deterministic tooling and lock-compliant catalog/parity assumptions.
- `vNext+31 Path D` depends on `vNext+27 Path A`:
  - requires canonical-json conformance and deterministic helper baseline.
- `vNext+29 Path B` depends on `vNext+27 Path A`:
  - governance hardening should start from lock-aligned deterministic foundation.
- Any default-on governance enforcement change in `vNext+29 Path B` requires an explicit new lock release (`L2`) before merge.

## 6) Explicit Planning Boundaries

- This document is planning-only and does not freeze contracts.
- No lock doc text is authored here.
- No code or fixture implementation is performed here.
- No new metric keys are proposed in this plan; additive keys are only in scope when a new evidence family is explicitly introduced and locked.
