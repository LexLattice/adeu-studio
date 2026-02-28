# Consolidated Territory Plan v0 (Draft)

This document consolidates prep work from:

- `docs/review.md`
- `docs/reviewv2.md`
- `docs/next arc.md`
- `docs/next arcv2.md`
- `docs/lean.md`
- `docs/leanv2.md`
- Lean prep artifacts:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`
- Drafting guidance authority:
  - `docs/gptguide.md`

Status: draft planning doc (not frozen).

## 1) Repo Truth Snapshot + Risk Register

### 1.1 Current repo truth (grounded)

- Latest locked continuation baseline is `vNext+26`:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
  - `artifacts/stop_gate/metrics_v26_closeout.json`
- Next vNext index is not yet locked in repo docs. Use `vNext+27+` placeholders for planning.
- Active lane artifacts are present through v26 (read-surface/cross-IR/normative-advice/trust/semantics-candidate/extraction-fidelity/proposer/tooling parity).
- v26 lock expects deterministic S9 precondition script, but the script is currently missing:
  - `apps/api/scripts/check_s9_triggers.py` (missing)
- Existing Lean foundation now includes additive ODEU formal scaffolding:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`

### 1.2 Top 10 repo-grounded risks/hotspots

1. `stop_gate_tools.py` remains a mega-module with mixed concerns.
- Path: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (`15179` LOC).

2. API `main.py` remains a mega-module with broad surface coupling.
- Path: `apps/api/src/adeu_api/main.py` (`7424` LOC).

3. Canonical JSON/hashing logic is duplicated across layers (drift risk).
- Paths:
  - `apps/api/src/adeu_api/hashing.py`
  - `packages/urm_runtime/src/urm_runtime/hashing.py`
  - `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`
  - `packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py`
  - `packages/adeu_explain/src/adeu_explain/explain_diff.py`
  - `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py`

4. v26 path normalization implementation is broader than the lock allowlist.
- Lock keys: `baseline_path`, `candidate_path`, `report_path`, `manifest_path`.
- Current code normalizes any `*_path` / `*_paths` key.
- Paths:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (`_normalize_vnext_plus26_parity_paths`)

5. Deterministic env lock is documented, but tooling entrypoints do not enforce it internally.
- Paths:
  - `apps/api/scripts/build_stop_gate_metrics.py`
  - `apps/api/scripts/build_quality_dashboard.py`

6. S9 trigger check is documented as executable precondition but script is absent.
- Paths:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
  - `apps/api/scripts/check_s9_triggers.py` (missing)

7. `/urm/worker/run` bypasses capability policy checks.
- Path: `apps/api/src/adeu_api/urm_routes.py` (`urm_worker_run_endpoint`).

8. Core-IR proposer idempotency cache is process-local and non-persistent.
- Path: `apps/api/src/adeu_api/main.py` (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`).

9. Active stop-gate manifest version wiring is duplicated across tooling surfaces.
- Paths:
  - `apps/api/scripts/build_stop_gate_metrics.py` (`_ACTIVE_MANIFEST_VERSIONS`)
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (vnext manifest constants/defaults)

10. Lean runner uses random temporary filenames (determinism contamination risk in evidence flows).
- Path: `packages/adeu_lean/src/adeu_lean/runner.py` (`NamedTemporaryFile`).

## 2) Consolidated Workstreams (Distinct, Cross-linked)

## 2.1 Workstream A: Tooling/Determinism Hardening + Refactor

### Purpose

Close concrete determinism and lock-drift risks in existing tooling before new evidence families expand operational load.

### Constraints/locks this stream must obey

- Preserve `stop_gate_metrics@1` continuity (additive-only keys, no renames).
- UI-only changes must not add stop-gate keys.
- Match lock text exactly for v26 parity projection behavior.
- Keep `SEMANTICS_v3` default runtime authority unchanged.

### Thin-slice arc proposals (`vNext+27+` placeholders)

- `vNext+27A` Tooling determinism hardening:
  - deterministic env helper enforcement in tooling entrypoints
  - v26 parity allowlist normalization fix
  - canonical-json conformance tests across layers
  - add missing `apps/api/scripts/check_s9_triggers.py`
- `vNext+28A` Stop-gate modularization + manifest registry single-source:
  - split `stop_gate_tools.py` internally
  - centralize active manifest version registry
- `vNext+29A` Runtime/tooling normalization cleanup:
  - repo-root discovery normalization
  - policy packaged-vs-repo sync coverage expansion

### Stop-gate impact

- `vNext+27A`: none (behavior-preserving, no new metric keys).
- `vNext+28A`: none (refactor-only, parity proof required).
- `vNext+29A`: none unless a new evidence family is introduced.

## 2.2 Workstream B: Product/UX Evidence Browsing Ladder

### Purpose

Make existing evidence families usable in product UX without introducing enforcement, provider expansion, or hidden recomputation.

### Constraints/locks this stream must obey

- Fixture-first authority remains binding for cross-IR/coherence until explicit release.
- Evidence explorer surfaces browse existing evidence only; they do not invent evidence.
- No enforcement flags or auto-apply behaviors in early UX slices.
- Keep single-version lock-doc style per arc.

### Thin-slice arc proposals (`vNext+27+` placeholders)

- `vNext+27B` Read-only Evidence Explorer:
  - deterministic list/catalog endpoints for existing evidence families
  - web evidence browsing surface (read-only)
  - trust lane + non-enforcement labels in UI
- `vNext+28B` Artifact evidence panel for existing DB-backed derived artifacts:
  - unify explain/semantic-depth/evidence navigation
  - no provider expansion
- `vNext+29B` Core-IR preview lane (read-only):
  - deterministic preview payloads
  - no persistence writes

### Stop-gate impact

- `vNext+27B`: none (UI/read-only; reuse existing fixtures/contracts).
- `vNext+28B`: none unless new evidence family is created.
- `vNext+29B`: none if read-only payload reuse; additive only if a new evidence family is introduced.

## 2.3 Workstream C: Formal Verification / Lean ODEU Template

### Purpose

Build additive formal evidence over already-frozen structural contracts, with canonical-json/sha256 treated as oracle boundaries unless explicitly released.

### Constraints/locks this stream must obey

- Formal lane is additive and non-authoritative for runtime behavior.
- `SEMANTICS_v3` remains runtime authority.
- Canonical-json + sha256 remain oracle-bounded in Lean unless a dedicated lock releases this.
- Proof outputs must map to existing evidence contracts when possible.

### Thin-slice arc proposals (`vNext+27+` placeholders)

- `vNext+27C` Lean ODEU skeleton stabilization:
  - compile-clean `AdeuCore.ODEU.*` module structure
  - prove easy structural invariants first
  - no runtime integration changes
- `vNext+28C` Fixture-backed Lean agreement checks:
  - deterministic Python canonicalization/codegen -> Lean typed constants
  - prove contract agreement for fixture samples
- `vNext+29C` Proof evidence bridge:
  - export Lean-backed checks through existing `proof_evidence@1` flows
  - do not create new enforcement semantics

### Stop-gate impact

- `vNext+27C`: none.
- `vNext+28C`: none unless adding fixture coverage to existing proof metrics.
- `vNext+29C`: additive only if introducing a new evidence family; prefer reusing existing `proof_evidence@1` to avoid metric churn.

## 3) Interleaving Roadmaps (Single-Arc Locks)

## Sequence S-A (Tooling-first, then Product, then Formal)

1. `vNext+27`: `27A` Tooling determinism hardening.
2. `vNext+28`: `27B` Evidence Explorer read-only UX.
3. `vNext+29`: `27C` Lean skeleton stabilization.
4. `vNext+30`: `28A` stop-gate modularization.
5. `vNext+31`: `28B` artifact evidence panel.
6. `vNext+32`: `28C` Lean fixture agreement.

Risk profile:
- Lowest lock-drift risk.
- Defers user-visible UX by one arc.

## Sequence S-B (Product-first, with tooling guardrail in same wave)

1. `vNext+27`: `27B` Evidence Explorer read-only UX.
2. `vNext+28`: `27A` Tooling determinism hardening.
3. `vNext+29`: `28B` artifact evidence panel.
4. `vNext+30`: `28A` stop-gate modularization.
5. `vNext+31`: `27C` Lean skeleton.
6. `vNext+32`: `28C` Lean fixture agreement.

Risk profile:
- Fastest user-visible value.
- Higher risk of accumulating tooling debt while UI surface expands.

## Sequence S-C (Formal-first, platform proof scaffold first)

1. `vNext+27`: `27C` Lean skeleton.
2. `vNext+28`: `27A` Tooling determinism hardening.
3. `vNext+29`: `27B` Evidence Explorer.
4. `vNext+30`: `28C` Lean fixture agreement.
5. `vNext+31`: `28A` modularization.
6. `vNext+32`: `28B` evidence panel.

Risk profile:
- Strong formal foundation early.
- Slower product feedback and no immediate UX leverage.

## Recommended sequence

Use **Sequence S-A**.

Reasoning:
- It resolves known deterministic drift/mismatch risks first (`v26` allowlist, env enforcement, missing S9 script).
- It preserves stop-gate continuity while enabling product read-only UX next.
- It keeps formal lane additive and independent, then integrates with lower risk.

## 4) Cross-stream Shared Primitives (Must be explicit)

1. Shared deterministic created-at stripping primitive.
- Single reusable helper path for recursive `created_at` exclusion behavior.
- No ad hoc field stripping in feature code.

2. Canonical-json conformance suite across API/runtime/kernel.
- Conformance tests are the oracle integrity fence across duplicated implementations.
- Required before broader formal+product scaling.

3. Central stop-gate manifest registry.
- One source of truth for active manifest versions used by scripts/tests/tooling.
- Eliminates drift from duplicated version tuples/constants.

4. Product explorer evidence boundary.
- Explorer browses existing fixture/declared evidence only.
- No undeclared discovery, no provider-driven evidence invention.

5. Formal lane oracle boundary declaration.
- Lean hard-proves structural invariants.
- sha256/canonical-json equivalence remains evidence-only unless separately released.

## 5) Immediate Small-Green PR Slicing (first 1–2 arcs)

## Arc `vNext+27A` (recommended first): Tooling determinism hardening

PR1
- Add deterministic tooling env helper and wire it into:
  - `apps/api/scripts/build_stop_gate_metrics.py`
  - `apps/api/scripts/build_quality_dashboard.py`

PR2
- Implement lock-conformant v26 parity path allowlist normalization in:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
- Add regression tests proving non-allowlisted fields are not normalized.

PR3
- Add canonical-json conformance tests across API/runtime/kernel helper implementations.

PR4
- Add missing deterministic S9 precondition script:
  - `apps/api/scripts/check_s9_triggers.py`
- Add tests covering missing metric / below-threshold fail-closed behavior.

Stop-gate impact:
- No new keys.
- Existing v26 parity/determinism metrics must remain unchanged.

## Arc `vNext+27B` (recommended second): Read-only Evidence Explorer

PR1
- Add deterministic evidence catalog/list endpoints for existing families.

PR2
- Add web Evidence Explorer pages (read-only packet/projection browsing).

PR3
- Add trust-lane and non-enforcement visual boundaries.

PR4
- Add deterministic ordering/no-provider-call/no-mutation tests for new read surfaces.

Stop-gate impact:
- None (UI/read-only scope).

## Notes for first lock drafting pass

- Keep each continuation doc single-version and step-block style.
- Preserve explicit out-of-scope sections to avoid lock bleed.
- Introduce new stop-gate metric keys only if a genuinely new evidence family is added.
