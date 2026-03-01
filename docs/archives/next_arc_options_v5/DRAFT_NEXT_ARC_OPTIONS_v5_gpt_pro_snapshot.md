# DRAFT Next Arc Options v5 (Post vNext+30)

Inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS28.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS29.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS30.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS28.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`
- consolidated territory notes (archived):
  - `docs/archives/consolidated_territory_cycle_v4/reviewv2.md`
  - `docs/archives/consolidated_territory_cycle_v4/lean.md`
  - `docs/archives/consolidated_territory_cycle_v4/next arc.md`

This is a planning document only.
It is **not** a lock doc and does **not** authorize runtime behavior changes.

---

## Baseline Agreement (Current Ground Truth)

### Lock chain status

- Locked continuation baseline is now **vNext+30** (formal ODEU lane activation).
- Prior completed arcs are locked (vNext+27 through vNext+30).

### Stop-gate baseline

- Stop-gate schema family remains: `stop_gate_metrics@1`.
- Latest committed closeout artifacts in this repo snapshot:
  - ✅ `artifacts/stop_gate/metrics_v28_closeout.json` (metric key count: **79**)
  - ✅ `artifacts/quality_dashboard_v28_closeout.json`
  - ✅ `artifacts/stop_gate/report_v28_closeout.md`
- **Drift / missing evidence warning:** this repo snapshot includes draft closeout decision docs for v29/v30 that reference artifacts that are **not present** under `artifacts/`.
  - This is treated as an actionable precondition for any post-v30 freeze candidate (see Path T2).

### Evidence surfaces now present

- **Evidence Explorer (vNext+29):**
  - API catalog endpoints:
    - `GET /urm/evidence-explorer/catalog`
    - `GET /urm/evidence-explorer/catalog/{family}`
  - Web UI route:
    - `apps/web/src/app/evidence-explorer/page.tsx`

- **Formal ODEU lane (vNext+30):**
  - Deterministic Lean workspace runner.
  - Agreement harness that produces deterministic report artifacts.
  - Frozen obligation set:
    - `pred_closed_world`
    - `exception_gating`
    - `conflict_soundness`

---

## Repo Truth Snapshot (Implementation Inventory)

### Implemented (directly usable)

- Deterministic tooling env enforcement:
  - `packages/urm_runtime/src/urm_runtime/deterministic_env.py`
  - enforced by:
    - `apps/api/scripts/build_stop_gate_metrics.py`
    - `apps/api/scripts/build_quality_dashboard.py`

- v26 parity-path normalization allowlist behavior:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` now gates normalization to:
    - `{baseline_path,candidate_path,report_path,manifest_path}`

- S9 trigger checker script:
  - `apps/api/scripts/check_s9_triggers.py`

- Canonical JSON conformance tests:
  - `apps/api/tests/test_canonical_json_conformance_vnext_plus27.py`

- Stop-gate registry + inactive-flag fail-closed:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_registry.py`

- v26 tooling transfer report builder + script:
  - `packages/urm_runtime/src/urm_runtime/tooling_transfer_report_vnext_plus26.py`
  - `apps/api/scripts/build_tooling_transfer_report_vnext_plus26.py`

- Evidence Explorer API endpoints + API test coverage:
  - `apps/api/src/adeu_api/main.py`
  - `apps/api/tests/test_evidence_explorer_*`

- Formal lane agreement harness:
  - `packages/adeu_lean/src/adeu_lean/agreement.py`
  - `packages/adeu_lean/src/adeu_lean/runner.py`

### Implemented but needs alignment / polish

- Evidence Explorer web UI **contract mismatch** (API vs web validation):
  - API `catalog` response returns `families[].list_ref.path = "/urm/evidence-explorer/catalog/{family}"` (template form).
  - Web UI validator currently expects `"/urm/evidence-explorer/catalog/${family}"` (expanded form).
  - This likely makes the web route fail closed on “payload invalid”.
  - Fix strategy is locked in Path T1.

- ODEU Lean prep modules exist but are not yet “activated” into the formal lane:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`
  - These files are presently documentary/prep; they are not tied to any persisted proof packet pipeline.

---

## Consolidated Post-v30 Path Families

The intent is to keep v31+ continuation work **thin-slice** and **lock-respecting**.

### T1) Evidence Explorer Contract Closure (C5)

**Lock class:** `L1` (lock-alignment correction; no runtime behavior change; fix payload contract mismatch)

**Goal**

Make the v29 Evidence Explorer UI usable end-to-end by aligning the web validator with the frozen API contract.

**Scope**

- Update `apps/web/src/app/evidence-explorer/page.tsx` runtime guards:
  - accept the template form `"/urm/evidence-explorer/catalog/{family}"` for `families[].list_ref.path`, OR
  - relax the check to “string + matches expected prefix”, while preserving safety.
- Add a minimal front-end unit test (or TypeScript test) that validates a golden catalog response fixture.
- Optional: add a small docs note clarifying whether `list_ref.path` is a URI template vs concrete link.

**Locks**

- Do not change the API payload shape already locked by `apps/api/tests/test_evidence_explorer_c1_endpoints.py`.
- No new evidence families.
- No new persistence authority.

**Acceptance**

- Evidence Explorer page loads and displays:
  - families list
  - entry list for a selected family
- The page remains deterministic in ordering and fail-closed behavior.

**Stop-gate impact**

- none (no new metric keys).

---

### T2) Closeout Artifact Completeness + Reference Lint (Z5)

**Lock class:** `L0` (behavior-preserving operational completeness + deterministic tooling evidence)

**Goal**

Restore the “docs reference → artifact exists” invariant for v29 and v30 closeout material.

**Observed gap in this repo snapshot**

- The following files are referenced in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md` and `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`, but are not present:
  - `artifacts/quality_dashboard_v29_closeout.json`
  - `artifacts/stop_gate/metrics_v29_closeout.json`
  - `artifacts/stop_gate/report_v29_closeout.md`
  - `artifacts/quality_dashboard_v30_closeout.json`
  - `artifacts/stop_gate/metrics_v30_closeout.json`
  - `artifacts/stop_gate/report_v30_closeout.md`

**Scope**

- Generate missing closeout artifacts deterministically (using the commands already embedded in the decision docs).
- Commit the generated artifacts.
- Add a fail-closed “reference lint” test:
  - scans `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS*.md` and asserts referenced `artifacts/...` files exist.
  - (Optional) also asserts referenced metric keysets remain frozen when the doc claims “no new keys”.

**Locks**

- No new stop-gate metric keys.
- Stop-gate schema family remains `stop_gate_metrics@1`.

**Acceptance**

- v29 and v30 decision docs become reproducible from committed artifacts.
- Reference lint test fails closed on future missing-artifact regressions.

**Stop-gate impact**

- none (this is a completeness + guard rail arc).

---

### T3) Formal ODEU Template v0.2 Activation (Core IR Contract Proof Packet)

**Lock class:** `L0` (evidence-only expansion inside formal lane; no enforcement)

**Goal**

Connect the existing ODEU Lean prep files to a deterministic “proof packet” artifact pipeline that proves (or checks) the **Core IR contract** for a frozen corpus of fixtures.

**Scope (thin-slice)**

- Fix/minimize Lean prep module issues so they compile under CI Lean toolchain:
  - (example) remove accidental field projections in `AdeuODEU/Invariants.lean` (`n.id` → `nodeId n`).
- Add a Python codegen bridge (new module) to render canonical Core IR fixtures as Lean constants.
- Generate an evidence-only proof packet artifact for at least one frozen fixture:
  - `checkContract(core_ir) = true` proved/validated under Lean.
- Keep output stored as deterministic artifact JSON (no new runtime enforcement).

**Locks**

- No change to runtime validators (`adeu_core_ir` / `urm_runtime` contract checks remain the enforcement authority).
- No stop-gate metric additions.
- Proof outputs are evidence-only.

**Acceptance**

- Deterministic generation of Lean source from canonical JSON fixtures.
- Deterministic proof packet artifact identity/hashes.
- CI lane executes with real Lean toolchain for the proof packet.

**Stop-gate impact**

- none (evidence-only).

---

### T4) Repo-root Consolidation + “No .git” Friendliness

**Lock class:** `L0`

**Goal**

Reduce repeated `.git`-based repo root scans and make scripts/tests friendlier to zip/monorepo export contexts.

**Scope**

- Consolidate repo-root resolution into one helper (prefer existing `adeu_ir.repo_root`).
- Replace local `.git` scans in:
  - `apps/api/scripts/check_s9_triggers.py`
  - `apps/api/tests/path_helpers.py`
  - `apps/api/tests/test_check_s9_triggers.py`
  - `apps/api/tests/test_canonical_json_conformance_vnext_plus27.py`
  - `urm_runtime.stop_gate_registry.discover_repo_root`

**Locks**

- Output behavior must remain deterministic.
- Any env override (`ADEU_REPO_ROOT`) must remain fail-closed if inconsistent.

**Acceptance**

- The same scripts/tests work when `.git` is absent but repo markers are present (`pyproject.toml`, `packages/`).

---

### T5) `/urm/worker/run` Governance Alignment

**Lock class:** `L2` (boundary release)

**Goal**

Align `/urm/worker/run` with the capability-policy gate (`authorize_action`) and make execution authority explicit.

**Scope**

- Wire `/urm/worker/run` through `authorize_action`.
- Add explicit “role → capability” checks for worker execution.
- Add audit events and deterministic denial details.

**Locks**

- Requires explicit lock text authorizing this boundary release.

**Acceptance**

- Unauthorized calls fail closed deterministically.
- Authorized calls preserve current worker-run behavior.

---

## Decision Matrix (vNext+31 Candidate Menu)

| Candidate | Path(s) | Lock class | Primary benefit | Key risk | Dependency notes |
|---|---|---:|---|---|---|
| **v31-A** | T1 only | L1 | Evidence Explorer becomes usable | low | purely UI contract alignment |
| **v31-B** | T2 only | L0 | Closeout chain becomes reproducible | low/med | requires running tooling deterministically |
| **v31-C** | T1 + T2 | L0/L1 | “Evidence Explorer works” + “closeout chain complete” | med | still thin-slice but touches both web + artifacts |
| **v31-D** | T3 only | L0 | Formal ODEU artifact proof pipeline begins | med/high | requires Lean CI + codegen + new artifact envelope |
| **v31-E** | T4 only | L0 | reduces repo-root drift + zip friendliness | low | mostly refactor + tests |
| **v31-F** | T5 only | L2 | closes a governance gap | high | boundary release requires new lock discipline |

---

## Recommended Order (if keeping thin-slice discipline)

1. **vNext+31 = v31-A (T1)**
   - minimal and makes the v29 “Evidence Explorer activation” actually consumable.
2. **vNext+32 = v31-B (T2)**
   - restore closeout artifact completeness and prevent future drift.
3. **vNext+33 = v31-D (T3)**
   - deepen formal lane into actual artifact contract proof packets.
4. **vNext+34+ = evaluate T4 and T5**
   - T4 is cheap hygiene; T5 is a governance boundary release.

If you want a single arc next: **v31-C (T1 + T2)** is the most “product-ready” combined slice.

---

## Proposed Freeze Candidate (Next Step)

Finalize `docs/LOCKED_CONTINUATION_vNEXT_PLUS31.md` for the selected post-v30 thin-slice continuation:

1. Freeze deterministic contract deltas for the selected v31 scope.
2. Preserve v14-v30 continuity locks unless an explicit release is approved.
3. Keep non-enforcement / no-mutation / no-provider-expansion boundaries explicit.
4. If selecting T2, include a lock clause that the referenced closeout artifact paths must exist and be committed.

