Here’s what I found in the **updated zip repo** (vs the 3 MDs you attached), what looks solid, what needs fixes/enhancements, what’s still missing, and a concrete “where to go next” draft.

I also wrote a **new next-arc options doc** in the repo with the same “planning/paths/matrix/freeze candidate” structure as `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`:

---

## 1) What’s already implemented (mapped to the 3 docs)

### A) From **reviewv2.md** (risk register + arc plan)

These are implemented in the repo snapshot:

* **R1 Canonical JSON conformance guard** ✅
  You now have `apps/api/tests/test_canonical_json_conformance_vnext_plus27.py`, which cross-checks canonical JSON output/hashes across multiple layers (API/runtime/kernel/explain/etc).

* **R2 v26 parity-path normalization allowlist fix** ✅
  `urm_runtime.stop_gate_tools._normalize_vnext_plus26_parity_paths` now gates normalization to an explicit allowlist (`baseline_path`, `candidate_path`, `report_path`, `manifest_path`) and avoids “normalize anything ending in `_path/_paths`”.

* **R3 deterministic tooling env enforcement** ✅
  `packages/urm_runtime/src/urm_runtime/deterministic_env.py` exists and is called by entrypoint scripts (e.g. stop-gate + quality dashboard builders).

* **R7 manifest registry duplication reduction** ✅
  `packages/urm_runtime/src/urm_runtime/stop_gate_registry.py` centralizes “active versions” + fail-closed inactive flag checks.

* **R12 Lean proof runner deterministic temp/workspace** ✅
  `packages/adeu_lean/src/adeu_lean/runner.py` now uses deterministic per-request workspace paths (hash-based directories), and normalizes output to avoid temp-path nondeterminism.

Partially addressed / still open from reviewv2:

* **R5 stop_gate_tools monolith** 🟡
  There *is* some modularization (e.g. `stop_gate_normalization.py`), but `stop_gate_tools.py` is still a massive hotspot. This is “started but not finished.”

* **R8 repo-root helper duplication** 🟡
  Multiple places still have their own “find `.git` in parents” logic (scripts/tests/runtime). Some newer code uses `Path(__file__).parents[...]` instead. It’s better than before, but not unified.

* **R4 `/urm/worker/run` governance divergence** ❌ (still present)
  `apps/api/src/adeu_api/urm_routes.py` shows `worker/run` still doesn’t route through `authorize_action`. If you still consider that L2, it remains a major deferred boundary issue.

* **R10 codex CLI strictness / ask-for-approval flag risk** ❌/🟡
  The worker runner probes for flag support and conditionally includes flags, but it does **not** fail closed if `--ask-for-approval` isn’t supported (still potential “interactive hang” class risk, depending on codex behavior).

* **R11 proposer idempotency cache** ❌
  The process-global `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` dict is still in `apps/api/src/adeu_api/main.py`.

---

### B) From **next arcv2.md** (roadmap: Evidence Explorer + transfer report + missing scripts)

These are implemented in the repo snapshot:

* **Missing script: `check_s9_triggers.py`** ✅
  Present at `apps/api/scripts/check_s9_triggers.py`.

* **v26 Tooling Transfer Report regeneration builder** ✅
  Present as:

  * `packages/urm_runtime/src/urm_runtime/tooling_transfer_report_vnext_plus26.py`
  * `apps/api/scripts/build_tooling_transfer_report_vnext_plus26.py`

* **Evidence Explorer (API + UI)** ✅ (but see one concrete contract mismatch below)
  Implemented:

  * API endpoints in `apps/api/src/adeu_api/main.py`

    * `GET /urm/evidence-explorer/catalog`
    * `GET /urm/evidence-explorer/catalog/{family}`
  * Web UI page in `apps/web/src/app/evidence-explorer/page.tsx`
  * API tests `apps/api/tests/test_evidence_explorer_*`

* **Later arcs beyond what next arcv2 anticipated** ✅
  The repo has `LOCKED_CONTINUATION_vNEXT_PLUS27..30.md` and related stop-gate draft decision docs; so you’ve gone past the “no v27” situation described in the older roadmap.

---

### C) From **leanv2.md** (ODEU formal template v0.2 plan)

What is already implemented:

* **Lean prep modules exist** ✅

  * `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  * `packages/adeu_lean/AdeuODEU/Invariants.lean`

What’s partially implemented vs leanv2’s intended structure:

* leanv2 proposed placing these under `AdeuCore/ODEU/*` so `lakefile.lean` globs pick them up automatically.
  In this repo snapshot, they live under **`AdeuODEU/*`**, not `AdeuCore/ODEU/*`. That’s not “wrong”, but it diverges from the plan and may affect build/import expectations.

* Invariants are encoded as *Boolean checks* (`checkContract`) which is consistent with an early-stage template, but…

What’s missing vs leanv2:

* **No Python JSON→Lean codegen bridge** ❌
  leanv2 proposed something like `packages/adeu_lean/src/adeu_lean/odeu_codegen.py` + fixture tests. That doesn’t exist in the snapshot.

* **No end-to-end “proof packet” pipeline** ❌
  The v30 formal lane is implemented (agreement harness + deterministic runner) but it’s proving the *existing frozen AdeuCore theorem set*, not proving “Core IR artifact contract checkContract = true” from real artifact inputs.

* **No theorems proving soundness/completeness** ❌
  The Lean files look like prep/stubs; they’re not connected to a formal proof workflow.

---

## 2) What needs fixes / enhancements (repo-level findings)

### 2.1 Evidence Explorer UI vs API contract mismatch (very likely a real bug)

* API (locked by API tests) returns:

  * `families[].list_ref.path = "/urm/evidence-explorer/catalog/{family}"` (template string)
* Web UI validator (`apps/web/src/app/evidence-explorer/page.tsx`) currently expects:

  * `"/urm/evidence-explorer/catalog/${family}"` (expanded string)

That means the UI will likely reject the API payload as invalid and fail closed.

**Suggested fix direction (matches the “lock discipline”):**

* Keep API as-is (since tests freeze it).
* Relax/adjust the **web validator** to accept the templated path (or accept both forms).

This is the #1 “obvious correctness” fix I’d do next because it blocks v29’s new UX.

---

### 2.2 Closeout chain mismatch: v29/v30 decision docs reference missing artifacts

In this snapshot:

* `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md` references:

  * `artifacts/quality_dashboard_v29_closeout.json`
  * `artifacts/stop_gate/metrics_v29_closeout.json`
  * `artifacts/stop_gate/report_v29_closeout.md`
* `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md` references:

  * `artifacts/quality_dashboard_v30_closeout.json`
  * `artifacts/stop_gate/metrics_v30_closeout.json`
  * `artifacts/stop_gate/report_v30_closeout.md`

…but none of those files exist in `artifacts/`.

So the “closeout paper trail” is currently non-reproducible from the repo snapshot.

**Enhancement:** add a fail-closed lint test that ensures “docs references → artifact exists” for all `DRAFT_STOP_GATE_DECISION` docs, so this can’t regress.

---

### 2.3 Lean ODEU prep files look non-activated / potentially non-compiling

I didn’t run Lean here (toolchain not present), but I can already see at least one likely compile issue:

* In `AdeuODEU/Invariants.lean`, `findNode?` uses `n.id` even though `CoreNode` is an inductive and doesn’t have `.id` as a field projection (you defined `nodeId : CoreNode → String`).

So even if the files are “prep only”, they’ll need basic correctness before you can activate them as formal checks.

Also: if the intent is to compile/build them as part of the library, consider:

* moving them under `AdeuCore/ODEU/*` (as leanv2 suggested), or
* updating `lakefile.lean` to include `AdeuODEU` in `globs`.

---

### 2.4 Repo-root discovery is inconsistent and still `.git`-dependent in many places

Because this zip snapshot has no `.git/`, anything doing “walk parents until `.git` exists” will fail if executed inside this snapshot as-is.

This is probably fine in CI (where it’s a real git checkout), but it makes:

* running scripts from “exported source bundles” fragile
* local tooling less portable

You already have `packages/adeu_ir/src/adeu_ir/repo.py:repo_root()` which supports an env override (`ADEU_REPO_ROOT`) and checks additional markers. Consolidating onto that would reduce drift.

---

## 3) What we still need to add (relative to the docs’ intent)

If you want to complete the **leanv2 ODEU formal template v0.2** vision, the main missing chunk is:

* **ODEU codegen bridge**: canonical JSON artifact → Lean constant(s)
* **Fixture-backed formal checks**: prove/validate `checkContract` for core IR fixtures
* **Evidence-only proof packet artifact envelope**: store results deterministically without changing runtime enforcement
* **Thin-slice theorem activation**: start with core IR contract only; don’t boil the ocean

If you want to complete the “reviewv2 risk register closure”, the big remaining “high risk” items are:

* `/urm/worker/run` governance alignment (L2)
* codex CLI strictness fail-closed policy (if still desired)
* main.py monolith reduction (optional / hygiene)

---

## 4) Where to go next

I generated a new planning doc with the same kind of structure as `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`, but updated for the repo’s actual current state **post vNext+30** and the concrete issues I found (Evidence Explorer contract mismatch + missing closeout artifacts + formal ODEU activation path).

[Download `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`](sandbox:/mnt/data/repo/adeu-studio-main/docs/DRAFT_NEXT_ARC_OPTIONS_v5.md)

High-level, this v5 doc proposes these post-v30 path families:

* **T1 (v31-A): Evidence Explorer Contract Closure (C5)**
  Fix the API/web mismatch without changing the locked API shape.
* **T2 (v31-B): Closeout Artifact Completeness + Reference Lint (Z5)**
  Generate/commit missing v29/v30 closeout artifacts + add a guard test.
* **T3 (v31-D): Formal ODEU Template v0.2 Activation**
  Start connecting real artifacts to Lean via codegen and produce evidence-only proof packets.
* **T4:** Repo-root consolidation and “no .git friendliness”
* **T5:** `/urm/worker/run` governance alignment (explicitly marked L2)

It also includes a decision matrix and recommended sequencing.

---

## 5) Extra “standard repo” notes you may want to action

* Add a **single “closeout consistency” guard** that checks:

  * decision docs reference existing artifacts
  * artifact schemas match declared schema ids
  * metric keysets are equal when docs claim “no new keys”
* Add a **tiny front-end contract fixture** for the Evidence Explorer catalog payload so the UI can be validated deterministically without needing the backend running.
* Consider a “formal lane activation checklist” for any new theorem family:

  * deterministic source generation
  * deterministic request id → workspace mapping
  * deterministic mapping_id derivation
  * no-provider/no-network guard

---
