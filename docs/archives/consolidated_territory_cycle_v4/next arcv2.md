## 1) State of the Repo summary (grounded)

### What’s in the repo (major subsystems)

**A. `apps/api` (FastAPI “ADEU Studio API”)**

* Hosts:

  * **Product APIs** for ADEU artifacts, concepts, explain/diff, semantic depth, puzzles, docs, proofs.
  * **URM evidence APIs** under `/urm/*` (mix of fixture-backed read surfaces + a few active write/materialize endpoints).
* Storage:

  * SQLite-backed persistence via `apps/api/src/adeu_api/storage.py` (tables for `artifacts`, `concept_artifacts`, `documents`, `proofs`, `explain`, `semantic_depth`; **no core-ir derived table** at present).

**B. `apps/web` (Next.js “ADEU Studio UI”)**

* Exists and ships a meaningful product surface:

  * `src/app/` includes pages for `artifacts`, `concepts`, `puzzles`, `papers`, `explain`, `copilot`.
* Current UI **does not expose URM vNext evidence packets** (grep shows only `/urm/copilot/*` and `/urm/policy/active` usage).

**C. `packages/*` (typed domain + runtime libraries)**

* Key packages:

  * `packages/urm_runtime`: stop-gate tooling, evidence/event helpers, policy/roles/capabilities, transfer-report builders for some arcs.
  * `packages/adeu_core_ir`, `packages/adeu_concepts`, `packages/adeu_kernel`, `packages/adeu_explain`, etc.
  * `packages/adeu_lean`: Lean backend integration exists (runner + Lean sources) and is used via `adeu_kernel`.

**D. `docs/` + `artifacts/` (governance + evidence)**

* Multiple locked continuation docs exist through **vNext+26**, and **closeout artifacts exist through v26**.
* `artifacts/stop_gate/` contains `metrics_v24_closeout.json`, `metrics_v25_closeout.json`, `metrics_v26_closeout.json` and matching reports.
* `artifacts/quality_dashboards/` contains closeout dashboards for v24–v26.

---

### The current frontier (latest lock + stop-gate evidence present)

**Latest continuation doc present:**

* `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` (marked “Draft Lock (not frozen yet)”) with supporting:

  * `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
  * `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
  * closeout evidence in `artifacts/stop_gate/report_v26_closeout.md` + `metrics_v26_closeout.json`

**Meaningfully “done” by repo truth (code + closeout artifacts):**

* v24–v26 are not just drafted: the repo contains closeout dashboards + stop-gate metrics/reports, and fixtures/manifests up through **`apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`**.
* There is **no** `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md` and **no** `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`.

✅ **Therefore the next vNext index inferred from repo state is `vNext+27`.**
(If you intended a different “next index,” I don’t see evidence of it in the zip.)

---

### Implemented vs only drafted (use file presence as truth)

**Implemented (code + fixtures + stop-gate evidence present)**

* **URM evidence surfaces v19–v24**:

  * v19 Read-surface payload builder exists: `apps/api/src/adeu_api/read_surface_payload_vnext_plus19.py`
  * v20 Cross-IR coherence exists: `apps/api/src/adeu_api/cross_ir_coherence_vnext_plus20.py`
  * v21 Normative advice exists: `apps/api/src/adeu_api/normative_advice_vnext_plus21.py`
  * v22 Trust invariant exists: `apps/api/src/adeu_api/trust_invariant_vnext_plus22.py`
  * v23 Candidate semantics v4 exists: `apps/api/src/adeu_api/semantics_v4_candidate_vnext_plus23.py`
  * v24 Extraction fidelity exists: `apps/api/src/adeu_api/extraction_fidelity_vnext_plus24.py`
  * All have fixture payloads under `apps/api/fixtures/stop_gate/vnext_plus19 … vnext_plus24/`
* **v25 Core-IR proposer activation is implemented**

  * Endpoint exists: `POST /urm/core-ir/propose` in `apps/api/src/adeu_api/main.py`
  * Transfer report exists: `docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md`
  * Closeout exists: `artifacts/stop_gate/report_v25_closeout.md` + `metrics_v25_closeout.json`
  * Fixtures exist: `apps/api/fixtures/stop_gate/vnext_plus25/*` + `vnext_plus25_manifest.json`
* **v26 Tooling consolidation / parity fixtures are implemented**

  * v26 manifest exists: `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`
  * Tooling parity fixtures exist: `apps/api/fixtures/stop_gate/vnext_plus26/*`
  * Closeout exists: `artifacts/stop_gate/report_v26_closeout.md` + `metrics_v26_closeout.json`
  * Tooling transfer report doc exists: `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`

**Drafted / partially missing (repo truth)**

* **No vNext+27 lock doc / fixtures / stop-gate artifacts exist yet.**
* Some “tooling/ops” items appear **promised by docs but not present as code artifacts**:

  * `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` references `apps/api/scripts/check_s9_triggers.py`, but that file is **not present** in `apps/api/scripts/`.
  * There is **no** obvious script/builder for the v26 tooling transfer report (contrast: there *is* code for v24 and v25 transfer-report builders in `packages/urm_runtime/src/urm_runtime/*_transfer_report_*.py`, but **no** `tooling_transfer_report_vnext_plus26.py`).

That mismatch matters because it’s exactly the kind of “determinism regime drift” you’ll want to close before expanding surface area.

---

### Active evidence surfaces (only listed because code + fixtures exist)

Below are the surfaces you explicitly asked about, with where they live:

**1) Read-surface (vNext+19)**

* Code:

  * `apps/api/src/adeu_api/read_surface_payload_vnext_plus19.py`
  * Read-surface endpoints in `apps/api/src/adeu_api/main.py`:

    * `GET /urm/core-ir/artifacts/{artifact_id}`
    * `GET /urm/core-ir/artifacts/{artifact_id}/lane-projection`
    * `GET /urm/core-ir/artifacts/{artifact_id}/lane-report`
    * `GET /urm/core-ir/artifacts/{artifact_id}/integrity/{family}`
* Fixtures / stop-gate:

  * `apps/api/fixtures/stop_gate/vnext_plus19/*`
  * `apps/api/fixtures/stop_gate/vnext_plus19_manifest.json`

**2) Cross-IR (vNext+20)**

* Code:

  * `apps/api/src/adeu_api/cross_ir_coherence_vnext_plus20.py`
  * `apps/api/src/adeu_api/cross_ir_bridge_vnext_plus20.py` (bridge manifest construction + pair catalog)
* Fixtures / stop-gate:

  * `apps/api/fixtures/stop_gate/vnext_plus20/*`
  * `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json` + referenced payloads

**3) Normative advice (vNext+21)**

* Code:

  * `apps/api/src/adeu_api/normative_advice_vnext_plus21.py`
* API:

  * `GET /urm/normative-advice/pairs/{source_text_hash}/{core_ir_artifact_id}/{concept_artifact_id}`
  * `GET /urm/normative-advice/projection`
* Fixtures:

  * `apps/api/fixtures/stop_gate/vnext_plus21/*`

**4) Trust-invariant (vNext+22)**

* Code:

  * `apps/api/src/adeu_api/trust_invariant_vnext_plus22.py`
* API uses “proof-trust” naming:

  * `GET /urm/proof-trust/pairs/{source_text_hash}/{core_ir_artifact_id}/{concept_artifact_id}`
  * `GET /urm/proof-trust/projection`
* Fixtures:

  * `apps/api/fixtures/stop_gate/vnext_plus22/*`

**5) Candidate semantics (vNext+23)**

* Code:

  * `apps/api/src/adeu_api/semantics_v4_candidate_vnext_plus23.py`
* API:

  * `GET /urm/semantics-v4/pairs/{source_text_hash}/{core_ir_artifact_id}/{concept_artifact_id}`
  * `GET /urm/semantics-v4/projection`
* Fixtures:

  * `apps/api/fixtures/stop_gate/vnext_plus23/*`

**6) Extraction fidelity (vNext+24)**

* Code:

  * `apps/api/src/adeu_api/extraction_fidelity_vnext_plus24.py`
* API:

  * `GET /urm/extraction-fidelity/sources/{source_text_hash}`
  * `GET /urm/extraction-fidelity/projection`
* Fixtures:

  * `apps/api/fixtures/stop_gate/vnext_plus24/*`

---

### “Active” vs “fixture-backed only” surfaces today

**Active surfaces (runtime computes from user input and/or DB)**

* **ADEU Studio product** (DB-backed):

  * artifact creation and listing (`/artifacts/*`)
  * concept creation/edit/apply-patch (`/concepts/*`)
  * documents/papers (`/papers/*`)
  * proofs stored (`proofs` table)
* **Safe write workflows already exist (DB-backed derived artifacts)**

  * `POST /urm/explain/materialize`
  * `POST /urm/semantic_depth/materialize`
* **Provider-involved active surface**

  * `POST /urm/core-ir/propose` (vNext+25; idempotent but uses an in-process idempotency cache dict today)

**Fixture-backed only (read-only; deterministic payloads from fixture catalogs)**

* v19 read-surface endpoints (core-ir artifact / lane / integrity)
* v21 normative advice packet + projection
* v22 proof-trust packet + projection
* v23 semantics-v4 packet + projection
* v24 extraction-fidelity sources + projection
  …and the v20 cross-ir coherence logic is present, but it’s *not* exposed as a first-class `/urm/cross-ir/*` route; it is consumed inside the higher packets.

---

### Frozen hashing/serialization profile and where it lives

The repo has explicit canonical JSON + sha256 helpers in multiple places; the key “frozen” profile for deterministic artifacts is:

* **`apps/api/src/adeu_api/hashing.py`**

  * `canonical_json(...)` uses `sort_keys=True`, `separators=(",", ":")`, `ensure_ascii=False`
  * `sha256_canonical_json(...)`, `sha256_text(...)`
  * `strip_created_at_recursive(...)` used to remove timestamps before hashing
* **`packages/urm_runtime/src/urm_runtime/hashing.py`**

  * same canonicalization profile (runtime-side)

This is the “do not move” foundation under your non-negotiable canonical JSON/hashing lock.

---

### Constraint box (what is frozen unless explicitly released)

Non-negotiables you stated, plus what the repo reinforces:

* **Default runtime semantics remains `docs/SEMANTICS_v3.md`** (no default switch).
* **Candidate/advisory lanes are non-enforcing by default**:

  * Normative advice / candidate semantics are evidence, not gates.
* **Canonical JSON/hashing profile is frozen** (see hashing helpers above).
* **Stop-gate metric immutability**:

  * stop-gate schema is `stop_gate_metrics@1` and existing metric names/meaning must not change (additive-only new metrics).
* **Provider parity constraints** remain binding:

  * provider matrices + parity fixtures exist; new provider expansion requires explicit lock release.
* **Trust lanes remain explicit and separate** (mapping/solver/proof trust separation is a core governance primitive).
* **Deterministic replay acceptance remains mandatory** for anything added to the stop-gate lane.

---

## 2) Three Roadmap Sequences (12–18 months)

Each sequence below is a **consistent vNext+27 → vNext+36** plan, but with a different philosophy. All arcs are designed to be **additive-first**, preserve deterministic replay evidence, and avoid any default semantic change.

### Sequence 1 — Product-forward (make evidence usable in the product, then add safe writes)

**Philosophy:** Turn today’s fixture-backed evidence into a navigable product surface first, then progressively introduce **safe, non-enforcing write workflows** that store *derived* evidence (not mutations), and only later enable curated “apply” actions.

---

#### vNext+27 — URM Evidence Explorer (read-only UI + catalog listing endpoints)

* **Goal (1 sentence):** Ship a web UI to browse existing URM evidence packets (v19–v24) without introducing any enforcement or new providers.
* **Touches (packages/files):**

  * `apps/web/src/app/*` (new page(s), shared components)
  * `apps/api/src/adeu_api/main.py` (add catalog/list routes)
  * `apps/api/src/adeu_api/read_surface_payload_vnext_plus19.py` (reuse list helper)
  * `apps/api/src/adeu_api/cross_ir_bridge_vnext_plus20.py` (reuse `list_cross_ir_catalog_pairs_vnext_plus20`)
* **Explicit lock constraints:**

  * No DB writes; no new tables.
  * No provider calls; no change to provider matrix.
  * No new stop-gate metrics (UI-only) unless you decide to stop-gate the catalog endpoints explicitly.
  * Preserve canonical hashing helpers unchanged.
* **Acceptance criteria:**

  * Web can list and deep-link all fixture-backed surfaces:

    * read-surface artifact ids (v19)
    * cross-ir pair tuples (v20 catalog)
    * normative advice / proof-trust / semantics-v4 / extraction-fidelity fixtures
  * UI displays **trust lane labels** + a “non-enforcing” disclaimer on candidate/advice pages.
  * API list endpoints are deterministic and sorted.
* **Stop-gate impact:**

  * **None required** (unless you opt to add stop-gate coverage for the new list endpoints; if so, reuse existing fixture catalogs with no new metrics keys).

---

#### vNext+28 — Artifact “Evidence Panel” (surface existing DB-backed derived artifacts)

* **Goal:** Make existing safe-write derived artifacts (explain + semantic depth) first-class on artifact detail pages.
* **Touches:**

  * `apps/web/src/app/artifacts/[artifact_id]/page.tsx`
  * `apps/web/src/app/explain/page.tsx` (reuse components)
  * `apps/api/src/adeu_api/main.py` (no API change required; just consume existing endpoints)
* **Explicit lock constraints:**

  * No new enforcement; no provider changes.
  * Writes limited to existing endpoints `/urm/explain/materialize` and `/urm/semantic_depth/materialize`.
* **Acceptance:**

  * On artifact page: “Generate explain” and “Generate semantic depth” create/read stored records.
  * Display hashes + request IDs + “created_at excluded from hash” note (matching regime).
* **Stop-gate impact:**

  * None (product surface only).

---

#### vNext+29 — Deterministic Core-IR Preview for stored artifacts (read-only, no persistence)

* **Goal:** Add a deterministic **preview-only** Core-IR build from stored `clause_text`, without persisting new tables.
* **Touches:**

  * `apps/api/src/adeu_api/main.py` (new endpoint: e.g. `GET /artifacts/{id}/core-ir/preview`)
  * `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py` (reuse `build_core_ir_from_source_text`)
  * `apps/web` (artifact page adds “Preview Core-IR” viewer)
* **Explicit lock constraints:**

  * No provider calls; this must be pure deterministic pipeline.
  * No DB writes; preview is computed and returned.
  * Canonical JSON/hashing unchanged; preview response includes `preview_hash`.
* **Acceptance:**

  * Preview output is stable given same stored text.
  * Preview includes lane/integrity references **only if** they can be derived deterministically; otherwise explicitly marks “not produced reasons.”
* **Stop-gate impact:**

  * Optional but recommended: add a **single** stop-gate fixture + metric such as

    * `artifact_core_ir_preview_determinism_pct`
  * Keep replay count small (1–3) to protect CI budget.

---

#### vNext+30 — Core-IR Materialize (safe write, derived-only)

* **Goal:** Persist deterministic Core-IR derivations for an ADEU artifact as a **new derived artifact family** (safe write).
* **Touches:**

  * `apps/api/src/adeu_api/storage.py` (new table e.g. `core_ir_derivations`)
  * `apps/api/src/adeu_api/main.py` (new endpoint: `POST /urm/core-ir/materialize`)
  * `apps/web` (artifact page: “Materialize Core-IR”)
* **Explicit lock constraints:**

  * Must remain **non-enforcing**: storage is evidence only.
  * No provider involvement.
  * Idempotency must follow the existing pattern (`client_request_id` + semantic hash).
* **Acceptance:**

  * Materialize is idempotent and returns the same payload on replay.
  * Stored rows include: request payload hash, core-ir hash, and created_at excluded-from-hash rules.
* **Stop-gate impact:**

  * New manifest optional but likely: `vnext_plus30_manifest.json`
  * Minimal new metrics:

    * `artifact_core_ir_materialize_replay_determinism_pct`
    * `artifact_core_ir_materialize_idempotency_pct`

---

#### vNext+31 — Alignment Session v1 (bridge manifest + coherence for DB artifacts; non-enforcing)

* **Goal:** Enable “alignment sessions” between a materialized Core-IR derivation and a selected concept artifact, producing bridge + coherence evidence.
* **Touches:**

  * `apps/api/src/adeu_api/storage.py` (new `alignment_sessions` table)
  * `apps/api/src/adeu_api/cross_ir_bridge_vnext_plus20.py` (reuse bridging logic; add “from DB payloads” wrapper)
  * `apps/api/src/adeu_api/cross_ir_coherence_vnext_plus20.py`
  * `apps/web` (new page: Alignment Session viewer/creator)
* **Explicit lock constraints:**

  * If source-text hashes don’t match, session must record mismatch deterministically (no silent normalization changes).
  * Still non-enforcing; no automatic edits.
  * Trust lane taxonomy unchanged; session stores mapping/coherence as evidence.
* **Acceptance:**

  * Create session is idempotent; produces stable session hash.
  * Coherence diagnostics are deterministic; schema remains vNext+20.
* **Stop-gate impact:**

  * New minimal metrics only if stop-gated:

    * `artifact_alignment_session_replay_determinism_pct`
    * `artifact_alignment_session_coherence_valid_pct`

---

#### vNext+32 — Normative Advice Session + Review Queue (non-enforcing safe write)

* **Goal:** Generate and persist normative advice for an alignment session, then let users record review decisions (accept/reject) without enforcement.
* **Touches:**

  * `apps/api/src/adeu_api/normative_advice_vnext_plus21.py` (wrap/adapt for DB inputs)
  * `apps/api/src/adeu_api/storage.py` (tables: `advice_sessions`, `advice_reviews`)
  * `apps/web` (review UI)
* **Explicit lock constraints:**

  * “Advice” remains non-enforcing; review decisions do not auto-apply changes.
  * Preserve v21 advice semantics + ordering rules.
* **Acceptance:**

  * Advice session deterministically reproduced from session inputs.
  * Review records are append-only; each review has stable hash.
* **Stop-gate impact:**

  * Add only if necessary:

    * `artifact_advice_session_replay_determinism_pct`

---

#### vNext+33 — Safe Apply v0 (explicit user action; strict stale-hash guard)

* **Goal:** Add an opt-in “apply” workflow that produces a new concept artifact revision **only when** the user explicitly confirms and stale-hash checks pass.
* **Touches:**

  * `apps/api/src/adeu_api/main.py` concept artifact endpoints
  * `apps/api/src/adeu_api/storage.py` (store apply events / provenance links)
  * `apps/web` (apply UI)
* **Explicit lock constraints:**

  * No automatic apply; must be user-triggered.
  * Must enforce stale-hash / revision guards deterministically.
  * Still no default enforcement of advice.
* **Acceptance:**

  * Apply emits evidence linking: advice item → review decision → new concept artifact hash.
  * Apply failures are deterministic with stable error codes.
* **Stop-gate impact:**

  * Likely none initially (product workflow), unless you want deterministic apply fixtures.

---

#### vNext+34 — Evidence Bundle Export (DB → deterministic pack)

* **Goal:** Add a deterministic export format for sessions/reviews/apply events to support replay outside the DB.
* **Touches:**

  * `packages/urm_runtime` (new export helper in evidence tooling)
  * `apps/api/scripts/*` (export CLI)
  * `apps/api` endpoint optional: `GET /urm/evidence/export?...`
* **Explicit lock constraints:**

  * Export must use canonical JSON/hashing.
  * Export is read-only against DB; no mutation.
* **Acceptance:**

  * Exported bundle contains all refs + hashes to replay alignment/advice.
* **Stop-gate impact:**

  * Optional: a single determinism fixture for bundle export.

---

#### vNext+35 — Candidate Semantics UI (still non-enforcing; fixture-first)

* **Goal:** Make the v23 semantics-v4 candidate evidence viewable and comparable in the UI (start with fixtures).
* **Touches:** `apps/web` pages; no core API changes unless adding list endpoints.
* **Explicit lock constraints:** no semantics default switch; candidate remains advisory.
* **Acceptance:** UI can browse pairs and show v3 vs v4 diffs.
* **Stop-gate impact:** none.

---

#### vNext+36 — Promotion Lane Draft (explicitly candidate; no default enforcement)

* **Goal:** Introduce a *candidate-only* “promotion checklist” artifact that collects required evidence for any future lock release (semantics change, enforcement, provider expansion).
* **Touches:** `apps/api/storage.py` new table; `apps/web` UI; `packages/urm_runtime/evidence`.
* **Explicit lock constraints:** does not change defaults; purely evidence/packaging.
* **Acceptance:** checklist artifact references all required evidence families and hashes.
* **Stop-gate impact:** none.

---

### Sequence 2 — Formal/verification-forward (Lean/ATP lane strengthened without destabilizing runtime)

**Philosophy:** Make proofs and solver evidence first-class: better exportability, replayability, and coverage—while keeping runtime stable and default semantics unchanged.

---

#### vNext+27 — Proof & Solver Evidence Viewer in the web UI (read-only)

* **Goal:** Expose existing `proofs` and solver evidence artifacts in the UI with trust-lane annotations.
* **Touches:** `apps/web` (new proofs page, link from artifacts), `apps/api` proof read endpoints (if missing).
* **Lock constraints:** no new proof gating; no trust lane taxonomy changes.
* **Acceptance:** proof rows render with `proof_trust`, backend kind, and links to originating artifact(s).
* **Stop-gate impact:** none.

---

#### vNext+28 — Deterministic Proof Obligation Export (evidence artifact)

* **Goal:** Add an export artifact for proof obligations (e.g., “Lean file text” + canonical hash) without changing proof execution.
* **Touches:** `packages/adeu_kernel` / `packages/adeu_lean` (export helpers), `apps/api/storage.py` (new `proof_exports` table), UI.
* **Locks:** export is additive; no new proof backend kind; canonical JSON/hashing unchanged.
* **Acceptance:** same obligation always exports identical bytes + hash.
* **Stop-gate impact:** optional new metric `artifact_proof_export_determinism_pct`.

---

#### vNext+29 — Lean Replay Harness (CI-safe, pinned toolchain)

* **Goal:** Add a reproducible harness that can replay a small set of Lean proofs deterministically in CI without affecting runtime paths.
* **Touches:** `packages/adeu_lean`, CI config, `packages/adeu_kernel`.
* **Locks:** harness is not a runtime dependency; failures do not block default flows unless explicitly enabled.
* **Acceptance:** “lean replay pack” runs on fixtures and yields stable outputs.
* **Stop-gate impact:** none (unless you include it in stop-gate; likely keep separate to protect CI budget).

---

#### vNext+30 — Proof Coverage Evidence (non-enforcing “coverage packet”)

* **Goal:** Produce an evidence packet summarizing what fraction of semantics invariants have proofs (Lean) vs solver-only.
* **Touches:** `packages/urm_runtime/evidence.py`, `apps/api` + storage.
* **Locks:** does not alter `proof_trust` taxonomy; just measures.
* **Acceptance:** packet deterministically computed from stored proofs.
* **Stop-gate impact:** optional metric `artifact_proof_coverage_pct` (new metric, only if you truly need it).

---

#### vNext+31 — Lean Strengthening for SEMANTICS_v3 invariants (fixture-driven)

* **Goal:** Expand Lean modules to cover a small, well-scoped subset of SEMANTICS_v3 obligations already represented in fixtures.
* **Touches:** `packages/adeu_lean/Lean/*`, `packages/adeu_kernel`.
* **Locks:** SEMANTICS_v3 remains default; proofs remain non-enforcing unless explicitly enabled.
* **Acceptance:** new proofs pass; old proofs unchanged; failures fail closed to “not checked” in evidence.
* **Stop-gate impact:** none initially.

---

#### vNext+32 — Candidate Semantics “Proof/Counterexample” Evidence

* **Goal:** For the v23 candidate semantics lane, produce either a proof sketch or a counterexample witness artifact (still advisory).
* **Touches:** `apps/api` semantics v4 module wrappers + storage, `packages/adeu_lean` (optional).
* **Locks:** no semantics switch; advisory only.
* **Acceptance:** artifacts are deterministic, content-addressed, and link to the semantics pair.
* **Stop-gate impact:** optional determinism metric if you stop-gate it.

---

#### vNext+33 — ATP integration path (hint-only, no new backend kind)

* **Goal:** Integrate an “ATP hint generator” that produces optional hints for Lean proofs (stored as evidence), without creating a new trust lane category.
* **Touches:** `packages/adeu_kernel` validator tooling, `packages/urm_runtime/evidence`.
* **Locks:** hints do not change proof status; no gating.
* **Acceptance:** hints are deterministic for a given obligation.
* **Stop-gate impact:** none.

---

#### vNext+34 — Proof Bundle Export (portable)

* **Goal:** Export proof artifacts + exports + hints as a deterministic bundle for external review.
* **Touches:** `packages/urm_runtime`, scripts.
* **Locks:** canonicalization unchanged.
* **Acceptance:** bundle hash stable; replay instructions included.
* **Stop-gate impact:** optional.

---

#### vNext+35 — UI “Trust Lane Drill-down” (trust-first debugging)

* **Goal:** One UI view that aggregates mapping/solver/proof trust and links to evidence payloads.
* **Touches:** `apps/web`.
* **Locks:** no enforcement.
* **Acceptance:** consistent trust summary across artifacts.
* **Stop-gate impact:** none.

---

#### vNext+36 — Opt-in gated mode (candidate-only)

* **Goal:** Add an explicit opt-in mode where certain actions are blocked unless a proof condition is met (candidate lane only).
* **Touches:** policy configs + `urm_runtime` enforcement toggle + UI.
* **Locks:** defaults remain non-enforcing; must require explicit enablement.
* **Acceptance:** gated mode works; default mode unchanged.
* **Stop-gate impact:** none.

---

### Sequence 3 — Infrastructure-forward (determinism + tooling + fixtures→DB migration options)

**Philosophy:** Reduce governance/tooling drift, harden determinism boundaries, and build migration tooling so product expansions don’t destabilize stop-gate or hashing guarantees.

---

#### vNext+27 — Tooling drift closure (S9 trigger checker + tooling transfer report builder)

* **Goal:** Close the gap between lock docs and code by implementing the missing “S9 trigger checker” and a deterministic tooling transfer-report builder.
* **Touches:**

  * `apps/api/scripts/` (add `check_s9_triggers.py` per v26 doc expectations)
  * `packages/urm_runtime` (new `tooling_transfer_report_vnext_plus26.py` or equivalent)
  * `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md` generation path (script output)
* **Lock constraints:**

  * Must not change stop-gate outputs; parity-only and additive scripting.
  * Canonical JSON/hashing unchanged.
* **Acceptance:**

  * Script reproduces the S9 trigger summary deterministically from closeout metrics.
  * Tooling transfer report can be regenerated byte-identically from fixtures.
* **Stop-gate impact:** none.

---

#### vNext+28 — Replace in-process idempotency caches with DB-backed ledger (for `/urm/core-ir/propose`)

* **Goal:** Make proposer idempotency robust across processes by persisting the idempotency envelope in DB.
* **Touches:** `apps/api/src/adeu_api/main.py`, `apps/api/src/adeu_api/storage.py` (new table).
* **Locks:** idempotency semantic hash rules stay frozen (v25 constraints); provider parity unaffected.
* **Acceptance:** replay with same `client_request_id` returns same payload even after restart.
* **Stop-gate impact:** optional metric `artifact_proposer_restart_replay_pct` (only if you want to assert it).

---

#### vNext+29 — Fixture export/import tooling (DB → deterministic fixtures)

* **Goal:** Add tooling to snapshot DB artifacts into fixture packs usable by stop-gate without changing runtime semantics.
* **Touches:** `packages/urm_runtime/stop_gate_tools.py` (support), `apps/api/scripts/`.
* **Locks:** exported fixtures must respect created_at exclusion; canonical hashing unchanged.
* **Acceptance:** export→replay yields identical hashes.
* **Stop-gate impact:** optional.

---

#### vNext+30 — Stop-gate runtime scaling (performance-only; no output changes)

* **Goal:** Improve stop-gate runtime scalability (caching file reads, stable iteration) while preserving output byte identity.
* **Touches:** `packages/urm_runtime/stop_gate_tools.py`.
* **Locks:** output immutability; schema unchanged; runtime_observability fields unchanged.
* **Acceptance:** outputs identical; runtime improves or stays within ceilings.
* **Stop-gate impact:** none (parity-only).

---

#### vNext+31 — Canonical hashing parity tests (API vs runtime)

* **Goal:** Guarantee `apps/api` hashing and `urm_runtime` hashing stay equivalent (guard against accidental drift).
* **Touches:** new tests + maybe shared fixtures; no production logic change required.
* **Locks:** no hashing changes allowed; test-only.
* **Acceptance:** a test suite proves canonicalization parity on representative payload classes.
* **Stop-gate impact:** none.

---

#### vNext+32 — Fixture-backed surfaces → DB-backed option layer (read-through cache, not migration)

* **Goal:** Add an optional DB cache for fixture-backed packets to decouple runtime from filesystem layout (still deterministic).
* **Touches:** `storage.py` new table; `main.py` read-through behavior behind flag.
* **Locks:** default behavior unchanged; deterministic ordering preserved.
* **Acceptance:** cache hits return identical payloads; cache can be cleared safely.
* **Stop-gate impact:** none.

---

#### vNext+33 — Evidence retention & redaction hardening (ops-safe)

* **Goal:** Harden retention policies and redaction for stored evidence while keeping deterministic artifacts unaffected.
* **Touches:** `packages/urm_runtime/retention.py`, `apps/api/storage.py`.
* **Locks:** hashed payload excludes redacted fields already; do not change existing artifact hashes.
* **Acceptance:** retention can delete non-hash-critical operational records only.
* **Stop-gate impact:** none.

---

#### vNext+34 — Provider fixture capture improvements (offline parity)

* **Goal:** Improve provider response capture workflow so parity fixtures are easier to refresh without changing providers.
* **Touches:** scripts + fixture conventions.
* **Locks:** provider matrix unchanged; fixtures remain canonical.
* **Acceptance:** capture produces deterministic fixture files.
* **Stop-gate impact:** none.

---

#### vNext+35 — Deterministic environment enforcement (CI + local)

* **Goal:** Enforce `TZ=UTC`, `LC_ALL=C`, sorted filesystem iteration at the harness level (make drift harder).
* **Touches:** scripts, CI configs.
* **Locks:** runtime semantics unchanged.
* **Acceptance:** deterministic harness fails fast when env is wrong.
* **Stop-gate impact:** none.

---

#### vNext+36 — Formal lane packaging stability (Lean + z3 pinned visibility)

* **Goal:** Make solver/proof backend versions visible and pinned in evidence outputs without changing semantics.
* **Touches:** `adeu_kernel/validator.py`, evidence packets.
* **Locks:** do not include version strings in hashed payloads unless explicitly frozen.
* **Acceptance:** versions recorded in non-hashed operational fields only.
* **Stop-gate impact:** none.

---

## 3) Next Arc Recommendation (single best bet)

### Recommended next arc: **vNext+27 — URM Evidence Explorer (read-only UI + catalog listing endpoints)**

**Why this is lowest risk / highest leverage**

* **Lowest risk:**

  * No semantics changes (SEMANTICS_v3 untouched).
  * No new enforcement (pure read-only).
  * No provider work (avoids parity landmines).
  * No stop-gate metric churn required.
* **Highest leverage:**

  * Makes the existing v19–v24 investment *usable* in the product.
  * Creates a common “evidence navigation substrate” that every later arc can reuse (alignment sessions, advice review, candidate semantics).
* **Unlocks:**

  * A stable way to “see what the system knows” before building any write workflows.
  * A natural place to expose trust-lane labels and non-enforcement boundaries to users.
* **Defers (intentionally):**

  * Any DB-backed migration of fixture surfaces.
  * Any new enforcement modes.
  * Any provider surface expansion.

---

### Draft lock doc skeleton (repo-established style)

```markdown
# Locked Continuation vNext+27 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- v26 closeout evidence exists in:
  - `artifacts/stop_gate/report_v26_closeout.md`
  - `artifacts/stop_gate/metrics_v26_closeout.json`
  - `artifacts/quality_dashboards/quality_dashboard_v26_closeout.md`
- The repo currently includes fixture-backed URM evidence packets (v19–v24) but no product UX for browsing them.
- v27 is reserved for read-only evidence UX activation only, without enforcement or provider expansion.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior in this arc.
- All advisory/candidate lanes remain non-enforcing unless explicitly released (none in this arc).
- Canonical JSON/hashing profile is frozen (no changes):
  - `apps/api/src/adeu_api/hashing.py`
  - `packages/urm_runtime/src/urm_runtime/hashing.py`
- Stop-gate metric immutability is frozen:
  - `stop_gate_metrics@1` metrics remain additive-only (no renames, no semantic changes).
- Provider parity constraints remain frozen:
  - no new providers
  - no new provider-surface expansion in this arc
  - no live provider calls in evidence browsing flows
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- Deterministic ordering lock:
  - all catalog/list endpoints must return lexicographically sorted outputs.
- Non-enforcement boundary lock:
  - UI must clearly label candidate/advice surfaces as non-enforcing.
  - API surfaces added in this arc must not introduce enforcement knobs.

## Arc Scope (Draft Lock)

This arc activates evidence browsing UX only:

1. `X1` Add deterministic catalog/list endpoints for fixture-backed URM surfaces.
2. `X2` Add a minimal web UI surface to browse URM evidence packets and projections.
3. `X3` Add trust-lane and “non-enforcing” boundary presentation in UI.
4. `X4` Add documentation and tests to keep the evidence UX additive and stable.

Out-of-scope:

- DB-backed migration of fixture surfaces.
- Any new stop-gate schemas or metric renames.
- Any provider expansion or new provider-dependent endpoints.
- Any default semantic changes (SEMANTICS_v3 remains default).
- Any enforcement or auto-apply workflows.

## X1) Deterministic Catalog/List Endpoints

### Goal
Expose fixture-backed evidence catalogs via read-only API endpoints to support UX navigation.

### Scope
- Add endpoints such as:
  - `GET /urm/read-surface/catalog` (v19 artifact ids)
  - `GET /urm/cross-ir/catalog` (v20 pair tuples)
  - `GET /urm/normative-advice/catalog`
  - `GET /urm/proof-trust/catalog`
  - `GET /urm/semantics-v4/catalog`
  - `GET /urm/extraction-fidelity/catalog` (source_text_hash list)

### Locks
- No provider calls.
- Must not load from DB; fixtures-only.
- Output ordering must be lexicographically sorted and stable.

### Acceptance
- Endpoints return stable outputs across runs.
- Error behavior is deterministic when catalogs are missing or invalid.

## X2) Web Evidence Explorer

### Goal
Add a browseable UI for URM evidence packets and projections.

### Scope
- Add `/evidence` (or `/urm/evidence`) route(s) in `apps/web`.
- Implement a minimal JSON viewer with:
  - copy canonical JSON
  - show schema id and key hashes
  - show trust lane tags when present

### Locks
- UI must not call provider surfaces.
- UI must not introduce write workflows in this arc.

### Acceptance
- From the UI, a user can:
  - enumerate available fixture entries
  - view the packet payload and projection payload for each surface
  - deep-link to a specific fixture tuple

## X3) Trust Lanes + Non-enforcement Boundary Presentation

### Goal
Make governance boundaries visible to users.

### Scope
- UI labels:
  - candidate semantics (v23) = advisory
  - normative advice (v21) = advisory
- Display trust lane fields where present (mapping/solver/proof).

### Locks
- No change to trust-lane taxonomy.
- No enforcement toggles.

### Acceptance
- Every candidate/advice view contains explicit “non-enforcing” language.
- Trust lane fields are displayed without reinterpreting semantics.

## X4) Docs + Tests

### Goal
Prevent drift and accidental enforcement.

### Scope
- Add tests:
  - list endpoints are sorted and deterministic
  - no provider calls are introduced by evidence browsing endpoints
- Add a short doc section in `docs/FUTURE_CLEANUPS.md` or a v27 note explaining the UI’s non-enforcing scope.

### Acceptance
- CI green.
- No changes to stop-gate closeout artifacts are required for this arc.

## Error Code Additions (if any)

- Prefer reusing existing error codes.
- If new codes are needed for catalog endpoints, they must be:
  - deterministic
  - documented
  - scoped (no generic “unknown error” codes)

## Commit Plan (small-green)

1. Add catalog/list helpers for each surface (no routes yet).
2. Add API endpoints for catalogs + tests for sorted outputs.
3. Add web evidence explorer route + basic navigation.
4. Add packet/projection viewers and trust-lane badges.
5. Add docs + final regression pass.

## Preconditions

- v26 closeout artifacts present and unchanged.
- SEMANTICS_v3 remains default.
- Provider parity baselines remain green.

## Exit Criteria

- Evidence Explorer UI shipped and usable.
- Catalog/list endpoints are deterministic and sorted.
- No enforcement or provider expansion introduced.
- CI green; stop-gate outputs unchanged.
```

---

## 4) UX Track (concrete)

Because `apps/web` exists, this is grounded in the current Next.js structure.

### UX plan that ships with **no new enforcement** and **no provider expansion**

**A. Add a dedicated “Evidence” surface in the UI**

* New route: `apps/web/src/app/evidence/page.tsx`

  * Sections:

    * “Read surface (v19)”
    * “Normative advice (v21)”
    * “Proof-trust (v22)”
    * “Candidate semantics v4 (v23)”
    * “Extraction fidelity (v24)”
  * Each section:

    * fetches catalog list from new API list endpoints
    * renders a table of available fixture entries
    * deep-links to a detail page

**B. Add detail pages per surface**

* Example paths:

  * `apps/web/src/app/evidence/read-surface/[artifact_id]/page.tsx`
  * `apps/web/src/app/evidence/normative-advice/[source_text_hash]/[core_ir_artifact_id]/[concept_artifact_id]/page.tsx`
  * similarly for proof-trust and semantics-v4
  * `apps/web/src/app/evidence/extraction-fidelity/[source_text_hash]/page.tsx`

**C. Implement a shared JSON viewer component**

* Add: `apps/web/src/app/evidence/components/JsonViewer.tsx` (or similar)

  * render JSON with collapsible sections
  * “Copy JSON” button
  * show:

    * `schema`
    * hashes in payload (e.g., `source_text_hash`, `manifest_hash`, etc.)
    * “created_at excluded from hashing” note when applicable

**D. Add explicit governance cues in UI (non-enforcement + trust lanes)**

* For normative advice + semantics-v4:

  * banner: “Advisory evidence only — does not enforce behavior.”
* If packet includes trust fields:

  * render `mapping_trust`, `solver_trust`, `proof_trust` as small badges
  * link to a short glossary section on the same page

**E. Link Evidence into existing pages**

* Add a simple link block at the top of existing pages (pattern already used in many pages):

  * Home (`src/app/page.tsx`)
  * Artifacts list/detail
  * Explain / Copilot
* Keep it minimal: one new link “Evidence”.

**Explicitly out of scope for this UX track**

* No editing of evidence packets.
* No apply/commit workflows.
* No provider-driven suggestions.
* No “enforcement mode” switches.

---

## 5) Conceptual Track (ODEU / trust / governance)

These are **additive evidence artifacts first**, measured deterministically, with **no enforcement**.

### Concept upgrade 1 — ODEU Policy Trace Packets (typing maturity via evidence)

* **What it is:** A new evidence artifact family that records a *deterministic* trace of instruction policy evaluation:

  * which rules matched
  * which capability checks were consulted
  * what the decision was and why (without any runtime-only noise)
* **Artifact family:** `odeu_policy_trace_packet@0.1` (new additive schema)
* **Deterministic measurement:**

  * `artifact_odeu_policy_trace_replay_determinism_pct`
  * computed by hashing canonical JSON of trace packets across N replays (fixtures)
* **Why it’s valuable:** Moves ODEU “typing maturity” from implicit runtime behavior into explicit, replayable evidence.

### Concept upgrade 2 — Trust Lane Composition Report (evidence of boundary integrity)

* **What it is:** A report artifact that summarizes trust lane assignments for a workflow/session:

  * mapping trust used
  * solver trust used
  * proof trust used
  * links (hash refs) to the underlying evidence artifacts
* **Artifact family:** `trust_lane_composition_report@0.1`
* **Deterministic measurement:**

  * `artifact_trust_lane_composition_determinism_pct`
* **Why it’s valuable:** Makes “trust lanes remain explicit and separate” auditable at the product layer without enforcing anything.

### Concept upgrade 3 — Concept ↔ Core-IR Alignment Overlay Spec (manual alignment as evidence)

* **What it is:** A user-authored “overlay” mapping artifact that can supplement/override the bridge heuristic—**but only as evidence**, never auto-applied.
* **Artifact family:** `alignment_overlay@0.1`
* **Deterministic measurement:**

  * `artifact_alignment_overlay_hash_valid_pct` (overlay payload must hash to its id)
* **Why it’s valuable:** Provides a safe bridge from fixture-only cross-IR work toward real-world workflows while staying non-enforcing.

---

## 6) Critique of v1 `next arc.md` output

Reference: the v1 proposal you provided in `next arc.md`. 

### Where it’s too speculative vs repo reality

**1) It assumes DB-backed “core IR materialization” as an early step without acknowledging the current DB schema reality**

* Repo truth:

  * DB tables exist for `artifacts`, `concept_artifacts`, `documents`, `proofs`, `explain`, `semantic_depth`.
  * There is **no existing core-ir derived table**, and no migration framework beyond the repo’s “ensure schema” approach.
* Tightening:

  * Insert a **preview-only** Core-IR endpoint first (vNext+29 in my product-forward sequence) before committing to DB schema changes (vNext+30).

**2) It treats “cross-IR sessions on user artifacts” as straightforward, but the current cross-IR system is fixture-first**

* Repo truth:

  * Cross-IR logic exists, but catalog + pair fixtures are the “authority” today (`apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`).
  * There is no first-class `/urm/cross-ir/*` API surface; coherence is mostly consumed inside other packet builders.
* Tightening:

  * Make alignment sessions explicit about the required inputs:

    * a materialized (or preview) Core-IR payload
    * a concept artifact payload
    * (ideally) a matching `source_text_hash` derived deterministically from document/source text
  * Start with “session evidence” and only later add overlays/review flows.

**3) The v1 plan adds new stop-gate metrics freely**

* Repo constraint:

  * stop-gate metrics schema is frozen and additive-only; metrics are treated as governance-evidence.
* Tightening:

  * Only introduce new metrics when a new evidence family is added to stop-gate.
  * UI-only arcs should have **no stop-gate impact**.

**4) The v1 proposal spans multi-version arcs (e.g., “vNext+28–29”)**

* Repo style:

  * Existing continuations are written as single-arc locks with explicit step blocks (Y1–Y4, Z1–Z4).
* Tightening:

  * Split multi-version arcs into single vNext locks so each has clear acceptance + small-green commit plans.

**5) It doesn’t call out the existing “safe write” foundation already present**

* Repo truth:

  * `/urm/explain/materialize` and `/urm/semantic_depth/materialize` already establish a safe-write pattern.
* Tightening:

  * Product-forward path should reuse those patterns and extend them cautiously (derived-only, idempotent, non-enforcing).

### Tightened v1 direction (still consistent with its spirit, but repo-feasible)

If I compress the v1 idea into a repo-grounded ladder:

1. **vNext+27:** Evidence Explorer (read-only UI + catalogs)
2. **vNext+28:** Artifact Evidence Panel for existing DB-backed derived artifacts (explain + semantic depth)
3. **vNext+29:** Core-IR preview (read-only)
4. **vNext+30:** Core-IR materialize (safe write, derived-only, new table)
5. **vNext+31:** Alignment session evidence (bridge + coherence, non-enforcing)
6. **vNext+32:** Normative advice session + review queue (non-enforcing)

This preserves the intended direction (“read-only → product UX → safe write workflows”) but respects what the repo actually has today.

---

If you want, I can also rewrite your v1 `next arc.md` into a “v27 lock doc draft” that matches the repo’s exact continuation tone and vocabulary—but the content above is the realistic continuation map under the deterministic stop-gate regime.
