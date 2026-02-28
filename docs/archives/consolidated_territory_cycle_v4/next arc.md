## A) State of the world map

### Current frontier (repo-grounded)

**Latest “locked continuation” baseline present:**

* `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` (tooling consolidation follow-on; canonical serialization + determinism hygiene explicitly re‑affirmed).
* Closeout decision note: `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
* Stop-gate closeout artifacts:

  * `artifacts/stop_gate/metrics_v26_closeout.json`
  * `artifacts/stop_gate/report_v26_closeout.md`
* Latest transfer report (tooling parity lane):

  * `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
* vNext+26 stop-gate manifest source-of-truth:

  * `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`

**Frontier interpretation:** vNext+26 has “closed-out” evidence (metrics + report + transfer report), and the repo explicitly says **vNext+27 is pending freeze** (see the execution checkpoint in `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`). So the strategic next work should be framed as **post‑v26 additive arcs** that preserve the v14–v26 contract stack.

---

### Major subsystems (what they do)

**Apps**

* **`apps/api` (FastAPI backend)**

  * Core “product API” for ADEU IR, Concepts, Puzzles, Papers/Documents.
  * Provides **URM surfaces**: read-only evidence surfaces (mostly fixture-backed), plus a few DB-backed “materialize” write surfaces (`/urm/explain/materialize`, `/urm/semantic_depth/materialize`), plus **copilot session** endpoints.
  * Owns SQLite persistence via `apps/api/src/adeu_api/storage.py` for:

    * ADEU IR artifacts (`artifacts` table)
    * Concept artifacts (`concept_artifacts`)
    * Validator runs (`validator_runs`)
    * Proof artifacts (`proof_artifacts`)
    * Explain artifacts (`explain_artifacts`)
    * Semantic depth reports (`semantic_depth_reports`)
    * Documents (`documents`)
* **`apps/web` (Next.js UI)**

  * Current routes/surfaces:

    * `/` ADEU Studio (propose/check/store ADEU IR artifacts)
    * `/concepts` Concepts Studio
    * `/puzzles` Puzzle Studio
    * `/papers` Documents-first concepts workflow + cross-doc concept alignment
    * `/artifacts` Artifact Browser (stored ADEU IR artifacts)
    * `/explain` Explain materialization
    * `/copilot` Copilot console (URM runtime session, SSE, approvals, tool allowlist)

**Packages**

* **`packages/adeu_ir`**: base IR models + schema (`SchemaVersion = "adeu.ir.v0"`) and trust types like `MappingTrust = Literal["derived_bridge", "derived_alignment"]`.
* **`packages/adeu_kernel`**: deterministic kernel validation + proof backend wrapper (mock/lean), proof packet hashing/stripping helpers, etc.
* **`packages/adeu_core_ir`**: core IR projection primitives (O/E/D/U lanes) used by URM artifact families.
* **`packages/adeu_concepts` / `packages/adeu_puzzles`**: concept/puzzle IR + checks, patching, tournament orchestration.
* **`packages/adeu_explain`**: explain/diff modeling.
* **`packages/adeu_semantic_depth`**: semantic depth report validation.
* **`packages/urm_runtime`**: stop-gate tools, event tooling, copilot orchestration, policy evaluation, canonical hashing utilities, determinism/replay harness.
* **`packages/adeu_lean`**: Lean runner + minimal AdeuCore semantics/theorems + wrapper theorem generation.

---

### Trust lanes & evidence families

**Trust lanes (frozen sets in current codepaths)**

* `mapping_trust`: **`derived_bridge`**, **`derived_alignment`** (defined in `packages/adeu_ir/src/adeu_ir/models.py`).
* `solver_trust`: **`kernel_only | solver_backed | proof_checked`** (in `apps/api/src/adeu_api/main.py`).
* `proof_trust`: **`no_required_proofs | mock_backend_not_proof_checked | lean_core_v1_partial_or_failed | lean_core_v1_proved`** (in `apps/api/src/adeu_api/main.py`).

**Evidence families**

* Evidence references are typed via `EvidenceRef` with kinds: **`event | run | validator | proof | artifact`** (in `apps/api/src/adeu_api/main.py`).
* Proof evidence packets exist and are hashed via canonical JSON stripping helpers (kernel/runtime); proof generation is **optional** and fails closed into stored “failed” proof artifacts (rather than crashing runtime).

**Non-enforcement boundary (important)**

* The URM “diagnostic/advice/invariant/candidate” families are structured as **read-only evidence**:

  * cross‑IR coherence (vNext+20)
  * normative advice (vNext+21)
  * trust invariant (vNext+22)
  * semantics‑v4 candidate (vNext+23)
  * extraction fidelity (vNext+24)
* These surfaces are intentionally **non-authoritative**: they inform review, they do not mutate or enforce.

---

### Product surface today: active vs fixture-backed only

Here’s the repo-grounded split that matters for planning “read-only → UX → safe write.”

#### Active, DB-backed product surfaces

* **ADEU IR artifacts**

  * `POST /artifacts` (create + persist)
  * `GET /artifacts`, `GET /artifacts/{id}`
  * Validator runs and proof artifacts persisted alongside.
* **Concept artifacts**

  * Create/list/get concept artifacts; concept analysis stored in DB (`analysis_json` is persisted).
* **Documents/Papers**

  * `POST /documents`, `GET /documents`, `GET /documents/{id}`; papers workflow uses this heavily.
* **URM “materialize” write workflows**

  * `POST /urm/explain/materialize` → persisted explain packet
  * `POST /urm/semantic_depth/materialize` → persisted depth report
* **Copilot session**

  * `/urm/copilot/*` endpoints and `/copilot` UI (SSE events, approvals, tool allowlist).
  * Operationally “active,” but dependent on Codex availability/config.

#### Fixture-backed only (read-only evidence surfaces)

These are “real surfaces” in the API, but they **serve from vNext fixture catalogs** and do not persist new artifacts:

* `/urm/core-ir/artifacts*` + lane projection/report + integrity read-surface families

  * Built from vNext+19 fixture catalogs (see `docs/READ_SURFACE_TRANSFER_REPORT_vNEXT_PLUS19.md`).
* Cross‑IR coherence (vNext+20 transfer report: `docs/CROSS_IR_COHERENCE_TRANSFER_REPORT_vNEXT_PLUS20.md`)
* Normative advice (vNext+21 transfer report)
* Trust invariant (vNext+22 transfer report)
* Semantics-v4 candidate (vNext+23 transfer report)
* Extraction fidelity (vNext+24 transfer report)

#### Hybrid (active, but with fixture determinism + provider parity constraints)

* Proposer endpoints (ADEU IR, Concepts, Puzzles, Core‑IR proposer):

  * Have fixture-backed deterministic cases **and** can call providers when not fixture-matched.
  * Provider parity constraints are formalized via `apps/api/fixtures/provider_parity/vnext_plus25_provider_matrix.json`.

---

### Frozen hashing/serialization profile (and where it lives)

**Canonical JSON serialization profile (frozen)**

* **Config:** `json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)`
* **Hash:** sha256 over UTF-8 bytes of the canonical JSON string.

**Where it lives (two canonical implementations in repo)**

* `apps/api/src/adeu_api/hashing.py`:

  * `canonical_json(value: object) -> str`
  * `sha256_canonical_json(value: object) -> str`
* `packages/urm_runtime/src/urm_runtime/hashing.py`:

  * same profile + `sha256_text`

**SEMANTICS_v3 reproducibility hook**

* `docs/SEMANTICS_v3.md` freezes deterministic assertion naming like:

  * `json_path_hash = sha256(json_path).hexdigest()[:12]`

This is not just “nice to have”: it’s referenced by trust invariant checks and stop-gate replay determinism expectations.

---

### The constraint box (what cannot move without explicit lock releases)

These are the “do not touch unless you write a release lane and freeze it” constraints implied by the v14–v26 lock chain and the stop-gate machinery:

1. **Default semantics remains `SEMANTICS_v3`**

   * `docs/SEMANTICS_v3.md` is the default; `semantics-v4 candidate` is explicitly a *candidate* lane (vNext+23) and cannot silently become default.

2. **Provider parity constraints**

   * Provider kinds are frozen in runtime (`mock/openai/codex`).
   * Surfaces participating in provider parity are enumerated in provider matrix JSON (`apps/api/fixtures/provider_parity/vnext_plus25_provider_matrix.json`).
   * Any new provider-executed surface or new provider kind requires explicit lock + parity fixtures.

3. **Trust lane taxonomy is frozen**

   * `mapping_trust`, `solver_trust`, `proof_trust` value sets are effectively contract-level, because they are:

     * part of API response models
     * referenced by evidence/UX
     * entangled with stop-gate reporting conventions

4. **Stop-gate schema and existing metric keys are immutable**

   * `stop_gate_metrics@1` is frozen; existing metric keys are cumulative and must remain present.
   * Changes are additive only; do not rename, delete, or change semantics of existing metric keys.
   * CI budget ceiling exists (`VNEXT_PLUS18_CI_BUDGET_CEILING_MS = 120000` in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`) and must continue to pass.

5. **Non-enforcement boundaries**

   * Advisory/invariant/candidate packets must remain non-authoritative unless you propose a *separate explicit lane* and lock it (because enforcement implies semantics + workflow changes).

6. **Deterministic replay and canonical hashing are “hard locks”**

   * Canonical JSON profile + hash recomputation checks appear in trust invariant artifacts and stop-gate measurement; touching them is a lock-release-level event.

---

## B) Three candidate multi-arc sequences (vNext+27 → vNext+36 horizon)

Below: three “multi-arc” plans with different philosophies. Each arc is sized as ~1–2 vNext steps (so 5 arcs ≈ v27→v36).

---

# Sequence 1 — Product-forward

### Arc P1 (vNext+27): Evidence-first UX activation for URM read surfaces

**Goal**
Make the **existing read-only URM surfaces** first-class in ADEU Studio UX without adding write capability.

**Scope**

* Web: Add “Evidence” navigation to display:

  * core-ir read surface payloads
  * lane projection/report
  * integrity diagnostics surfaces
  * cross‑IR coherence/advice/invariant/candidate/fidelity packets (as *fixture-backed exemplars*)
* API: **No semantic changes**; only tiny helpers if needed (e.g., list endpoints already exist).

**Explicit locks**

* Preserve `SEMANTICS_v3` default.
* Preserve non-enforcement: UX must clearly label “read-only / evidence-only / fixture-backed.”
* Preserve trust lane labeling: show `mapping_trust/solver_trust/proof_trust` as *labels*, not controls.
* No provider calls and no writes introduced in this arc.

**Acceptance**

* Web can browse all fixture-backed URM artifacts without errors.
* UX explicitly surfaces “fixture-backed / non-enforcing” banner and provenance links (artifact_id/source hashes).
* No changes to stop-gate artifacts besides (optional) UI-only changes.

**Stop-gate metric additions**

* None required (reuse existing v19–v24 determinism metrics as implicit coverage).

**Small-green commit themes**

1. UI: Read-only “Evidence” pane scaffolding + routing.
2. UI: Core IR/Lane/Integrity rendering with stable keys and safe truncation.
3. UI: Add “packet viewers” for advice/invariant/candidate/fidelity.
4. Docs: add a short “Evidence surfaces are non-enforcing” UX note in README or docs.

---

### Arc P2 (vNext+28–29): DB-backed Core-IR materialization lane for stored ADEU artifacts

**Goal**
Bridge the product gap: enable **core-ir/lane/integrity** surfaces for **user-stored ADEU IR artifacts**, while remaining safe and deterministic.

**Scope**

* API:

  * Add **materialization endpoints** (parallel to existing explain/semantic_depth materializers), e.g.:

    * `POST /urm/core-ir/materialize` (input: `artifact_id`, `client_request_id`, optional `semantics_version` defaulting to v3)
    * `GET /urm/core-ir/materialized/{core_ir_id}` or `GET /artifacts/{artifact_id}/urm/core-ir`
  * Add DB tables for core-ir + derived views (or store as JSON blobs):

    * core_ir_artifacts (schema + hash + payload)
    * lane_projection, lane_report
    * integrity diagnostics captures (reusing existing family naming)
* Web:

  * On Artifact detail view, add “Compute / View Core IR” button (safe write: stores derived artifact, does **not** mutate ADEU IR).
* Determinism:

  * materialization must be idempotent by (`artifact_id`, `semantics_version`) and stable-hashed.

**Explicit locks**

* Do **not** change `/urm/core-ir/artifacts/*` fixture-backed endpoints; add new DB-backed surfaces.
* Canonical JSON hashing profile is frozen; stored hashes must recompute.
* Determinism: no wall-clock in hashed payloads; created_at excluded or treated as nonsemantic field.

**Acceptance**

* For a stored ADEU artifact:

  * core-ir materialization succeeds deterministically
  * repeated materialize requests return the same `core_ir_hash` and same payload hash
* DB roundtrip (store → fetch) preserves canonical hash recomputation.
* Web shows read-only views for materialized core-ir/lane/integrity.

**Stop-gate metric additions (additive)**

* New manifest: `stop_gate.vnext_plus28_manifest@1` (or v29) including DB-materialization fixtures.
* Suggested new metrics:

  * `artifact_core_ir_materialize_determinism_pct == 100.0`
  * `artifact_lane_materialize_determinism_pct == 100.0`
  * `artifact_integrity_materialize_determinism_pct == 100.0`
  * `artifact_materialized_hash_recompute_match_pct == 100.0` (trust-invariant style)

**Small-green commit themes**

1. DB schema + storage helpers for core-ir blobs and hashes.
2. Materialize endpoint + idempotency keying.
3. Deterministic fixtures + stop-gate manifest for materialization.
4. Web artifact detail integration + safe UI messaging.

---

### Arc P3 (vNext+30–31): “Alignment session” UX for Concept ↔ Core-IR (read-only coherence + advice)

**Goal**
Turn the cross‑IR stack into a usable review tool by letting users select a **concept artifact** and a **materialized core-ir artifact** and see coherence + normative advice.

**Scope**

* API:

  * Add a “session builder” endpoint that computes (and optionally persists) cross‑IR coherence diagnostics and normative advice **on user artifacts**, not only fixtures.
  * Keep the existing vNext+20/21 fixture-based builders as a reference baseline; add a new path that accepts DB-backed artifacts.
* Web:

  * Add “Align with Core-IR” flow in `/papers` and/or `/concepts`:

    * choose concept artifact
    * choose target core-ir artifact
    * render coherence issues + advice list
    * show trust lanes (`mapping_trust=derived_bridge`) and “non-enforcing” banner

**Explicit locks**

* Keep `mapping_trust` taxonomy unchanged: session results must use existing values (`derived_bridge`) or `null`.
* Non-enforcement: advice is review-only, no auto-application.
* Preserve canonical hashing and determinism for generated packets.

**Acceptance**

* Session outputs are deterministic for the same artifact pair.
* Session packets include stable evidence refs:

  * pointers to input artifact IDs/hashes
  * consistent ordering of issues/advice items

**Stop-gate metric additions**

* New manifest: `stop_gate.vnext_plus30_manifest@1` (or v31).
* Suggested new metrics:

  * `artifact_cross_ir_user_coherence_determinism_pct == 100.0`
  * `artifact_normative_advice_user_packet_determinism_pct == 100.0`

**Small-green commit themes**

1. API: “cross-ir session” request/response models (typed) + deterministic ordering rules.
2. API: computation + optional persistence (session table).
3. Stop-gate fixtures using known stored artifacts.
4. Web: session UX with clear “review-only” boundaries.

---

### Arc P4 (vNext+32–33): Safe write workflows for “review → commit” without mutating semantics

**Goal**
Introduce **safe write** operations that let users record decisions (accept/reject) and generate new derived artifacts **without changing default semantics**.

**Scope**

* Add “decision artifacts” / “review commits” that are:

  * idempotent
  * auditable
  * non-enforcing
* Candidate write surfaces:

  * “accept advice item” (stores a decision record + optional annotation)
  * “apply deterministic patch” to create a new concept artifact version (already supported concept patch mechanics exist; this turns it into a governed workflow)
  * “attach mapping override overlay” *as a separate artifact family* (avoid changing `mapping_trust` taxonomy)

**Explicit locks**

* No new `mapping_trust` values unless a lock-release lane is created; store manual overrides as separate overlay artifacts.
* ODEU/URM mode gates: require `writes_allowed` mode + explicit approval tokens (use existing approval model patterns from copilot tooling).
* Provider parity: keep this arc **provider-free** (no LLM dependency) unless explicitly put behind existing provider-matrix surfaces.

**Acceptance**

* Writes are blocked in read-only mode (hard gate).
* Every write produces:

  * deterministic artifact hash
  * evidence refs (who/what/why)
  * stable replay behavior (idempotency keys)
* UI supports “draft → review → commit” with explicit confirmation.

**Stop-gate metric additions**

* New manifest: `stop_gate.vnext_plus32_manifest@1` (or v33).
* Suggested new metrics:

  * `artifact_review_commit_idempotency_determinism_pct == 100.0`
  * `artifact_write_gate_enforcement_pct == 100.0` (tests that read-only mode cannot write)
  * `artifact_decision_artifact_hash_recompute_match_pct == 100.0`

**Small-green commit themes**

1. Add DB tables + typed models for decision artifacts + approvals.
2. Enforce mode/approval hard gates in API.
3. Deterministic fixtures for “attempted write in read-only mode” + “idempotent replay.”
4. Web: review/commit UI, audit trail viewer.

---

### Arc P5 (vNext+34–36): Workflow orchestration + optional proof lane surfacing (without destabilizing runtime)

**Goal**
Deliver an end-to-end product workflow (document → concept → core-ir → align → review → commit) and surface proof/trust status, while keeping proof optional.

**Scope**

* Web:

  * “Workflow” UX that strings together:

    * papers/doc ingestion
    * concept propose/analyze + alignment
    * core-ir materialize
    * cross-ir session + advice
    * review commit
* Formal lane:

  * Improve proof surfacing (show obligation status + proof evidence packets) but **do not block** runtime actions on proof failures by default.
* Copilot:

  * Add “assistant suggestions” that produce drafts only; committing remains user-approved (respect trust lanes + non-enforcement).

**Explicit locks**

* `SEMANTICS_v3` default unchanged; `semantics-v4 candidate` remains candidate-only.
* Proof backend remains optional (mock/lean); runtime must remain robust when lean unavailable.
* Provider parity constraints: any copilot provider usage must be behind existing allowlists/matrix, or explicitly locked as a new provider surface.

**Acceptance**

* End-to-end workflow produces deterministic artifacts with evidence linkage.
* Optional proof runs do not destabilize runtime and do not change default acceptance semantics.
* UX makes trust lanes legible at each step.

**Stop-gate metric additions**

* New manifest: `stop_gate.vnext_plus34_manifest@1` (or v36).
* Suggested new metrics:

  * `artifact_workflow_replay_determinism_pct == 100.0` (event-stream replay)
  * `artifact_proof_packet_hash_stability_pct` already exists historically; extend with:

    * `artifact_proof_ui_projection_determinism_pct == 100.0` (if a new projection is introduced)

**Small-green commit themes**

1. Workflow orchestration models + “session graph” persistence.
2. Web workflow wizard + safe defaults (read-only by default).
3. Optional proof surfacing (no gating).
4. Stop-gate replay fixtures for workflow sessions.

---

# Sequence 2 — Formal/verification-forward

### Arc F1 (vNext+27): Stabilize Lean/Proof lane as an “optional evidence producer”

**Goal**
Make Lean integration boring and deterministic: proofs are evidence; they never destabilize core product flows.

**Scope**

* Tighten proof backend handling:

  * consistent timeout behavior
  * deterministic error shaping into proof artifacts
  * improve proof evidence packet hashing conformance checks
* Add “proof availability diagnostics” surfaced as evidence (not runtime failures).

**Explicit locks**

* Proof remains optional; default mode continues to accept `mock` backend without changing semantics.
* Canonical hash + strip-nonsemantic rules remain unchanged.

**Acceptance**

* Proof generation never raises uncaught runtime exceptions.
* Proof evidence packets always recompute hash.

**Stop-gate additions**

* `artifact_proof_backend_graceful_degradation_pct == 100.0` (e.g., when lean unavailable)
* `artifact_proof_evidence_hash_recompute_match_pct == 100.0`

**Small-green commits**

1. Proof backend error normalization.
2. Deterministic fixtures for “lean unavailable.”
3. Stop-gate manifest + metrics.

---

### Arc F2 (vNext+28–29): Expand Lean obligation set (still runtime-independent)

**Goal**
Increase the “meaningfulness” of proofs without tying them to runtime-critical computation.

**Scope**

* Add new obligation kinds in `adeu_lean` that formalize:

  * selected invariants already tracked in trust-invariant packets (hash stability, replay stability as abstract properties)
* Keep wrapper-theorem strategy (still generic), but expand coverage.

**Explicit locks**

* No semantics changes; proofs remain about invariants of the formal model, not about changing outputs.

**Acceptance**

* New obligations compile and prove under pinned Lean toolchain when enabled.
* Proof artifacts remain deterministic in stored form.

**Stop-gate**

* `artifact_proof_obligation_coverage_pct == 100.0` (for required set)
* `proof_replay_determinism_pct` already exists; ensure remains green

**Small-green commits**

1. Add obligation kinds + Lean core theorem stubs.
2. Update proof packet schema usage.
3. Add fixtures.

---

### Arc F3 (vNext+30–31): ODEU typing maturity via policy proofs + deterministic evaluation traces

**Goal**
Make ODEU policy evaluation *auditable* and *typed* in a way that supports safe write workflows.

**Scope**

* Add deterministic policy evaluation trace packet (evidence-only).
* Optional: Lean lemma packs proving basic policy properties (e.g., mode gates imply deny in read-only).

**Explicit locks**

* Do not add new governance primitives; use existing policy schema (`odeu.instructions.v1`) and generated views.
* Policy changes require explicit lock and must remain deterministic.

**Acceptance**

* Policy evaluation trace is stable-hashed, reproducible, and can be rendered in UI.

**Stop-gate**

* `artifact_policy_trace_determinism_pct == 100.0`

**Small-green commits**

1. Policy trace builder + schema.
2. Fixtures + stop-gate.

---

### Arc F4 (vNext+32–33): Semantics v4 candidate formalization (no default flip)

**Goal**
Advance semantics-v4 from “candidate comparison packets” toward a formally characterized lane, without flipping the default.

**Scope**

* Extend semantics-v4 candidate packet with stronger structured comparisons (still non-enforcing).
* Add Lean-level formal model notes (as a lane).

**Explicit locks**

* `SEMANTICS_v3` remains default; v4 remains candidate-only.

**Acceptance**

* Candidate packet determinism remains 100% and adds more actionable comparison codes.

**Stop-gate**

* Extend `artifact_semantics_v4_candidate_*` metrics with additional invariant checks (additive keys only).

**Small-green commits**

1. Candidate packet expansion.
2. Lean model updates.
3. Transfer report refresh.

---

### Arc F5 (vNext+34–36): Proof-aware product UX (optional gating lane)

**Goal**
Expose proof status as a first-class UX dimension and optionally allow a “proof-preferred” lane for certain workflows.

**Scope**

* UI: proof dashboards per artifact, with obligation list and evidence refs.
* Optional gating lane: for specific workflows, require `proof_checked` in a new opt-in mode (not default).

**Explicit locks**

* Do not change default behavior; gating is opt-in via mode/policy.

**Acceptance**

* Proof surfacing doesn’t change artifact semantics; it only changes eligibility under explicit opt-in.

**Stop-gate**

* `artifact_proof_dashboard_projection_determinism_pct == 100.0`

**Small-green commits**

1. UI viewer + API projections.
2. Optional policy rule for proof-preferred mode.

---

# Sequence 3 — Infrastructure-forward (determinism + refactor + ops)

### Arc I1 (vNext+27): Determinism consolidation + drift-hardening

**Goal**
Reduce future drift risk and keep replay determinism cheap as surfaces grow.

**Scope**

* Consolidate canonical hashing usage to reduce duplication risk:

  * align `apps/api/src/adeu_api/hashing.py` with `urm_runtime/hashing.py` (single import source where feasible)
* Implement the deferred script:

  * `cleanup-vnext-plus26-s9-trigger-check-script` (explicit in `docs/FUTURE_CLEANUPS.md`)
* Consolidate read-surface guard harness scaffolding (also listed in cleanups).

**Explicit locks**

* No behavior changes: must be parity-only refactors.
* Canonical JSON profile must not change.

**Acceptance**

* Strict parity tests demonstrate hash outputs unchanged.
* S9 trigger checks are executable as a standalone preflight.

**Stop-gate**

* Potential new tooling parity metric if needed:

  * `artifact_hashing_consolidation_parity_pct == 100.0`

**Small-green commits**

1. Extract shared hashing import path + parity tests.
2. Add S9 check script + tests.
3. Guard harness consolidation.

---

### Arc I2 (vNext+28–29): DB-backed idempotency + multi-worker safety

**Goal**
Make idempotency correct beyond single-process dev mode (important for copilot + proposer workflows).

**Scope**

* Replace process-local idempotency caches (explicitly flagged in cleanups) with DB-backed stores.
* Add “idempotency key ledger” table:

  * request_hash → response_hash + artifact IDs
* Add deterministic conflict responses for reused keys with mismatched payload.

**Explicit locks**

* Provider parity: ensure idempotency does not change surface outputs.
* Deterministic hashing for request payloads is frozen.

**Acceptance**

* Multi-worker simulation tests show correct idempotent behavior.
* No parity regression for existing provider parity fixtures.

**Stop-gate**

* `artifact_idempotency_ledger_replay_determinism_pct == 100.0`
* `artifact_idempotency_conflict_stability_pct == 100.0`

**Small-green commits**

1. DB schema + helpers.
2. Wire into proposer endpoints and copilot workflows.
3. Add fixtures + stop-gate.

---

### Arc I3 (vNext+30–31): Fixtures ↔ DB migration toolchain (export/import)

**Goal**
Create a deterministic bridge so fixture-backed families can become DB-backed *without losing replay evidence*.

**Scope**

* Add tooling to:

  * seed DB from fixture catalogs (import)
  * export DB artifacts back into fixture-compatible payloads (export)
* Define a “snapshot schema” for exported payload sets.

**Explicit locks**

* Fixtures remain canonical for stop-gate; export must preserve canonical hashes.

**Acceptance**

* Exported fixtures match existing fixture payload hashes for known cases.

**Stop-gate**

* `artifact_fixture_export_hash_match_pct == 100.0`

**Small-green commits**

1. Export schema + exporter.
2. Importer.
3. Parity fixture suite.

---

### Arc I4 (vNext+32–33): Stop-gate scalability + CI budget headroom

**Goal**
Keep stop-gate cheap as metric families expand.

**Scope**

* Deterministic caching:

  * avoid repeated fixture file I/O
  * cache canonical_json encoding in-memory within a run
* Optional deterministic parallelization (careful: stable ordering of aggregation).

**Explicit locks**

* Must not change metric semantics.
* CI budget ceiling metric must remain green.

**Acceptance**

* Benchmarks show reduced elapsed_ms and stable output.
* All existing metrics remain unchanged.

**Stop-gate**

* Extend observability fields (additive):

  * `stop_gate_elapsed_ms_delta_vs_baseline` (or similar) **only if consistent with existing schema patterns**
  * Or keep as internal logging, not schema.

**Small-green commits**

1. Cache I/O.
2. Cache hashing.
3. Deterministic parallel aggregation (optional).

---

### Arc I5 (vNext+34–36): Operational readiness hardening

**Goal**
Prepare for longer-lived sessions, evidence retention, and real deployment pressure.

**Scope**

* SSE stability improvements for copilot
* Evidence retention policies + purge workflows (already exist conceptually in copilot evidence bundles)
* Connector snapshot durability and replay validation improvements

**Explicit locks**

* Keep non-enforcement and mode gating stable.
* No changes to trust lane taxonomy.

**Acceptance**

* Long session tests pass; evidence retrieval remains deterministic and safe.

**Stop-gate**

* Add a small suite of replay fixtures for long-running copilot sessions:

  * `scheduler_dispatch_replay_determinism_pct` family is already present historically; extend via fixtures, not via new semantics.

**Small-green commits**

1. SSE + reconnect hardening.
2. Evidence retention/purge tests.
3. Replay fixtures.

---

## C) Recommended default sequence (and why)

**Recommendation: Sequence 1 (Product-forward), with one explicit “infra guardrail rule”: do not start P4 until P2 is green.**

### Why it’s lowest risk / highest leverage

* **Lowest risk** because the first increment (P1) is almost entirely **UX wiring over already-locked read-only surfaces**. It doesn’t touch semantics, providers, or write paths.
* **High leverage** because it turns the repo’s largest existing asset (the v19–v24 URM evidence stack) into something users can actually *see and navigate*.
* The subsequent arcs (P2/P3) introduce DB-backed capabilities **via additive materialize-style endpoints**, matching patterns that already exist and are proven stable (`/urm/explain/materialize`, `/urm/semantic_depth/materialize`).

### What it unlocks

* A coherent “evidence ladder”:

  * stored ADEU IR → derived core-ir/lane/integrity → cross‑IR coherence/advice → review → commit decisions
* Product UX that makes **trust lanes legible** (and therefore makes safe writes feasible without governance surprises).
* A realistic runway for copilot assistance that respects:

  * mode gating
  * approvals
  * non-enforcement boundaries

### What it defers (intentionally)

* Any attempt to flip default semantics away from `SEMANTICS_v3` (kept candidate-only).
* Deep Lean/ATP commitments as gating requirements (kept optional, evidence-only).
* Heavy infrastructure refactors that don’t immediately support product workflows (but you can still cherry-pick I1/I2 if operational needs demand it).

---

## D) Arc template skeleton (repo-style lock doc)

Below is a **lock-doc skeleton** patterned after the current repo’s continuation locks (e.g., `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`). It uses the same primitives: global locks, scoped steps, additive error codes, stop-gate metric extensions, commit plan, exit criteria.

```md
# Locked Continuation vNext+XX (Draft Lock)

This document freezes the allowed scope for vNext+XX and the constraints that MUST remain unchanged
unless explicitly released by a follow-on lock.

Status: DRAFT LOCK (not yet frozen)

## Global Locks

- SEMANTICS:
  - `SEMANTICS_v3` remains the default semantics.
  - Any semantics-v4 work remains candidate-only and non-enforcing unless explicitly released.
- CANONICAL SERIALIZATION / HASHING:
  - canonical JSON profile is frozen (sort_keys + separators + UTF-8 sha256).
  - hash recomputation MUST match for all new artifact families.
- TRUST LANES:
  - `mapping_trust`, `solver_trust`, `proof_trust` value sets are frozen.
  - no new trust-lane values without explicit release.
- NON-ENFORCEMENT BOUNDARY:
  - advice/invariant/candidate packets remain review-only; no auto-mutation.
- PROVIDER PARITY:
  - provider kinds and provider-matrix surfaces remain frozen.
  - no new provider-executed surfaces without parity fixtures + lock.
- STOP-GATE:
  - `stop_gate_metrics@1` schema is frozen.
  - existing metric keys are immutable; additions must be additive-only.
  - CI budget ceiling must remain green.

## Arc Scope (Draft Lock)

One paragraph describing the single thin-slice objective for vNext+XX.
Explicitly note what is OUT OF SCOPE.

### X1) <Step name> (Goal)

Goal:
- <what this step achieves>

Scope:
- in:
  - <list>
- out:
  - <list>

Locks:
- <repeat any scope-specific locks that apply here>
- <explicit “no mutation” / “no provider expansion” statements>

Acceptance:
- <clear pass/fail list>
- <determinism and replay expectations>
- <docs/transfer report expectations if any>

### X2) <Step name> (Goal)

... same structure ...

### X3) <Step name> (Goal)

... same structure ...

### X4) <Step name> (Goal)

... same structure ...

## Stop-Gate Metric Extensions (vNext+XX)

- Manifest:
  - schema: `stop_gate.vnext_plusXX_manifest@1`
  - path: `apps/api/fixtures/stop_gate/vnext_plusXX_manifest.json`
- New metrics (additive keys only):
  - `<new_metric_key> == 100.0`
  - `<new_metric_key> == 100.0`
- Notes:
  - do not rename or remove any existing metrics.
  - include replay_count and bytes_hashed observability fields where consistent with prior arcs.

## Error Codes (Additive Only)

New error codes introduced by this arc (if any):
- `URM_ADEU_<SOMETHING>_<DETAIL>`
- `URM_ADEU_<SOMETHING>_<DETAIL>`

Rules:
- error code names must be stable, unique, and not reuse prior codes.
- error code meanings must not overlap existing codes.

## Commit Plan (Small-Green)

- PR1: scaffolding + models + no behavior change
- PR2: core implementation (feature flags / additive endpoints only)
- PR3: deterministic fixtures + stop-gate manifest additions
- PR4: docs + transfer report refresh + cleanup

## Exit Criteria

- All prior stop-gate metrics remain green at or above thresholds.
- All new vNext+XX metrics are green and reproducible via replay.
- Transfer report(s) updated/generated deterministically (if in scope).
- No provider parity regression; S9 triggers remain non-triggered (or explicitly addressed).
- No changes to default semantics or trust lane taxonomy.
```

---

If you want, I can also append a **“vNext+27 candidate lock draft”** (filled in using one of the above arcs, in the exact house style) — but the sections above are already structured so you can drop it straight into `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md` with minimal editing.
