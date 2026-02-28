A) Executive summary (10 bullets max)

**3 strongest parts**

* **Schema-first discipline + explicit schema/version sentinels are pervasive** (e.g., `schema_version: Literal["adeu.ir.v0"]` + `extra="forbid"` in `packages/adeu_ir/src/adeu_ir/models.py:AdeuIR`; schema export wiring in `packages/adeu_ir/src/adeu_ir/export_schema.py`; web type generation off JSON schema in `apps/web/scripts/gen-types.mjs`).
* **Determinism is treated as an invariant, not a hope** via canonical hashing + replay/guard harnesses (canonical JSON hashing in `apps/api/src/adeu_api/hashing.py`; stable IDs in `packages/adeu_ir/src/adeu_ir/ids.py:stable_id`; permutation/idempotence oracles in `apps/api/src/adeu_api/determinism_oracles.py`; “Z4 fail-closed” tooling guard that forbids provider/network and snapshots locked surfaces in `apps/api/tests/test_tooling_z4_guards.py`).
* **Stop-gates & continuity are concretely implemented as artifacts + manifests + tests**, not just docs (stop-gate manifest + hash chaining in `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`; metrics/report artifacts in `artifacts/stop_gate/metrics_v26_closeout.json` and `artifacts/stop_gate/report_v26_closeout.md`; lock narrative in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`).

**3 biggest risks**

* **Hash/canonicalization logic is duplicated across multiple “authoritative” places**, increasing silent drift risk (e.g., `apps/api/src/adeu_api/hashing.py`, `packages/urm_runtime/src/urm_runtime/hashing.py`, `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py:_canonical_json`, `packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py:_canonical_json`).
* **URM “read-only” posture is not uniformly enforced at the API boundary**: most URM tool calls go through policy (`apps/api/src/adeu_api/urm_routes.py:tool_call_endpoint` + `packages/urm_runtime/src/urm_runtime/capability_policy.py:authorize_action`), but `apps/api/src/adeu_api/urm_routes.py:urm_worker_run_endpoint` calls the worker runner directly; enforcement relies mainly on `packages/urm_runtime/src/urm_runtime/worker.py:CodexExecWorkerRunner` flags/role checks and deployment assumptions.
* **Maintainability hotspots are extreme enough to become correctness risks**: large, multi-responsibility modules make it hard to keep invariants intact during change (7k+ LoC `apps/api/src/adeu_api/main.py`; 15k+ LoC `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`).

**3 highest-leverage improvements**

* **Make “canonical JSON + sha256” a single contract with a conformance test suite**, then gradually consolidate implementations behind it (target the duplicated modules above; prove no behavioral change by running existing Z4/stop-gate tests in `apps/api/tests/test_tooling_z4_guards.py` and stop-gate tooling in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`).
* **Harden URM worker execution to match the repo’s “read-only claims”** by requiring sandbox support (or explicit opt-out) and gating `/urm/worker/run` under policy or an internal-only feature flag (entrypoint: `apps/api/src/adeu_api/urm_routes.py:urm_worker_run_endpoint`; execution: `packages/urm_runtime/src/urm_runtime/worker.py:_build_command`).
* **Refactor by extraction, not rewrite**: split `main.py` into routers and split `stop_gate_tools.py` into cohesive submodules while preserving public APIs and vNext continuity patterns (router inclusion pattern already exists in `apps/api/src/adeu_api/main.py` + `apps/api/src/adeu_api/urm_routes.py`; stop-gate public surface is exercised heavily by `apps/api/tests/test_urm_stop_gate_tools.py`).

---

B) Architecture map (grounded)

## High-level system map

### apps/api (endpoints, fixtures, stop-gates)

* **FastAPI app entry + most endpoint definitions**: `apps/api/src/adeu_api/main.py`

  * Core ADEU endpoints (check/propose/validator/proof/diff/artifacts/read-surface/etc) live directly here.
  * URM endpoints are mounted via router: `apps/api/src/adeu_api/urm_routes.py` (prefix `/urm`).
* **API persistence (SQLite)**: `apps/api/src/adeu_api/storage.py`

  * Tables for artifacts (`artifacts`, `concept_artifacts`, `proof_artifacts`, `explain_artifacts`, `semantic_depth_reports`, etc.).
  * Note the **idempotency semantics** for explain/semantic-depth are persisted (`client_request_id` UNIQUE) in `storage.py` (`_ensure_explain_artifact_schema`, `_ensure_semantic_depth_report_schema`).
* **Fixtures**: `apps/api/fixtures/**`

  * Stop gate manifests & run fixtures: `apps/api/fixtures/stop_gate/vnext_plus*_manifest.json`, plus referenced fixture payloads under `apps/api/fixtures/stop_gate/vnext_plus*/…`.
  * Provider parity matrix: `apps/api/fixtures/provider_parity/vnext_plus25_provider_matrix.json`.
  * Read surface catalog: `apps/api/fixtures/read_surface/vnext_plus19_catalog.json` (served via read-surface endpoints in `main.py`).
* **Tooling stop-gates & guard rails**:

  * Stop-gate computation library: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
  * CLI/script driver: `apps/api/scripts/build_stop_gate_metrics.py`
  * “Z4 fail-closed” tooling guard test: `apps/api/tests/test_tooling_z4_guards.py` (blocks provider calls + network + materialization/policy flow side effects, and snapshots locked surfaces).

### packages/* (schemas, runtime helpers, hashing/canonicalization, etc.)

* **ADEU IR schema + helpers**: `packages/adeu_ir/…`

  * Pydantic models + schema version contract: `packages/adeu_ir/src/adeu_ir/models.py`
  * Stable IDs: `packages/adeu_ir/src/adeu_ir/ids.py`
  * Schema export: `packages/adeu_ir/src/adeu_ir/export_schema.py` → outputs in `packages/adeu_ir/schema/*.json` and `spec/*.schema.json`
* **Kernel (deterministic checking / Z3 / proof plumb)**: `packages/adeu_kernel/…`

  * ADEU checker: `packages/adeu_kernel/src/adeu_kernel/checker.py` (`check_with_validator_runs`)
  * Validator runs (Z3 / proof hooks): `packages/adeu_kernel/src/adeu_kernel/validator.py`
  * JSON patch application constraints: `packages/adeu_kernel/src/adeu_kernel/patching.py` (delegates to `adeu_patch_core`)
  * Evidence hashing: `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`
* **Patch core (shared patch constraints)**: `packages/adeu_patch_core/src/adeu_patch_core/core.py`

  * Enforces patch op allowlists, path prefix allowlists, size budgets, and deterministic failure modes (`validate_patch`, `apply_patch`).
* **Concepts**: `packages/adeu_concepts/…`

  * Concept IR schema: `packages/adeu_concepts/src/adeu_concepts/models.py`
  * Semantic checker: `packages/adeu_concepts/src/adeu_concepts/checker.py:check_concept_ir`
  * Patch application with concept-specific constraints: `packages/adeu_concepts/src/adeu_concepts/patching.py`
* **Puzzles**: `packages/adeu_puzzles/…`

  * Puzzle IR + solve result schemas: `packages/adeu_puzzles/src/adeu_puzzles/models.py`, `packages/adeu_puzzles/schema/*.json`
* **Core IR / lanes / trust invariants / read surface**: `packages/adeu_core_ir/…`

  * Strong canonicalization + structural invariants: `packages/adeu_core_ir/src/adeu_core_ir/models.py`
  * Read surface payload schema and ordering constraints: `packages/adeu_core_ir/src/adeu_core_ir/read_surface_payload.py`
  * Trust invariant packet: `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py`
  * Normative advice packet: `packages/adeu_core_ir/src/adeu_core_ir/normative_advice_packet.py`
  * Lane report: `packages/adeu_core_ir/src/adeu_core_ir/lane_report.py`
* **Explain/diff**: `packages/adeu_explain/src/adeu_explain/models.py` + `packages/adeu_explain/src/adeu_explain/diffing.py`
* **Semantic depth**: `packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py` (report validation + hashing glue; schema snapshot test exists in `apps/api/tests/test_semantic_depth_report_schema.py`)
* **Lean bridge**: `packages/adeu_lean/src/adeu_lean/runner.py` (Lean proof-check runner; captures lean version in result via `_lean_version`)
* **URM runtime (policy, worker, storage, stop-gates)**: `packages/urm_runtime/…`

  * Policy + allowlists: `packages/urm_runtime/src/urm_runtime/capability_policy.py`
  * Worker runner (Codex exec): `packages/urm_runtime/src/urm_runtime/worker.py`
  * Stop-gate tooling: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
  * Packaged policy resources: `packages/urm_runtime/src/urm_runtime/policy/*.json` (also mirrored in repo root `policy/*.json` and selected at runtime in `capability_policy.py:_load_policy_bytes`)
* **URM domain tool packs**:

  * ADEU: `packages/urm_domain_adeu/src/urm_domain_adeu/domain.py`
  * Digest: `packages/urm_domain_digest/src/urm_domain_digest/domain.py`
  * Paper: `packages/urm_domain_paper/src/urm_domain_paper/domain.py`

### apps/web (if present)

* Next.js UI: `apps/web/src/app/**`

  * TS types generated from schemas: `apps/web/scripts/gen-types.mjs` → outputs under `apps/web/src/types/*.ts` (currently ADEU IR + check report).
  * UI currently carries manual Concept types in `apps/web/src/app/concepts/page.tsx` (drift risk vs `packages/adeu_concepts/schema/adeu.concepts.v0.json`).

### packages/adeu_lean (if present)

* Lean request/runner and models: `packages/adeu_lean/src/adeu_lean/models.py`, `packages/adeu_lean/src/adeu_lean/runner.py`.

## Latest vNext lock state from docs/

* **Newest locked continuation doc**: `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
* **Newest stop-gate decision doc (draft)**: `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`

  * References the closeout artifacts `artifacts/stop_gate/metrics_v26_closeout.json` and `artifacts/stop_gate/report_v26_closeout.md`.
* **Newest stop-gate manifest**: `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json` (and it is included in the Z4 locked surface snapshot in `apps/api/tests/test_tooling_z4_guards.py:_z4_mutable_surface_paths`).

## Current hard contracts and enforcement points

### Schema contracts (shape/version)

* **ADEU IR (`adeu.ir.v0`)**:

  * Contract definition: `packages/adeu_ir/src/adeu_ir/models.py:AdeuIR`
  * JSON schema export artifact: `packages/adeu_ir/schema/adeu.ir.v0.json` and `spec/adeu.ir.v0.schema.json` (exporter: `packages/adeu_ir/src/adeu_ir/export_schema.py`)
  * Enforced at runtime by kernel entry: `packages/adeu_kernel/src/adeu_kernel/checker.py:check_with_validator_runs` (`AdeuIR.model_validate`)
* **Check report (`adeu.check_report.v0`)**: `packages/adeu_ir/src/adeu_ir/models.py:CheckReport`, schema in `packages/adeu_ir/schema/adeu.check_report.v0.json`
* **Concept IR (`adeu.concepts.v0`)**: `packages/adeu_concepts/src/adeu_concepts/models.py:ConceptIR`, schema in `packages/adeu_concepts/schema/adeu.concepts.v0.json`
* **Puzzle IR + solve result**: `packages/adeu_puzzles/src/adeu_puzzles/models.py`, schemas in `packages/adeu_puzzles/schema/*.json`
* **Core IR + lane/read-surface/trust packets**: contract in `packages/adeu_core_ir/src/adeu_core_ir/*.py` (e.g., `read_surface_payload.py`, `trust_invariant_packet.py`, `normative_advice_packet.py`), schema export in `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py` → `spec/adeu_core_ir.schema.json`, etc.
* **URM policy + runtime event contracts**: `packages/urm_runtime/src/urm_runtime/models.py`, plus JSON policy resources `policy/*.json` and `packages/urm_runtime/src/urm_runtime/policy/*.json` loaded/validated in `packages/urm_runtime/src/urm_runtime/capability_policy.py`

### Semantic contracts (meaningful invariants beyond shape)

* **Kernel semantics (conflicts, exception gating, proof obligations)** enforced in `packages/adeu_kernel/src/adeu_kernel/checker.py` + `packages/adeu_kernel/src/adeu_kernel/validator.py` (Z3 model & unsat core extraction ordering in `validator.py`, deterministic assertion naming in `checker.py:_assertion_name`).
* **Patch discipline (size/prefix/op restrictions)** enforced by `packages/adeu_patch_core/src/adeu_patch_core/core.py` and used in both kernel and concepts patching (`packages/adeu_kernel/src/adeu_kernel/patching.py`, `packages/adeu_concepts/src/adeu_concepts/patching.py`).
* **Trust/lane separation constraints** are explicit and validated (e.g., canonical ordering of lane report rows in `packages/adeu_core_ir/src/adeu_core_ir/lane_report.py:AdeuLaneReport`; trust invariant ordering constraints in `packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py:AdeuTrustInvariantPacket`).
* **URM policy “writes_allowed/approvals” enforcement** is explicit in `packages/urm_runtime/src/urm_runtime/capability_policy.py:authorize_action` and invoked by `/urm/tools/call` endpoint in `apps/api/src/adeu_api/urm_routes.py:tool_call_endpoint`.

### Evidence / reporting

* Stop-gate metrics + markdown: `artifacts/stop_gate/metrics_v26_closeout.json`, `artifacts/stop_gate/report_v26_closeout.md` (computed by `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` via `apps/api/scripts/build_stop_gate_metrics.py`).
* Transfer reports: `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md` and `docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md` are explicitly included in Z4 guarded surfaces (`apps/api/tests/test_tooling_z4_guards.py:_z4_mutable_surface_paths`).
* Tooling transfer report: `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md` is included conditionally if present in the same Z4 guard snapshot list.

---

C) Quality assessment by dimension (each with findings + fixes)

## 1) Determinism & replay discipline

### Observed

| Hotspot                                                                                                                                                                                                                                                                             | Risk                                                                                                       | Fix                                                                                                                                                                                                                                             |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Canonical JSON hashing duplicated across subsystems (`apps/api/src/adeu_api/hashing.py`, `packages/urm_runtime/src/urm_runtime/hashing.py`, `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`, `packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py`) | Silent drift breaks stop-gate hashes / fixture parity / idempotency hashes when one copy changes           | Define one canonical implementation + add “hashing conformance” tests that assert equivalence across all call sites before consolidating (new tests alongside `apps/api/tests/test_tooling_z4_guards.py`)                                       |
| Stop-gate replay & determinism are computed as first-class metrics (`packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:build_stop_gate_metrics` and manifest wiring in `apps/api/scripts/build_stop_gate_metrics.py`)                                                         | If a new endpoint or new surface is added without being included in active manifests, regressions can slip | Add a “manifest coverage” checklist + code-level lint/test that enforces new vNext surfaces register either a manifest entry or a guard test (pattern anchored in `apps/api/tests/test_tooling_z4_guards.py:_manifest_referenced_paths`)        |
| Z3 determinism relies on stable assertion naming + stable ordering in model extraction (`packages/adeu_kernel/src/adeu_kernel/checker.py:_assertion_name`, `packages/adeu_kernel/src/adeu_kernel/validator.py:_sort_model_items`)                                                   | Any iteration over unordered collections in check/validator could perturb unsat core or trace ordering     | Add a deterministic ordering audit: grep/guard against iterating sets/dicts without sorting in kernel paths, enforced by a test that compares canonical hash of evidence packets (`packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`) |
| Non-deterministic fields exist (timestamps/UUIDs) in persisted artifacts (`apps/api/src/adeu_api/storage.py:create_artifact`, `packages/urm_runtime/src/urm_runtime/worker.py` uses random worker_id)                                                                               | Replay/compare tooling must consistently strip/ignore these or hashes will be unstable                     | Centralize “hash excluded fields” logic for reports (stop-gate already strips many fields in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`), and add explicit tests that hashes ignore `created_at`/IDs where intended              |

### Inferred (explicitly)

* The repo assumes a **deterministic execution environment** (timezone/locale), but it’s largely documented rather than enforced. This is implied by the environment lock bullets in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` and by the fact that tooling scripts (`apps/api/scripts/build_stop_gate_metrics.py`) do not themselves set locale/timezone.

  * Why it matters: JSON schema export ordering and date formatting can be locale/timezone sensitive in edge cases.

### Practical fixes (non-breaking)

* Add a **single canonical JSON spec** as a doc string + tests first, then consolidate implementations (see backlog proposals QW1/M2).
* Add a “deterministic runtime preflight” helper invoked by tooling scripts, but default to *warn-only* to avoid breaking CI unexpectedly (see proposal M? or QW3-style script pattern).

---

## 2) Contract/schema hygiene (versioning, export wiring, drift risk)

### Observed

| Hotspot                                                                                                                                                                                                                                           | Risk                                                                           | Fix                                                                                                                                                              |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Strong schema version sentinels exist but schema exports are not uniformly regression-tested (e.g., `packages/adeu_ir/src/adeu_ir/models.py` + `packages/adeu_ir/schema/*.json`, but no dedicated sync test)                                      | Model/schema drift can land silently and only surface in downstream codegen/UI | Add schema sync tests similar to existing schema tests (pattern: `apps/api/tests/test_semantic_depth_report_schema.py`) for ADEU IR + core IR + concepts/puzzles |
| Web type generation covers only ADEU IR/check report (`apps/web/scripts/gen-types.mjs`) while Concept UI uses hand-rolled TS types (`apps/web/src/app/concepts/page.tsx`)                                                                         | Frontend/backend drift risk; runtime failures if API changes shape             | Extend `gen-types.mjs` to include concept/puzzle/core IR schemas from `packages/*/schema` / `spec/*` and adopt generated types incrementally                     |
| Policy resources are mirrored in two locations (repo root `policy/*.json` and package resources `packages/urm_runtime/src/urm_runtime/policy/*.json`, selected by `packages/urm_runtime/src/urm_runtime/capability_policy.py:_load_policy_bytes`) | Drift between “dev-in-repo” and “installed package” behavior                   | Add explicit sync tests for allow policy + instruction policies (existing lattice sync test: `apps/api/tests/test_urm_capability_lattice_sync.py`)               |

### Inferred

* The “schema discipline” invariant includes **additive-only evolution** of schemas (vNext style), implied by the proliferation of vNext+ modules and stop-gate manifests (e.g., `apps/api/fixtures/stop_gate/vnext_plus24_manifest.json`..`vnext_plus26_manifest.json`) and by locked docs `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`.

  * Recommendation: enforce additive-only changes via schema diff tooling in CI (proposal M3).

---

## 3) Runtime layering boundaries (O/D/E/U separation, trust lanes, enforcement guards)

### Observed

| Hotspot                                                                                                                                                                                                               | Risk                                                                                                                 | Fix                                                                                                                                                                                                      |
| --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Core IR/trust/lane packets encode trust lanes with strict ordering/structure (`packages/adeu_core_ir/src/adeu_core_ir/trust_invariant_packet.py`, `lane_report.py`, `normative_advice_packet.py`)                     | If upstream API endpoints emit inconsistent trust labels or omit required lane metadata, downstream invariants break | Ensure all endpoints that produce these packets validate via the Pydantic models at the boundary (and add contract tests for any endpoint returning these structures in `apps/api/src/adeu_api/main.py`) |
| Read surface is treated as “read-only / provider-free” and guarded in tooling tests (`apps/api/src/adeu_api/read_surface_runtime_guards.py`, `apps/api/tests/test_tooling_z4_guards.py`)                              | In prod, nothing stops accidental provider calls unless tests catch it                                               | Keep the guard test, but also add a runtime feature flag to enable the guard in prod for “tooling” mode (optional, non-breaking)                                                                         |
| ADEU IR itself is structurally separated into core lists but the “O/D/E” semantics are largely enforced in kernel logic (`packages/adeu_ir/src/adeu_ir/models.py`, `packages/adeu_kernel/src/adeu_kernel/checker.py`) | Layer boundary violations might be caught only deep in kernel reasons, not at schema boundary                        | Add lightweight schema-time validators for the most basic lane invariants (e.g., ensure references resolve) in models where feasible without duplicating kernel (proposal M3/E-section)                  |

### Inferred

* O/D/E/U separation is a design invariant (from the project framing), but **U** is not clearly represented as an explicit structure in `packages/adeu_ir/src/adeu_ir/models.py` (observed: no “utility” field). If U is intended, it’s currently implicit or out-of-scope.

---

## 4) Test strategy & fixture strategy (coverage, brittleness, missing negative fixtures)

### Observed

| Hotspot                                                                                                                                                      | Risk                                                                                                        | Fix                                                                                                                                                                                                      |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Strong tooling guard tests exist (provider/network deny + locked-surface snapshots) (`apps/api/tests/test_tooling_z4_guards.py`)                             | If new “locked surfaces” are added but not included in `_z4_mutable_surface_paths`, they can drift silently | Provide a single registry of locked surfaces (data file or manifest) instead of hardcoding in test; test loads it (proposal M? / strategic S2)                                                           |
| Semantic-depth schema is regression tested (`apps/api/tests/test_semantic_depth_report_schema.py`) but ADEU IR + core IR schemas are not similarly validated | Drift in core schemas isn’t caught until consumers fail                                                     | Add parallel schema sync tests for ADEU IR/core IR/concepts/puzzles (proposal M3)                                                                                                                        |
| Many fixtures are stored under `apps/api/fixtures/**` and addressed by relative paths in manifests (`apps/api/fixtures/stop_gate/vnext_plus*_manifest.json`) | Fixture path correctness becomes “stringly typed”                                                           | Add strict validation that manifests reference existing files and forbid absolute paths (or warn-only first) in stop-gate loader (`packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`), plus tests |

### Inferred

* Fixture brittleness risk: because tooling depends on repo-relative paths (e.g., `apps/api/scripts/build_stop_gate_metrics.py:_manifest_path`), running outside a git checkout may fail unless packaged resources are used. URM policy already supports this pattern (`capability_policy.py:_load_policy_bytes`), but stop-gate fixtures do not.

---

## 5) Tooling/CI cost & sustainability (runtime budget, duplication, bottlenecks)

### Observed

| Hotspot                                                                                                                                                                                  | Risk                                                                                 | Fix                                                                                                                                                                               |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Extremely large stop-gate tooling module (`packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`)                                                                                     | Hard to review, easy to introduce subtle determinism regressions                     | Split into submodules with a compatibility shim preserving `urm_runtime.stop_gate_tools` exports; rely on existing extensive tests (`apps/api/tests/test_urm_stop_gate_tools.py`) |
| API main module is monolithic (`apps/api/src/adeu_api/main.py`)                                                                                                                          | Cross-feature coupling; higher chance of “unrelated” changes breaking invariants     | Split into routers; maintain path stability; keep vNext modules untouched                                                                                                         |
| Tooling scripts assume a consistent environment but mostly don’t enforce it (`apps/api/scripts/build_stop_gate_metrics.py`; documentation in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`) | CI flakiness across environments, especially if schema generation or timestamps leak | Add a deterministic tooling preflight (warn-only at first) and record environment fingerprint as non-gating metadata in artifacts (proposal S2)                                   |

---

## 6) API surface design (idempotency, caching headers, response envelopes)

### Observed

| Hotspot                                                                                                                                                                                                                | Risk                                                                                                                                                | Fix                                                                                                                                                                           |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Persistent idempotency for semantic-depth and explain materialize (`apps/api/src/adeu_api/main.py:semantic_depth_materialize_endpoint`, `explain_materialize_endpoint` + tables in `apps/api/src/adeu_api/storage.py`) | Good; but other flows still use in-memory idempotency (`apps/api/src/adeu_api/main.py:_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`) which is process-local | Move remaining idempotency caches to storage (additive DB migration) or make it explicit in API docs that core-ir proposer idempotency is best-effort (proposal M5)           |
| Read surface has explicit caching semantics (`apps/api/src/adeu_api/main.py:_set_read_surface_cache_header`)                                                                                                           | Other read-only endpoints may be uncached, increasing load                                                                                          | Add ETag/Cache-Control for fixture-backed endpoints (non-breaking), but only where response is immutable by lock                                                              |
| Some endpoints use “format=legacy vs packet” union returns (diff endpoint: `apps/api/src/adeu_api/main.py:diff_endpoint`)                                                                                              | Client complexity; response type depends on query param                                                                                             | Keep additive approach but consider new explicit `/diff/packet` endpoint or include a mandatory `schema` discriminator in both formats (proposal M4-ish / API evolution plan) |

---

## 7) Security/abuse considerations (esp. “read-only” claims: how enforced)

### Observed

| Hotspot                                                                                                                                                                                                 | Risk                                                                                                                                   | Fix                                                                                                                                        |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------ |
| URM policy gating exists and is used for tool calls (`packages/urm_runtime/src/urm_runtime/capability_policy.py:authorize_action`, invoked by `apps/api/src/adeu_api/urm_routes.py:tool_call_endpoint`) | Strong baseline                                                                                                                        | Add coverage tests ensuring every externally reachable “action” endpoint routes through `authorize_action` (proposal M? / QW?)             |
| `/urm/worker/run` bypasses policy gating (`apps/api/src/adeu_api/urm_routes.py:urm_worker_run_endpoint`)                                                                                                | If endpoint is exposed, callers can execute Codex runs without approvals/session checks; role allowlist is not a substitute for policy | Either gate the endpoint with policy (requires session context) or make it internal-only behind env flag; add migration (proposal M? / S?) |
| Worker runner “read-only” depends on Codex flags, but runner will run even if flags unsupported (`packages/urm_runtime/src/urm_runtime/worker.py:_build_command` uses `_supports_flag`)                 | “Read-only” claim can be false on older Codex; this is a safety gap                                                                    | Add `URM_REQUIRE_CODEX_SANDBOX` default true; fail closed unless explicit opt-out; test with fake codex help output (proposal QW4)         |

### Inferred

* There is no authentication/authorization at the general API layer in-repo (observed: `apps/api/src/adeu_api/main.py` adds CORS but no auth middleware). This likely relies on deployment perimeter controls. If that perimeter is relaxed, several endpoints become abuse vectors (LLM calls, worker runs, artifact storage growth). This is a deployment assumption, not a repo-enforced invariant.

---

## 8) Maintainability hotspots (duplication, large modules, unclear naming)

### Observed

| Hotspot                                                                                                                                                                                                                                        | Risk                                                        | Fix                                                                           |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------- | ----------------------------------------------------------------------------- |
| `apps/api/src/adeu_api/main.py` combines request models, endpoint handlers, caching logic, fixture plumbing, and vNext wiring                                                                                                                  | High coupling; changes are harder to keep within invariants | Router/module split; preserve endpoint paths; keep old imports for continuity |
| `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` is a “god module” (manifest parsing + metrics + markdown rendering + parity tooling + CLI)                                                                                           | Review/ownership bottleneck; refactors become risky         | Split into cohesive submodules with explicit public API and strict tests      |
| Duplicated “repo root discovery” logic across modules (`packages/urm_runtime/src/urm_runtime/capability_policy.py:_discover_repo_root`, `packages/urm_runtime/src/urm_runtime/policy_tools.py:_discover_repo_root`, and various scripts/tests) | Inconsistent behavior when packaged vs repo-run             | Centralize in one helper and re-export; keep behavior identical               |

---

D) Concrete refactor proposals (prioritized backlog)

### Quick wins (1–2 days)

#### QW1) Hashing/canonical-json conformance tests (no behavior change)

* **Why**: Determinism depends on canonical JSON being *identical everywhere*, but implementations are duplicated and could drift silently.
* **Where**:

  * `apps/api/src/adeu_api/hashing.py`
  * `packages/urm_runtime/src/urm_runtime/hashing.py`
  * `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py` (local `_canonical_json`)
  * `packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py` (local `_canonical_json`)
* **What change**: Add a single pytest module that feeds a representative nested payload and asserts **byte-for-byte** equality of canonical JSON strings and sha256 digests across these modules.
* **Risk**: Low; only adds tests.
* **How to prove safe**: Run existing stop-gate/Z4 tests unchanged (`apps/api/tests/test_tooling_z4_guards.py`, `apps/api/tests/test_urm_stop_gate_tools.py`).
* **Small green commit plan**:

  1. Add `apps/api/tests/test_hashing_conformance.py` with canonical payload and assertions.
  2. Add one “known tricky payload” case (unicode, floats, nested dict ordering) to prevent future regressions.
  3. Wire into CI (if CI config exists in repo; otherwise keep as pytest default discovery).

#### QW2) Add policy resource sync test (repo root vs packaged resources)

* **Why**: URM policy loader conditionally uses repo-root `policy/*.json` or package resources `packages/urm_runtime/src/urm_runtime/policy/*.json` (`capability_policy.py:_load_policy_bytes`). Drift is a real footgun.
* **Where**:

  * Repo policy files: `policy/urm.allow.v1.json`, `policy/urm.capability_lattice.v1.json`, etc.
  * Packaged copies: `packages/urm_runtime/src/urm_runtime/policy/*.json`
  * Tests: add beside `apps/api/tests/test_urm_capability_lattice_sync.py`
* **What change**: Extend sync testing to at least `urm.allow.v1.json` (lattice already has a sync test).
* **Risk**: Low; test may fail if drift already exists (which is good).
* **How to prove safe**: Tests passing implies no behavior change; only enforces an invariant already assumed by runtime selection logic.
* **Small green commit plan**:

  1. Add `apps/api/tests/test_urm_policy_resource_sync.py` comparing canonical JSON hashes of repo vs package copies.
  2. (If mismatch) update the drifting file(s) by copying canonical source (single commit per file).
  3. Add a short comment in the test pointing to `capability_policy.py:_load_policy_bytes` as the reason.

#### QW3) Implement the missing “S9 trigger check” script referenced by lock docs

* **Why**: `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` references `apps/api/scripts/check_s9_triggers.py`, but that script does not exist (observed absence in `apps/api/scripts/`). This is a tooling/documentation integrity gap.
* **Where**:

  * New: `apps/api/scripts/check_s9_triggers.py`
  * Input metrics: `artifacts/stop_gate/metrics_v25_closeout.json` (as used in `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`)
* **What change**: Add a script that reads the stop-gate metrics JSON and verifies required trigger metrics (as listed in `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`), emitting the same summary fields (`required_metrics`, `observed`, `all_passed`, etc.).
* **Risk**: Low; additive tooling only.
* **How to prove safe**: Add a unit test comparing script output to expected (or at least checking `all_passed` for the repo’s checked-in metrics).
* **Small green commit plan**:

  1. Create script with CLI args: `--metrics-path` defaulting to `artifacts/stop_gate/metrics_v25_closeout.json`.
  2. Add `apps/api/tests/test_check_s9_triggers_script.py` asserting it returns success and expected fields.
  3. Optionally add a `--json` / `--pretty` output mode to support doc copy/paste.

#### QW4) Fail-closed on missing Codex sandbox support (with explicit opt-out)

* **Why**: The repo claims “read-only” URM worker execution, but `CodexExecWorkerRunner` will run even if the Codex binary doesn’t support `--sandbox` (`packages/urm_runtime/src/urm_runtime/worker.py:_supports_flag` / `_build_command`). That can violate “read-only” invariants.
* **Where**:

  * `packages/urm_runtime/src/urm_runtime/worker.py:_build_command`
  * `packages/urm_runtime/src/urm_runtime/config.py:URMRuntimeConfig.from_env`
  * Tests: `apps/api/tests/test_urm_worker_runner.py`
* **What change**:

  * Add config/env `URM_REQUIRE_CODEX_SANDBOX` (default **true**) so worker fails with a clear `URMError` if sandbox flag unsupported.
  * Provide migration: allow setting `URM_REQUIRE_CODEX_SANDBOX=0` to preserve old behavior temporarily.
* **Risk**: Medium-low; could break environments running older Codex, but explicit opt-out provides continuity.
* **How to prove safe**: Extend worker runner tests to cover both paths (sandbox supported vs unsupported) by patching `_supports_flag` or by using fake codex help output.
* **Small green commit plan**:

  1. Add config flag + parsing in `URMRuntimeConfig` (`config.py`).
  2. Implement fail-closed branch in `_build_command` (`worker.py`).
  3. Add/adjust tests in `apps/api/tests/test_urm_worker_runner.py`.
  4. Document env var in `docs/LOCKED_URM_CODEX_INTEGRATION_v0.md` (if that doc exists) or in `README.md`.

#### QW5) Make StopGateMetricsInput kwarg wiring strict (without breaking legacy)

* **Why**: `StopGateMetricsInput.from_legacy_kwargs` silently ignores unknown keys (it enumerates known keys and calls `kwargs.get(key)` in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:StopGateMetricsInput.from_legacy_kwargs`). Silent typos can lead to missing manifest paths and misleading metrics.
* **Where**:

  * `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:StopGateMetricsInput.from_legacy_kwargs`
  * `apps/api/scripts/build_stop_gate_metrics.py`
  * Tests: `apps/api/tests/test_urm_stop_gate_tools.py`
* **What change**:

  * Add `strict: bool = False` parameter; when strict, raise on unknown keys.
  * Update scripts to call strict mode (scripts are controlled entrypoints).
* **Risk**: Low if default stays non-strict.
* **How to prove safe**: Existing call sites still work (default non-strict), scripts become safer, and stop-gate tests remain stable.
* **Small green commit plan**:

  1. Add `strict` parameter and unknown-key detection.
  2. Update `apps/api/scripts/build_stop_gate_metrics.py` to use strict mode.
  3. Add a unit test that introduces a misspelled key and asserts it fails in strict mode.

---

### Medium (up to 1–2 weeks)

#### M1) Split `apps/api` monolith into routers (no path changes)

* **Why**: `apps/api/src/adeu_api/main.py` mixes many concerns (endpoint logic + request models + caching + fixture plumbing), which increases risk of invariant regressions during change.
* **Where**:

  * Primary: `apps/api/src/adeu_api/main.py`
  * New modules: `apps/api/src/adeu_api/routes/*.py` (or similar)
* **What change**:

  * Extract cohesive endpoint groups into routers: e.g., `routes/check.py`, `routes/concepts.py`, `routes/puzzles.py`, `routes/read_surface.py`, `routes/explain.py`, `routes/core_ir.py`.
  * Keep `main.py` as the composition root, preserving all existing path strings and OpenAPI tags.
* **Risk**: Medium (import cycles; missing shared helpers; minor OpenAPI diffs).
* **How to prove safe**:

  * Run full API test suite, especially tooling guards (`apps/api/tests/test_tooling_z4_guards.py`) and URM tests.
  * Snapshot the generated OpenAPI (if you already snapshot it somewhere; if not, add a stable “endpoint inventory” test).
* **Small green commit plan** (incremental extraction):

  1. Create `routes/read_surface.py`; move only read-surface GET endpoints and `_set_read_surface_cache_header` (since it’s already cohesive in `main.py`).
  2. Create `routes/explain.py`; move `diff_endpoint`, `explain_materialize_endpoint`, and related request/response models.
  3. Create `routes/semantic_depth.py`; move semantic depth endpoints and idempotency plumbing.
  4. Create `routes/artifacts.py`; move list/get endpoints.
  5. Continue with concepts/puzzles/core-ir as separate commits; each commit keeps all paths identical.

#### M2) Split `stop_gate_tools.py` into a package while keeping a compatibility shim

* **Why**: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` is too large to safely evolve; it’s also the spine of stop-gate discipline and is heavily relied upon in tests/scripts.
* **Where**:

  * Current: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
  * New: `packages/urm_runtime/src/urm_runtime/stop_gate/` (modules: `manifest.py`, `metrics.py`, `render.py`, `inputs.py`, `parity.py`, etc.)
* **What change**:

  * Move internal helpers into new modules; keep `stop_gate_tools.py` exporting the same public API (`StopGateMetricsInput`, `build_stop_gate_metrics`, `stop_gate_markdown`, etc.).
  * No signature changes; no behavior changes.
* **Risk**: Medium (accidental behavior drift; import cycles).
* **How to prove safe**:

  * Run stop-gate tests (`apps/api/tests/test_urm_stop_gate_tools.py`) and tooling guard tests (`apps/api/tests/test_tooling_z4_guards.py`).
  * Assert `artifacts/stop_gate/report_v26_closeout.md` can be reproduced byte-for-byte in a controlled environment (if you have a reproducible script).
* **Small green commit plan**:

  1. Add new package directory + empty modules; move only constants/types first (no logic).
  2. Move manifest parsing/resolution functions.
  3. Move metric evaluation functions.
  4. Move markdown rendering.
  5. Keep `stop_gate_tools.py` as a thin import/re-export shim; ensure CLI entry still works.

#### M3) Add schema export synchronization tests for key schemas

* **Why**: Schema discipline is strong, but drift between `model_json_schema()` output and checked-in `packages/*/schema/*.json` / `spec/*.schema.json` is not uniformly guarded (semantic depth has such a guard; ADEU IR does not).
* **Where**:

  * Exporters: `packages/adeu_ir/src/adeu_ir/export_schema.py`, `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`, `packages/adeu_concepts/src/adeu_concepts/export_schema.py` (if present), `packages/adeu_puzzles/src/adeu_puzzles/export_schema.py` (if present)
  * Schema files: `packages/adeu_ir/schema/*.json`, `packages/adeu_concepts/schema/*.json`, `packages/adeu_puzzles/schema/*.json`, `spec/*.schema.json`
  * Tests: add under `apps/api/tests/` (pattern from `apps/api/tests/test_semantic_depth_report_schema.py`)
* **What change**:

  * For each schema, compute model_json_schema in test, canonicalize via canonical JSON (to neutralize key order), compare to checked-in schema.
* **Risk**: Medium (schema generation can change with dependency bumps; but that’s exactly what you want to detect under “locks”).
* **How to prove safe**: If tests pass, schema exports are consistent. If they fail, you have a clear “regenerate schema” path via existing export scripts.
* **Small green commit plan**:

  1. Add a helper test function `assert_schema_matches(model, path)` using canonical JSON.
  2. Add ADEU IR + check report schema tests.
  3. Add concepts + puzzles schema tests.
  4. Add core IR schema tests.
  5. Update CI docs/Makefile with a `make export-schemas` target if needed.

#### M4) Expand web type generation to cover Concepts/Puzzles/Core IR (drift reduction)

* **Why**: UI currently uses generated types only for ADEU IR/check report (`apps/web/scripts/gen-types.mjs`), but has hand-rolled types for Concepts (e.g., `apps/web/src/app/concepts/page.tsx`).
* **Where**:

  * `apps/web/scripts/gen-types.mjs`
  * Inputs: `packages/adeu_concepts/schema/adeu.concepts.v0.json`, `packages/adeu_puzzles/schema/*.json`, core IR schemas in `spec/*.schema.json` (e.g., `spec/adeu_core_ir.schema.json`)
  * UI usage sites: `apps/web/src/app/concepts/page.tsx` (incremental adoption)
* **What change**:

  * Add additional schema compilations to `gen-types.mjs`; write outputs into `apps/web/src/types/`.
  * Adopt generated types in UI incrementally (no big rewrite).
* **Risk**: Medium (TS build breaks if schema-to-types adds stricter types).
* **How to prove safe**: `pnpm typecheck` and `pnpm build` should pass; no runtime change.
* **Small green commit plan**:

  1. Add schema compilation targets for Concepts/Puzzles into `gen-types.mjs`.
  2. Commit generated types (or keep generated artifacts out of repo if that’s your norm; repo currently has `apps/web/src/types/adeu-ir.ts`, so committing is consistent).
  3. Update one UI page (concepts) to import generated types in a narrow slice.
  4. Add a simple CI check that `pnpm gen-types && git diff --exit-code` (optional).

#### M5) Persist core-ir proposer idempotency (align with other materialize flows)

* **Why**: Core IR proposer uses in-memory idempotency map (`apps/api/src/adeu_api/main.py:_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`), while semantic depth/explain have persisted idempotency (`apps/api/src/adeu_api/storage.py` tables with unique `client_request_id`). Process-local idempotency is brittle under multi-worker deployment.
* **Where**:

  * `apps/api/src/adeu_api/main.py` (core IR proposer endpoints)
  * `apps/api/src/adeu_api/storage.py` (add a new table, e.g., `core_ir_proposals`)
* **What change**:

  * Add a new table keyed by `client_request_id` (or `idempotency_key`) with stored response + request hash.
  * Keep the in-memory cache as a fallback during migration, but prefer DB lookup when available.
* **Risk**: Medium (DB migration, subtle conflict semantics).
* **How to prove safe**:

  * Unit tests mirroring the explain/semantic-depth idempotency conflict behavior in `main.py` (pattern: conflict when same `client_request_id` but different request hash).
  * No changes to response shape.
* **Small green commit plan**:

  1. Add schema migration in `storage.py` (new table + indexes).
  2. Implement storage helpers: `get_core_ir_proposal_by_client_request_id`, `create_core_ir_proposal`.
  3. Modify endpoint to use DB first, then fallback to in-memory (feature flag if needed).
  4. Add tests for exact idempotency semantics.

---

### Strategic (multi-arc)

#### S1) Content-addressed artifacts (hash-based addressing) with additive migration

* **Why**: Determinism and replay get much easier if “artifact identity” is content-derived rather than random UUIDs. Today, artifacts are UUID-based (`apps/api/src/adeu_api/storage.py:create_artifact`, `create_concept_artifact`), which complicates cross-run reproducibility and caching.
* **Where**:

  * Storage: `apps/api/src/adeu_api/storage.py` tables (`artifacts`, `concept_artifacts`, etc.)
  * Hashing: canonical JSON functions used by artifact materializers (`apps/api/src/adeu_api/hashing.py`, plus any payload hash stored/derived)
  * API endpoints that accept artifact IDs: `apps/api/src/adeu_api/main.py` read endpoints
* **What change** (additive plan):

  * Add a new column `content_hash` (sha256 over canonicalized content) and a new “content address” `artifact_ref` format like `sha256:<hash>`.
  * Endpoints accept both legacy UUID artifact IDs and new content-address refs.
  * On create: compute `content_hash`; optionally de-duplicate inserts if content already exists (idempotent create).
* **Risk**: High (DB migration + API semantics + de-dup interactions).
* **How to prove safe**:

  * Preserve legacy paths fully (UUID remains primary key or remains accepted).
  * Add stop-gate metric comparing old behavior vs new for a set of fixtures (add a new vNext+ manifest entry under `apps/api/fixtures/stop_gate/`).
* **Small green commit plan**:

  1. Add new nullable `content_hash` columns + indexes; backfill for existing rows.
  2. Add read helpers that can resolve either UUID or `sha256:` ref.
  3. Add write path that computes content_hash but still writes UUID id.
  4. Add optional de-dup mode (feature flag) that reuses existing row if same content_hash.
  5. Add stop-gate fixtures & manifest entry to prove stable behavior.
  6. Gradually update internal callers (read surface / trust packets) to prefer content refs.

#### S2) A unified “replay harness” that produces a deterministic attestation artifact

* **Why**: You already have determinism oracles (`apps/api/src/adeu_api/determinism_oracles.py`) and stop-gate metrics (`packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`), plus tooling guards (`apps/api/tests/test_tooling_z4_guards.py`). What’s missing is one **single, explicit “replay harness” artifact** that captures: env fingerprint, manifest set, outputs, and hashes.
* **Where**:

  * Harness core: likely `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (or new `urm_runtime/replay_harness.py`)
  * Driver script: `apps/api/scripts/build_stop_gate_metrics.py` (extend or add a sister script)
  * Output artifacts: `artifacts/stop_gate/*`
* **What change**:

  * Add an “attestation” JSON output alongside metrics/report that includes non-gating environment fingerprint (Python version, platform, tz, locale), and the exact manifest hashes/paths used.
  * Ensure the attestation’s *hash basis* excludes env fields, consistent with determinism invariants, but records them for debugging.
* **Risk**: Medium-high (new artifact schema; need to keep additive and excluded from existing lock hashes unless intentionally locked).
* **How to prove safe**:

  * Add the attestation as **additive** output; do not modify existing metrics hash computation.
  * Add a stop-gate rule that attestation exists and includes required fields, but does not gate on values.
* **Small green commit plan**:

  1. Define `attestation@0.1` schema (new file under `spec/`).
  2. Implement builder that collects env + manifest set + tool versions.
  3. Emit attestation in build script.
  4. Add tests asserting presence and schema validity.

#### S3) Expand Lean proof coverage from “core obligations” to “schema + patch + lane invariants”

* **Why**: `packages/adeu_lean/src/adeu_lean/runner.py` already proves a small set of obligations (`OBLIGATION_KINDS`) and captures lean version. You can leverage this to formalize invariants you currently enforce only by tests/validators (patch constraints, lane ordering, conflict candidate soundness boundaries).
* **Where**:

  * Lean runner and obligation builder: `packages/adeu_lean/src/adeu_lean/runner.py`
  * Proof evidence plumbing: kernel proof/evidence paths (`packages/adeu_kernel/src/adeu_kernel/proof.py`, plus evidence packets if present)
  * Candidate new Lean theorems in the Lean project under `packages/adeu_lean/` (Lean source tree)
* **What change**:

  * Add new obligation kinds for: “patch op constraints preserve well-formedness” (mirroring `packages/adeu_patch_core/src/adeu_patch_core/core.py` invariants) and “lane report ordering is a total order” (mirroring `packages/adeu_core_ir/src/adeu_core_ir/lane_report.py`).
  * Keep it additive: new obligations do not replace existing ones; they just add evidence fields.
* **Risk**: High (Lean dev cost, proof maintenance, CI runtime).
* **How to prove safe**:

  * Gate only on “proof compiles” for a small fixed set initially; treat as non-blocking stop-gate until stabilized.
* **Small green commit plan**:

  1. Add new obligation kind in `adeu_lean/models.py` + runner maps in `runner.py`.
  2. Add Lean theorem stubs + proofs in Lean project.
  3. Thread new obligations into proof request building (kernel).
  4. Add a new stop-gate metric “lean_obligation_coverage_pct” as informational.
  5. Stabilize and then promote to gating.

---

E) Invariant gaps (what’s *not* yet formalized)

1. **Canonical JSON is a global invariant but not a single encoded contract**

* **Observed reliance**: multiple canonicalization implementations (`apps/api/src/adeu_api/hashing.py`, `packages/urm_runtime/src/urm_runtime/hashing.py`, `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`, `packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py`).
* **Gap**: no single “authoritative” module + no test asserting equivalence across all.
* **Encode it**: **runtime check + unit tests** first (QW1), then consolidate to a single module (M2/S2).

2. **“Read-only” worker execution is assumed, not guaranteed**

* **Observed reliance**: `CodexExecWorkerRunner` uses `--sandbox read-only` when supported, but can run without it (`packages/urm_runtime/src/urm_runtime/worker.py:_build_command`).
* **Gap**: invariant “worker runs are read-only” is not enforced when flags are unavailable.
* **Encode it**: **runtime check (fail closed)** in worker runner (QW4) + a **stop-gate** that asserts sandbox enforcement is active (S2).

3. **Every URM side-effecting action should go through `authorize_action`, but not all endpoints do**

* **Observed**: tool calls do (`apps/api/src/adeu_api/urm_routes.py:tool_call_endpoint`), worker/run does not (`apps/api/src/adeu_api/urm_routes.py:urm_worker_run_endpoint`).
* **Gap**: invariant “policy gates everything that can do work” is partial.
* **Encode it**: **runtime check** (endpoint gating) + **test** that enumerates URM endpoints and asserts policy usage for those that can mutate (new test beside URM route tests).

4. **Schema export drift is not uniformly prevented**

* **Observed**: semantic depth schema is tested (`apps/api/tests/test_semantic_depth_report_schema.py`), but ADEU IR/core IR schemas are not.
* **Gap**: invariant “checked-in schemas match runtime models” is not encoded.
* **Encode it**: **CI/unit test** (M3) and optionally a **stop-gate** metric that fails when schema sync breaks.

5. **Stop-gate manifest path safety/validity is not consistently enforced at load time**

* **Observed**: Z4 guard test snapshots referenced paths (`apps/api/tests/test_tooling_z4_guards.py:_manifest_referenced_paths` + `_path_snapshot_hash`), but stop-gate loader path resolution doesn’t obviously forbid absolute paths (`packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_resolve_manifest_relative_path`).
* **Gap**: invariant “manifests only reference repo-contained files” is implicit.
* **Encode it**: **runtime check** in stop-gate loader (warn-only → fail-closed) + **stop-gate** validation step.

6. **Idempotency semantics are inconsistent across endpoints**

* **Observed**: persisted idempotency for explain/semantic depth (`apps/api/src/adeu_api/storage.py`), but in-memory for core-ir proposer (`apps/api/src/adeu_api/main.py:_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`).
* **Gap**: invariant “idempotency is stable across deployments” is only partially true.
* **Encode it**: **storage-level contract** (M5) + optionally a **stop-gate** replay test for proposer endpoints.

7. **“Locked surfaces” registry is encoded in tests, not as a formal data artifact**

* **Observed**: the list of paths considered locked is computed in code (`apps/api/tests/test_tooling_z4_guards.py:_z4_mutable_surface_paths`).
* **Gap**: invariant “these are the locked continuity surfaces” is not expressed as data (harder to audit/change).
* **Encode it**: **stop-gate manifest extension or dedicated lock registry file** (S2), and keep the test as the enforcement mechanism.

8. **Lean proofs exist but only cover a small obligation set; many invariants remain “test-only”**

* **Observed**: obligations are limited to three kinds (`packages/adeu_lean/src/adeu_lean/models.py:OBLIGATION_KINDS`, `runner.py:_OBLIGATION_TO_CORE_THEOREM`).
* **Gap**: invariants like patch constraints and lane ordering are not formally proved.
* **Encode it**: **Lean proofs** for selected invariants (S3), initially non-gating.

---

F) Suggested next actions

## PR 1: “Hashing invariants: conformance tests + policy resource sync”

* **Why**: Immediately reduces the probability of silent determinism drift and policy-packaging drift without changing runtime behavior.
* **Files touched**:

  * `apps/api/tests/test_hashing_conformance.py` (new)
  * `apps/api/tests/test_urm_policy_resource_sync.py` (new)
  * Potentially update drifting files in `policy/` or `packages/urm_runtime/src/urm_runtime/policy/` if the sync test reveals mismatch
* **Acceptance criteria**:

  * Tests prove canonical JSON + sha256 matches across `adeu_api.hashing`, `urm_runtime.hashing`, and kernel/semantic-depth canonicalizers.
  * Repo-root policy JSON and packaged policy JSON match (at least `urm.allow.v1.json`), or the PR includes the sync fix.

## PR 2: “URM worker hardening: require sandbox (fail-closed) with opt-out”

* **Why**: Aligns implementation with the repo’s “read-only” security posture; closes the largest enforcement gap with minimal surface change.
* **Files touched**:

  * `packages/urm_runtime/src/urm_runtime/config.py` (add `URM_REQUIRE_CODEX_SANDBOX`)
  * `packages/urm_runtime/src/urm_runtime/worker.py` (enforce sandbox support in `_build_command`)
  * `apps/api/tests/test_urm_worker_runner.py` (add tests for sandbox-required behavior)
* **Acceptance criteria**:

  * When Codex flags are unsupported and `URM_REQUIRE_CODEX_SANDBOX=1`, worker run fails with a clear structured `URMError`.
  * When `URM_REQUIRE_CODEX_SANDBOX=0`, behavior matches current (legacy compatibility).
  * No changes to stop-gate metrics output and Z4 tooling guard still passes.

## PR 3: “Tooling continuity integrity: implement check_s9_triggers + strict StopGateMetricsInput wiring”

* **Why**: Removes a doc/tooling inconsistency and prevents silent miswiring of stop-gate inputs—both directly strengthen continuity.
* **Files touched**:

  * `apps/api/scripts/check_s9_triggers.py` (new)
  * `apps/api/tests/test_check_s9_triggers_script.py` (new)
  * `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (`StopGateMetricsInput.from_legacy_kwargs(strict=…)`)
  * `apps/api/scripts/build_stop_gate_metrics.py` (use strict mode)
* **Acceptance criteria**:

  * Script exists at the documented path and reproduces the “S9 trigger check” summary shape used in `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`.
  * Stop-gate build scripts fail fast on unknown/misspelled kwargs (strict mode), preventing partial stop-gate runs.
  * Existing stop-gate tests (`apps/api/tests/test_urm_stop_gate_tools.py`) still pass unchanged.
