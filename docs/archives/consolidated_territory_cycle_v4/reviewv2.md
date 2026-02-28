## 1) Current Architecture Snapshot (repo-grounded)

### 1.1 Dependency sketch of major components (observed)

**Monorepo layout**

* API server: `apps/api/src/adeu_api/main.py` (FastAPI app, 7,424 LOC), mounts URM router `apps/api/src/adeu_api/urm_routes.py` via `app.include_router(urm_router)` in `main.py` (see `apps/api/src/adeu_api/main.py`).
* URM runtime/tooling: `packages/urm_runtime/src/urm_runtime/*` (policy evaluation, worker runner, stop-gate tooling, transfer reports).
* Core IR: `packages/adeu_core_ir/src/adeu_core_ir/*` (schema + canonicalization + pipeline-ish helpers).
* Kernel: `packages/adeu_kernel/src/adeu_kernel/*` (checker/validator/proof + evidence builders).
* IR: `packages/adeu_ir/src/adeu_ir/*` (base schemas and repo-root helper).
* Web UI: `apps/web/*` (Next.js), typegen script `apps/web/scripts/gen-types.mjs`.
* Lean integration: `packages/adeu_lean/src/adeu_lean/*` (Lean runner + models).

**Declared package deps (pyproject-based)**

* `apps/api/pyproject.toml` depends on: `adeu_ir`, `adeu_concepts`, `adeu_kernel`, `adeu_explain`, `adeu_semantic_depth`, `adeu_puzzles`, `urm_runtime`, `adeu_core_ir` (and others).
  → authority: API is orchestration layer (`apps/api/pyproject.toml`).
* `packages/urm_runtime/pyproject.toml` depends on `adeu_ir`, `adeu_kernel`, `adeu_lean` (tooling + runtime boundary).
  → authority: URM runtime owns policy/worker/stop-gates (`packages/urm_runtime/pyproject.toml`).
* `packages/adeu_kernel/pyproject.toml` depends on `adeu_ir`, `adeu_patch_core`, `adeu_lean`, `z3-solver` (kernel + proof lane).
  → authority: kernel enforces semantics + evidence (`packages/adeu_kernel/pyproject.toml`).
* `packages/adeu_core_ir/pyproject.toml` depends on `adeu_ir` (core IR is “schema + canonicalization on top of base IR”).
  → authority: core IR contract (`packages/adeu_core_ir/pyproject.toml`).

### 1.2 Major flows (observed → inferred)

**Flow A: Request → kernel/concepts → response**

* HTTP entrypoints are in `apps/api/src/adeu_api/main.py` (e.g. `/check`, `/concepts/*`, `/diff`, `/concepts/semantic_depth`, `/urm/*`).
  Example endpoint definitions appear via decorators like `@app.post("/check", response_model=CheckReport)` and `@app.post("/urm/core-ir/propose", ...)` in `main.py`.
* Business logic routes into package layers (examples):

  * Core IR proposer uses `adeu_kernel.proposer.propose` in `apps/api/src/adeu_api/main.py:urm_core_ir_propose_endpoint`.
  * Semantic depth calls are wired through `apps/api/src/adeu_api/main.py` and schema-validated by `packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py:validate_semantic_depth_report` (used in tests like `apps/api/tests/test_semantic_depth_report_schema.py`).

**Flow B: URM “tool call” policy gate**

* URM tool calls go through `apps/api/src/adeu_api/urm_routes.py:urm_tool_call_endpoint` which:

  1. resolves a policy action (`_resolve_tool_policy_action`)
  2. loads session state (`_load_session_access_state`)
  3. resolves approval precheck (`_resolve_approval_precheck`)
  4. calls `packages/urm_runtime/src/urm_runtime/capability_policy.py:authorize_action`
  5. only then executes the tool (`manager` / connectors / etc.).
     (All in `apps/api/src/adeu_api/urm_routes.py`.)

**Flow C: Stop-gate and tooling continuity**

* Stop-gate manifests: `apps/api/fixtures/stop_gate/vnext_plus*_manifest.json` (v7..v26 set is referenced in tests and scripts).
* Stop-gate engine: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (15,179 LOC) provides `build_stop_gate_metrics(...)` and parity hashing utilities.
* Tooling scripts:

  * Metrics builder: `apps/api/scripts/build_stop_gate_metrics.py` uses `StopGateMetricsInput.from_legacy_kwargs(...)` then `build_stop_gate_metrics(...)`.
  * Quality dashboard builder: `apps/api/scripts/build_quality_dashboard.py` calls `apps/api/src/adeu_api/quality_dashboard.py:write_quality_dashboard`.
* v26 toolchain consolidation artifacts:

  * Lock + constraints: `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`.
  * Closeout decision: `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`.
  * Closeout metrics/report: `artifacts/stop_gate/metrics_v26_closeout.json`, `artifacts/stop_gate/report_v26_closeout.md`.

**Flow D: Transfer-report builders for v24/v25 families (observed)**

* Consolidated builders live in `packages/urm_runtime/src/urm_runtime/`:

  * `extraction_fidelity_transfer_report_vnext_plus24.py`
  * `core_ir_proposer_transfer_report_vnext_plus25.py`
* These are referenced by the v26 tooling transfer report `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md` and invoked in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (see `build_tooling_transfer_report_metrics` referenced in the lock docs).

### 1.3 Authority boundaries (schema vs validation vs runtime vs tooling)

| Boundary                 | Authority                                  | Repo evidence (entrypoints)                                                                                                                                                                                                                                                                        | Notes                                                                                                                                                   |
| ------------------------ | ------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Schema contracts**     | Pydantic models + frozen JSON schemas      | Base IR: `packages/adeu_ir/src/adeu_ir/models.py`; Core IR: `packages/adeu_core_ir/src/adeu_core_ir/models.py`; URM events: `packages/urm_runtime/src/urm_runtime/models.py`; Frozen artifact schemas: `spec/*.schema.json` + tests like `apps/api/tests/test_validator_evidence_packet_schema.py` | Pydantic `ConfigDict(extra="forbid")` appears in many model files, enforcing strictness at parse time (e.g., `packages/adeu_ir/src/adeu_ir/models.py`). |
| **Validation contracts** | Kernel + specialized validators            | Kernel semantics: `packages/adeu_kernel/src/adeu_kernel/checker.py`, `validator.py`, `semantics_diagnostics.py`; Core IR invariants: validators in `packages/adeu_core_ir/src/adeu_core_ir/models.py`; Semantic depth: `packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py`    | Determinism-sensitive normalization happens in evidence builders (e.g., `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`).                  |
| **Runtime policy gates** | URM capability policy + API routing        | Policy decision: `packages/urm_runtime/src/urm_runtime/capability_policy.py:authorize_action`; HTTP gate wiring: `apps/api/src/adeu_api/urm_routes.py:urm_tool_call_endpoint`                                                                                                                      | Worker run endpoint is separate and does **not** call `authorize_action` (see risks).                                                                   |
| **Tooling/stop-gates**   | `stop_gate_tools.py` + scripts + Z4 guards | Engine: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`; scripts: `apps/api/scripts/build_stop_gate_metrics.py`, `apps/api/scripts/build_quality_dashboard.py`; guard tests: `apps/api/tests/test_tooling_z4_guards.py`                                                                  | Lock-chain constraints are documented in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` and enforced operationally by scripts + tests.                      |

---

## 2) Risk Register (top 12)

> Each item: **Observed** facts are backed by file excerpts; **Inferred** notes are explicitly labeled.

### R1) Canonical JSON / sha256 helpers are duplicated across layers (drift risk)

* **Severity:** high
* **Evidence (observed)**

  * `apps/api/src/adeu_api/hashing.py:canonical_json` / `sha256_canonical_json`

    ```py
    def canonical_json(value: object) -> str:
        return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)

    def sha256_canonical_json(value: object) -> str:
        return sha256_text(canonical_json(value))
    ```
  * `packages/urm_runtime/src/urm_runtime/hashing.py:canonical_json` / `sha256_canonical_json`

    ```py
    def canonical_json(value: Any) -> str:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    ```
  * Kernel also re-implements canonicalization:
    `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py:_canonical_json`

    ```py
    def _canonical_json(value: Any) -> str:
        return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    ```
  * Additional copies exist (e.g., `packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py:_canonical_json`, `packages/adeu_explain/src/adeu_explain/explain_diff.py:_canonical_json`, `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py:_canonical_json`).
* **Why it matters under determinism/stop-gate**

  * Stop-gates rely on canonical hashing for parity/replay stability (`packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` computes hashes over canonicalized payloads). A “tiny” divergence (e.g., separators/ensure_ascii/sort policy) becomes a systemic determinism break across artifacts and fixtures.
* **Proposed fix (minimal, behavior-preserving)**

  * Add a **single conformance test** that asserts all canonical-json implementations in-tree produce identical output and sha256 for a fixed corpus of payloads.
  * Then (optional, incremental) introduce a shared helper in the lowest common dependency (likely `packages/adeu_ir/src/adeu_ir/`) and migrate call sites gradually **without changing output**.
* **Safety proof (tests/fixtures)**

  * New test file, e.g. `apps/api/tests/test_canonical_json_conformance.py`:

    * Compare `adeu_api.hashing.canonical_json`, `urm_runtime.hashing.canonical_json`, and a representative subset of `_canonical_json` helpers (via import) across:

      * nested dicts with unicode,
      * lists with mixed types,
      * floats used in stop-gate metrics,
      * ordering stress cases.
    * Proves: “canonicalization profile is stable and identical across layers.”
* **Lock classification**

  * **Allowed in current locks** (test-only + refactor guarded by parity fixtures; no schema changes).

---

### R2) v26 parity-path normalization in code is broader than the lock allowlist (potential drift masking)

* **Severity:** high
* **Evidence (observed)**

  * Lock text restricts normalization to an explicit allowlist: `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`:

    > “path normalization applies only to this frozen field-key allowlist: `baseline_path`, `candidate_path`, `report_path`, `manifest_path` … no non-allowlist fields may be path-normalized” (see section around the “Host-path normalization lock”).
  * Implementation normalizes **any** key ending with `_path` or `_paths`:
    `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_normalize_vnext_plus26_parity_paths`

    ```py
    if parent_key.endswith("_path") and isinstance(value, str):
        return _normalize_vnext_plus26_path_value(value, repo_root=repo_root)
    if parent_key.endswith("_paths") and isinstance(value, list):
        ...
        return sorted(candidate_paths)
    ```
* **Why it matters under determinism/stop-gate**

  * If parity projection normalizes *more than allowed*, it can **hide real drift** (e.g., list ordering changes, path differences in non-allowlisted fields) and incorrectly keep `artifact_*_parity_pct` at 100%.
  * Also: doc/code mismatch undermines “lock-as-contract” discipline.
* **Proposed fix (minimal, behavior-preserving)**

  * Make normalization explicitly allowlist-driven:

    * Normalize only `baseline_path`, `candidate_path`, `report_path`, `manifest_path`.
    * Leave other `*_paths` untouched (still canonical JSON sorting will handle map keys, but don’t rewrite values).
  * Keep existing behavior behind a compatibility toggle **only if needed** (but prefer matching the lock).
* **Safety proof**

  * Extend/add a targeted test in `apps/api/tests/test_tooling_z4_guards.py` or a new `test_stop_gate_parity_projection_vnext_plus26.py`:

    * Load an existing v26 parity fixture payload (e.g., `apps/api/fixtures/stop_gate/vnext_plus26/stop_gate_input_model_parity_baseline_case_a.json`).
    * Assert:

      1. computed parity hash remains unchanged vs current closeout (`artifacts/stop_gate/metrics_v26_closeout.json` implies parity passes),
      2. a synthetic payload containing non-allowlisted `_paths` fields with intentionally “bad” order is **not** normalized (hash differs).
    * Proves: “projection obeys allowlist; doesn’t mask non-allowlisted drift.”
* **Lock classification**

  * **Allowed in current locks** *if* output hashes for locked fixtures remain unchanged.
  * If hashes change for existing v26 locked fixtures: **Requires lock release** (or new projection ID) because stop-gate parity semantics would change.

---

### R3) Deterministic environment locks are documented but not enforced by tooling entrypoints

* **Severity:** high
* **Evidence (observed)**

  * Lock requires deterministic env values set/enforced by tooling entrypoints: `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`:

    * `TZ=UTC`
    * `LC_ALL=C`
    * “deterministic acceptance entrypoints … must set/enforce these env values explicitly”
  * Closeout runs set env externally in the command line: `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md` shows `TZ=UTC LC_ALL=C ... python ...`.
  * Tooling scripts themselves do **not** set/check env (no `os.environ` usage):

    * `apps/api/scripts/build_stop_gate_metrics.py` begins with `import argparse` / `from pathlib import Path` and no env logic.
    * `apps/api/scripts/build_quality_dashboard.py` similarly has no env logic.
* **Why it matters under determinism/stop-gate**

  * “Operator-enforced env” is brittle: CI runners or local runs can silently drift and change locale/timezone-dependent behavior (especially around datetime parsing/formatting or filesystem ordering), producing non-reproducible hashes.
* **Proposed fix (minimal)**

  * Add `urm_runtime.determinism.enforce_tooling_env()` (new module) that:

    * sets `TZ=UTC` and `LC_ALL=C` if unset,
    * **fails** if set to conflicting values (fail-fast),
    * (optional) provides a helper `sorted_glob()` wrapper if you later standardize glob ordering.
  * Call it at the top of:

    * `apps/api/scripts/build_stop_gate_metrics.py`
    * `apps/api/scripts/build_quality_dashboard.py`
    * `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:main()` (CLI path)
* **Safety proof**

  * Add a unit test that runs these entrypoints (or calls the helper) with conflicting env and asserts deterministic failure code/message.
  * Also add a “no-change” golden test that re-runs stop gate metrics on fixtures and matches `artifacts/stop_gate/metrics_v26_closeout.json`.
* **Lock classification**

  * **Allowed in current locks** (this is explicitly required by the lock; should not change deterministic outputs, only make them reliable).

---

### R4) `/urm/worker/run` bypasses URM policy/approval gates

* **Severity:** high
* **Evidence (observed)**

  * Worker run endpoint is a straight call to runner:
    `apps/api/src/adeu_api/urm_routes.py:urm_worker_run_endpoint`

    ```py
    @router.post("/worker/run", response_model=WorkerRunResult)
    def urm_worker_run_endpoint(request: WorkerRunRequest) -> WorkerRunResult:
        runner = _get_worker_runner()
        return runner.run(request)
    ```
  * Tool calls are policy-gated via `authorize_action`:
    `apps/api/src/adeu_api/urm_routes.py:urm_tool_call_endpoint`

    ```py
    decision = authorize_action(
        role=request.role,
        action=action,
        writes_allowed=session_writes_allowed,
        approval_provided=bool(request.approval_id),
        ...
    )
    ```
* **Why it matters under determinism/stop-gate**

  * Under the “read-only claims + stop-gates” regime, *execution* must be within enforced trust lanes. A bypassed policy gate makes it easy to accidentally expand authority without lock-aware checks (even if the worker runner itself tries to be safe).
* **Proposed fix (minimal, behavior-preserving)**

  * **Phase 1 (allowed now):** add an explicit hard comment + runtime audit log event that this endpoint is “ungated by capability policy” (so it’s visible).
  * **Phase 2 (safer):** add an **opt-in** policy check:

    * introduce a synthetic action kind (e.g., `urm.worker.run`) evaluated via `authorize_action`, but only if an env flag is set (default off to preserve behavior).
* **Safety proof**

  * Add tests in `apps/api/tests/test_urm_routes_policy.py` (new) that:

    * confirms `/tools/call` is denied when writes not allowed and action requires it (already partially covered),
    * confirms `/worker/run` remains unchanged when feature flag is off,
    * confirms `/worker/run` is denied when feature flag is on and policy denies.
* **Lock classification**

  * **Allowed in current locks** for “audit + feature-flagged gating with default behavior unchanged”.
  * **Requires lock release** if you change default behavior or introduce a new mandatory policy coupling for existing clients.

---

### R5) `stop_gate_tools.py` is a mega-module (15k LOC) that mixes responsibilities (high refactor risk)

* **Severity:** high
* **Evidence (observed)**

  * File size: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` is 15,179 lines (measured in-repo).
  * It contains:

    * versioned manifest logic (`VNEXT_PLUS*` constants at top),
    * replay + hashing + parity projection functions,
    * markdown rendering,
    * CLI entrypoint `main()`,
    * plus v24/v25/v26 tooling parity logic (`_tooling_parity_hash_projection_vnext_plus26`, `build_tooling_transfer_report_metrics`, etc.).
* **Why it matters under determinism/stop-gate**

  * One-file changes are extremely likely to introduce accidental lock violations (ordering drift, path normalization drift, metric key drift).
  * Review cost is high; “small green commits” are hard if a file is a god-object.
* **Proposed fix (minimal, behavior-preserving)**

  * Split internally while preserving the external import path:

    * Create `packages/urm_runtime/src/urm_runtime/stop_gate/` package with modules:

      * `types.py` (StopGateMetricsInput)
      * `manifests.py`
      * `replay.py`
      * `parity.py`
      * `render.py`
      * `metrics_vnext_plus*.py` as-needed
    * Keep `stop_gate_tools.py` as a thin façade that re-exports the same symbols and CLI.
* **Safety proof**

  * Add/extend tests that execute:

    * `apps/api/scripts/build_stop_gate_metrics.py` end-to-end on fixtures,
    * `apps/api/tests/test_tooling_z4_guards.py` locked surfaces guard,
    * `apps/api/tests/test_urm_stop_gate_tools.py` functional parity.
  * Proves: “refactor is a pure move; output identical for locked fixtures.”
* **Lock classification**

  * **Allowed in current locks** (no behavior/schema change; guarded by fixtures).

---

### R6) `apps/api/main.py` is a mega-module and is imported by deterministic tooling modules (layer bleed + side-effect risk)

* **Severity:** medium–high
* **Evidence (observed)**

  * `apps/api/src/adeu_api/main.py` is 7,424 LOC and defines endpoints, helpers, and caches.
  * Deterministic tooling imports it directly:

    * `apps/api/src/adeu_api/quality_dashboard.py`:

      ```py
      import adeu_api.main as api_main
      ```
    * `apps/api/src/adeu_api/determinism_oracles.py`:

      ```py
      import adeu_api.main as api_main
      ```
* **Why it matters under determinism/stop-gate**

  * Tooling should ideally depend on **pure** helpers, not “server module import side effects” (FastAPI app construction, router wiring, global caches). Importing `main.py` increases risk of:

    * accidental dependency on runtime-only globals,
    * import-time behavior differences across env,
    * slowed CI for stop-gate tooling.
* **Proposed fix (minimal)**

  * Extract the specific reused helpers into a small module and re-export:

    * Move `_question_dedupe_key`, `_concept_ir_hash`, `_adeu_ir_hash` out of `main.py` (currently in `apps/api/src/adeu_api/main.py`) into e.g. `apps/api/src/adeu_api/semantic_keys.py`.
    * Update `quality_dashboard.py` and `determinism_oracles.py` to import the new module, not `main.py`.
    * Keep backward compatibility by importing/re-exporting in `main.py`.
* **Safety proof**

  * Add a unit test that imports `adeu_api.quality_dashboard` and asserts it does **not** import `adeu_api.main` (or at least that it doesn’t initialize the FastAPI app as a side-effect).
  * Run existing stop-gate scripts and compare artifact hashes (`artifacts/quality_dashboard_v26_closeout.json` + stop-gate closeout).
* **Lock classification**

  * **Allowed in current locks**.

---

### R7) Active stop-gate manifest set is duplicated across script/test plumbing (drift risk on next arc)

* **Severity:** medium
* **Evidence (observed)**

  * Script-side list: `apps/api/scripts/build_stop_gate_metrics.py:_ACTIVE_MANIFEST_VERSIONS`

    ```py
    _ACTIVE_MANIFEST_VERSIONS = (7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26)
    ```
  * Test-side list: `apps/api/tests/test_tooling_z4_guards.py:_base_stop_gate_kwargs` defines a local `manifest_versions = (...)` with the same values.
* **Why it matters under determinism/stop-gate**

  * Adding vNext+27 (or removing an arc) requires edits in multiple places; missing one silently reduces coverage of locked continuity surfaces.
* **Proposed fix (minimal)**

  * Define a single source of truth in URM tooling layer, e.g.:

    * `packages/urm_runtime/src/urm_runtime/stop_gate/registry.py:ACTIVE_MANIFEST_VERSIONS`
  * Import that list from:

    * `apps/api/scripts/build_stop_gate_metrics.py`
    * `apps/api/tests/test_tooling_z4_guards.py`
    * any other stop-gate harness.
* **Safety proof**

  * Add a test that asserts the set of `vnext_plus*_manifest.json` files in `apps/api/fixtures/stop_gate/` matches `ACTIVE_MANIFEST_VERSIONS`.
* **Lock classification**

  * **Allowed in current locks**.

---

### R8) Repo-root discovery is implemented differently across subsystems (path determinism & portability risk)

* **Severity:** medium
* **Evidence (observed)**

  * Robust root discovery with env override exists in `packages/adeu_ir/src/adeu_ir/repo.py:repo_root` (supports `ADEU_REPO_ROOT`, `.git`, `pyproject.toml`+`packages/`).
  * Stop-gate tooling uses a weaker discovery:
    `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py:_discover_repo_root`

    ```py
    for candidate in (start, *start.parents):
        if (candidate / ".git").exists():
            return candidate
    return None
    ```
* **Why it matters under determinism/stop-gate**

  * Host-path normalization relies on stable notion of “repo root” (esp. parity hashing and report builders). Divergent root heuristics can cause:

    * absolute paths to leak into hashed payloads in some environments,
    * inconsistent path normalization behavior across tools.
* **Proposed fix (minimal)**

  * Replace URM’s local `_discover_repo_root` with `adeu_ir.repo.repo_root(anchor=...)` (URM depends on `adeu_ir` already per `packages/urm_runtime/pyproject.toml`).
  * Keep the “optional None” behavior by wrapping exceptions in URM tooling where needed.
* **Safety proof**

  * Run `apps/api/tests/test_tooling_z4_guards.py` and stop-gate closeout scripts; assert hashes unchanged.
  * Add a unit test that sets `ADEU_REPO_ROOT` and asserts stop-gate tooling uses it (e.g., manifest resolution picks correct path).
* **Lock classification**

  * **Allowed in current locks** if fixture outputs unchanged; otherwise, treat as “requires lock release” because parity hashing could change.

---

### R9) Policy JSON duplication is only partially sync-tested (packaged vs repo drift risk)

* **Severity:** medium
* **Evidence (observed)**

  * There is a sync test only for lattice:
    `apps/api/tests/test_urm_capability_lattice_sync.py` compares:

    * `policy/urm.capability.lattice.v1.json`
    * `packages/urm_runtime/src/urm_runtime/policy/urm.capability.lattice.v1.json`
  * But multiple other policy files exist in both places, e.g.:

    * `policy/urm.allow.v1.json` vs `packages/urm_runtime/src/urm_runtime/policy/urm.allow.v1.json`
    * `policy/urm.profiles.v1.json` vs `packages/.../urm.profiles.v1.json`
    * `policy/urm.connector_exposure_mapping.v1.json` vs packaged copy
* **Why it matters under determinism/stop-gate**

  * Installed/runtime behavior can diverge from repo behavior depending on which copy is loaded (see loader in `packages/urm_runtime/src/urm_runtime/capability_policy.py:_load_policy_json_pair`).
  * That undermines “repo-grounded determinism” when running from a packaged environment.
* **Proposed fix (minimal)**

  * Add a sync test that compares **all** duplicated policy files, not just lattice.
* **Safety proof**

  * New test file, e.g. `apps/api/tests/test_urm_policy_packaged_sync.py`, enumerating policy filenames and asserting exact JSON equality.
* **Lock classification**

  * **Allowed in current locks** (tests only).

---

### R10) Worker runner can silently drop `--ask-for-approval` / `--output-schema` depending on CLI support (hang/parse risk)

* **Severity:** medium
* **Evidence (observed)**

  * `packages/urm_runtime/src/urm_runtime/worker.py:CodexExecWorkerRunner.run`:

    ```py
    supports_output_schema_flag = self._supports_exec_flag("--output-schema")
    supports_ask_for_approval_flag = self._supports_exec_flag("--ask-for-approval")
    use_output_schema_flag = bool(request.output_schema_path and supports_output_schema_flag)
    use_ask_for_approval_flag = supports_ask_for_approval_flag
    ```
  * `_build_command(...)` only appends flags if `include_*` are True; if not supported, it runs without them.
* **Why it matters under determinism/stop-gate**

  * If `--ask-for-approval` is unsupported, codex may prompt interactively (inferred), potentially hanging deterministic pipelines.
  * If `--output-schema` is unsupported, outputs may be less structured and artifact extraction becomes less reliable (observed: extraction relies on `extract_artifact_candidate(events)` and optional schema validation).
* **Proposed fix (minimal)**

  * Add a runner config flag (env-driven) to **require** noninteractive support in CI/locked runs:

    * e.g., `URM_REQUIRE_CODEX_ASK_FOR_APPROVAL_FLAG=1`
    * if unsupported, fail with a clear `URMError(code="URM_CODEX_CLI_INCOMPATIBLE")`.
  * Default should preserve current behavior to avoid breaking older toolchains.
* **Safety proof**

  * Unit tests in `apps/api/tests/test_urm_worker_runner.py` (or new) mocking `_supports_exec_flag` to return False and asserting:

    * when require flag off: behavior unchanged,
    * when require flag on: fail fast with deterministic error.
* **Lock classification**

  * **Allowed in current locks** if default behavior is unchanged (opt-in hardening).
  * **Requires lock release** if you make the stricter behavior the default.

---

### R11) Core-IR proposer idempotency cache is global, unbounded, and not persisted

* **Severity:** medium
* **Evidence (observed)**

  * Global dict with no eviction:
    `apps/api/src/adeu_api/main.py:_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`

    ```py
    _CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY: dict[tuple[str, str], _CoreIRProposerIdempotencyRecord] = {}
    ```
  * Used by endpoint:
    `apps/api/src/adeu_api/main.py:urm_core_ir_propose_endpoint`

    * caches by `(_CORE_IR_PROPOSER_SURFACE_ID, req.client_request_id)`
    * stores response payload indefinitely.
* **Why it matters under determinism/stop-gate**

  * Determinism-adjacent: idempotency behavior depends on process lifetime. Across restarts, the same `client_request_id` can produce a different response (inferred).
  * Operational: unbounded growth is a memory risk in long-running environments (observed: no max size / TTL).
* **Proposed fix (minimal)**

  * Phase 1: add a bounded cache wrapper but keep semantics for typical windows:

    * e.g., LRU with large max size and an explicit metric/log when evicting.
  * Phase 2 (stronger, likely needs DB): persist idempotency to SQLite like worker runs do (`packages/urm_runtime/src/urm_runtime/storage.py` already has idempotency machinery).
* **Safety proof**

  * Add tests:

    * idempotency replay returns identical payload for same `client_request_id` within cache window
    * eviction behavior is deterministic and explicitly signaled.
* **Lock classification**

  * Phase 1 (instrumentation + optional cap): **Allowed in current locks** if default behavior is effectively unchanged in normal CI.
  * Phase 2 (DB persistence / migration): **Requires lock release** (new DB schema + behavioral contract).

---

### R12) Lean proof runner uses random temp filenames; could leak nondeterminism into evidence when enabled

* **Severity:** low–medium (currently low because default backend is mock)
* **Evidence (observed)**

  * `packages/adeu_lean/src/adeu_lean/runner.py:run_lean_request` uses `NamedTemporaryFile(...)`:

    ```py
    with NamedTemporaryFile(
        mode="w",
        suffix=".lean",
        prefix="adeu_obligation_",
        ...
    ) as handle:
        file_name = Path(handle.name).name
        for cmd in ([lake_bin, "env", "lean", file_name], [lean_bin, file_name]):
            proc = _run_command(...)
    ```
  * Kernel default backend is “mock” but can switch via env:
    `packages/adeu_kernel/src/adeu_kernel/proof.py:build_proof_backend` uses `ADEU_PROOF_BACKEND` default `"mock"`.
* **Why it matters under determinism/stop-gate**

  * If Lean is enabled, error outputs can include the randomized temp filename (inferred), which may change `proof_hash` / evidence payloads and violate replay determinism expectations.
* **Proposed fix (minimal)**

  * Use a deterministic filename derived from theorem id + input hash (already computed in `adeu_lean.runner:_hash_inputs`).
  * Keep old behavior behind a flag if you’re worried about compatibility.
* **Safety proof**

  * Add tests for Lean runner in isolation (can be “no lean binary” path):

    * assert generated filename is stable given same request,
    * assert proof_hash does not incorporate random names on failure path (if you sanitize).
* **Lock classification**

  * **Allowed in current locks** (default proof backend is mock; change is isolated to Lean backend path).
  * If Lean is already used in production and people depend on current evidence format: treat as “requires lock release” for that surface.

---

## 3) Refactor Plan as vNext Arcs (thin-slice)

> Current lock-chain reality (observed): vNext+26 is the latest locked toolchain arc (`docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`) with closeout in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md` and outputs in `artifacts/stop_gate/metrics_v26_closeout.json`.
> Next arc number is **unknown** in-repo (no v27 docs), so I’ll label proposals as **vNext+27..** placeholders.

### Arc vNext+27 — “Tooling determinism hardening (env + parity allowlist + hash conformance)”

* **Scope**

  * Enforce deterministic env inside tooling entrypoints (R3).
  * Add canonical JSON conformance tests across packages (R1).
  * Align v26 parity projection to the documented allowlist (R2).
* **Explicit locks**

  * Do not change `stop_gate_metrics@1` schema (see `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` and `artifacts/stop_gate/metrics_v26_closeout.json`).
  * Do not change `SEMANTICS_v3` semantics (doc: `docs/SEMANTICS_v3.md`).
  * Preserve existing parity projection ID `stop_gate_parity.v1` unless outputs remain identical (lock text in `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`).
* **Acceptance criteria**

  * `apps/api/scripts/build_quality_dashboard.py` and `build_stop_gate_metrics.py` run deterministically without relying on external env exports (still producing the same closeout artifacts when given the same inputs).
  * `apps/api/tests/test_tooling_z4_guards.py` remains green.
  * Stop-gate closeout hashes remain identical for v26 fixtures (no change to `artifact_*_parity_pct`).
* **Stop-gate impacts**

  * **None** (no new metric keys; rely on existing Z4 + parity fixtures).
* **Small-green commit plan (5–7 commits)**

  1. Add `urm_runtime/determinism.py` with `enforce_tooling_env()`.
  2. Call `enforce_tooling_env()` in `apps/api/scripts/build_quality_dashboard.py`.
  3. Call `enforce_tooling_env()` in `apps/api/scripts/build_stop_gate_metrics.py` and `urm_runtime/stop_gate_tools.py:main()`.
  4. Add `apps/api/tests/test_canonical_json_conformance.py`.
  5. Refactor `_normalize_vnext_plus26_parity_paths` to use allowlist (no behavior change on fixtures).
  6. Add parity allowlist regression test(s).
  7. Run/lock artifact parity: confirm closeout metrics unchanged.

---

### Arc vNext+28 — “Stop-gate tooling modularization + manifest registry single-source”

* **Scope**

  * Split `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` internally (R5).
  * Centralize `ACTIVE_MANIFEST_VERSIONS` and manifest path resolution used by scripts/tests (R7).
* **Explicit locks**

  * Maintain existing import surface `urm_runtime.stop_gate_tools` (keep façade).
  * No schema changes, no metric key changes, no new stop-gate manifests required.
* **Acceptance criteria**

  * `build_stop_gate_metrics.py` produces identical JSON+MD output for fixtures.
  * `apps/api/tests/test_urm_stop_gate_tools.py` passes (this is your broad regression net).
* **Stop-gate impacts**

  * None.
* **Small-green commit plan (6–8 commits)**

  1. Introduce `urm_runtime/stop_gate/types.py` and move `StopGateMetricsInput` there.
  2. Add `urm_runtime/stop_gate/registry.py` with `ACTIVE_MANIFEST_VERSIONS`.
  3. Update `apps/api/scripts/build_stop_gate_metrics.py` to import registry.
  4. Update `apps/api/tests/test_tooling_z4_guards.py` to import registry.
  5. Move parity projection helpers to `stop_gate/parity.py` and re-export.
  6. Move markdown rendering to `stop_gate/render.py`.
  7. Keep `stop_gate_tools.py` as façade and run parity fixture tests.

---

### Arc vNext+29 — “Repo-root + packaged resource normalization”

* **Scope**

  * Standardize repo root discovery across URM tooling/policy (R8).
  * Add policy-file sync coverage beyond lattice (R9).
* **Explicit locks**

  * Must not change the resolved paths in locked stop-gate fixtures (guard via Z4 + parity).
  * Must not change policy semantics; only ensure packaged/repo copies stay equal.
* **Acceptance criteria**

  * Stop-gate parity hashes unchanged.
  * New tests guarantee repo vs packaged policy JSON equality for all duplicated policy files.
* **Stop-gate impacts**

  * None.
* **Small-green commit plan**

  1. Add `apps/api/tests/test_urm_policy_packaged_sync.py` enumerating policy files.
  2. Refactor `urm_runtime.stop_gate_tools._discover_repo_root` to use `adeu_ir.repo.repo_root` (wrapping to optional).
  3. Refactor transfer report builders (`extraction_fidelity_transfer_report_vnext_plus24.py`, `core_ir_proposer_transfer_report_vnext_plus25.py`) to use unified helper.
  4. Run tooling transfer report / Z4 tests.

---

### Arc vNext+30 — “URM execution governance + CLI compatibility hardening”

* **Scope**

  * Add optional capability-policy gating for `/urm/worker/run` (R4).
  * Add opt-in strictness for codex CLI compatibility (R10).
* **Explicit locks**

  * If you change default behavior of `/urm/worker/run`, **requires lock release** (API behavior + likely client impact).
  * Otherwise keep default unchanged and gate behind env flags.
* **Acceptance criteria**

  * With feature flag off: behavior identical.
  * With feature flag on: explicit deny/allow decisions are enforced and tested.
* **Stop-gate impacts**

  * Prefer **none** (tests only). If you later want a stop-gate metric (e.g., “worker_run_gated_pct”), that would be a new metric key and needs a lock plan.
* **Small-green commit plan**

  1. Add config plumbing to URM manager to optionally require policy for worker runs.
  2. Implement policy evaluation path for worker.run (synthetic action).
  3. Add tests for both modes.
  4. Add CLI “require ask-for-approval flag” enforcement behind env var + tests.

---

### Arc vNext+31 — “Proof backend determinism prep (Lean temp files)”

* **Scope**

  * Deterministic temp filenames in Lean runner (R12).
* **Explicit locks**

  * Keep default proof backend mock (already default via `ADEU_PROOF_BACKEND` in `packages/adeu_kernel/src/adeu_kernel/proof.py`).
* **Acceptance criteria**

  * Lean runner is stable given same inputs (even failure path).
* **Stop-gate impacts**

  * None unless/ until Lean is used in locked fixtures.

---

## 4) Concrete “Diff-Oriented” Suggestions (highest ROI)

> 8 specific, file-scoped changes with minimal API sketches.

### D1) Add deterministic tooling env enforcement helper

* **Files to touch**

  * Add: `packages/urm_runtime/src/urm_runtime/determinism.py`
  * Edit: `apps/api/scripts/build_stop_gate_metrics.py`
  * Edit: `apps/api/scripts/build_quality_dashboard.py`
  * Edit: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (CLI path)
* **Minimal API**

  ```py
  # urm_runtime/determinism.py
  def enforce_tooling_env(*, tz: str = "UTC", lc_all: str = "C") -> None: ...
  ```

  * behavior: set if missing, raise if conflicting.

---

### D2) Centralize active stop-gate manifest registry

* **Files to touch**

  * Add: `packages/urm_runtime/src/urm_runtime/stop_gate/registry.py`
  * Edit: `apps/api/scripts/build_stop_gate_metrics.py`
  * Edit: `apps/api/tests/test_tooling_z4_guards.py`
* **Minimal API**

  ```py
  ACTIVE_MANIFEST_VERSIONS: tuple[int, ...] = (7, 8, 9, 10, 11, 13, ..., 26)

  def manifest_filename(version: int) -> str: ...
  ```

  * Script/test both import this; removes duplicated tuples.

---

### D3) Make v26 parity normalization explicitly allowlist-driven

* **Files to touch**

  * Edit: `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
  * Add tests: `apps/api/tests/test_stop_gate_parity_projection_vnext_plus26.py` (new)
* **Minimal API sketch**

  ```py
  def _normalize_vnext_plus26_parity_paths(
      value: object,
      *,
      parent_key: str = "",
      repo_root: Path | None = None,
      allowlist: frozenset[str] = frozenset({"baseline_path","candidate_path","report_path","manifest_path"}),
  ) -> object:
      ...
  ```

  * Only normalize when `parent_key in allowlist`.

---

### D4) Canonical JSON conformance test across layers

* **Files to touch**

  * Add: `apps/api/tests/test_canonical_json_conformance.py`
* **Minimal test idea**

  * Import:

    * `adeu_api.hashing.canonical_json`
    * `urm_runtime.hashing.canonical_json`
    * representative `_canonical_json` helpers (kernel/explain/core_ir)
  * Assert same outputs on corpus; assert same `sha256_text(...)`.

---

### D5) Expand policy packaged-vs-repo sync tests (beyond lattice)

* **Files to touch**

  * Add: `apps/api/tests/test_urm_policy_packaged_sync.py`
* **Minimal API sketch**

  * Just a test enumerating:

    * `urm.allow.v1.json`, `urm.profiles.v1.json`, `urm.connector_exposure_mapping.v1.json`, etc.

---

### D6) Extract “pure helper” functions out of `main.py` and stop importing it from tooling

* **Files to touch**

  * Add: `apps/api/src/adeu_api/semantic_keys.py`
  * Edit: `apps/api/src/adeu_api/main.py` (import + re-export)
  * Edit: `apps/api/src/adeu_api/quality_dashboard.py`
  * Edit: `apps/api/src/adeu_api/determinism_oracles.py`
* **Minimal API**

  ```py
  # adeu_api/semantic_keys.py
  def question_dedupe_key(question: str) -> str: ...
  def concept_ir_hash(concept_ir: dict[str, Any]) -> str: ...
  def adeu_ir_hash(adeu_ir: dict[str, Any]) -> str: ...
  ```

  * `main.py` keeps backward-compatible aliases.

---

### D7) Add opt-in strictness for worker runner CLI compatibility

* **Files to touch**

  * Edit: `packages/urm_runtime/src/urm_runtime/worker.py`
  * Add tests: `apps/api/tests/test_urm_worker_runner_cli_compat.py` (new)
* **Minimal API**

  ```py
  # in worker runner config
  require_ask_for_approval_flag: bool = False
  require_output_schema_flag: bool = False
  ```

  * When enabled and unsupported → deterministic fail-fast.

---

### D8) Proof determinism: deterministic temp filename for Lean runner

* **Files to touch**

  * Edit: `packages/adeu_lean/src/adeu_lean/runner.py`
  * Add tests: `packages/adeu_lean/tests/test_runner_deterministic_filename.py` (new) or `apps/api/tests/...` if you centralize tests there
* **Minimal API**

  * No new public API; internal change:

    * replace `NamedTemporaryFile` with a deterministic path like:
      `project_dir / f"adeu_obligation_{sanitize(theorem_id)}_{inputs_hash[:8]}.lean"`
    * ensure cleanup.

---

## 5) v1 Review Cross-check

I reviewed the prior v1 output (`review.md`) and re-validated items against the current repo state. 

### v1 findings that remain strongest (verified)

* **Mega-modules are real hotspots**

  * v1 flagged `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` and `apps/api/src/adeu_api/main.py` as “god modules.”
  * Verified: 15,179 LOC and 7,424 LOC respectively, plus mixed responsibilities in both.
* **Canonical JSON/hashing duplication is real**

  * v1 flagged multiple duplicated canonicalization implementations. Verified across:

    * `apps/api/src/adeu_api/hashing.py`
    * `packages/urm_runtime/src/urm_runtime/hashing.py`
    * several `packages/adeu_kernel/src/adeu_kernel/*` modules (`*_evidence.py`, `semantics_diagnostics.py`)
* **URM worker run bypasses capability policy**

  * v1 flagged `/urm/worker/run` bypassing policy gates. Verified in `apps/api/src/adeu_api/urm_routes.py`.

### v1 findings that are now weak / insufficiently evidenced (or outdated relative to current code)

* **`StopGateMetricsInput.from_legacy_kwargs` “silently ignores unknown keys”**

  * v1 claimed it used a `kwargs.get(...)` pattern and would silently drop unknown keys. 
  * Current repo: `StopGateMetricsInput.from_legacy_kwargs(...)` is an explicit-parameter constructor (no `**kwargs`) in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`, so unknown keys will error at call-site (TypeError) rather than being ignored. This risk is no longer accurate as stated.
* **“Worker can run without sandbox if unsupported”**

  * v1 suggested fail-closed on missing `--sandbox`. 
  * Current code: `_build_command` always includes `--sandbox read-only` (unconditional) in `packages/urm_runtime/src/urm_runtime/worker.py`, so a CLI that doesn’t recognize it will likely fail (already “fail-ish closed”).
  * The more relevant compatibility risk now is **`--ask-for-approval` and `--output-schema`** being optional (see R10).

### Missing-but-critical areas v1 didn’t emphasize enough (now surfaced in v2)

* **Lock text vs code mismatch for v26 path normalization allowlist**

  * v1 didn’t call out the specific mismatch between `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` allowlist and the broader `_path/_paths` normalization logic in `stop_gate_tools.py` (R2).
* **Policy packaged-vs-repo drift beyond lattice**

  * v1 noted some registry sync issues, but the repo currently only sync-tests `urm.capability.lattice.v1.json` (`apps/api/tests/test_urm_capability_lattice_sync.py`) and not the rest of policy files (R9).
* **Tooling entrypoint env enforcement**

  * v1 discussed determinism generally, but the v26 lock explicitly calls out `TZ=UTC` / `LC_ALL=C` enforcement; current scripts rely on operator-provided env (R3).

---

If you want, I can also produce a **“lock-aware PR cut list”** that maps the Arc plan directly into 3 concrete PRs with exact diffs and “parity proof” tests (but the above already gives the per-arc commit slicing and acceptance criteria).
