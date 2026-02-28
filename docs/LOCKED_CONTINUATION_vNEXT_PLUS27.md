# Locked Continuation vNext+27 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v4.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v4_FACT_CHECKS.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- v26 remains the latest locked baseline with closeout evidence present.
- Consolidated territory planning selected Option A gate-0 sequencing:
  - v27 is the gate-opening arc and blocks expansion work until all gate-0 items are green.
- v27 scope is limited to `W1 / Path A` lock-alignment and determinism hardening only.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md` remain authoritative for baseline semantics.
- All changes in this arc are additive and behavior-preserving except bounded lock-alignment corrections explicitly frozen below.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remains frozen and unchanged.
- Stop-gate schema-family remains unchanged:
  - `stop_gate_metrics@1` only; no schema fork in this arc.
- Stop-gate metric-key policy for this arc is frozen:
  - no new metric keys are introduced in v27.
- Provider surface continuity remains frozen:
  - no provider expansion or proposer-surface expansion in this arc.
- L2 boundaries remain deferred in this arc:
  - no default-on `/urm/worker/run` governance release,
  - no persistent proposer idempotency storage release.
- Closeout observability continuity lock is frozen:
  - v27 closeout must include runtime-observability comparison row against v26 canonical baseline.
- Bounded behavior-change lock is frozen:
  - `A3` intentionally introduces fail-closed behavior when deterministic tooling env vars are present with conflicting values.
  - this is a lock-alignment correction, not a regression.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with four implementation slices (one PR each):

1. `A1` deterministic S9 trigger checker script (fail-closed)
2. `A2` v26 allowlist-normalization lock-alignment correction
3. `A3` deterministic tooling env enforcement helper + entrypoint wiring
4. `A4` canonical-json conformance test suite across API/runtime/kernel helpers

Out-of-scope note:

- stop-gate internal modularization (planned for v28)
- v26 tooling transfer-report builder path formalization (planned for v28)
- read-only evidence explorer product surface work (planned for v29)
- formal ODEU implementation lane expansion (planned for v30)
- any L2 boundary releases

## A1) Deterministic S9 Trigger Checker Script

### Goal

Add the missing executable S9 precondition checker as a deterministic fail-closed script.

### Scope

- Add script:
  - `apps/api/scripts/check_s9_triggers.py`
- Add tests:
  - `apps/api/tests/test_check_s9_triggers.py`
- Required metric keys checked:
  - `provider_route_contract_parity_pct`
  - `codex_candidate_contract_valid_pct`
  - `provider_parity_replay_determinism_pct`

### Locks

- Script contract lock is frozen:
  - input:
    - `--metrics-path` (default: `artifacts/stop_gate/metrics_v25_closeout.json`)
    - `--required-threshold` (default: `100.0`)
  - default-path resolution:
    - when `--metrics-path` is omitted, default path is resolved relative to repository root, not caller CWD.
    - repository root for this script is derived from `apps/api/scripts/check_s9_triggers.py` location in-repo.
    - effective default target remains:
      - `artifacts/stop_gate/metrics_v25_closeout.json`
  - comparator:
    - default metrics path must exist; missing path fails closed with exit `1`
    - fail when any required metric is missing
    - fail when any required metric is below threshold
    - required keys are frozen exactly to:
      - `provider_route_contract_parity_pct`
      - `codex_candidate_contract_valid_pct`
      - `provider_parity_replay_determinism_pct`
    - key-name mismatches fail closed deterministically
  - output:
    - deterministic JSON summary on stdout with frozen shape:
      - `schema = "s9_trigger_check@1"`
      - `metrics_path`
      - `threshold`
      - `required_keys`
      - `missing`
      - `below`
      - `pass`
    - stdout always emits the `s9_trigger_check@1` JSON summary (including failures).
    - when JSON text is emitted, serialization follows canonical JSON profile (sorted keys, compact separators, UTF-8).
    - list ordering is frozen:
      - `required_keys` preserves the frozen key order from this lock.
      - `missing` is sorted lexicographically.
      - `below` is sorted lexicographically by metric key.
    - deterministic error summary on stderr for failures
    - stderr is additive failure-only human hint output and does not replace stdout summary emission.
  - exit codes:
    - `0` pass
    - `1` fail (missing key, parse/shape error, or threshold failure)
- v25 default reference rationale lock is frozen:
  - v26 lock binds S9 hard-precondition checks to v25 closeout evidence; script default mirrors this binding until a future lock updates it.
- Side-effect lock is frozen:
  - script is read-only and writes no artifacts.

### Acceptance

- Pass-case test (all keys present and `>= threshold`) returns exit `0`.
- Missing-default-path test returns exit `1` with deterministic error payload.
- Cross-CWD default-path test runs from repository root and non-root working directory (for example `apps/api`) and resolves the same default metrics artifact deterministically.
- Missing-key test returns exit `1` with deterministic error payload.
- Below-threshold test returns exit `1` with deterministic error payload.
- Malformed payload test returns exit `1` deterministically.
- Success/failure stdout payloads are asserted against frozen `s9_trigger_check@1` key set.

## A2) v26 Allowlist Normalization Lock-Alignment

### Goal

Align v26 parity normalization implementation with frozen allowlist-only lock semantics.

### Scope

- Update v26 parity normalization path handling in:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
- Add focused parity projection tests.

### Locks

- Allowlist lock is frozen to exactly:
  - `baseline_path`
  - `candidate_path`
  - `report_path`
  - `manifest_path`
- Non-allowlist immutability lock is frozen:
  - non-allowlisted keys must not be normalized even when names end in `_path` or `_paths`.
- Recursive application-scope lock is frozen:
  - allowlist normalization applies recursively at any dict depth.
  - normalization applies only when a dict key is exactly one of:
    - `baseline_path`
    - `candidate_path`
    - `report_path`
    - `manifest_path`
- Synthetic adversarial fixture lock is frozen:
  - tests must include representative non-allowlisted path-like keys (for example `extra_path`, `extra_paths`) and assert they remain byte-identical.
- Compatibility lock is frozen:
  - locked fixture parity/hash outputs remain unchanged after correction.
- Precondition audit lock is frozen:
  - before landing correction, audit locked v26 parity fixtures for non-allowlisted keys ending in `_path` or `_paths`.
  - audit enforcement must be executable (dedicated test or CI-invoked script); manual-only audit is out-of-scope.
  - if any such key would change normalization output under allowlist-only behavior, fail closed with deterministic message and require explicit follow-on lock decision before changing historical parity/hash outputs.

### Acceptance

- Key-level test proves allowlisted keys can normalize while non-allowlisted keys remain unchanged.
- Locked v26 parity fixtures remain hash-identical.
- Executable audit test/script produces deterministic report output and fails closed on detected non-allowlisted path-like mutation risk.

## A3) Deterministic Tooling Env Enforcement

### Goal

Enforce deterministic tooling env constraints at entrypoints rather than relying on caller shell discipline.

### Scope

- Add shared helper under runtime tooling package.
- Wire helper into entrypoints:
  - `apps/api/scripts/build_stop_gate_metrics.py`
  - `apps/api/scripts/build_quality_dashboard.py`

### Locks

- Policy lock is frozen to set-then-assert:
  - if `TZ` or `LC_ALL` are missing, set to `UTC` and `C` respectively.
  - after setting `TZ`, helper must call `time.tzset()` when available; absence of `tzset` is not an error.
  - if present with conflicting values, fail closed deterministically.
- Conflict-definition lock is frozen:
  - comparison uses normalized env values (`strip()` applied before compare).
  - empty or whitespace-only values are conflicting.
  - for enforced keys, any value other than exact `TZ=UTC` and `LC_ALL=C` is conflicting.
- `LANG` handling lock is frozen:
  - this arc enforces `TZ` and `LC_ALL` only; `LANG` is not a pass/fail comparator in this slice.
- CI/env continuity lock is frozen:
  - deterministic tooling entrypoints in this arc require `LC_ALL=C` (not `C.UTF-8`) and `TZ=UTC`.
- Helper-reuse continuity lock is frozen:
  - A3 helper is the sole blessed mechanism for deterministic env enforcement on tooling entrypoints in this arc.
- Output continuity lock is frozen:
  - entrypoint wiring must not change locked fixture outputs.

### Acceptance

- Missing-env case auto-sets and proceeds deterministically.
- Correct-env case passes unchanged.
- Conflicting-env case fails deterministically.
- Locked fixture outputs remain unchanged.

## A4) Canonical JSON Conformance Suite

### Goal

Prove canonical-json behavior is identical across existing helper implementations used by deterministic hashing flows.

### Scope

- Add conformance tests comparing canonical output/hash on shared corpora across helper implementations in:
  - API
  - runtime
  - kernel/related helper modules
  - core-ir / explain / semantic-depth helper modules

### Locks

- No-helper-mutation lock is frozen:
  - this slice introduces test coverage only unless a later lock explicitly authorizes helper consolidation.
- Corpus determinism lock is frozen:
  - fixture corpus is static and deterministic.
- Corpus validity lock is frozen:
  - conformance corpus is JSON-serializable only (no `NaN`, `Infinity`, `bytes`, or non-JSON runtime objects).
- Equality semantics lock is frozen:
  - conformance checks require both:
    - canonical JSON text equality across helper entrypoints
    - `sha256` hash equality over canonical JSON text across helper entrypoints
  - canonical JSON text comparison is strict:
    - returned value is UTF-8 text (`str`) with no trailing newline.
    - trailing newline differences are mismatches.
- Helper-entrypoint lock is frozen:
  - conformance targets are exactly:
    - `apps/api/src/adeu_api/hashing.py::canonical_json`
    - `apps/api/src/adeu_api/hashing.py::sha256_canonical_json`
    - `packages/urm_runtime/src/urm_runtime/hashing.py::canonical_json`
    - `packages/urm_runtime/src/urm_runtime/hashing.py::sha256_canonical_json`
    - `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py::_canonical_json`
    - `packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py::_canonical_json`
    - `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py::_canonical_json`
    - `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py::_canonical_json`
    - `packages/adeu_explain/src/adeu_explain/explain_diff.py::_canonical_json`
    - `packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py::_canonical_json`
- Coverage-completeness lock is frozen:
  - A4 conformance coverage in this arc includes all currently known repo-local `canonical_json` / `_canonical_json` helper entrypoints used by deterministic hashing flows.
  - omissions fail closed in tests.
- Entrypoint-availability and discovery-report lock is frozen:
  - missing or moved frozen helper entrypoints fail closed in tests.
  - suite emits deterministic, lexicographically sorted discovery report of repo-local `canonical_json` / `_canonical_json` definitions for visibility only.
  - discovery report does not expand the frozen authoritative conformance target set in this arc.

### Acceptance

- Conformance tests pass with identical canonical JSON outputs/hashes across all targeted helpers.
- Coverage guard test proves the full frozen helper-entrypoint set is exercised by the conformance suite.

## Stop-Gate Impact (v27)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity metrics remain required.
- v27 closeout must include runtime-observability comparison row against v26 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v27 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md` inside a machine-checkable JSON block.
- Runtime-observability comparison schema lock is frozen:
  - JSON block schema:
    - `schema = "runtime_observability_comparison@1"`
  - required keys:
    - `baseline_arc`
    - `current_arc`
    - `baseline_elapsed_ms`
    - `current_elapsed_ms`
    - `delta_ms`
  - optional keys:
    - `notes`

## Error/Exit Policy (v27)

- No new URM error-code family is planned in this arc.
- `A1` checker script uses deterministic exit codes (`0`/`1`) and deterministic stderr/stdout payload shapes.

## Commit / PR Plan (Small Green PRs)

1. `tooling: add deterministic S9 trigger checker script and fail-closed tests`
2. `metrics: align v26 parity normalization to frozen allowlist and add boundary tests`
3. `tooling: add deterministic env helper and wire stop-gate/dashboard entrypoints`
4. `tests: add canonical-json conformance suite across API/runtime/kernel helpers`

## Intermediate Preconditions (for v27 start)

1. v26 lock/closeout artifacts remain authoritative and unchanged.
2. v25 closeout metrics artifact is present for S9 precondition checks:
   - `artifacts/stop_gate/metrics_v25_closeout.json`
3. No L2 release is introduced in this arc.
4. CI precondition for A3 is satisfied:
   - stop-gate/dashboard entrypoint jobs must not pre-set `LC_ALL` to non-`C` values.

## Exit Criteria (Draft)

- `A1` through `A4` merged with green CI.
- No new stop-gate metric keys introduced.
- Locked v26 fixture parity outputs remain unchanged.
- Existing continuity thresholds remain at required values.
- v27 closeout evidence includes runtime-observability comparison row against v26 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
