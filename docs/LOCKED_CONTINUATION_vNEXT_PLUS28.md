# Locked Continuation vNext+28 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v4.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v4_FACT_CHECKS.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+27` (`A1`-`A4`) is merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`.
- Consolidated territory planning sequence remains:
  - `vNext+28 = W2 / Path A` (tooling sustainability consolidation).
- `vNext+28` is constrained to deterministic tooling sustainability only:
  - single-source active-manifest registry first
  - stop-gate internal modularization with compatibility facade second
  - deterministic v26 tooling transfer-report regeneration formalization third
  - parity/regression guard rails and continuity proof fourth

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md` remain authoritative for baseline semantics.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remains frozen and unchanged.
- Stop-gate schema-family remains unchanged:
  - `stop_gate_metrics@1` only; no schema fork in this arc.
- Stop-gate metric-key policy for this arc is frozen:
  - no new metric keys are introduced in v28.
- Stop-gate metric-cardinality continuity lock is frozen:
  - total stop-gate metric-key count remains `54` in this arc.
- Existing continuity thresholds from prior arcs remain required and unchanged.
- Bounded behavior-change lock is frozen:
  - `B1` intentionally introduces fail-closed behavior for inactive-version CLI flags.
  - this is a lock-alignment correction to enforce frozen active-version boundaries.
- Provider surface continuity remains frozen:
  - no provider expansion or proposer-surface expansion in this arc.
- Non-enforcement/no-mutation continuity remains frozen for tooling paths.
- L2 boundaries remain deferred in this arc:
  - no default-on `/urm/worker/run` governance release,
  - no persistent proposer idempotency storage release.
- Closeout observability continuity lock is frozen:
  - v28 closeout must include runtime-observability comparison row against v27 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with four implementation slices (one PR each):

1. `B1` active stop-gate manifest registry consolidation (single source of truth)
2. `B2` stop-gate tooling modularization with compatibility facade (behavior-preserving)
3. `B3` deterministic v26 tooling transfer-report builder + script formalization
4. `B4` parity/regression guard suite for `B1`-`B3` continuity proof

Out-of-scope note:

- read-only evidence explorer product surface work (planned for v29)
- formal ODEU implementation lane expansion (planned for v30)
- any L2 boundary releases
- new `/urm/...` runtime endpoint additions
- new stop-gate metric keys or stop-gate schema-family forks
- externalizing active-manifest registry to root-level JSON/TOML for non-Python consumers
- generic multi-arc transfer-report pipeline replacing per-arc builder/script entrypoints

## B1) Active Manifest Registry Consolidation

### Goal

Eliminate duplicated active stop-gate manifest version declarations across runtime/scripts/tests.

### Scope

- Introduce one runtime-owned active-manifest registry consumed by:
  - `apps/api/tests/test_tooling_z4_guards.py`
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
  - `apps/api/scripts/build_stop_gate_metrics.py`
- Migrate any other stop-gate tests carrying local active-version tuples to registry consumption in this arc.
- Keep current CLI option surface and default manifest-path behavior unchanged.

### Locks

- Single-source registry lock is frozen:
  - active manifest versions are centrally declared once and imported by callers.
- Registry module location lock is frozen:
  - authoritative registry module path:
    - `packages/urm_runtime/src/urm_runtime/stop_gate_registry.py`
- Registry import-light lock is frozen:
  - registry module may expose constants/path resolvers only and must not import
    `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`.
  - registry imports must remain side-effect free for script/test startup.
- Active-version set lock is frozen to exactly:
  - `7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26`
- Legacy-set equivalence lock is frozen:
  - registry active-version set must equal the frozen v27 baseline set previously declared in
    `apps/api/scripts/build_stop_gate_metrics.py::_ACTIVE_MANIFEST_VERSIONS`.
- Intentional-gap lock is frozen:
  - omission of `vNext+12` from the active-version set is intentional in this arc and must not be auto-filled by normalization/lint logic.
  - drift detectors treat the frozen set above as authoritative.
- Ordering lock is frozen:
  - version iteration order is deterministic ascending numeric order.
- Default path continuity lock is frozen:
  - each version default remains `apps/api/fixtures/stop_gate/vnext_plus{N}_manifest.json`.
- Default-path resolution lock is frozen:
  - registry default path resolution is deterministic and repository-root anchored.
  - repository root discovery follows runtime-owned deterministic repo-root helper behavior;
    caller CWD must not affect resolved defaults.
- Default-path byte-identity lock is frozen:
  - resolved default manifest path strings for active versions must remain byte-identical to
    v27 baseline defaults.
- CLI compatibility lock is frozen:
  - existing `--vnext-plus{N}-manifest` flags remain accepted.
- CLI override precedence lock is frozen:
  - for active versions only, explicit `--vnext-plus{N}-manifest` values override registry defaults for version `N`.
- Inactive-version CLI lock is frozen:
  - inactive-version flags (including `--vnext-plus12-manifest`) are unsupported in this arc.
  - attempts to pass inactive-version flags fail closed deterministically before stop-gate computation starts.
- No-local-tuple lock is frozen:
  - hard-coded active-version tuples are not allowed outside the frozen registry module.

### Acceptance

- Registry-consumer parity test proves script/runtime/tests consume the same active-version set and ordering.
- Static drift detector test fails closed when a local hard-coded active-version tuple is reintroduced outside the registry module.
- CLI override precedence test proves active-version override flags replace registry defaults deterministically.
- Inactive-version CLI test proves unsupported version flags fail closed deterministically and emit no output artifacts.
- Default-path byte-identity test proves active-version default manifest paths are unchanged from v27 baseline.
- Existing CLI invocations produce unchanged outputs for identical inputs.

## B2) Stop-Gate Internal Modularization (Compatibility Facade)

### Goal

Reduce stop-gate mega-module maintenance risk while preserving externally observable behavior.

### Scope

- Extract internal stop-gate logic into runtime-owned submodules/helpers.
- Preserve public compatibility facade at:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
- Keep script and call-site interfaces unchanged.

### Locks

- Public API continuity lock is frozen:
  - existing public entrypoints remain stable and behavior-compatible.
- Public symbol-set lock is frozen for compatibility facade import path:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` must continue exporting:
    - `STOP_GATE_SCHEMA`
    - `StopGateMetricsInput`
    - `build_stop_gate_metrics_from_input`
    - `build_stop_gate_metrics`
    - `stop_gate_markdown`
- Public signature continuity lock is frozen:
  - exported compatibility-facade symbol call signatures and default values remain identical to frozen v27 baseline.
  - signature parity is asserted from a deterministic v27 snapshot fixture under tests.
- Behavior-parity lock is frozen:
  - for locked fixture inputs, stop-gate outputs remain canonical-hash identical under existing frozen parity projection rules.
- No-side-effects-expansion lock is frozen:
  - modularization may not introduce new writes, provider calls, or policy side effects.
- Import-boundary lock is frozen:
  - modularized stop-gate tooling modules may not import API server runtime modules
    (for example `adeu_api.main` or `adeu_api.storage`).
- Error-domain continuity lock is frozen:
  - reuse existing tooling/common error-domain codes; no new error-code family in this slice.
- Created-at canonical-helper lock is frozen:
  - recursive `created_at` stripping is consolidated into one runtime-owned helper:
    - `packages/urm_runtime/src/urm_runtime/stop_gate_normalization.py::strip_created_at_recursive`
  - stop-gate parity hashing and transfer-report regeneration paths in this arc must use this helper and may not fork ad hoc recursive strippers.
- Legacy helper equivalence lock is frozen:
  - consolidated helper behavior must be semantically equivalent to legacy helper behavior for frozen parity inputs from:
    - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py::_strip_created_at_fields`
    - `apps/api/src/adeu_api/hashing.py::strip_created_at_recursive`
    - `apps/api/src/adeu_api/trust_invariant_vnext_plus22.py::_strip_created_at_recursive`
    - `apps/api/src/adeu_api/semantics_v4_candidate_vnext_plus23.py::_strip_created_at_recursive`
  - equivalence in this arc means:
    - strip only keys exactly named `created_at` recursively
    - preserve non-`created_at` values and list structure
    - emit deterministic key ordering for downstream canonical-hash parity.

### Acceptance

- Baseline-vs-candidate parity tests pass on locked fixture suites.
- Existing script/API call paths continue to pass unchanged.
- Signature-compatibility test (`inspect.signature`) passes against frozen v27 facade snapshot.
- Coverage test proves all v28 stop-gate parity hashing paths use the single frozen `strip_created_at_recursive` helper.
- Legacy-equivalence corpus test proves consolidated helper matches frozen legacy helper outputs on locked fixture corpus before legacy call sites are redirected.

## B3) Deterministic v26 Tooling Transfer-Report Regeneration

### Goal

Make `vNext+26` tooling transfer-report regeneration mechanical and deterministic with explicit contracts.

### Scope

- Add runtime-owned v26 tooling transfer-report data builder under `packages/urm_runtime/src/urm_runtime/`.
- Add deterministic script entrypoint under `apps/api/scripts/` to generate:
  - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
- Builder emits machine-checkable JSON payload data; script formats markdown wrapper.
- Script exposes deterministic inputs for regeneration:
  - `--vnext-plus26-manifest` (default `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`)
  - `--stop-gate-metrics` (default `artifacts/stop_gate/metrics_v26_closeout.json`)
  - `--s9-metrics-path` (default `artifacts/stop_gate/metrics_v25_closeout.json`)

### Locks

- Output-path lock is frozen:
  - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`.
- Schema lock is frozen:
  - JSON block `schema = "tooling_transfer_report.vnext_plus26@1"`.
- Top-level key lock is frozen:
  - `vnext_plus26_manifest_hash`
  - `coverage_summary`
  - `stop_gate_input_model_parity_summary`
  - `transfer_report_builder_parity_summary`
  - `s9_trigger_check_summary`
  - `replay_summary`
- Runtime-observability key lock for `replay_summary.runtime_observability` is frozen:
  - `elapsed_ms`
  - `total_fixtures`
  - `total_replays`
  - `bytes_hashed_per_replay`
  - `bytes_hashed_total`
- Baseline extraction lock is frozen:
  - parity baseline is extracted from checked-in report markdown by selecting the unique fenced JSON block whose `schema` equals `tooling_transfer_report.vnext_plus26@1`.
  - missing block, duplicate matching blocks, or parse/schema mismatch fail closed.
- S9 summary source lock is frozen:
  - `s9_trigger_check_summary` is derived from v25 closeout metrics by default:
    - `artifacts/stop_gate/metrics_v25_closeout.json`
  - required S9 keys and threshold remain:
    - `provider_route_contract_parity_pct`
    - `codex_candidate_contract_valid_pct`
    - `provider_parity_replay_determinism_pct`
    - threshold `100.0`
- Parity basis lock is frozen:
  - parity compares parsed JSON payloads (canonical JSON hash), not raw markdown bytes.
- No-clobber-before-compare lock is frozen:
  - script extracts baseline payload first, computes regenerated payload, and performs parity comparison before any write.
  - default mode is check-only (no file mutation).
  - write mode is explicit via `--write` and may write only after parity comparison passes.
- Markdown wrapper continuity lock is frozen:
  - script may update deterministic heading/description wrappers and the fenced JSON payload block.
  - builder logic remains runtime-owned; API/docs layers may not fork equivalent builder logic.
- Deterministic-source lock is frozen:
  - builder reads only frozen manifests and persisted fixture/metrics artifacts declared in repository.
  - no live provider calls or undeclared discovery paths.
- Arc-local builder scope lock is frozen:
  - this arc formalizes v26-specific builder/script only.
  - generic cross-arc transfer-report pipeline consolidation is deferred to a future lock.
- Pure-function regeneration lock is frozen:
  - v26 transfer-report regeneration is a pure computation over persisted inputs and deterministic flags.
  - regeneration must not introduce new stop-gate metric keys, schema families, or evidence families.

### Acceptance

- Regenerated payload hash matches extracted baseline payload hash for identical inputs.
- Wrong/missing/duplicate schema-block extraction cases fail closed deterministically.
- Repeated script runs are idempotent for identical inputs.
- Check-only mode leaves output markdown byte-identical when parity fails.
- `--write` mode fails closed (no mutation) when parity check fails.
- Non-expansion assertion proves regeneration path does not emit or require any new stop-gate metric keys.

## B4) Parity and Regression Guard Suite

### Goal

Prove `B1`-`B3` consolidation is behavior-preserving and reproducible.

### Scope

- Add regression/parity coverage for:
  - manifest-registry consumer consistency
  - stop-gate modularization baseline-vs-candidate continuity
  - v26 tooling transfer-report payload regeneration parity

### Locks

- No-new-metric-keys lock is frozen:
  - v28 test additions may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - v26 tooling parity metrics remain at frozen thresholds:
    - `artifact_stop_gate_input_model_parity_pct == 100.0`
    - `artifact_transfer_report_builder_parity_pct == 100.0`
- Fail-closed regression lock is frozen:
  - detected canonical-hash drift in locked baseline comparisons fails CI and blocks merge.
- Static drift-detector lock is frozen:
  - suite includes deterministic static checks that fail closed when:
    - active manifest version tuples are duplicated outside the frozen registry module.
    - duplicated hard-coded stop-gate default manifest path templates are introduced outside approved registry/path-resolver modules.
- Minimum adversarial guard set lock is frozen:
  - inactive-version invocation case (for example `--vnext-plus12-manifest`) fails closed.
  - duplicated active-version tuple outside registry module fails closed.
  - path-like non-allowlisted keys remain non-normalized in parity projection checks.

### Acceptance

- Guard suites pass deterministically across reruns.
- Locked continuity metrics and parity evidence remain unchanged.
- Static drift detector reports are deterministic and lexicographically ordered.

## Stop-Gate Impact (v28)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity metrics remain required.
- v28 closeout must include runtime-observability comparison row against v27 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v28 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS28.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v28)

- No new URM error-code family is planned in this arc.
- Deterministic tooling scripts in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `runtime: centralize active stop-gate manifest registry and wire script/runtime consumers`
2. `runtime: modularize stop-gate internals behind compatibility facade`
3. `tooling: add deterministic vnext+26 tooling transfer-report builder and script`
4. `tests: add vnext+28 parity/regression guard suite for registry/modularization/report regen`

## Intermediate Preconditions (for v28 start)

1. v27 lock/closeout artifacts remain authoritative and unchanged.
2. v26 tooling transfer-report baseline exists:
   - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
3. v26 closeout metrics remain available for transfer-report regeneration checks:
   - `artifacts/stop_gate/metrics_v26_closeout.json`
4. No L2 release is introduced in this arc.

## Exit Criteria (Draft)

- `B1` through `B4` merged with green CI.
- No new stop-gate metric keys introduced.
- Locked fixture parity outputs remain unchanged.
- v26 tooling transfer-report payload regeneration is canonical-hash identical to locked baseline payload for identical inputs.
- Existing continuity thresholds remain at required values.
- v28 closeout evidence includes runtime-observability comparison row against v27 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
