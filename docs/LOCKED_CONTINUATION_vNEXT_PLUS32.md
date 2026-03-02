# Locked Continuation vNext+32 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS31.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+31` (`E1`-`E2`) is merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md`.
- Post-v31 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`.
- Selected v32 thin-slice default is repo-root resolution consolidation
  (`V31-D` path family from options menu).
- `vNext+32` is constrained to deterministic additive hardening only:
  - no solver/runtime semantics release,
  - no policy-enforcement expansion,
  - no L2 boundary release.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS31.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v32,
  - v32 keyset must be exactly equal to v31 keyset (set equality, derived cardinality),
  - keyset authority is `stop_gate_metrics@1` payload field `metrics` object keys only.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion.
- Non-enforcement/no-mutation continuity remains frozen for evidence surfaces in this arc.
- L2 boundaries remain deferred in this arc:
  - no `/urm/worker/run` governance boundary release,
  - no proposer idempotency persistence boundary release.
- L2 scaffolding prohibition remains frozen:
  - no partial implementation of L2 authority/persistence surfaces may land under this L1/L0 arc.
- v31 continuity guarantees remain frozen:
  - Evidence Explorer template-path contract closure (`V31-A`) remains authoritative,
  - closeout consistency lint and continuity assertion grammar (`V31-B`) remain authoritative.
- Closeout observability continuity lock is frozen:
  - v32 closeout must include a runtime-observability comparison row against v31 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `F1` canonical repo-root resolution consolidation (`V31-D`)
2. `F2` repo-root determinism/parity regression guard suite (`V31-D`)

Out-of-scope note:

- any runtime policy-enforcement behavior changes,
- any `SEMANTICS_v4` runtime contract release,
- any L2 governance/persistence releases (`V31-F`, `V31-G`),
- formal-lane expansion path (`V31-C`),
- worker CLI safety policy path (`V31-E`),
- workspace-marker offloading (for example `.odeu-workspace`) and
  cross-language resolver contract expansion,
- new stop-gate metric keys or schema-family forks.

## F1) Canonical Repo-Root Resolution Consolidation (`V31-D`)

### Goal

Replace fragmented repo-root discovery logic with one canonical deterministic resolver flow.

### Scope

- Consolidate script/test/runtime root resolution to one canonical helper surface.
- Canonical helper authority for this arc:
  - `packages/adeu_ir/src/adeu_ir/repo.py` (`repo_root`).
- Migrate known duplicated callsites in scope to canonical helper semantics:
  - `apps/api/scripts/check_s9_triggers.py` (`_repo_root`)
  - `apps/api/tests/path_helpers.py` (`repo_root`)
  - `apps/api/tests/test_check_s9_triggers.py` (`_repo_root`)
  - `apps/api/tests/test_canonical_json_conformance_vnext_plus27.py` (`_repo_root`)
  - `packages/urm_runtime/src/urm_runtime/stop_gate_registry.py` (`discover_repo_root`, `default_stop_gate_manifest_path`)
- Preserve behavior-compatible outputs for business logic and policy logic.

### Locks

- Canonical helper authority lock is frozen:
  - `repo_root` in `packages/adeu_ir/src/adeu_ir/repo.py` is the single resolution authority in this arc.
- Resolution precedence lock is frozen:
  - `ADEU_REPO_ROOT` when set and valid,
  - otherwise nearest ancestor satisfying `pyproject.toml` +
    `packages/urm_runtime/`,
  - otherwise nearest ancestor containing `.git` marker (directory or file),
  - otherwise fail closed.
- Precedence-delta acknowledgment lock is frozen:
  - this arc intentionally changes canonical precedence from legacy
    `.git`-first behavior to structural-marker-first behavior.
  - this is a bounded deterministic behavior change within resolver-only
    surfaces, not a runtime policy semantic release.
- Canonicalization lock is frozen:
  - resolver canonicalizes anchor paths with symlink resolution before upward
    traversal (`resolve(strict=True)` semantics).
- Marker precision lock is frozen:
  - `pyproject.toml` + `packages/urm_runtime/` is the only non-env
    structural marker pair accepted in this arc.
- Structural-marker export policy lock is frozen:
  - source exports/checkouts that do not contain `packages/urm_runtime/`
    must provide valid `ADEU_REPO_ROOT`; fallback discovery in such layouts
    is out-of-scope for this arc.
- `.git` marker semantics lock is frozen:
  - `.git` fallback accepts either directory or file presence.
- `ADEU_REPO_ROOT` normalization lock is frozen:
  - input must be absolute and canonicalized (`expanduser` +
    `resolve(strict=True)` semantics).
  - relative env-root values are invalid and fail closed.
- Env-strictness transition lock is frozen:
  - legacy silent acceptance of relative `ADEU_REPO_ROOT` values is removed.
  - relative env-root inputs fail closed before fallback traversal.
- Env-strictness migration note (docs-only) is frozen:
  - this is an intentional tooling-configuration breaking change for
    deterministic resolution.
  - canonical operator example: `export ADEU_REPO_ROOT="$(pwd -P)"`.
- Marker disagreement lock is frozen:
  - if `ADEU_REPO_ROOT` is set but does not satisfy required marker validity, fail closed.
  - no silent fallback away from an explicitly configured env root.
- Resolver anchor lock is frozen:
  - when `ADEU_REPO_ROOT` is not set, in-scope callsites must pass explicit
    anchor derived from callsite module path (`Path(__file__).resolve()`),
    not process CWD.
  - runtime entrypoints must anchor from their own module file path (or an
    explicitly injected anchor), never from CWD.
- Resolver cache-strategy lock is frozen:
  - anchor-parameterized canonical resolver may not use
    `lru_cache(maxsize=1)` behavior in this arc.
  - either caching is disabled or cache keys are exactly
    `(canonical_anchor, canonical_env_root_or_empty)`.
  - implicit global state (for example `Path.cwd()`) is forbidden in cache keys.
- CWD-independence lock is frozen:
  - resolver outcomes for identical filesystem state may not depend on caller
    working directory when anchor is explicit.
- Duplicate resolver removal lock is frozen:
  - bespoke check-then-walk repo-root helpers in in-scope callsites are removed or converted to canonical helper delegation.
- In-scope migration boundary lock is frozen:
  - only callsites listed in this lock are mandatory migration scope.
  - newly discovered duplicate callsites are deferred unless they are
    strictly equivalent and low-risk to migrate in the same slice.
- Runtime helper continuity lock is frozen:
  - `discover_repo_root`-based manifest defaults remain callable in this arc,
  - implementation may delegate to canonical helper but may not introduce path nondeterminism.
- Legacy-helper deprecation-observability lock is frozen:
  - if legacy resolver helpers are retained as delegation shims in this arc,
    calls must emit deterministic `DeprecationWarning` with stable message
    prefix for migration tracking.
  - deprecation warnings in this arc are informational by default and may not
    fail CI unless a lane explicitly opts into warning-as-error policy.
- No-network/no-provider lock is frozen:
  - no provider dispatch or outbound-network behavior is introduced by this
    slice.
- No-provider-init-side-effects lock is frozen:
  - resolver flows may not trigger provider client initialization side effects.
- Business-output continuity lock is frozen:
  - no business/policy decision output contract changes are introduced by resolver consolidation alone.
- Deterministic error semantics lock is frozen:
  - unresolved root conditions fail closed with deterministic error behavior.
  - non-existent paths under strict canonicalization fail closed before
    fallback traversal.
- Error-shape lock is frozen:
  - resolver-level failures use deterministic exception class and stable
    message prefix.
  - CLI-facing wrappers retain deterministic structured failure payloads
    (`code`, `message`) where already present.

### Acceptance

- In-scope script/test/runtime callsites resolve repository root deterministically through canonical helper semantics.
- Valid `ADEU_REPO_ROOT` override behavior remains deterministic and explicit.
- Invalid `ADEU_REPO_ROOT` configuration fails closed with no silent fallback.
- Default manifest and artifact path derivations remain behavior-compatible
  for normal checkouts.
- Normal-checkout definition lock is frozen:
  - checkout includes `pyproject.toml` and `packages/urm_runtime/` at
    repository root, with or without `.git` marker presence.

## F2) Repo-Root Determinism/Parity Regression Guards (`V31-D`)

### Goal

Prove `F1` consolidation is deterministic, behavior-preserving, and free from hidden resolver drift.

### Scope

- Add deterministic regression tests/guards for:
  - precedence order (`ADEU_REPO_ROOT`, marker fallback, fail-closed terminal path),
  - invalid env-root rejection behavior,
  - CWD-independence across in-scope callsites,
  - parity against frozen expected outputs under v32 resolver rules for
    representative fixtures.
- Cross-CWD test mechanism lock is frozen:
  - CWD-independence coverage uses subprocess execution or controlled
    `chdir` fixtures with deterministic restoration.
- Parity baseline mechanism is frozen:
  - parity assertions use frozen golden expected resolved-path outputs per
    fixture layout and env setting.
  - test-only duplication of removed legacy resolvers is out-of-scope.
  - golden comparisons may not assert raw host-absolute paths; comparisons
    must be fixture-root-relative POSIX-normalized expectations.

### Locks

- No-new-metric-keys lock is frozen:
  - v32 tests may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v31 continuity metrics remain at required values.
- Deterministic-ordering lock is frozen:
  - guard outputs and compared path lists are emitted in deterministic sorted order.
- Path-normalization lock is frozen:
  - resolver-path comparisons in guards use repository-relative POSIX path
    normalization (`as_posix()`), not host-native separators.
- Fail-closed regression lock is frozen:
  - detected resolver precedence drift or CWD-coupled behavior fails CI and blocks merge.
- No-provider/no-network guard lock is frozen:
  - tests fail closed when in-scope resolver flows trigger provider dispatch,
    outbound-network calls, or provider-client initialization side effects.
- Fixture-mutation guard lock is frozen:
  - guard suite includes deterministic pre/post fixture snapshot checks and fails closed on mutation.

### Acceptance

- Guard suites pass deterministically across reruns.
- Resolver precedence and invalid-env behavior are test-covered and deterministic.
- No provider/network side effects are introduced by in-scope resolver flows.

## Stop-Gate Impact (v32)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v32 closeout must include runtime-observability comparison row against v31 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v32 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS32.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v32)

- No new URM error-code family is introduced in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `tooling: consolidate repo-root resolution to canonical helper across scripts/tests/runtime callsites`
2. `tests: add v32 repo-root determinism and parity guard suite`

## Intermediate Preconditions (for v32 start)

1. v31 lock/closeout artifacts remain authoritative and unchanged.
2. v31 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md`
3. Existing resolver helpers remain available at v32 start:
   - `packages/adeu_ir/src/adeu_ir/repo.py` (`repo_root`)
   - `packages/urm_runtime/src/urm_runtime/stop_gate_registry.py` (`discover_repo_root`)
4. Existing in-scope duplicate resolver callsites remain identifiable:
   - `apps/api/scripts/check_s9_triggers.py`
   - `apps/api/tests/path_helpers.py`
   - `apps/api/tests/test_check_s9_triggers.py`
   - `apps/api/tests/test_canonical_json_conformance_vnext_plus27.py`
5. No L2 boundary release is introduced in this arc.

## Exit Criteria (Draft)

- `F1` and `F2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- In-scope repo-root resolution paths are consolidated to canonical helper semantics under frozen precedence rules.
- Resolver guard suites pass deterministically on baseline and reruns.
- v32 closeout evidence includes runtime-observability comparison row against v31 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
