# Locked Continuation vNext+34 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS33.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS33.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+33` (`G1`-`G2`) is merged on `main` via PR `#212` and PR `#213` with green CI checks.
- `vNext+33` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS33.md` with `all_passed = true`.
- Post-v33 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`.
- Selected v34 thin-slice default is formal ODEU template activation (evidence-only) (`V31-C` path family from options menu).
- `vNext+34` is constrained to deterministic additive hardening only:
  - no solver/runtime semantics release,
  - no policy-enforcement expansion,
  - no L2 boundary release.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS33.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v34,
  - v34 keyset must be exactly equal to v33 keyset (set equality, derived cardinality),
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
- v32 continuity guarantees remain frozen:
  - canonical repo-root resolution consolidation (`V31-D`, `F1`) remains authoritative,
  - repo-root determinism/parity guard suite (`V31-D`, `F2`) remains authoritative.
- v33 continuity guarantees remain frozen:
  - worker CLI fail-closed safety policy closure (`V31-E`, `G1`) remains authoritative,
  - worker CLI determinism/regression guard suite (`V31-E`, `G2`) remains authoritative.
- Closeout observability continuity lock is frozen:
  - v34 closeout must include a runtime-observability comparison row against v33 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `H1` formal ODEU evidence contract closure (`V31-C`)
2. `H2` formal-lane determinism/regression guard suite (`V31-C`)

Out-of-scope note:

- any runtime policy-enforcement behavior changes,
- any `SEMANTICS_v4` runtime contract release,
- any L2 governance/persistence releases (`V31-F`, `V31-G`),
- repo-root consolidation path (`V31-D`) beyond continuity maintenance,
- worker CLI safety path (`V31-E`) beyond continuity maintenance,
- dry-run/execute-probe capability detection migration for worker CLI path,
- diagnostic-tail schema expansion for formal report payloads (for example `lean_stderr_tail`),
- bounded parallel Lean execution/concurrency tuning,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v34)

- Formal diagnostics schema-hardening path (v35+) may evaluate optional deterministic diagnostic-tail fields with explicit schema-version treatment.
- Formal-lane throughput path (v35+) may evaluate bounded parallel Lean execution with deterministic ordering guarantees.

## H1) Formal ODEU Evidence Contract Closure (`V31-C`)

### Goal

Start a deterministic artifact-to-Lean agreement evidence report flow for core contract checks without enforcement release.

Lock-class rationale:

- this slice remains `L1` because it closes an evidence artifact contract surface (`odeu_agreement.report@0.1`) while runtime enforcement authority remains unchanged.
- terminology lock for this arc: "proof packet" refers only to the agreement evidence report payload (`odeu_agreement.report@0.1`); no second formal artifact family is introduced.

### Scope

- Fix ODEU prep compile/accessor drift in in-scope Lean/Python formal-lane surfaces where required for deterministic fixture execution:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`
  - `packages/adeu_lean/src/adeu_lean/runner.py`
- Freeze and harden deterministic fixture-to-request bridge and report emission authority on:
  - `packages/adeu_lean/src/adeu_lean/agreement.py` (`build_agreement_report_from_fixture_path`, `validate_agreement_report`)
  - `packages/adeu_lean/src/adeu_lean/models.py` (`OBLIGATION_KINDS`, `DEFAULT_SEMANTICS_VERSION`)
- Keep real-lane coverage anchored to existing formal lane checks:
  - `packages/adeu_lean/tests/test_agreement_real_lean.py`
  - `apps/api/tests/test_formal_lane_real_lean.py`
- Preserve evidence-only posture:
  - generated agreement evidence reports are read-only evidence artifacts,
  - no runtime policy mutation or enforcement release is introduced.

### Locks

- Runtime-validator authority lock is frozen:
  - runtime validator and existing policy lanes remain enforcement authority.
  - formal-lane agreement outputs in this arc are evidence-only.
- Formal-evidence schema boundary lock is frozen:
  - `odeu_agreement.fixtures@0.1` and `odeu_agreement.report@0.1` are repo-internal formal-lane evidence schemas in this arc.
  - public API/exported product schema commitment and external compatibility guarantees for these schemas are out-of-scope in v34.
- Agreement schema continuity lock is frozen:
  - fixture schema remains `odeu_agreement.fixtures@0.1`.
  - report schema remains `odeu_agreement.report@0.1`.
  - no schema-family fork or dual-schema acceptance path in this arc.
- Evidence artifact lifecycle lock is frozen:
  - authoritative v34 agreement evidence artifact is the in-memory validated report payload produced by the formal harness/test flow.
  - deterministic report hashing/identity assertions are computed from payload content, not filesystem location.
  - deterministic on-disk persistence contract for agreement report payloads is out-of-scope in this arc.
  - closeout evidence for replay determinism must reference deterministic guard outputs/assertions, not ad-hoc temporary file paths.
- Semantics-version continuity lock is frozen:
  - `proof_semantics_version` remains `adeu.lean.core.v1`.
  - no semantics version bump is introduced in this arc.
- Semantics terminology boundary lock is frozen:
  - request-level `semantics_version` and bundle/report-level `proof_semantics_version` remain distinct field names in this arc.
  - deterministic mapping is required: each generated request `semantics_version` must equal the active bundle/report `proof_semantics_version`.
  - alias expansion, field renaming, or independent dual-version tracking is out-of-scope in this arc.
- Semantics mismatch fail-closed lock is frozen:
  - any effective semantics-version mismatch in formal request generation/validation must fail closed with deterministic reason token `SEMANTICS_VERSION_MISMATCH`.
  - fixture/report inputs may not introduce per-row semantics-version overrides in this arc.
- Compile/accessor drift change-budget lock is frozen:
  - compile/accessor drift fixes in this arc are syntactic/structural compatibility fixes only.
  - drift fixes may not expand `OBLIGATION_KINDS`, may not change `DEFAULT_SEMANTICS_VERSION`, and may not reinterpret existing agreement report field meanings.
- Obligation-kind continuity lock is frozen:
  - obligation kind set remains exactly `OBLIGATION_KINDS` from `packages/adeu_lean/src/adeu_lean/models.py`.
  - no obligation-kind expansion or reinterpretation in this arc.
- Mapping/proof hash identity lock is frozen:
  - mapping/proof hash fields remain 64-char lowercase SHA-256 hex with deterministic construction.
- Agreement report identity projection lock is frozen:
  - v34 determinism comparisons for agreement report identity use canonical JSON serialization of the full validated report payload.
  - no field exclusions are permitted in this arc.
  - nondeterministic report fields (for example runtime timestamps) are out-of-scope and may not be added in this arc.
  - agreement report payload must not include nondeterministic observability fields such as `created_at`, `timestamp`, `generated_at`, `elapsed_ms`, or `duration_ms` in this arc.
- Deterministic ordering lock is frozen:
  - agreement report fixture rows remain sorted deterministically by `(fixture_id, obligation_kind)`.
- Formal execution timeout/classification lock is frozen:
  - formal-lane execution timeout for v34 real-lane checks is `formal_lean_timeout_ms = 15000`.
  - timeout/nonzero/launch-failure branches are classified deterministically as reason tokens:
    - `LEAN_TIMEOUT`
    - `LEAN_NONZERO_EXIT`
    - `LEAN_LAUNCH_FAILED`
- Formal reason-token placement lock is frozen:
  - authoritative timeout/nonzero/launch-failure reason tokens are carried in structured formal result fields (for example `LeanResult.details["reason"]`) rather than free-form prose.
  - test/log mirrors of reason tokens are informational only and non-authoritative.
  - these reason tokens are not URM error-code mappings.
- Formal timeout calibration lock is frozen:
  - before v34 freeze, timeout-budget calibration evidence must be recorded from at least two CI runs and referenced in `docs/ASSESSMENT_vNEXT_PLUS34_EDGES.md`.
  - timeout-budget adjustments are allowed only before lock freeze.
  - after freeze, timeout-budget changes require an explicit lock update in the same arc chain.
- Formal timeout cleanup lock is frozen:
  - timeout handling for Lean subprocess execution must fail closed with deterministic child-process cleanup.
  - in-scope runner implementation must apply process-group/session isolation and terminate the full spawned process group on timeout before returning `LEAN_TIMEOUT`.
  - timeout cleanup behavior may not leave long-lived orphan compiler/checker processes.
  - v34 `lean-formal` execution assumes Linux/POSIX process semantics; non-POSIX runner behavior for this lane is out-of-scope and may not introduce alternate cleanup semantics in this arc.
- Fail-closed formal-lane lock is frozen:
  - missing fixture, invalid fixture JSON/schema, unsupported result status, and Lean execution failures must fail closed with deterministic error semantics.
- Formal-lane error determinism lock is frozen:
  - deterministic failure assertions in this arc use structured fields (`code`, `reason`, `fixture_id`, `obligation_kind`) where present.
  - human prose in error messages is non-authoritative for determinism assertions.
  - no new URM error-code family is introduced by this lock.
- No-network/no-provider expansion lock is frozen:
  - this slice introduces no provider dispatch expansion and no outbound-network behavior.
- Frozen fixture corpus lock is frozen:
  - `packages/adeu_lean/tests/fixtures/agreement_fixtures_v30.json` remains the canonical corpus for v34 comparability.
  - new fixture-corpus expansion is deferred to v35+.

### Acceptance

- Deterministic generated Lean requests and agreement report artifacts replay to stable identities for frozen fixtures.
- Real Lean lane checks execute under CI lane gating and remain fail-closed.
- No runtime enforcement behavior changes are introduced by formal evidence generation alone.

## H2) Formal-Lane Determinism/Regression Guards (`V31-C`)

### Goal

Prove `H1` formal evidence flow is deterministic, regression-resistant, and contract-stable.

### Scope

- Add/adjust deterministic tests/guards for:
  - fixture-to-request deterministic generation over frozen fixtures,
  - semantics-version boundary enforcement (`proof_semantics_version`/`semantics_version` mapping and mismatch fail-closed behavior),
  - agreement report contract validation and summary invariants,
  - fail-closed behavior on invalid fixture/report payload shapes,
  - deterministic timeout/nonzero/launch-failure reason-token classification coverage via structured result fields,
  - no fixture mutation side effects during report generation,
  - canonical report replay identity checks over repeated runs,
  - real-lane determinism smoke under existing Lean CI lane.
- Keep real-lane CI anchor explicit:
  - `.github/workflows/ci.yml` job `lean-formal` remains required for v34 lane evidence.
- Keep deterministic environment/time posture in guard execution:
  - guard command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v34 tests may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v33 continuity metrics remain at required values.
- Deterministic-probe/runner lock is frozen:
  - guard outputs and compared report payloads are emitted in deterministic ordering.
- Semantics boundary guard lock is frozen:
  - tests must fail closed on effective semantics mismatch with deterministic reason token `SEMANTICS_VERSION_MISMATCH`.
  - tests must assert one effective semantics version across generated requests/report payload, equal to frozen `adeu.lean.core.v1`.
- Fail-closed regression lock is frozen:
  - regression that reintroduces permissive/non-deterministic handling for invalid formal-lane inputs fails CI and blocks merge.
- Real-lane CI lock is frozen:
  - `lean-formal` lane remains fail-closed for in-scope v34 formal checks.
  - required CI job-name string is exactly `lean-formal`; renaming requires explicit lock update in the same arc.
  - `lean-formal` lane must execute a deterministic Lean warm-up build step before timed pytest formal checks to reduce cold-start timeout flake risk.
  - warm-up step is preparation-only and may not alter formal result contract assertions.
- No-provider/no-network guard lock is frozen:
  - tests fail closed if in-scope formal evidence flows trigger provider expansion or outbound-network calls.
- Fixture-mutation guard lock is frozen:
  - formal fixture snapshots are checked pre/post run and must remain unchanged.
- Replay-identity guard lock is frozen:
  - for canonical frozen fixtures, agreement report generation run `3x` with identical inputs must produce byte-identical canonical JSON payloads and identical SHA-256 digests.

### Acceptance

- Guard suites pass deterministically across reruns.
- Formal-lane evidence contracts are test-covered, deterministic, and fail-closed.
- Canonical frozen-fixture replay produces byte-identical canonical report payloads and identical SHA-256 digests across `3x` reruns.
- Structured reason-token classification remains deterministic and machine-assertable for timeout/nonzero/launch-failure/mismatch branches.
- Timed formal execution path demonstrates deterministic timeout classification with no orphan-process side effects.
- No policy/enforcement side effects are introduced by in-scope formal-lane flows.

## Stop-Gate Impact (v34)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v34 closeout must include runtime-observability comparison row against v33 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v34 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS34.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v34)

- No new URM error-code family is introduced in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `formal: close deterministic ODEU evidence contract flow under real Lean lane`
2. `tests: add v34 formal-lane determinism and regression guard suite`

## Intermediate Preconditions (for v34 start)

1. v33 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v33 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS33.md`
3. In-scope formal-lane authority surfaces remain available at v34 start:
   - `packages/adeu_lean/src/adeu_lean/agreement.py`
   - `packages/adeu_lean/src/adeu_lean/runner.py`
   - `packages/adeu_lean/src/adeu_lean/models.py`
4. Existing frozen fixture bundle remains available for deterministic report generation:
   - `packages/adeu_lean/tests/fixtures/agreement_fixtures_v30.json`
5. Existing real-lane CI anchor remains enabled:
   - `.github/workflows/ci.yml` (`lean-formal` job)
6. Pre-freeze timeout calibration evidence is captured:
   - `docs/ASSESSMENT_vNEXT_PLUS34_EDGES.md` records at least two CI-run observations for the timed formal lane.
7. No L2 boundary release is introduced in this arc.

## Exit Criteria (Draft)

- `H1` and `H2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic formal-lane agreement evidence flow is closed and test-covered under evidence-only authority.
- v34 closeout evidence includes runtime-observability comparison row against v33 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
