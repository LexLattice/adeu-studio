# Locked Continuation vNext+30 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS29.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v4.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v4_FACT_CHECKS.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+29` (`C1`-`C4`) is merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md`.
- Consolidated territory planning sequence remains:
  - `vNext+30 = W4 / Path C` (additive formal ODEU lane with deterministic agreement checks).
- `vNext+30` is constrained to deterministic additive formal-lane work only:
  - deterministic Lean runner temp-path hardening first
  - fixture-backed Python↔Lean agreement harness second
  - first structural invariant theorem set and evidence mapping third
  - parity/regression guard rails and continuity proof fourth

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS29.md` remain authoritative for baseline semantics.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remains frozen and unchanged.
- Stop-gate schema-family remains unchanged:
  - `stop_gate_metrics@1` only; no schema fork in this arc.
- Stop-gate metric-key policy for this arc is frozen:
  - no new metric keys are introduced in v30.
- Stop-gate metric-keyset continuity lock is frozen:
  - v30 stop-gate metric keyset must be exactly equal to v29 keyset.
  - continuity is evaluated as set equality; absolute cardinality is derived, not hardcoded.
- Existing continuity thresholds from prior arcs remain required and unchanged.
- Provider surface continuity remains frozen:
  - no provider expansion or proposer-surface expansion in this arc.
- Non-enforcement/no-mutation continuity remains frozen for formal-lane outputs in v30.
- Bounded behavior-change lock is frozen:
  - `D1` introduces deterministic file-path behavior for Lean runner temporary files.
  - this is a lock-alignment correction for deterministic execution evidence, not an enforcement release.
- Proof-backend default continuity lock is frozen:
  - default proof backend remains unchanged (`mock` unless explicitly configured).
  - Lean backend remains explicit/opt-in.
- Terminology boundary lock is frozen:
  - `SEMANTICS_v3` governs runtime/solver semantics only.
  - formal-lane semantics in this arc are tracked as `proof_semantics_version`.
  - runtime/solver `semantics_version` and formal `proof_semantics_version` may not be conflated in contracts, schema keys, or evidence reports.
- Proof-semantics field continuity lock is frozen:
  - existing proof-backend contract field name `semantics_version` remains unchanged in v30 for backward compatibility.
  - v30 agreement/report artifacts expose the same value under `proof_semantics_version`.
  - mapping rule is frozen:
    - `proof_semantics_version = proof_request.semantics_version` (value-preserving rename only, no transformation).
- Lean-enabled CI lock is frozen:
  - at least one CI lane in this arc must execute D2/D3 agreement checks with a real Lean toolchain.
  - missing Lean toolchain in that lane is fail-closed for v30.
  - the required Lean lane must set `ADEU_PROOF_BACKEND=lean` (or equivalent explicit Lean backend selector) for formal checks in scope.
  - lane evidence for formal checks must record backend kind `lean`; backend kind `mock` is fail-closed for that lane.
- L2 boundaries remain deferred in this arc:
  - no default-on `/urm/worker/run` governance release,
  - no persistent proposer idempotency storage release.
- Closeout observability continuity lock is frozen:
  - v30 closeout must include runtime-observability comparison row against v29 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with four implementation slices (one PR each):

1. `D1` deterministic Lean runner temp-path hardening
2. `D2` fixture-backed Python↔Lean agreement harness (read-only evidence)
3. `D3` first structural invariant theorem set + formal evidence mapping continuity
4. `D4` parity/regression guard suite for `D1`-`D3` continuity proof

Out-of-scope note:

- any runtime policy-enforcement behavior driven by formal outputs
- any `SEMANTICS_v4` runtime contract release
- any L2 boundary releases
- new provider matrix entries or proposer endpoint expansion
- new stop-gate metric keys or stop-gate schema-family forks
- generalized theorem-library expansion beyond the frozen initial invariant set
- mutation/acknowledgement workflows for formal-lane outputs

## D1) Deterministic Lean Runner Temp-Path Hardening

### Goal

Eliminate nondeterministic temporary Lean filename behavior while preserving existing proof-check request/response contracts.

### Scope

- Replace nondeterministic temporary-file allocation in `packages/adeu_lean/src/adeu_lean/runner.py` with deterministic, hash-derived temp-path behavior.
- Keep command fallback semantics unchanged (`lake env lean` first, direct `lean` second).
- Keep result-status and proof-hash semantics behavior-compatible for identical command outputs.

### Locks

- Runner path lock is frozen:
  - authoritative implementation path:
    - `packages/adeu_lean/src/adeu_lean/runner.py`
- Temp-file allocator lock is frozen:
  - `NamedTemporaryFile` usage in runner temp-path creation is removed in this arc.
- Deterministic temp filename lock is frozen:
  - temp filename is derived from deterministic request identity inputs only:
    - `theorem_id`
    - `proof_request.semantics_version` (report alias: `proof_semantics_version`)
    - `obligation_kind_or_empty`
    - `theorem_src_hash`
    - `inputs_hash`
  - no wall-clock, PID, randomness, or host-entropy sources are allowed in temp-path derivation.
- Invocation overlap lock is frozen:
  - runner invocations for the same deterministic request identity may not overlap.
  - overlapping same-identity invocation attempts fail closed before command dispatch.
- Overlap arbitration lock is frozen:
  - same-identity overlap detection must be enforced with atomic create-or-fail semantics on the deterministic temp path.
  - deterministic identity workspace claim uses atomic directory creation under the deterministic temp root.
  - non-atomic check-then-create patterns (`exists`/`isfile` before write) are forbidden for overlap enforcement in this arc.
- CI execution overlap lock is frozen:
  - Lean-enabled CI agreement checks for identical request identities run in non-overlapping mode.
- Temp directory lock is frozen:
  - temp path root is deterministic and project-root anchored.
  - project root is resolved from `Path(__file__).resolve()` at runner module location via fixed parent traversal.
  - root discovery may not use CWD-dependent heuristics, recursive discovery scans, or host-specific search order.
  - caller CWD may not affect resolved temp-path location.
- Cleanup lock is frozen:
  - successful, failed, timeout, and missing-binary paths all perform deterministic cleanup of runner temp files.
- Collision behavior lock is frozen:
  - temp-path collisions with non-matching content fail closed before proof-check command dispatch.
- Proof-hash projection lock is frozen:
  - proof-result hashing uses a canonical projection that excludes temp-path leakage.
  - any temp-path substrings in captured outputs are normalized deterministically before hash computation.
  - command projection canonicalization is frozen:
    - the Lean source-path argument in hashed command representations is replaced with a constant placeholder token before hashing.
    - absolute/relative temp-directory differences may not affect `LeanResult.proof_hash`.
  - normalization scope lock is frozen:
    - redaction is limited to deterministic temp-root path occurrences and the Lean source-path command argument slot.
    - broad generic filesystem-path redaction outside frozen scope is forbidden.
- Diagnostic path redaction lock is frozen:
  - any resolved deterministic temp-root path occurrences in runner diagnostics are normalized to a constant token (`<LEAN_WORKSPACE>`) in deterministic hash/evidence projections.
  - host-specific absolute path segments may not affect replay equality decisions.
- Diagnostic color-stability lock is frozen:
  - runner diagnostics included in deterministic hash/evidence projections must be color-stable.
  - ANSI escape sequences are stripped from projected stdout/stderr before hash/evidence computation.
- Command-order lock is frozen:
  - fallback order remains deterministic and unchanged:
    - `[lake_bin, "env", "lean", file_name]`
    - `[lean_bin, file_name]`
- No-network/no-provider lock is frozen:
  - runner execution in this arc may not add provider calls or outbound network behavior.
- Proof-result contract continuity lock is frozen:
  - `LeanResult` top-level fields and status semantics remain behavior-compatible.

### Acceptance

- Identical request inputs under identical binaries produce deterministic temp-path resolution and stable proof hashes.
- Proof hashes are invariant to temp-path location details after canonical path normalization.
- Runner leaves no temp-file residue after execution for all frozen exit paths.
- Missing-binary and timeout behavior remain fail-closed and behavior-compatible.
- Existing proof backend public interfaces continue to pass unchanged.

## D2) Fixture-Backed Python↔Lean Agreement Harness

### Goal

Provide deterministic agreement evidence between Python-side obligation construction and Lean proof-check outcomes over frozen fixtures.

### Scope

- Add a fixture-backed agreement harness module and tests for frozen structural obligations.
- Consume persisted fixtures only; no live provider interaction.
- Emit machine-checkable agreement output for deterministic replay comparison.

### Locks

- Harness source authority lock is frozen:
  - agreement inputs are fixture-backed and repository-declared only.
  - filesystem globs, undeclared directories, and dynamic discovery scans are out-of-scope.
- Agreement report schema lock is frozen:
  - machine-checkable payload schema:
    - `schema = "odeu_agreement.report@0.1"`
- Agreement report top-level key lock is frozen:
  - required keys:
    - `schema`
    - `proof_semantics_version`
    - `fixtures`
    - `summary`
- Agreement summary key lock is frozen:
  - required `summary` keys:
    - `total_rows`
    - `agree_rows`
    - `disagree_rows`
    - `all_agree`
    - `fail_closed`
- Fixture row key lock is frozen:
  - required `fixtures[]` keys:
    - `fixture_id`
    - `theorem_prefix`
    - `obligation_kind`
    - `inputs_hash`
    - `mapping_id`
    - `python_expected_status`
    - `lean_observed_status`
    - `agreement`
    - `proof_hash`
- Agreement status taxonomy lock is frozen:
  - `python_expected_status` and `lean_observed_status` allowed values are frozen to:
    - `proved`
    - `failed`
  - unknown status values fail closed before agreement evaluation/report emission.
- Agreement identity/hash format lock is frozen:
  - `mapping_id` is full lowercase hex SHA-256 (`64` chars), no truncation.
  - `proof_hash` is full lowercase hex SHA-256 (`64` chars), no truncation.
  - `proof_hash` equals runner-emitted `LeanResult.proof_hash` for the same fixture row.
- Agreement ordering lock is frozen:
  - fixture rows are emitted in deterministic lexicographic order by:
    - `fixture_id`, `obligation_kind`.
- Agreement-set lock is frozen:
  - only the frozen first-set obligations are included in this arc:
    - `pred_closed_world`
    - `exception_gating`
    - `conflict_soundness`
- Fail-closed lock is frozen:
  - missing fixtures, schema-invalid fixtures, or obligation-kind drift fail deterministically before report emission.
- Read-only boundary lock is frozen:
  - harness flows are evidence-only and may not mutate runtime policy state.
- Agreement schema classification lock is frozen:
  - `odeu_agreement.report@0.1` is capture-only/testing schema in v30.
  - promotion to a runtime/public schema family is deferred to a later lock.
- Proof-semantics report mapping lock is frozen:
  - harness reads proof-backend `semantics_version` from Lean request/result structures.
  - harness emits that value as `proof_semantics_version` in `odeu_agreement.report@0.1`.
  - mapping is deterministic and value-preserving.
- Agreement boolean rule lock is frozen:
  - `agreement = true` iff:
    - `python_expected_status == lean_observed_status`
    - and the row identity fields (`fixture_id`, `obligation_kind`, `inputs_hash`, `mapping_id`) are internally consistent.
  - any inconsistency forces `agreement = false` and fail-closed summary status.
- Negative-agreement limitation lock is frozen:
  - for non-`proved` expected statuses, v30 agreement remains status/identity based only.
  - reason-class/diagnostic-substring equivalence for negative outcomes is explicitly deferred beyond this arc.

### Obligation Semantics (Frozen Intent)

- `pred_closed_world`:
  - Python side constructs closed-world predicate evidence over frozen fixture inputs and deterministic input normalization.
  - Lean theorem intent: predicates absent/false in context evaluate to false (no open-world fallback).
  - expected status: `proved` when fixture preconditions satisfy closed-world theorem assumptions.
- `exception_gating`:
  - Python side constructs evaluatability + false-predicate context evidence for exception checks.
  - Lean theorem intent: non-evaluable/false predicates cannot defeat a norm by exception.
  - expected status: `proved` when fixture inputs satisfy exception-gating assumptions.
- `conflict_soundness`:
  - Python side constructs conflict-candidate evidence over frozen structural conflict fixtures.
  - Lean theorem intent: any marked conflict candidate implies conflict soundness relation.
  - expected status: `proved` when fixture candidate encoding is valid and theorem preconditions hold.
- normalization boundary:
  - Python fixture normalization for all three obligations is deterministic, case-preserving, and canonical-json/hash-bounded.
  - obligation meaning may not be changed without lock update even if obligation names stay the same.

### Acceptance

- Agreement harness reruns are deterministic for identical fixtures and binaries.
- Agreement report ordering and hashes are stable across reruns.
- Invalid fixture/schema/obligation inputs fail closed deterministically.
- Harness execution emits no provider calls and no policy mutations.

## D3) First Structural Invariant Theorem Set + Evidence Mapping Continuity

### Goal

Activate a bounded first formal invariant set as evidence-only artifacts without changing runtime enforcement semantics.

### Scope

- Keep initial theorem set bounded to the three frozen obligations.
- Preserve deterministic theorem wrapper generation from existing request identities.
- Preserve evidence mapping continuity from proof requests/results to persisted proof artifacts.

### Locks

- Theorem-set lock is frozen to exactly:
  - `pred_closed_world`
  - `exception_gating`
  - `conflict_soundness`
- Proof-semantics-version lock is frozen:
  - default proof semantics version remains:
    - `adeu.lean.core.v1`
- Wrapper-source determinism lock is frozen:
  - generated wrapper theorem source remains deterministic from frozen request fields.
- Theorem mapping continuity lock is frozen:
  - obligation-to-core-theorem and obligation-to-theorem-type mapping remains aligned with existing runner tables in this arc.
  - remapping frozen obligations to different core theorem identifiers/types is out-of-scope without lock update.
- Evidence-only trust-lane lock is frozen:
  - formal proof outputs in this arc are evidence-only and non-enforcing.
  - no automatic policy allow/deny mutation may be introduced by formal results.
- Proof artifact continuity lock is frozen:
  - existing proof artifact envelope/identity behavior remains unchanged for identical inputs.
- Evidence mapping identity lock is frozen:
  - `mapping_id` is deterministic and computed as:
    - `sha256(canonical_json({theorem_id, obligation_kind, inputs_hash, proof_semantics_version, theorem_src_hash}))`
  - mapping continuity checks in this arc must use `mapping_id` as the primary evidence identity key.
- Kernel/runtime continuity lock is frozen:
  - no default runtime behavior change is introduced outside formal-lane evidence surfaces.

### Acceptance

- Frozen theorem set compiles/checks deterministically over locked fixtures.
- Proof artifact identity and hashing remain behavior-compatible for identical inputs.
- Formal-lane outputs differ only when underlying fixture inputs or toolchain outputs differ.

## D4) Parity and Regression Guard Suite

### Goal

Prove `D1`-`D3` activation is deterministic, behavior-preserving, and non-enforcing.

### Scope

- Add regression/parity coverage for:
  - deterministic temp-path behavior and cleanup
  - agreement harness ordering/hash determinism
  - theorem-set coverage and evidence-only continuity

### Locks

- No-new-metric-keys lock is frozen:
  - v30 test additions may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v29 continuity metrics remain at frozen required values.
- Fail-closed regression lock is frozen:
  - detected canonical-hash drift in locked baseline comparisons fails CI and blocks merge.
- No-provider/no-network guard lock is frozen:
  - tests fail closed when formal-lane flows trigger provider dispatch or outbound network calls.
- Real-Lean lane guard lock is frozen:
  - the required Lean-enabled CI lane must execute with real Lean backend configuration.
  - the lane must explicitly set `ADEU_PROOF_BACKEND=lean` (or equivalent explicit Lean selector in that job).
  - tests in that lane must assert observed backend kind is `lean` for in-scope formal checks.
  - silent fallback from Lean lane to mock backend fails closed.
- Overlap race guard lock is frozen:
  - tests must verify same-identity concurrent runner attempts are atomically rejected under the deterministic temp-path policy.
  - TOCTOU-style overlap acceptance is fail-closed.
- Temp-file cleanup guard lock is frozen:
  - tests fail closed when deterministic runner temp files persist after execution.
- Static theorem coverage lock is frozen:
  - tests fail closed when any frozen theorem obligation is missing from coverage.
- Deterministic ordering guard lock is frozen:
  - tests fail closed when agreement report ordering diverges from frozen ordering rules.
- Fixture snapshot guard lock is frozen:
  - guard suite includes deterministic pre/post fixture snapshot checks and fails closed on mutation.

### Acceptance

- Guard suites pass deterministically across reruns.
- Locked continuity metrics and parity evidence remain unchanged.
- No-provider/no-mutation guard tests pass for formal-lane flows.

## Stop-Gate Impact (v30)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity metrics remain required.
- Formal-lane outputs in this arc are evidence-only surfaces and do not introduce new stop-gate metric families.
- v30 closeout must include runtime-observability comparison row against v29 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v30 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v30)

- No new URM error-code family is planned in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `lean: harden deterministic temp-path behavior and cleanup in runner`
2. `lean/tests: add fixture-backed python-lean agreement harness and report checks`
3. `kernel/lean: lock first structural invariant theorem set evidence mapping`
4. `tests: add vnext+30 deterministic formal-lane parity and no-provider/no-mutation guards`

## Intermediate Preconditions (for v30 start)

1. v29 lock/closeout artifacts remain authoritative and unchanged.
2. v29 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md`
3. Existing ODEU Lean prep files remain available:
   - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
   - `packages/adeu_lean/AdeuODEU/Invariants.lean`
   - `packages/adeu_lean/AdeuCore/Theorems.lean`
4. Existing proof backend interfaces remain callable in CI at v30 start.
5. No L2 release is introduced in this arc.

## Exit Criteria (Draft)

- `D1` through `D4` merged with green CI.
- No new stop-gate metric keys introduced.
- Existing evidence-family and proof artifact payload contracts remain unchanged.
- Formal-lane runner/harness outputs are deterministic for identical persisted inputs.
- Existing continuity thresholds remain at required values.
- v30 closeout evidence includes runtime-observability comparison row against v29 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
