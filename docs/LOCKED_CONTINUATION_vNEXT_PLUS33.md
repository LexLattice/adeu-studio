# Locked Continuation vNext+33 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS32.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS32.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock implemented on `main` (PR `#212` and PR `#213` merged on March 2, 2026 UTC); closeout evidence is captured in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS33.md`.

Decision basis:

- `vNext+32` (`F1`-`F2`) is merged on `main` via PR `#210` and PR `#211` with green CI checks.
- `vNext+32` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS32.md`.
- Post-v32 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`.
- Selected v33 thin-slice default is worker CLI safety tightening (`V31-E` path family from options menu).
- `vNext+33` is constrained to deterministic additive hardening only:
  - no solver/runtime semantics release,
  - no policy-enforcement expansion,
  - no L2 boundary release.
- `vNext+33` (`G1`-`G2`) is now merged on `main` via PR `#212` and PR `#213` with green CI checks.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS32.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v33,
  - v33 keyset must be exactly equal to v32 keyset (set equality, derived cardinality),
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
- Closeout observability continuity lock is frozen:
  - v33 closeout must include a runtime-observability comparison row against v32 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `G1` worker CLI fail-closed safety-policy closure (`V31-E`)
2. `G2` worker CLI determinism/regression guard suite (`V31-E`)

Out-of-scope note:

- any runtime policy-enforcement behavior changes,
- any `SEMANTICS_v4` runtime contract release,
- any L2 governance/persistence releases (`V31-F`, `V31-G`),
- formal-lane expansion path (`V31-C`),
- repo-root consolidation path (`V31-D`) beyond continuity maintenance,
- dry-run/execute-probe capability detection (for example `codex exec --dry-run ...`) in place of frozen help-text probing,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v33)

- Probe-hardening path (v34+) may evaluate dry-run/validate-only capability checks when a stable CLI contract exists for deterministic probing without help-text parsing.

## G1) Worker CLI Fail-Closed Safety Policy Closure (`V31-E`)

### Goal

Lock deterministic fail-closed behavior when required `codex exec` safety flags are unsupported by the active CLI.

### Scope

- Freeze worker CLI safety policy to fail closed:
  - worker runs require `--ask-for-approval never` for execution safety posture in this arc.
  - when support probe reports `--ask-for-approval` unsupported, worker run fails deterministically before subprocess spawn.
- Freeze support-detection mechanism to explicit `codex exec --help` probing via `_supports_exec_flag`.
- Freeze support-probe parsing contract:
  - probe argv is exactly `[codex_bin, "exec", "--help"]`,
  - probe text source is `(stdout + "\\n" + stderr)`,
  - support is true iff probe text contains exact case-sensitive substring `--ask-for-approval`,
  - non-zero exit, timeout, or process launch failure is treated as unsupported and follows the same deterministic fail-closed path with frozen reason-token suffix semantics.
- Keep probe caching behavior deterministic:
  - one help snapshot per runner instance,
  - cache lifetime is the runner instance lifetime,
  - no intra-instance version discrimination beyond the instance's configured `codex_bin`.
  - executable mtime/hash-based cache invalidation is out-of-scope in this arc.
  - operational cache policy in this arc is restart-based: refreshed capability detection after codex binary upgrade requires runner process recreation.
- Preserve command-shape continuity for supported environments:
  - when supported, command continues to include `--ask-for-approval never`.
- Replace compatibility-first omission behavior in runner execution path with deterministic pre-spawn rejection.
- Scope boundary freeze:
  - required-flag enforcement applies only to worker start-path codex-exec command assembly and launch,
  - cancel/status/read surfaces are unaffected by this lock.
- Keep implementation authority for this slice on:
  - `packages/urm_runtime/src/urm_runtime/worker.py` (`_supports_exec_flag`, command assembly, pre-spawn validation),
  - associated API-facing worker runner tests.

### Locks

- Required-flag policy lock is frozen:
  - `--ask-for-approval` is required for worker runs in this arc.
  - unsupported required flag is a deterministic start failure, not a best-effort downgrade.
- Pre-spawn failure lock is frozen:
  - unsupported required flag must fail before `subprocess.Popen` invocation.
  - fail-closed branch may not register an active worker process handle.
  - guard evaluation order is frozen: support probe outcome is computed first, required-flag check is applied next, and only then may command spawn/handle registration paths execute.
- Error-code continuity lock is frozen:
  - fail-closed unsupported-flag path uses existing `URM_WORKER_START_FAILED` family (no new URM error-code family).
- Error-shape lock is frozen:
  - failure payload remains deterministic and machine-checkable (`code`, `message`).
  - unsupported required-flag failures use frozen base message prefix token `UNSUPPORTED_REQUIRED_FLAG:--ask-for-approval`.
  - unsupported required-flag failures append deterministic reason suffix token from:
    - `FLAG_ABSENT`
    - `PROBE_TIMEOUT`
    - `PROBE_LAUNCH_FAILED`
    - `PROBE_NONZERO_EXIT`
  - reason-token mapping is frozen:
    - `FLAG_ABSENT` is valid only when help probe launch succeeds, does not timeout, returns exit code `0`, and parsed help text lacks `--ask-for-approval`.
    - probe execution failures (`timeout`, launch failure, non-zero exit) must map to their corresponding probe-failure reason token and may not be collapsed to `FLAG_ABSENT`.
- Probe-timeout budget lock is frozen:
  - help probe timeout is frozen to `help_probe_timeout_ms = 10000` in this arc.
  - timeout enforcement must use monotonic elapsed-time semantics (wall-clock independent).
- Support-probe lock is frozen:
  - `_supports_exec_flag("--ask-for-approval")` remains sourced from `codex exec --help` output only using the frozen parsing contract in this doc.
  - alternate heuristic probing and silent retry modes are out-of-scope.
- Compatibility-fallback prohibition lock is frozen:
  - omission fallback for unsupported required `--ask-for-approval` is forbidden in this arc.
- Supported-command-shape lock is frozen:
  - supported branch argv contains exactly one `--ask-for-approval` occurrence.
  - value tokenization is frozen as two argv tokens: `["--ask-for-approval", "never"]` (not equals-style tokenization).
- Output-schema continuity lock is frozen:
  - this slice does not expand or reinterpret `--output-schema` policy behavior beyond existing contracts.
- Endpoint-contract continuity lock is frozen:
  - no `/urm/worker/run` or `/urm/worker/{worker_id}/cancel` API contract expansion in this arc.
  - required-flag enforcement in this arc does not alter cancel/status/read endpoint semantics.
- No-network/no-provider-expansion lock is frozen:
  - no new provider dispatch or outbound-network behavior is introduced by this slice.
- Rejection-observability lock is frozen:
  - fail-closed rejection must be exposed via deterministic error response contract (`URM_WORKER_START_FAILED` plus frozen message token rules).
  - fail-closed rejection must emit deterministic stderr audit line with frozen prefix `URM_WORKER_START_FAILED UNSUPPORTED_REQUIRED_FLAG`.
  - stderr audit line in this arc may not include runtime clock fields (for example timestamp strings).

### Acceptance

- Worker run fails closed deterministically when `--ask-for-approval` is required but unsupported by CLI probe.
- Failure occurs pre-spawn (no worker subprocess start side effects).
- Unsupported branch emits deterministic `URM_WORKER_START_FAILED` with frozen base message prefix token `UNSUPPORTED_REQUIRED_FLAG:--ask-for-approval` and one frozen reason suffix token.
- Unsupported branch emits deterministic stderr audit line with frozen prefix `URM_WORKER_START_FAILED UNSUPPORTED_REQUIRED_FLAG` and no runtime clock fields.
- Supported environments continue successful runs with `--ask-for-approval never` included.
- Supported branch uses frozen argv shape with exactly one `--ask-for-approval` token pair.
- Existing worker endpoint contracts remain behavior-compatible outside the frozen safety-policy delta.

## G2) Worker CLI Determinism/Regression Guards (`V31-E`)

### Goal

Prove the `G1` fail-closed policy is deterministic, test-covered, and resistant to regression back to compatibility-first behavior.

### Scope

- Add/adjust deterministic tests for:
  - unsupported required `--ask-for-approval` fail-closed behavior,
  - pre-spawn rejection (`subprocess.Popen` not called),
  - no active-process handle registration in the unsupported branch,
  - supported-flag path continuity,
  - supported branch argv shape (`["--ask-for-approval", "never"]`, exactly one occurrence),
  - deterministic error payload and stable failure semantics,
  - deterministic stderr rejection-audit prefix and no runtime clock fields.
- Replace legacy compatibility-first coverage that expected omission fallback when `--ask-for-approval` is unsupported.
  - explicit replacement target is `apps/api/tests/test_urm_worker_runner.py` (`test_worker_runner_omits_ask_for_approval_when_flag_unsupported`) with a fail-closed equivalent assertion path.
- Keep fixture-driven fake codex help behavior as deterministic support-probe source.
- Preserve deterministic sorted assertions and stable fixture usage where guard outputs are compared.

### Locks

- No-new-metric-keys lock is frozen:
  - v33 tests may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v32 continuity metrics remain at required values.
- Fail-closed regression lock is frozen:
  - reintroduction of omission fallback for unsupported required flag fails CI and blocks merge.
- Deterministic-probe lock is frozen:
  - tests pin support/unsupported branches via deterministic fake `codex exec --help` fixtures only.
  - tests cover non-zero/timeout/launch-failure probe outcomes as unsupported with the same deterministic fail-closed path and expected reason suffix token.
  - tests must enforce that `FLAG_ABSENT` appears only in successful-help/no-flag branch and not in probe-failure branches.
- Error-contract regression lock is frozen:
  - expected failure code/message contract for unsupported required flag remains explicit and deterministic.
- Rejection-audit regression lock is frozen:
  - expected stderr audit prefix for unsupported required flag remains explicit and deterministic.
  - audit output in this branch remains free of runtime clock fields.
- No-provider/no-network guard lock is frozen:
  - tests fail closed if in-scope worker CLI safety flows trigger provider expansion or outbound-network calls.

### Acceptance

- Guard suites pass deterministically across reruns.
- Unsupported required flag behavior is explicit, deterministic, and test-covered.
- No compatibility-mode fallback remains in supported test matrix for required flag path.

## Stop-Gate Impact (v33)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- This arc preserves the no-new-metric-key continuity streak through v33.
- v33 closeout must include runtime-observability comparison row against v32 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v33 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS33.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v33)

- No new URM error-code family is introduced in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `runtime: enforce fail-closed worker start when required ask-for-approval flag is unsupported`
2. `tests: add v33 worker-cli safety determinism and regression guard suite`

## Intermediate Preconditions (for v33 start)

1. v32 lock implementation remains authoritative and unchanged.
2. v32 closeout decision exists and remains green before freeze:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS32.md`
   - closeout-consistency lint passes for the closeout decision chain including v32.
3. Worker runner support-probe anchors remain available at v33 start:
   - `packages/urm_runtime/src/urm_runtime/worker.py` (`_supports_exec_flag`, command assembly and start path)
4. Existing compatibility-first behavior is still identifiable for replacement coverage:
   - `apps/api/tests/test_urm_worker_runner.py` (`test_worker_runner_omits_ask_for_approval_when_flag_unsupported`)
5. No L2 boundary release is introduced in this arc.

## Exit Criteria (Draft)

- `G1` and `G2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Worker CLI unsupported required-flag behavior is fail-closed, deterministic, and test-covered.
- v33 closeout evidence includes runtime-observability comparison row against v32 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.

Implementation status (March 2, 2026 UTC):

- `G1` and `G2` are merged on `main` with green CI checks.
- v33 closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS33.md`.
