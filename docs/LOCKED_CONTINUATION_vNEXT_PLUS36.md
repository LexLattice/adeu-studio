# Locked Continuation vNext+36 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS35.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+35` (`I1`-`I2`) is merged on `main` via PR `#216` and PR `#217` with green CI checks.
- `vNext+35` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS35.md` with `all_passed = true`.
- Post-v35 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`.
- Selected v36 thin-slice default is first boundary-release candidate:
  - `V31-F` (`/urm/worker/run` governance alignment).
- `vNext+36` is constrained to deterministic additive hardening for `V31-F` only:
  - no solver/runtime semantics release,
  - no proposer idempotency persistence release (`V31-G`) in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v36,
  - v36 keyset must be exactly equal to v35 keyset (set equality, derived cardinality),
  - keyset authority is `stop_gate_metrics@1` payload field `metrics` object keys only.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v35 continuity guarantees remain frozen as release preconditions:
  - `l2_boundary_readiness_assertion@1` / `l2_boundary_blocker_registry@1` contract grammar remains authoritative for `V31-F`/`V31-G` planning continuity,
  - v35 boundary-readiness lint/guard suite remains authoritative baseline (`apps/api/scripts/lint_l2_boundary_readiness.py`).
- Boundary-release scope lock for v36 is frozen:
  - this arc authorizes `V31-F` boundary release only,
  - `V31-G` persistence boundary release remains deferred.
- Deferred persistence continuity lock remains frozen:
  - no replacement of process-local proposer idempotency cache with persisted storage in this arc.
- Closeout observability continuity lock is frozen:
  - v36 closeout must include a runtime-observability comparison row against v35 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `J1` worker-route governance boundary release (`V31-F`)
2. `J2` governance-release determinism/regression guard suite (`V31-F`)

Out-of-scope note:

- any `SEMANTICS_v4` runtime contract release,
- any `V31-G` proposer idempotency persistence release implementation,
- replacing process-local proposer idempotency cache with persisted storage,
- repo-root consolidation path (`V31-D`) beyond continuity maintenance,
- worker CLI safety path (`V31-E`) beyond continuity maintenance,
- formal-lane evidence path (`V31-C`) beyond continuity maintenance,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v36)

- v37+ persistence boundary release path may implement `V31-G` only after v36 governance release closeout is frozen and merged.
- v37+ governance policy-shaping may introduce a distinct worker-cancel action identifier only via explicit lock update if policy needs to diverge from shared `urm.agent.cancel` behavior.
- v38+ policy-operations hardening may evaluate deterministic hot-reload/versioned capability-policy refresh with explicit hash/version guards and fail-closed fallback semantics.

## V35 Readiness Consumption (Machine-Checkable)

```json
{
  "schema": "l2_boundary_release_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md",
  "source_assertion_schema": "l2_boundary_readiness_assertion@1",
  "target": "V31-F",
  "authorized_surfaces": [
    "apps/api/src/adeu_api/urm_routes.py#urm_worker_cancel_endpoint",
    "apps/api/src/adeu_api/urm_routes.py#urm_worker_run_endpoint",
    "packages/urm_runtime/src/urm_runtime/capability_policy.py#authorize_action"
  ],
  "required_blockers": [
    "BOUNDARY_LOCK_APPROVED",
    "DENIAL_PAYLOAD_CONTRACT_FROZEN",
    "POLICY_GATE_REGRESSION_GUARDS_GREEN"
  ]
}
```

Consumption lock:

- `l2_boundary_release_consumption@1` values for `authorized_surfaces` and `required_blockers` must be exact-set matches to the authoritative v35 `target = "V31-F"` readiness assertion block.
- set-equality comparison is order-insensitive with deterministic canonicalization (lexicographic sort before compare).
- duplicate values in `authorized_surfaces` or `required_blockers` are invalid and fail closed.

## V31-F Policy Action Membership Assertion (Machine-Checkable)

```json
{
  "schema": "v31f_policy_action_membership_assertion@1",
  "policy_lattice_path": "policy/urm.capability.lattice.v1.json",
  "required_action_ids": [
    "urm.agent.cancel",
    "urm.spawn_worker"
  ],
  "expected_relation": "required_action_ids_subset_of_policy_actions"
}
```

## V31-F Role Derivation Assertion (Machine-Checkable)

```json
{
  "schema": "v31f_worker_role_derivation_assertion@1",
  "resolver_module_path": "apps/api/src/adeu_api/urm_routes.py",
  "resolver_symbol": "_resolve_worker_route_authorization_role",
  "canonical_role": "copilot",
  "payload_role_authoritative": false,
  "missing_context_behavior": "deterministic_policy_denial"
}
```

## J1) Worker-Route Governance Boundary Release (`V31-F`)

### Goal

Release policy-governed authorization for worker execution endpoints using existing capability/instruction policy authority with deterministic denial behavior.

Lock-class rationale:

- this slice is `L2` because it activates governance boundary authority on existing runtime endpoints.

### Scope

- Apply `authorize_action` enforcement on:
  - `apps/api/src/adeu_api/urm_routes.py`:
    - `POST /urm/worker/run` (`urm_worker_run_endpoint`)
    - `POST /urm/worker/{worker_id}/cancel` (`urm_worker_cancel_endpoint`)
- Enforce existing provider boundary precheck before policy evaluation and execution:
  - both worker run/cancel routes must apply `_require_codex_provider(request.provider)`.
  - non-`codex` provider requests must be rejected before invoking `authorize_action`.
- Use existing capability-policy action identifiers for this release:
  - worker run -> `urm.spawn_worker`
  - worker cancel -> `urm.agent.cancel`
- Resolve governance actor role through server-owned derivation only:
  - effective authorization role in this arc is canonical `copilot`,
  - role input to `authorize_action` is derived only from runtime-owned resolver `_resolve_worker_route_authorization_role` in `apps/api/src/adeu_api/urm_routes.py`,
  - missing/unresolvable auth context fails closed before worker action execution,
  - client payload fields (including `WorkerRunRequest.role`) are non-authoritative for capability-gate identity.
- Include resource metadata in policy action payload as non-gating observability context:
  - worker run payload includes `client_request_id`,
  - worker cancel payload includes `worker_id`,
  - metadata fields are observability-only and are non-authoritative for capability permit/deny decisions.
- Preserve existing success response model contracts:
  - `WorkerRunResult`
  - `WorkerCancelResponse`
- Preserve existing provider boundary:
  - `provider = "codex"` only for these endpoints.
- Keep policy evaluation evidence emission path consistent with current runtime policy-event pipeline.

### Locks

- Governance surface lock is frozen:
  - only worker run/cancel endpoints are released in this arc,
  - no additional endpoint governance release is authorized by this lock.
- Actor-role projection lock is frozen:
  - governance actor role for worker route authorization is canonical `copilot` in this arc,
  - role input to `authorize_action` is resolved only by `_resolve_worker_route_authorization_role` in `apps/api/src/adeu_api/urm_routes.py`,
  - request payload field `WorkerRunRequest.role` remains task role metadata and is non-authoritative for capability-gate identity,
  - authorization permit/deny decisions must not be derived from payload role values in this arc,
  - missing/invalid role derivation fails closed with deterministic policy denial semantics.
- Provider-precheck ordering lock is frozen:
  - worker run/cancel must reject non-`codex` provider before `authorize_action` evaluation and before worker execution side effects,
  - invalid-provider branches must not invoke `authorize_action`.
- Action mapping lock is frozen:
  - worker run authorization action is `urm.spawn_worker`,
  - worker cancel authorization action is `urm.agent.cancel`,
  - both action identifiers must be validated as present in capability policy action set before freeze.
- Action identifier source lock is frozen:
  - route-level `authorize_action` action identifiers for this release must be sourced from centralized capability-policy exported constants/types,
  - ad-hoc raw string literals in worker route handlers are forbidden in this arc.
- Deterministic denial lock is frozen:
  - denied requests fail closed via existing URM structured error envelope (`code`, `message`, `context`),
  - denial envelopes must include structured minimum fields (`code`, `context.role`, `context.action`) for every authorization denial branch in this release,
  - worker run/cancel denial shaping may inject missing `context.role`/`context.action` fields deterministically for authorization-denial branches without changing denial `code` selection semantics,
  - denial-shaping adjustments in this lock are scoped to worker run/cancel release surfaces and are non-authoritative for other endpoint families,
  - denial assertions are machine-authoritative on structured fields (`code`, `context.role`, `context.action`),
  - prose `message` is non-authoritative for determinism assertions.
- Worker-route policy-context default lock is frozen:
  - until explicit session/approval wiring is introduced by a future lock, worker run/cancel policy evaluation context remains deterministic:
    - `writes_allowed = false`
    - `approval_provided = false`
    - `session_active = false`
- Error-code continuity lock is frozen:
  - no new URM error-code family is introduced by this release,
  - existing policy/approval denial code paths from `authorize_action` remain authoritative.
- No-L2-scaffolding spillover lock is frozen:
  - v36 may not introduce `V31-G` persistence wiring,
  - `apps/api/src/adeu_api/main.py` and `apps/api/src/adeu_api/storage.py` may not be modified for persistence release behavior in this arc,
  - no idempotency persistence migrations/DDL/table-introduction work may land in this arc.
- Replay/no-mutation continuity lock is frozen:
  - release may not introduce nondeterministic response fields on worker run/cancel envelopes.

### Acceptance

- Worker run/cancel requests are policy-gated through `authorize_action`.
- Allowed requests preserve existing response contracts.
- Denied requests fail closed with deterministic structured URM error fields.
- No `V31-G` persistence boundary behavior is introduced.

## J2) Governance-Release Determinism/Regression Guards (`V31-F`)

### Goal

Prove the `V31-F` boundary release is deterministic, fail-closed, and regression-resistant while preventing accidental `V31-G` release coupling.

### Scope

- Add/adjust deterministic tests/guards for:
  - worker run/cancel authorization callgraph coverage (both endpoints invoke `authorize_action`),
  - HTTP-path callgraph proof for authorization gating:
    - required callgraph assertions are demonstrated through request execution via API test client over real route/dependency wiring,
    - direct endpoint-function invocation alone is non-authoritative for callgraph release evidence,
  - provider boundary precheck assertions:
    - worker run/cancel reject non-`codex` provider values before worker execution side effects,
    - invalid-provider branches assert `authorize_action` is not invoked,
  - server-owned role derivation assertions (effective role is canonical `copilot` and is non-spoofable by request payload),
  - deterministic action mapping assertions (`urm.spawn_worker`, `urm.agent.cancel`),
  - worker-route policy-context default assertions (`writes_allowed = false`, `approval_provided = false`, `session_active = false`),
  - policy action membership assertions for required action identifiers in `policy/urm.capability.lattice.v1.json`,
  - deterministic denial assertions on structured URM error fields (`code`, `context.role`, `context.action`),
  - deterministic allow-path proof under frozen defaults:
    - at least one allow-path fixture/test proves `urm.spawn_worker` is authorized for effective role `copilot` with frozen worker-route defaults,
  - deterministic allowed-path contract compatibility for worker run/cancel response envelopes,
  - anti-coupling checks that v36 release does not introduce `V31-G` persistence behavior:
    - no new persistence migration files,
    - no new idempotency-persistence table references,
    - no new persistence helper imports/calls in worker-route governance codepaths.
- Replace v35 anti-release callgraph expectation for worker run/cancel:
  - v35 lock expected no `authorize_action` calls on these routes,
  - v36 lock requires and asserts `authorize_action` calls on these routes.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v36 tests/guards may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v35 continuity metrics remain at required values.
- Required-callgraph lock is frozen:
  - v36 guards fail closed if worker run/cancel paths do not invoke `authorize_action`.
- Provider-precheck callgraph ordering lock is frozen:
  - v36 guards fail closed if non-`codex` provider branches invoke `authorize_action`.
- HTTP-path callgraph evidence lock is frozen:
  - release evidence for required `authorize_action` invocation must come from test-client-driven request paths through mounted route/dependency wiring,
  - pure unit-level direct handler invocation is insufficient as merge-blocking callgraph evidence.
- v35-to-v36 callgraph inversion lock is frozen:
  - v35 anti-release expectation (`no authorize_action on worker run/cancel`) is superseded by v36 release expectation (`authorize_action required on worker run/cancel`),
  - guard suite must assert v36 expectation only and fail closed on regression in either direction.
- Deterministic-denial assertion lock is frozen:
  - v36 guards assert structured denial fields (`code`, `context.role`, `context.action`) and required-field presence,
  - v36 guards may not depend on prose matching.
- Persistence anti-coupling lock is frozen:
  - v36 guards fail closed if proposer idempotency persistence release behavior appears in this arc,
  - v36 guards fail closed on new migration files under `apps/**/migrations/**`,
  - v36 guards fail closed on new SQL/DDL files under `apps/**/*.sql`,
  - v36 guards fail closed on changes that introduce proposer-idempotency persistence coupling through:
    - `apps/api/src/adeu_api/main.py`
    - `apps/api/src/adeu_api/storage.py`
    - references to `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` outside deferred `V31-G` release scope.
- Deterministic-guard-output lock is frozen:
  - guard outputs are deterministic and machine-checkable under fixed inputs.
- No-provider/no-network expansion lock is frozen:
  - no new provider types beyond existing `codex` are allowed for worker-route governance release in this arc,
  - allowed-path tests run with deterministic worker/spawn mocking and may not require outbound network.
- CI lane continuity lock is frozen:
  - in-scope v36 governance guards must run in the default Python CI lane,
  - workflow/job renaming is allowed only if required guard coverage remains equivalent and explicit in CI config.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required `authorize_action` callgraph assertions are green for worker run/cancel paths.
- Non-`codex` provider branches reject before policy evaluation and do not call `authorize_action`.
- Structured denial behavior is deterministic and machine-assertable.
- At least one deterministic allow-path assertion proves `urm.spawn_worker` is authorized for effective role `copilot` under frozen worker-route policy-context defaults.
- Worker run/cancel allowed-path response contracts remain compatible.
- No `V31-G` persistence release behavior lands in v36 scope.

## Stop-Gate Impact (v36)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v36 closeout must include runtime-observability comparison row against v35 baseline.
- Runtime-observability comparison schema lock is frozen:
  - comparison block schema is docs-only `runtime_observability_comparison@1`,
  - required keys are:
    - `schema`
    - `baseline_arc`
    - `current_arc`
    - `baseline_source`
    - `current_source`
    - `baseline_elapsed_ms`
    - `current_elapsed_ms`
    - `delta_ms`
    - `notes`
  - optional keys may be included for richer continuity evidence (`baseline_total_fixtures`, `current_total_fixtures`, `baseline_total_replays`, `current_total_replays`, `baseline_bytes_hashed_per_replay`, `current_bytes_hashed_per_replay`, `baseline_bytes_hashed_total`, `current_bytes_hashed_total`) but are non-required for v36 closeout compatibility with frozen v35 baseline artifacts.
- Runtime-observability closeout placement lock is frozen:
  - v36 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS36.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v36)

- No new URM error-code family is introduced in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `runtime/api: release V31-F worker governance boundary through authorize_action`
2. `tests: add v36 governance-release determinism and regression guard suite`

## Intermediate Preconditions (for v36 start)

1. v35 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v35 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS35.md`
3. v35 readiness authority surfaces remain available at v36 start:
   - `apps/api/src/adeu_api/urm_routes.py`
   - `packages/urm_runtime/src/urm_runtime/capability_policy.py`
4. Required `V31-F` action identifiers remain present in capability policy action set at v36 start:
   - `policy/urm.capability.lattice.v1.json` contains:
     - `urm.spawn_worker`
     - `urm.agent.cancel`
5. Existing boundary-readiness lint remains enabled:
   - `apps/api/scripts/lint_l2_boundary_readiness.py`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. Frozen `V31-G` deferred surfaces remain unchanged at v36 start:
   - `apps/api/src/adeu_api/main.py`
   - `apps/api/src/adeu_api/storage.py`

## Exit Criteria (Draft)

- `J1` and `J2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic worker-route governance release (`V31-F`) is closed and test-covered.
- v36 closeout evidence includes runtime-observability comparison row against v35 baseline.
- `V31-G` persistence boundary remains deferred and unreleased in v36.
- No solver semantics contract delta and no trust-lane regression introduced.
