# Locked Continuation vNext+35 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS34.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS34.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock with `I1` + `I2` merged on `main`; pending stop-gate closeout freeze.

Decision basis:

- `vNext+34` (`H1`-`H2`) is merged on `main` via PR `#214` and PR `#215` with green CI checks.
- `vNext+34` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS34.md` with `all_passed = true`.
- `vNext+35` (`I1`-`I2`) is merged on `main` via PR `#216` and PR `#217` with green CI checks.
- Post-v34 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`.
- Selected v35 thin-slice default is explicit L2 boundary-lock preparation for:
  - `V31-F` (`/urm/worker/run` governance alignment),
  - `V31-G` (proposer idempotency persistence alignment).
- `vNext+35` is constrained to deterministic additive hardening only:
  - no solver/runtime semantics release,
  - no policy-enforcement expansion in runtime behavior,
  - no L2 boundary release in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS34.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v35,
  - v35 keyset must be exactly equal to v34 keyset (set equality, derived cardinality),
  - keyset authority is `stop_gate_metrics@1` payload field `metrics` object keys only.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Non-enforcement/no-mutation continuity remains frozen for evidence surfaces in this arc.
- L2 release prohibition lock remains frozen in v35:
  - no `/urm/worker/run` governance boundary release,
  - no proposer idempotency persistence boundary release.
- L2 scaffolding prohibition remains frozen:
  - no partial implementation of L2 authority/persistence surfaces may land under this preparatory arc.
- v31 continuity guarantees remain frozen:
  - Evidence Explorer template-path contract closure (`V31-A`) remains authoritative,
  - closeout consistency lint and continuity assertion grammar (`V31-B`) remain authoritative.
- v32 continuity guarantees remain frozen:
  - canonical repo-root resolution consolidation (`V31-D`, `F1`) remains authoritative,
  - repo-root determinism/parity guard suite (`V31-D`, `F2`) remains authoritative.
- v33 continuity guarantees remain frozen:
  - worker CLI fail-closed safety policy closure (`V31-E`, `G1`) remains authoritative,
  - worker CLI determinism/regression guard suite (`V31-E`, `G2`) remains authoritative.
- v34 continuity guarantees remain frozen:
  - formal ODEU evidence contract closure (`V31-C`, `H1`) remains authoritative,
  - formal-lane determinism/regression guard suite (`V31-C`, `H2`) remains authoritative.
- Closeout observability continuity lock is frozen:
  - v35 closeout must include a runtime-observability comparison row against v34 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `I1` L2 boundary-release precondition contract closure (`V31-F` + `V31-G` prep)
2. `I2` boundary-precondition determinism/regression guard suite (`V31-F` + `V31-G` prep)

Out-of-scope note:

- any runtime policy-enforcement behavior changes,
- any `SEMANTICS_v4` runtime contract release,
- any L2 governance/persistence release implementation for `V31-F`/`V31-G`,
- wiring `authorize_action` onto `/urm/worker/run` or `/urm/worker/{worker_id}/cancel`,
- replacing process-local proposer idempotency cache with persisted storage,
- repo-root consolidation path (`V31-D`) beyond continuity maintenance,
- worker CLI safety path (`V31-E`) beyond continuity maintenance,
- formal-lane evidence path (`V31-C`) beyond continuity maintenance,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v35)

- v36+ governance release path may implement `V31-F` only after v35 boundary preconditions are frozen and merged.
- v37+ persistence release path may implement `V31-G` only after v35 boundary preconditions are frozen and merged.

## L2 Boundary Readiness Assertions (Machine-Checkable)

Location lock:

- boundary-readiness assertions are emitted only in this document under this heading.
- exactly two fenced `json` blocks with schema `l2_boundary_readiness_assertion@1` are required under this heading:
  - one block with `target = "V31-F"`,
  - one block with `target = "V31-G"`.
- no additional `l2_boundary_readiness_assertion@1` blocks are allowed elsewhere in v35 lock artifacts.

Schema lock (`docs-only`):

- assertion schema is frozen as `l2_boundary_readiness_assertion@1`.
- required keys are exactly:
  - `schema`
  - `target`
  - `candidate_surfaces`
  - `source_of_truth`
  - `denial_semantics`
  - `rollback_semantics`
  - `release_blockers`
- `candidate_surfaces` rules are frozen:
  - non-empty list,
  - unique entries,
  - lexicographically sorted ascending,
  - each entry is a `path#symbol` string.
- `source_of_truth` enum is frozen:
  - allowed values: `capability_policy_authority`, `persisted_store_only`.
- `denial_semantics` object keys are frozen:
  - `mode`
  - `deterministic_fields`
  - `nondeterministic_fields_excluded`
- `rollback_semantics` object keys are frozen:
  - `mode`
  - `requires_explicit_lock_update`
  - `partial_enablement_forbidden`
  - `migration_down_contract`
- `release_blockers` rules are frozen:
  - non-empty list,
  - unique entries,
  - lexicographically sorted ascending,
  - each entry must be an uppercase snake-case blocker ID present in the authoritative `l2_boundary_blocker_registry@1` JSON block in this document.
- Denial deterministic-field authority lock is frozen:
  - `denial_semantics.deterministic_fields` must include only structured fields (`code`, `reason`, `context`) in this arc.
  - prose field `message` is non-authoritative and must not be included in deterministic-field assertions.

### Release Blocker Registry (v35)

| Blocker ID | Evidence Ref Type | Evidence Ref |
|---|---|---|
| `BOUNDARY_LOCK_APPROVED` | `DOC` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md#L2_Boundary_Readiness_Assertions` |
| `DENIAL_PAYLOAD_CONTRACT_FROZEN` | `DOC` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md#I1` |
| `PERSISTENCE_SOURCE_OF_TRUTH_FROZEN` | `DOC` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md#I1` |
| `POLICY_GATE_REGRESSION_GUARDS_GREEN` | `CHECK` | `ci / python` |
| `REPLAY_CONFLICT_REGRESSION_GUARDS_GREEN` | `CHECK` | `ci / python` |

```json
{
  "schema": "l2_boundary_blocker_registry@1",
  "blockers": [
    {
      "id": "BOUNDARY_LOCK_APPROVED",
      "evidence_ref_type": "DOC",
      "evidence_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md#L2_Boundary_Readiness_Assertions"
    },
    {
      "id": "DENIAL_PAYLOAD_CONTRACT_FROZEN",
      "evidence_ref_type": "DOC",
      "evidence_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md#I1"
    },
    {
      "id": "PERSISTENCE_SOURCE_OF_TRUTH_FROZEN",
      "evidence_ref_type": "DOC",
      "evidence_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md#I1"
    },
    {
      "id": "POLICY_GATE_REGRESSION_GUARDS_GREEN",
      "evidence_ref_type": "CHECK",
      "evidence_ref": "ci / python"
    },
    {
      "id": "REPLAY_CONFLICT_REGRESSION_GUARDS_GREEN",
      "evidence_ref_type": "CHECK",
      "evidence_ref": "ci / python"
    }
  ]
}
```

```json
{
  "schema": "l2_boundary_readiness_assertion@1",
  "target": "V31-F",
  "candidate_surfaces": [
    "apps/api/src/adeu_api/urm_routes.py#urm_worker_cancel_endpoint",
    "apps/api/src/adeu_api/urm_routes.py#urm_worker_run_endpoint",
    "packages/urm_runtime/src/urm_runtime/capability_policy.py#authorize_action"
  ],
  "source_of_truth": "capability_policy_authority",
  "denial_semantics": {
    "mode": "deterministic_policy_denial",
    "deterministic_fields": [
      "code",
      "reason",
      "context"
    ],
    "nondeterministic_fields_excluded": [
      "created_at",
      "generated_at",
      "request_id",
      "timestamp"
    ]
  },
  "rollback_semantics": {
    "mode": "all_or_nothing_route_gate_revert",
    "requires_explicit_lock_update": true,
    "partial_enablement_forbidden": true,
    "migration_down_contract": "not_applicable"
  },
  "release_blockers": [
    "BOUNDARY_LOCK_APPROVED",
    "DENIAL_PAYLOAD_CONTRACT_FROZEN",
    "POLICY_GATE_REGRESSION_GUARDS_GREEN"
  ]
}
```

```json
{
  "schema": "l2_boundary_readiness_assertion@1",
  "target": "V31-G",
  "candidate_surfaces": [
    "apps/api/src/adeu_api/main.py#_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY",
    "apps/api/src/adeu_api/main.py#urm_core_ir_propose_endpoint",
    "apps/api/src/adeu_api/storage.py#transaction"
  ],
  "source_of_truth": "persisted_store_only",
  "denial_semantics": {
    "mode": "deterministic_idempotency_conflict",
    "deterministic_fields": [
      "code",
      "reason",
      "context"
    ],
    "nondeterministic_fields_excluded": [
      "created_at",
      "generated_at",
      "request_id",
      "timestamp"
    ]
  },
  "rollback_semantics": {
    "mode": "single_source_revert_with_explicit_lock",
    "requires_explicit_lock_update": true,
    "partial_enablement_forbidden": true,
    "migration_down_contract": "required_pre_release"
  },
  "release_blockers": [
    "BOUNDARY_LOCK_APPROVED",
    "PERSISTENCE_SOURCE_OF_TRUTH_FROZEN",
    "REPLAY_CONFLICT_REGRESSION_GUARDS_GREEN"
  ]
}
```

## I1) L2 Boundary-Release Precondition Contract Closure (`V31-F` + `V31-G` Prep)

### Goal

Freeze a deterministic, machine-checkable boundary-precondition contract for `V31-F`/`V31-G` without changing runtime behavior.

Lock-class rationale:

- this slice remains preparatory and non-release; it records boundary authority and persistence release prerequisites without activating them.

### Scope

- Freeze boundary inventory and authority surfaces for deferred release paths:
  - `apps/api/src/adeu_api/urm_routes.py` (`/worker/run`, `/worker/{worker_id}/cancel`),
  - `packages/urm_runtime/src/urm_runtime/capability_policy.py` (`authorize_action` authority anchor),
  - `apps/api/src/adeu_api/main.py` (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`),
  - `apps/api/src/adeu_api/storage.py` (persisted idempotency reference surfaces).
- Add explicit, deterministic boundary-release readiness assertions for both deferred paths (`V31-F`, `V31-G`) with independent target-specific blocks and checklists.
- Keep this slice docs/contract-oriented only:
  - no runtime endpoint behavior changes,
  - no persistence wiring changes,
  - no API/output contract changes.

### Locks

- Boundary-release prohibition lock is frozen:
  - v35 may not change runtime behavior for `/urm/worker/run`/`cancel` authorization or proposer idempotency persistence.
- Boundary-authority declaration lock is frozen:
  - v35 must enumerate exactly which surfaces are candidates for future L2 release and which remain unchanged in this arc.
- Boundary-inventory completeness lock is frozen:
  - v35 boundary inventory for deferred release paths is complete and authoritative for this arc.
  - silent inventory expansion is forbidden in v35; newly discovered candidate surfaces require explicit follow-on lock update.
- Assertion placement and schema lock is frozen:
  - boundary readiness must be represented only by the two `l2_boundary_readiness_assertion@1` blocks under `## L2 Boundary Readiness Assertions`.
  - `V31-F` and `V31-G` assertions must remain separate and may not be merged into one combined assertion block.
- Source-of-truth lock for deferred persistence release is frozen:
  - v35 must declare a single-source-of-truth requirement for any future proposer idempotency persistence release.
  - once persistence is released in a future arc, in-memory cache may not remain authoritative.
  - dual-read/dual-write operation is forbidden unless a future lock explicitly defines migration semantics.
- No-L2-scaffolding definition lock is frozen:
  - v35 may not introduce capability-policy checks in worker routes (including permissive/allow-all stubs).
  - v35 may not introduce idempotency-persistence schema artifacts (new tables/migrations/DDL) for proposer flows.
  - v35 may not introduce new config/env flags that toggle deferred `V31-F`/`V31-G` release behavior.
- Deterministic-denial semantics precondition lock is frozen:
  - v35 must define deterministic denial/rollback expectations for future L2 releases as prerelease contract text.
  - no active denial-path behavior changes may land in this arc.
- Docs-only schema boundary lock is frozen:
  - any machine-checkable boundary assertions introduced in v35 are docs-validation-only and are not runtime/public schema-family additions.
- V35 no-touch L2 surface lock is frozen:
  - v35 may not modify these runtime files:
    - `apps/api/src/adeu_api/urm_routes.py`
    - `packages/urm_runtime/src/urm_runtime/capability_policy.py`
    - `apps/api/src/adeu_api/main.py`
    - `apps/api/src/adeu_api/storage.py`
- Branch-owned diff semantics lock is frozen:
  - no-touch enforcement compares branch-owned changes only using merge-base semantics against `--base-ref` (`origin/main`).
  - raw two-dot diff against ref tips is forbidden for no-touch enforcement in this arc.
- No-network/no-provider expansion lock is frozen:
  - this slice introduces no provider dispatch expansion and no outbound-network behavior.

### Acceptance

- Boundary-readiness contract text for `V31-F` and `V31-G` is explicit, deterministic, and machine-checkable.
- No runtime behavior changes are introduced while preparing L2 release prerequisites.
- Future release preconditions (authority surfaces, source-of-truth, rollback/denial semantics) are explicit enough to block ambiguous L2 implementation starts.

### I1 Implementation Snapshot

- Contract authority is now frozen in this document through:
  - `## L2 Boundary Readiness Assertions (Machine-Checkable)`,
  - `## Release Blocker Registry (v35)`,
  - `## I1) L2 Boundary-Release Precondition Contract Closure`.
- Boundary-preparation edge assessment and repository-state verification are recorded in:
  - `docs/ASSESSMENT_vNEXT_PLUS35_EDGES.md`.
- Merge evidence:
  - PR `#216` merged at `17b40760b838ec9fc80c891e26ee5efd9c2c1a91`.
- This `I1` implementation remains docs-only by design:
  - no runtime endpoint behavior changes,
  - no persistence wiring changes,
  - no API/output contract changes.

## I2) Boundary-Precondition Determinism/Regression Guards (`V31-F` + `V31-G` Prep)

### Goal

Prove v35 boundary-preparation remains deterministic, fail-closed, and resistant to accidental early L2 release.

### Scope

- Add/adjust deterministic docs/tooling guards for:
  - required presence and schema-validity of v35 boundary-readiness assertion block(s),
  - required count/target set of readiness blocks (`V31-F`, `V31-G`) with no extras,
  - deterministic parsing/validation of boundary-readiness assertions,
  - deterministic parsing/validation of `l2_boundary_blocker_registry@1` and blocker-id membership checks,
  - keyset/enum validation for `l2_boundary_readiness_assertion@1`,
  - deterministic ordering/uniqueness checks for `candidate_surfaces` and `release_blockers`,
  - fail-closed behavior when required assertion blocks are missing/invalid,
  - fail-closed diff guard checks that in-scope v35 branch does not introduce partial L2 scaffolding through runtime-file modifications,
  - fail-closed callgraph guard checks that `/urm/worker/run` and `/urm/worker/{worker_id}/cancel` request paths do not invoke `authorize_action` in v35 (monkeypatch/guard failure is merge-blocking),
  - fail-closed behavior sentinel checks that `/urm/worker/run` and `/urm/worker/{worker_id}/cancel` response envelopes remain behavior-compatible with frozen v34 baseline snapshots.
- Behavior sentinel fixture location lock is frozen:
  - sentinel baseline fixtures are sourced only from:
    - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_run_response_v34_baseline.json`
    - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_cancel_response_v34_baseline.json`
  - sentinel comparison is performed on canonical JSON object payloads with frozen high-entropy field exclusion.
- Behavior sentinel provenance lock is frozen:
  - sentinel baseline fixtures must be captured from v34 baseline behavior on `main` at merge commit `fd9a48de8ab7852d371080659c9fc15aa24b8b70`.
  - hand-authored sentinel payload edits are forbidden; updates require regenerated capture evidence and explicit lock-update rationale.
- Behavior sentinel metadata lock is frozen:
  - each sentinel fixture payload must include top-level `meta` object with:
    - `captured_from_commit`
    - `captured_by_script`
    - `captured_at`
  - lint must verify `meta.captured_from_commit == "fd9a48de8ab7852d371080659c9fc15aa24b8b70"`.
- Behavior sentinel normalization lock is frozen:
  - exclusion set is deterministic and recursive across response envelopes and includes:
    - `created_at`
    - `timestamp`
    - `generated_at`
    - `request_id`
    - `trace_id`
    - `hostname`
    - `pid`
    - `meta.captured_at`
  - adding/removing excluded fields requires explicit lock update in the same arc chain.
- Guard entrypoint lock is frozen:
  - closeout-chain continuity lint remains `apps/api/scripts/lint_closeout_consistency.py`.
  - boundary-readiness/anti-release lint entrypoint is `apps/api/scripts/lint_l2_boundary_readiness.py`.
  - frozen v35 boundary lint CLI is:
    - `TZ=UTC LC_ALL=C PYTHONPATH=apps/api/src:packages/urm_runtime/src .venv/bin/python apps/api/scripts/lint_l2_boundary_readiness.py --lock-doc docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md --base-ref origin/main --sentinel-dir apps/api/tests/fixtures/l2_boundary_sentinels`
  - frozen v35 boundary lint exit-code contract is:
    - `0` = pass
    - `2` = assertion schema/placement/ordering violation
    - `3` = no-touch diff guard violation
    - `4` = behavior sentinel drift
    - `5` = base-ref unavailable/unresolvable for merge-base diff guard
  - base-ref availability precondition is frozen:
    - lint must verify `--base-ref` is fetchable/resolvable before diff evaluation.
    - unresolved base-ref fails closed with exit code `5` (never silent-pass).
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v35 tests/guards may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v34 continuity metrics remain at required values.
- Fail-closed docs-guard lock is frozen:
  - missing/invalid boundary-readiness assertion blocks fail CI and block merge.
- Anti-release regression lock is frozen:
  - accidental introduction of runtime `V31-F`/`V31-G` release behavior in v35 fails CI and blocks merge.
  - no-touch diff guard failure on frozen runtime files is merge-blocking.
- No-authorize-action-calls guard lock is frozen:
  - v35 guards must fail closed if worker run/cancel paths invoke `authorize_action`.
- Behavior-sentinel lock is frozen:
  - v35 must keep deterministic sentinel snapshots for `/urm/worker/run` and `/urm/worker/{worker_id}/cancel` behavior compatible with v34 baseline outputs.
  - sentinel comparison authority is structured response JSON with frozen high-entropy field exclusion set.
- Deterministic-guard-output lock is frozen:
  - guard outputs are deterministic and machine-checkable under fixed inputs.
- No-provider/no-network guard lock is frozen:
  - tests fail closed if in-scope boundary-prep flows trigger provider expansion or outbound-network calls.

### Acceptance

- Guard suites pass deterministically across reruns.
- Missing/invalid boundary-readiness assertions fail closed.
- No-touch runtime-file diff guard remains green.
- No-authorize-action-calls callgraph guard remains green for worker run/cancel paths.
- Behavior sentinel snapshots remain compatible with v34 baseline.
- No runtime behavior implementation files from the frozen no-touch list are modified in v35 PR scope.
- No partial L2 release/scaffolding behavior lands under v35 preparatory scope.

### I2 Implementation Snapshot

- Boundary-readiness lint entrypoint implemented:
  - `apps/api/scripts/lint_l2_boundary_readiness.py`.
- Frozen sentinel fixtures added:
  - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_run_response_v34_baseline.json`
  - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_cancel_response_v34_baseline.json`
- Deterministic guard test suite added:
  - `apps/api/tests/test_l2_boundary_readiness_lint.py`.
- CI wiring added in `.github/workflows/ci.yml` with frozen lint CLI and deterministic env posture (`TZ=UTC`, `LC_ALL=C`).
- Merge evidence:
  - PR `#217` merged at `ac5f1897f9855234a3a9988691370ebdae3a50fe`.

## Stop-Gate Impact (v35)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v35 closeout must include runtime-observability comparison row against v34 baseline.
- Runtime-observability closeout placement lock is frozen:
  - v35 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS35.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v35)

- No new URM error-code family is introduced in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `docs: freeze v35 L2 boundary-release precondition contract for V31-F/V31-G` (implemented)
2. `tests/docs: add v35 boundary-readiness lint, no-touch diff guard, and behavior sentinel checks` (implemented)

## Intermediate Preconditions (for v35 start)

1. v34 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v34 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS34.md`
3. In-scope boundary authority surfaces remain available at v35 start:
   - `apps/api/src/adeu_api/urm_routes.py`
   - `packages/urm_runtime/src/urm_runtime/capability_policy.py`
   - `apps/api/src/adeu_api/main.py`
   - `apps/api/src/adeu_api/storage.py`
4. Frozen boundary gap baselines remain true at v35 start:
   - `/urm/worker/run` and `/urm/worker/{worker_id}/cancel` are not yet routed through `authorize_action`.
   - proposer idempotency authority remains process-local `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`.
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. Boundary-readiness lint entrypoint exists and remains enabled:
   - `apps/api/scripts/lint_l2_boundary_readiness.py`
7. Sentinel baseline fixtures exist and are sourced from v34 baseline behavior:
   - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_run_response_v34_baseline.json`
   - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_cancel_response_v34_baseline.json`
8. No L2 boundary release is introduced in this arc.

## Exit Criteria (Draft)

- `I1` and `I2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic boundary-release precondition contract for `V31-F`/`V31-G` is closed and test-covered.
- Frozen no-touch runtime file set remains unchanged through v35 merge commits.
- v35 closeout evidence includes runtime-observability comparison row against v34 baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
