# Locked Continuation vNext+42 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS41.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+41` (`P1`-`P2`) is merged on `main` via PR `#228` and PR `#229` with green CI checks.
- `vNext+41` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS41.md` with `all_passed = true`.
- Post-v41 planning baseline remains `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.
- Selected v42 thin-slice default is CI/closeout wiring candidate:
  - `V32-E` (CI gate + closeout evidence wiring, keyset-preserving).
- `vNext+42` is constrained to deterministic additive hardening for `V32-E` only:
  - no solver/runtime semantics release,
  - no governance/persistence boundary release expansion,
  - no stop-gate metric-key expansion release in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v42,
  - v42 keyset must be exactly equal to v41 keyset (set equality, derived cardinality),
  - baseline derived cardinality at v42 start is `79` and must remain unchanged in this arc,
  - repository closeout artifacts for v36/v37/v38/v39/v40/v41 each report derived metric-key cardinality `79`,
  - keyset authority is `stop_gate_metrics@1` payload field `metrics` object keys only,
  - keyset extraction/comparison in this arc is from closeout artifacts produced by `apps/api/scripts/build_stop_gate_metrics.py` and validated by deterministic docs lint `apps/api/scripts/lint_closeout_consistency.py` using exact-set equality.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v36 continuity guarantees remain frozen as release preconditions:
  - worker-route governance release contract (`V31-F`, `J1`) remains authoritative,
  - v36 governance-release guard suite (`V31-F`, `J2`) remains authoritative baseline.
- v37 continuity guarantees remain frozen as release preconditions:
  - proposer persisted idempotency source-of-truth contract (`V31-G`, `K1`) remains authoritative,
  - v37 persistence-release guard suite (`V31-G`, `K2`) remains authoritative baseline.
- v38 continuity guarantees remain frozen as release preconditions:
  - commitments IR schema authority/mirror parity contract (`V32-A`, `M1`) remains authoritative,
  - v38 commitments deterministic guard suite (`V32-A`, `M2`) remains authoritative baseline.
- v39 continuity guarantees remain frozen as release preconditions:
  - semantic-source parser/normalizer contract (`V32-B`, `N1`) remains authoritative,
  - v39 semantic-source deterministic guard suite (`V32-B`, `N2`) remains authoritative baseline.
- v40 continuity guarantees remain frozen as release preconditions:
  - compiler-core pass pipeline contract (`V32-C`, `O1`) remains authoritative,
  - v40 compiler-core determinism/fail-closed guard suite (`V32-C`, `O2`) remains authoritative baseline.
- v41 continuity guarantees remain frozen as release preconditions:
  - surface governance/codegen contract (`V32-D`, `P1`) remains authoritative,
  - v41 surface governance determinism/fail-closed guard suite (`V32-D`, `P2`) remains authoritative baseline.
- Boundary-release scope lock for v42 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- ASC semantic interpretation boundary lock is frozen:
  - semantic authority for ASC-path work derives only from explicit semantic blocks,
  - narrative prose is non-authoritative for semantic hash derivation,
  - prose-inference parsing is forbidden unless explicitly authorized by a future lock.
- Closeout observability continuity lock is frozen:
  - v42 closeout must include a runtime-observability comparison row against v41 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `Q1` CI gate + closeout evidence wiring MVP (`V32-E`)
2. `Q2` CI/closeout determinism-fail-closed guard suite (`V32-E`)

Out-of-scope note:

- any `SEMANTICS_v4` runtime contract release,
- commitments IR schema evolution release (`V32-A`) in this arc,
- semantic-source grammar/parser surface evolution release (`V32-B`) in this arc,
- compiler core pass-sequence or diagnostics contract evolution release (`V32-C`) in this arc,
- surface snapshot/delta contract evolution release (`V32-D`) in this arc,
- stop-gate metric-key expansion for semantic compiler evidence (`V32-F`) in this arc,
- compiler partial-execution CLI (`--stop-after`) in this arc,
- bootstrap overflow circuit-breaker / PR split chunk-size policy release in this arc,
- semantic-equivalency delta-evaluation release in this arc,
- deep-path keyset extraction semantics release in this arc,
- resolver namespace aliasing/workspace-scoped bindings in this arc,
- any provider or proposer endpoint expansion,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v42)

- v43+ optional stop-gate metric extension for semantic compiler evidence (`V32-F`) via explicit lock update.
- v44+ compiler developer ergonomics (`--stop-after`, intermediate IR dumps) under explicit lock text.
- v45+ resolver namespace aliasing/workspace-scoped bindings under explicit lock text.
- v46+ deterministic bootstrap overflow controls + PR split chunking under explicit lock text.
- v47+ semantic-equivalency delta evaluation lane for structured surfaces under explicit lock text.
- v48+ deep-path keyset extraction semantics under explicit lock text.

## V41 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
  "target": "V32-E",
  "required_continuity_guards": [
    "V31_F_GOVERNANCE_CONTINUITY_GREEN",
    "V31_G_PERSISTENCE_CONTINUITY_GREEN",
    "V32_A_COMMITMENTS_CONTINUITY_GREEN",
    "V32_B_SEMANTIC_SOURCE_CONTINUITY_GREEN",
    "V32_C_COMPILER_CORE_CONTINUITY_GREEN",
    "V32_D_SURFACE_CODEGEN_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v42.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V32-E CI/Closeout Wiring Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v32e_ci_closeout_contract@1",
  "target_arc": "vnext_plus42",
  "target_path": "V32-E",
  "semantic_compiler_entrypoint": "python -m adeu_semantic_compiler.compile",
  "input_artifacts": {
    "v41_surface_snapshot": "artifacts/semantic_compiler/v41/surface_snapshot.json",
    "v41_surface_diff": "artifacts/semantic_compiler/v41/surface_diff.json",
    "v41_evidence_manifest": "artifacts/semantic_compiler/v41/evidence_manifest.json",
    "v41_pr_splits_markdown": "docs/generated/semantic_compiler/v41/PR_SPLITS.md",
    "v41_quality_dashboard": "artifacts/quality_dashboard_v41_closeout.json",
    "v41_stop_gate_metrics": "artifacts/stop_gate/metrics_v41_closeout.json"
  },
  "ci_wiring": {
    "workflow_authority": ".github/workflows/ci.yml",
    "required_lane": "python",
    "lint_entrypoint": "apps/api/scripts/lint_semantic_compiler_closeout.py",
    "deterministic_env": {
      "TZ": "UTC",
      "LC_ALL": "C"
    },
    "workflow_rename_policy": "allowed_only_if_guard_coverage_equivalent_and_explicit"
  },
  "closeout_doc_policy": {
    "decision_doc": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS42.md",
    "required_json_blocks": [
      "runtime_observability_comparison@1",
      "metric_key_continuity_assertion@1",
      "v32e_ci_wiring_evidence@1"
    ],
    "semantic_compiler_evidence_authority": "v41_artifacts_referenced_with_schema_and_hash_consistency"
  },
  "stop_gate_continuity_policy": {
    "schema_family": "stop_gate_metrics@1",
    "metric_key_change": "forbidden",
    "expected_keyset_relation": "exact_set_equality_with_v41",
    "expected_cardinality": 79
  },
  "fail_closed_conditions": [
    "missing_required_semantic_compiler_artifact",
    "semantic_compiler_artifact_schema_mismatch",
    "semantic_compiler_artifact_hash_mismatch",
    "required_closeout_block_missing",
    "stop_gate_metric_keyset_drift",
    "ci_wiring_coverage_drift"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## Q1) CI Gate + Closeout Evidence Wiring MVP (`V32-E`)

### Goal

Introduce deterministic CI/docs wiring that validates semantic compiler closeout evidence without changing stop-gate metric keys.

Lock-class rationale:

- this slice is `L0` because it wires deterministic CI/docs guard behavior on existing artifact contracts without releasing new runtime/provider/persistence boundaries.

### Scope

- Add deterministic lint entrypoint for semantic compiler closeout evidence wiring:
  - required semantic compiler artifacts must exist at frozen paths,
  - required artifact schemas must match frozen contract IDs,
  - referenced artifact hashes in closeout decision docs must match computed SHA-256 values,
  - closeout decision doc must include required machine-checkable JSON blocks.
- Add deterministic CI lane wiring:
  - v42 CI integration runs in default Python lane,
  - lane coverage must include v42 semantic-compiler closeout lint checks,
  - workflow/job renames are allowed only when equivalent coverage remains explicit.
- Add deterministic closeout-doc wiring:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS42.md` must include v42 runtime observability comparison row against v41 baseline,
  - metric-key continuity assertion must remain exact-set equality from v41 to v42,
  - v42 closeout must emit `v32e_ci_wiring_evidence@1` block.
- Preserve stop-gate continuity in v42 wiring:
  - no new metric keys,
  - no schema-family fork,
  - no threshold-policy widening introduced by this slice.
- Preserve v41 semantic compiler artifact contract authority:
  - no contract-ID churn for v41 artifact families in this arc,
  - no V32-D behavior expansion in this arc.

### Locks

- Contract-surface lock is frozen:
  - v42 introduces CI/closeout wiring contract only.
- CI-lane authority lock is frozen:
  - required guard execution authority is default Python CI lane.
- Closeout-lint entrypoint lock is frozen:
  - `apps/api/scripts/lint_semantic_compiler_closeout.py` is authoritative in this arc.
- Closeout-doc schema lock is frozen:
  - v42 decision doc must contain required machine-checkable JSON block families.
- Artifact-schema continuity lock is frozen:
  - v41 semantic compiler artifact schema identifiers remain authoritative in this arc.
- Artifact-hash continuity lock is frozen:
  - referenced artifact hashes must match deterministic recomputation.
- Stop-gate keyset continuity lock is frozen:
  - v42 must preserve exact keyset equality and derived cardinality continuity from v41.
- Scope fence lock is frozen:
  - v42 may not release `V32-F` metric-key expansion behavior.
- Runtime boundary lock is frozen:
  - v42 may not modify runtime endpoint behavior/policy semantics.

### Acceptance

- CI fails closed on missing/mismatched semantic-compiler closeout artifacts.
- v42 closeout-doc required blocks are machine-checkable and deterministic.
- Stop-gate keyset continuity remains exact-set equal to v41.
- No regression of v36/v37/v38/v39/v40/v41 continuity guards.

## Q2) CI/Closeout Determinism-Fail-Closed Guard Suite (`V32-E`)

### Goal

Prove v42 CI/docs integration behavior is deterministic, fail-closed, and continuity-preserving.

### Scope

- Add/adjust deterministic tests/guards for:
  - closeout-lint rerun determinism under fixed inputs,
  - fail-closed handling for missing semantic compiler artifacts,
  - fail-closed handling for schema-ID drift in semantic compiler artifacts,
  - fail-closed handling for artifact hash mismatch against decision-doc references,
  - fail-closed handling for missing required closeout JSON block families,
  - fail-closed handling for stop-gate metric keyset drift,
  - deterministic metric-key cardinality assertions (`79`),
  - deterministic CI lane coverage assertions for v42-required checks,
  - continuity-preservation assertions for v36/v37/v38/v39/v40/v41 frozen suites.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v42 tests/guards may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v41 continuity metrics remain at required values.
- Required-closeout-lint-determinism lock is frozen:
  - v42 guards fail closed if lint reruns drift under fixed inputs.
- Required-closeout-blocks lock is frozen:
  - v42 guards fail closed if required closeout block families are missing or malformed.
- Required-artifact-schema lock is frozen:
  - v42 guards fail closed if referenced semantic compiler artifact schemas drift from frozen IDs.
- Required-artifact-hash lock is frozen:
  - v42 guards fail closed when referenced artifact hash values mismatch deterministic recomputation.
- Required-keyset-continuity lock is frozen:
  - v42 guards fail closed if stop-gate keysets drift from v41 exact-set baseline.
- Required-cardinality lock is frozen:
  - v42 guards fail closed if derived metric-key cardinality drifts from `79`.
- Required-ci-lane-coverage lock is frozen:
  - v42 guards fail closed when required Python-lane coverage is removed or silently relocated.
- Continuity-preservation lock is frozen:
  - v42 guards fail closed if v36/v37/v38/v39/v40/v41 continuity suites regress.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required closeout wiring and fail-closed assertions are green.
- CI/docs wiring strictness behavior is fail-closed and test-covered.
- v36/v37/v38/v39/v40/v41 continuity guard suites remain green under v42 scope.

## Stop-Gate Impact (v42)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v42 closeout must include runtime-observability comparison row against v41 baseline.
- v42 closeout must include CI wiring evidence block:
  - block schema is docs-only `v32e_ci_wiring_evidence@1`,
  - required keys are:
    - `schema`
    - `lint_entrypoint`
    - `workflow_path`
    - `required_lane`
    - `closeout_doc`
    - `required_blocks_present`
    - `artifact_hashes_verified`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v41`
    - `notes`
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
- Runtime-observability closeout placement lock is frozen:
  - v42 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS42.md` inside a machine-checkable JSON block.
- Runtime-observability interpretation lock is frozen:
  - v42 runtime-observability comparison row is required evidence and is informational-only for this arc,
  - no new pass/fail threshold is introduced in this arc on elapsed timing deltas.

## Error/Exit Policy (v42)

- No new URM error-code family is introduced in this arc.
- Semantic-compiler reason-code registry in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V32-E CI gate and closeout evidence wiring (keyset-preserving)`
2. `tests: add v42 CI/closeout determinism and fail-closed guard suite`

## Intermediate Preconditions (for v42 start)

1. v41 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v41 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS41.md`
3. Existing semantic compiler entrypoint remains available at v42 start:
   - `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py`
4. Existing v41 semantic compiler artifacts remain available at v42 start:
   - `artifacts/semantic_compiler/v41/surface_snapshot.json`
   - `artifacts/semantic_compiler/v41/surface_diff.json`
   - `artifacts/semantic_compiler/v41/evidence_manifest.json`
   - `docs/generated/semantic_compiler/v41/PR_SPLITS.md`
5. Existing v41 closeout artifacts remain available at v42 start:
   - `artifacts/quality_dashboard_v41_closeout.json`
   - `artifacts/stop_gate/metrics_v41_closeout.json`
   - `artifacts/stop_gate/report_v41_closeout.md`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. Existing v31g persistence continuity lint remains enabled:
   - `apps/api/scripts/lint_v31g_persistence_release.py`
8. No additional `L2` boundary release beyond v41 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `Q1` and `Q2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic CI/closeout evidence wiring MVP (`V32-E`) is closed and test-covered.
- v42 closeout evidence includes runtime-observability comparison row against v41 baseline.
- v36 governance, v37 persistence, v38 commitments, v39 semantic-source, v40 compiler-core, and v41 surface-governance continuity remain green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
