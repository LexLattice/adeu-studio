# Locked Continuation vNext+41 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS40.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+40` (`O1`-`O2`) is merged on `main` via PR `#226` and PR `#227` with green CI checks.
- `vNext+40` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS40.md` with `all_passed = true`.
- Post-v40 planning baseline remains `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.
- Selected v41 thin-slice default is surface governance/codegen candidate:
  - `V32-D` (surface snapshot/delta + PR/evidence codegen).
- `vNext+41` is constrained to deterministic additive hardening for `V32-D` only:
  - no solver/runtime semantics release,
  - no governance/persistence boundary release expansion,
  - no semantic-compiler CI gate integration release in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v41,
  - v41 keyset must be exactly equal to v40 keyset (set equality, derived cardinality),
  - baseline derived cardinality at v41 start is `79` and must remain unchanged in this arc,
  - repository closeout artifacts for v36/v37/v38/v39/v40 each report derived metric-key cardinality `79`,
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
- Boundary-release scope lock for v41 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- ASC semantic interpretation boundary lock is frozen:
  - semantic authority for ASC-path work derives only from explicit semantic blocks,
  - narrative prose is non-authoritative for semantic hash derivation,
  - prose-inference parsing is forbidden unless explicitly authorized by a future lock.
- Closeout observability continuity lock is frozen:
  - v41 closeout must include a runtime-observability comparison row against v40 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `P1` surface snapshot/delta + PR/evidence codegen MVP (`V32-D`)
2. `P2` surface governance determinism/fail-closed guard suite (`V32-D`)

Out-of-scope note:

- any `SEMANTICS_v4` runtime contract release,
- commitments IR schema evolution release (`V32-A`) in this arc,
- semantic-source grammar/parser surface evolution release (`V32-B`) in this arc,
- compiler core pass-sequence or diagnostics contract evolution release (`V32-C`) in this arc,
- semantic-compiler CI gate integration release (`V32-E`) in this arc,
- stop-gate metric-key expansion for semantic compiler evidence (`V32-F`) in this arc,
- compiler partial-execution CLI (`--stop-after`) in this arc,
- resolver namespace aliasing/workspace-scoped bindings in this arc,
- any provider or proposer endpoint expansion,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v41)

- v42+ CI/closeout evidence wiring (`V32-E`).
- v43+ optional stop-gate metric extension for semantic compiler evidence (`V32-F`) via explicit lock update.
- v44+ compiler developer ergonomics (`--stop-after`, intermediate IR dumps) under explicit lock text.
- v45+ resolver namespace aliasing/workspace-scoped bindings under explicit lock text.

## V40 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md",
  "target": "V32-D",
  "required_continuity_guards": [
    "V31_F_GOVERNANCE_CONTINUITY_GREEN",
    "V31_G_PERSISTENCE_CONTINUITY_GREEN",
    "V32_A_COMMITMENTS_CONTINUITY_GREEN",
    "V32_B_SEMANTIC_SOURCE_CONTINUITY_GREEN",
    "V32_C_COMPILER_CORE_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v41.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V32-D Surface Governance/Codegen Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v32d_surface_codegen_contract@1",
  "package_root": "packages/adeu_semantic_compiler",
  "export_entrypoint": "packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py",
  "export_call_pattern": "python -m adeu_semantic_compiler.compile",
  "input_ir_contract_id": "adeu_commitments_ir@0.1",
  "input_diagnostics_contract_id": "semantic_compiler_diagnostics@0.1",
  "input_pass_manifest_contract_id": "semantic_compiler_pass_manifest@0.1",
  "input_artifacts": {
    "commitments_ir": "artifacts/semantic_compiler/v40/commitments_ir.json",
    "diagnostics": "artifacts/semantic_compiler/v40/semantic_compiler.diagnostics.json",
    "pass_manifest": "artifacts/semantic_compiler/v40/pass_manifest.json"
  },
  "input_handoff_policy": {
    "compiler_diagnostics_errors": "fail_closed",
    "pass_manifest_chain_complete": "required",
    "pass_hash_subject_continuity": "canonical_json_bytes_of_pass_value"
  },
  "surface_kinds_enabled": [
    "schema",
    "manifest",
    "file",
    "markdown_json_block"
  ],
  "surface_selector_normalization": {
    "path_separator": "posix",
    "collapse_dot_segments": true,
    "allow_absolute_paths": false,
    "symlink_resolution": "forbidden_for_signature_basis"
  },
  "surface_registry_ordering": "surface_id_lexicographic",
  "delta_rule_modes": [
    "freeze",
    "additive_only",
    "exact_set"
  ],
  "delta_policy": {
    "freeze_violation": "error",
    "additive_break_violation": "error",
    "exact_set_violation": "error"
  },
  "baseline_snapshot_policy": {
    "preferred_baseline_snapshot": "artifacts/semantic_compiler/v40/surface_snapshot.json",
    "when_missing": "bootstrap_no_baseline",
    "bootstrap_surface_diff_mode": "no_baseline"
  },
  "output_artifacts": {
    "surface_snapshot": "artifacts/semantic_compiler/v41/surface_snapshot.json",
    "surface_diff": "artifacts/semantic_compiler/v41/surface_diff.json",
    "evidence_manifest": "artifacts/semantic_compiler/v41/evidence_manifest.json",
    "pr_splits_markdown": "docs/generated/semantic_compiler/v41/PR_SPLITS.md"
  },
  "output_artifact_path_policy": {
    "artifacts_base": "artifacts/semantic_compiler/v41",
    "docs_generated_base": "docs/generated/semantic_compiler/v41",
    "allow_outside_base_dir": false
  },
  "output_contract_ids": {
    "surface_snapshot": "semantic_compiler_surface_snapshot@0.1",
    "surface_diff": "semantic_compiler_surface_diff@0.1",
    "evidence_manifest": "semantic_compiler_evidence_manifest@0.1",
    "pr_splits_markdown": "semantic_compiler_pr_splits_markdown@0.1"
  },
  "evidence_manifest_required_fields": [
    "schema",
    "arc",
    "compiler_entrypoint",
    "source_set_hash",
    "required_evidence",
    "artifacts",
    "artifact_hashes"
  ],
  "pr_splits_ordering": {
    "primary": "slice_id",
    "secondary": "module_id"
  },
  "diagnostic_code_namespace": "SCC",
  "diagnostic_code_pattern": "^SCC[0-9]{4}$",
  "fail_closed_conditions": [
    "unknown_surface_kind",
    "surface_selector_resolution_error",
    "delta_rule_violation",
    "output_path_policy_violation",
    "evidence_manifest_schema_violation",
    "pr_split_generation_drift"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## P1) Surface Snapshot/Delta + PR/Evidence Codegen MVP (`V32-D`)

### Goal

Introduce deterministic surface-governance artifacts and deterministic PR/evidence codegen derived from v40 compiler-core outputs.

Lock-class rationale:

- this slice is `L1` because it introduces new deterministic artifact contracts (`surface_snapshot`, `surface_diff`, `evidence_manifest`, `PR_SPLITS`) consumed by follow-on governance/CI paths.

### Scope

- Extend `packages/adeu_semantic_compiler` with deterministic surface extraction and governance artifact generation for:
  - `schema` surfaces,
  - `manifest` surfaces,
  - `file` surfaces,
  - `markdown_json_block` surfaces.
- Freeze v41 input boundary:
  - v41 surface/codegen flow consumes v40 compiler-core artifacts (`commitments_ir`, `semantic_compiler.diagnostics`, `pass_manifest`) only,
  - input diagnostics handoff is strict: any v40 compiler diagnostic with severity `ERROR` fails closed,
  - input pass-manifest chain completeness is required and fail-closed.
- Freeze deterministic surface registry/order policy:
  - normalized surface selectors are deterministic and path-normalized,
  - surface registry ordering is lexicographic by `surface_id`.
- Freeze deterministic surface delta policy:
  - supported delta-rule modes are `freeze`, `additive_only`, and `exact_set`,
  - any freeze/additive/exact-set rule violation fails closed,
  - baseline snapshot policy is deterministic bootstrap: if `artifacts/semantic_compiler/v40/surface_snapshot.json` is absent, v41 emits deterministic `no_baseline` diff mode rather than implicit behavior.
- Freeze deterministic output artifact boundary:
  - `surface_snapshot`: `artifacts/semantic_compiler/v41/surface_snapshot.json`,
  - `surface_diff`: `artifacts/semantic_compiler/v41/surface_diff.json`,
  - `evidence_manifest`: `artifacts/semantic_compiler/v41/evidence_manifest.json`,
  - `PR_SPLITS`: `docs/generated/semantic_compiler/v41/PR_SPLITS.md`.
- Freeze codegen determinism:
  - `PR_SPLITS` ordering is deterministic (`slice_id`, `module_id`),
  - evidence-manifest required-field set is fixed and deterministic in this arc.
- Freeze fail-closed core behavior:
  - unknown surface kinds fail closed,
  - ambiguous surface extraction results fail closed,
  - output-path policy violations fail closed,
  - evidence-manifest contract violations fail closed.
- Keep v41 contract surface-governance/codegen only:
  - no CI lane integration behavior (`V32-E`) is introduced in this arc,
  - no stop-gate metric-key expansion (`V32-F`) is introduced in this arc.

### Locks

- Contract-surface lock is frozen:
  - v41 introduces surface snapshot/delta + PR/evidence codegen contract only.
- Entrypoint lock is frozen:
  - compile command authority remains single-entrypoint (`python -m adeu_semantic_compiler.compile`); alternate entrypoints are non-authoritative.
- Input-boundary lock is frozen:
  - v41 surface/codegen flow consumes only v40 compiler artifacts (`commitments_ir`, `semantic_compiler.diagnostics`, `pass_manifest`).
  - v40 compiler diagnostics containing any `ERROR` are fail-closed for v41 input handoff.
  - pass-manifest chain completeness is required.
- Surface-kind lock is frozen:
  - supported kinds are exactly `schema`, `manifest`, `file`, and `markdown_json_block`.
- Surface-selector-normalization lock is frozen:
  - selectors are normalized with POSIX separators,
  - dot segments are collapsed deterministically,
  - absolute paths are forbidden,
  - symlink resolution is not used in signature basis.
- Surface-registry ordering lock is frozen:
  - surfaces are serialized in deterministic `surface_id` lexicographic order.
- Delta-policy lock is frozen:
  - supported rule modes are exactly `freeze`, `additive_only`, `exact_set`.
  - violations of any locked rule mode are invalid and fail closed.
- Baseline-bootstrap lock is frozen:
  - preferred baseline snapshot is `artifacts/semantic_compiler/v40/surface_snapshot.json`.
  - if absent, deterministic `no_baseline` diff mode is required.
- Output-contract lock is frozen:
  - compiler outputs are exactly `surface_snapshot`, `surface_diff`, `evidence_manifest`, and `PR_SPLITS` in v41 paths.
  - writes outside frozen v41 artifact/doc generated roots are invalid and fail closed.
- Evidence-manifest lock is frozen:
  - required top-level field set is frozen for this arc.
- PR-splits lock is frozen:
  - generated PR split ordering is deterministic by `(slice_id, module_id)`.
- Diagnostics continuity lock is frozen:
  - diagnostics namespace continuity remains `SCC[0-9]{4}`.
- Canonical-hash lock is frozen:
  - all JSON artifact hashes use frozen canonical JSON SHA-256 profile.
- No-runtime-mutation lock is frozen:
  - v41 may not modify runtime endpoint behavior/policy semantics.
- No-ci-gate-release lock is frozen:
  - v41 may not release `V32-E` CI/closeout integration behavior.
- No-metrics-expansion lock is frozen:
  - v41 may not introduce stop-gate metric-key changes.

### Acceptance

- Surface snapshot/delta + PR/evidence codegen MVP is present with deterministic artifact outputs.
- Compiler reruns under fixed v40 inputs are byte-identical for v41 artifacts.
- No regression of v36/v37/v38/v39/v40 continuity guards.

## P2) Surface Governance Determinism/Fail-Closed Guard Suite (`V32-D`)

### Goal

Prove v41 surface-governance/codegen behavior is deterministic, fail-closed, and regression-resistant.

### Scope

- Add/adjust deterministic tests/guards for:
  - v41 rerun determinism (repeat runs yield byte-identical `surface_snapshot`, `surface_diff`, `evidence_manifest`, and `PR_SPLITS` outputs),
  - frozen surface-kind assertions:
    - only `schema`, `manifest`, `file`, `markdown_json_block` are accepted,
    - unknown surface kinds fail closed,
  - deterministic selector normalization assertions:
    - absolute paths are rejected,
    - dot-segment normalization is deterministic,
    - selector normalization remains POSIX,
  - strict delta-policy assertions:
    - freeze-rule violations fail closed,
    - additive-only breaking deltas fail closed,
    - exact-set violations fail closed,
  - baseline-bootstrap assertions:
    - absent baseline snapshot yields deterministic `no_baseline` diff mode,
    - baseline-present mode remains deterministic and byte-stable,
  - deterministic evidence-manifest assertions:
    - required top-level field set is present and stable,
    - artifact hash sections are deterministic across reruns,
  - deterministic PR split assertions:
    - `PR_SPLITS.md` ordering follows frozen `(slice_id, module_id)` ordering,
    - equal inputs reproduce byte-identical markdown output,
  - output-path policy assertions:
    - writes outside v41 artifact/doc generated roots fail closed,
  - generated-artifact cleanliness assertion:
    - rerun compiler entrypoint and fail closed if v41 artifacts differ from committed bytes,
  - continuity-preservation assertions:
    - v36/v37/v38/v39/v40 continuity suites remain green and unreverted.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v41 tests/guards may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v40 continuity metrics remain at required values.
- Required-surface-determinism lock is frozen:
  - v41 guards fail closed if surface/codegen reruns drift by bytes.
- Required-fail-closed lock is frozen:
  - v41 guards fail closed if invalid surface selectors/kinds/deltas are silently accepted.
- Required-input-handoff lock is frozen:
  - v41 guards fail closed when v40 input diagnostics contain any `ERROR` or pass-manifest chain completeness drifts.
- Required-delta-policy lock is frozen:
  - v41 guards fail closed if freeze/additive/exact-set semantics drift from frozen contract.
- Required-bootstrap-policy lock is frozen:
  - v41 guards fail closed if missing-baseline handling drifts from deterministic `no_baseline` mode.
- Required-output-path lock is frozen:
  - v41 guards fail closed if artifact writes escape frozen output roots.
- Generated-artifact cleanliness lock is frozen:
  - v41 guards fail closed when deterministic artifacts regenerate to non-committed deltas.
- Continuity-preservation lock is frozen:
  - v41 guards fail closed if v36/v37/v38/v39/v40 continuity suites regress.
- Deterministic-guard-output lock is frozen:
  - guard outputs are deterministic and machine-checkable under fixed inputs.
- CI lane continuity lock is frozen:
  - in-scope v41 surface/codegen guards must run in default Python CI lane,
  - workflow/job renaming is allowed only if required guard coverage remains equivalent and explicit in CI config.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required surface determinism, delta-policy freeze, and fail-closed assertions are green.
- Surface governance/codegen strictness behavior is fail-closed and test-covered.
- v36/v37/v38/v39/v40 continuity guard suites remain green under v41 scope.

## Stop-Gate Impact (v41)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v41 closeout must include runtime-observability comparison row against v40 baseline.
- v41 closeout must include surface-governance/codegen artifact evidence block:
  - block schema is docs-only `v32d_surface_codegen_evidence@1`,
  - required keys are:
    - `schema`
    - `surface_snapshot_artifact`
    - `surface_diff_artifact`
    - `evidence_manifest_artifact`
    - `pr_splits_artifact`
    - `surface_snapshot_sha256`
    - `surface_diff_sha256`
    - `evidence_manifest_sha256`
    - `pr_splits_sha256`
    - `delta_eval_mode`
    - `byte_replay_equal`
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
  - v41 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS41.md` inside a machine-checkable JSON block.
- Runtime-observability interpretation lock is frozen:
  - v41 runtime-observability comparison row is required evidence and is informational-only for this arc,
  - no new pass/fail threshold is introduced in this arc on elapsed timing deltas.

## Error/Exit Policy (v41)

- No new URM error-code family is introduced in this arc.
- Semantic-compiler reason-code registry in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V32-D surface snapshot/delta and PR/evidence codegen MVP`
2. `tests: add v41 surface governance determinism and fail-closed guard suite`

## Intermediate Preconditions (for v41 start)

1. v40 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v40 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS40.md`
3. Existing semantic compiler entrypoint remains available at v41 start:
   - `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py`
4. Existing commitments IR contract remains available at v41 start:
   - `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`
5. Existing v40 compiler artifacts remain available at v41 start:
   - `artifacts/semantic_compiler/v40/commitments_ir.json`
   - `artifacts/semantic_compiler/v40/semantic_compiler.diagnostics.json`
   - `artifacts/semantic_compiler/v40/pass_manifest.json`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. Existing v31g persistence continuity lint remains enabled:
   - `apps/api/scripts/lint_v31g_persistence_release.py`
8. No additional `L2` boundary release beyond v40 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `P1` and `P2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic surface snapshot/delta + PR/evidence codegen MVP (`V32-D`) is closed and test-covered.
- v41 closeout evidence includes runtime-observability comparison row against v40 baseline.
- v36 governance, v37 persistence, v38 commitments, v39 semantic-source, and v40 compiler-core continuity remain green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
