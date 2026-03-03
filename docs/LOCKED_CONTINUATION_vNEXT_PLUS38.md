# Locked Continuation vNext+38 (Closed Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS37.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: closed lock (implemented on `main`, March 3, 2026 UTC).

Decision basis:

- `vNext+37` (`K1`-`K2`) is merged on `main` via PR `#220` and PR `#221` with green CI checks.
- `vNext+37` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS37.md` with `all_passed = true`.
- Post-v37 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.
- Selected v38 thin-slice default is first ASC contract bootstrap candidate:
  - `V32-A` (commitments IR contract bootstrap).
- `vNext+38` is constrained to deterministic additive hardening for `V32-A` only:
  - no solver/runtime semantics release,
  - no governance/persistence boundary release expansion,
  - no semantic parser/compiler pipeline release in this arc.
- `vNext+38` (`M1`-`M2`) is now merged on `main` via PR `#222` and PR `#223` with green CI checks.
- `vNext+38` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS38.md` with `all_passed = true`.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v38,
  - v38 keyset must be exactly equal to v37 keyset (set equality, derived cardinality),
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
- Boundary-release scope lock for v38 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- ASC semantic interpretation boundary lock is frozen:
  - semantic authority for ASC-path work derives only from explicit semantic blocks,
  - narrative prose is non-authoritative for semantic hash derivation,
  - prose-inference parsing is forbidden unless explicitly authorized by a future lock.
- Closeout observability continuity lock is frozen:
  - v38 closeout must include a runtime-observability comparison row against v37 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `M1` commitments IR contract/bootstrap package (`V32-A`)
2. `M2` commitments IR determinism/parity guard suite (`V32-A`)

Out-of-scope note:

- any `SEMANTICS_v4` runtime contract release,
- semantic-source parser/block extraction release (`V32-B`) in this arc,
- compiler pass-manager release (`V32-C`) in this arc,
- surface snapshot/delta/codegen release (`V32-D`) in this arc,
- semantic-compiler CI gate integration release (`V32-E`) in this arc,
- stop-gate metric-key expansion for semantic compiler evidence (`V32-F`) in this arc,
- any provider or proposer endpoint expansion,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v38)

- v39+ semantic source grammar/parser/normalizer (`V32-B`).
- v40+ compiler core pass pipeline (`V32-C`).
- v41+ surface snapshot/delta + PR/evidence codegen (`V32-D`).
- v42+ CI/closeout evidence wiring (`V32-E`) and optional stop-gate metric extension (`V32-F`) via explicit lock update.

## V37 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md",
  "target": "V32-A",
  "required_continuity_guards": [
    "V31_F_GOVERNANCE_CONTINUITY_GREEN",
    "V31_G_PERSISTENCE_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v38.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V32-A Schema Export Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v32a_schema_export_contract@1",
  "package_root": "packages/adeu_commitments_ir",
  "authoritative_schema_path": "packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json",
  "mirror_schema_path": "spec/adeu_commitments_ir.schema.json",
  "export_entrypoint": "packages/adeu_commitments_ir/src/adeu_commitments_ir/export_schema.py",
  "export_call_pattern": "python -m adeu_commitments_ir.export_schema",
  "json_schema_call_profile": {
    "by_alias": true
  },
  "schema_contract_id": "adeu_commitments_ir@0.1",
  "module_union_discriminator": "module_kind",
  "reason_code_namespace_format": "ASC-CIR-0001",
  "version_file_convention": "authoritative_v0_1_plus_spec_schema_mirror",
  "mirror_relation": "mirror_matches_authoritative"
}
```

## M1) Commitments IR Contract Bootstrap (`V32-A`)

### Goal

Introduce typed commitments IR contract in repo-native form with deterministic schema export/mirror discipline.

Lock-class rationale:

- this slice is `L1` because it introduces a new versioned schema contract mirrored under `spec/`.

### Scope

- Add package `packages/adeu_commitments_ir` with:
  - deterministic typed models,
  - discriminated module union for commitments IR modules,
  - stable ID helper(s),
  - deterministic reason-code registry (`ASC-CIR-0001` namespace format).
- Enforce strict model posture:
  - `extra="forbid"` for v0 model contract.
- Add schema export entrypoint and authoritative/mirror outputs:
  - authoritative schema file `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`,
  - mirrored schema in `spec/adeu_commitments_ir.schema.json`.
- Freeze union discriminator key for module union:
  - commitments IR discriminated union key is `module_kind`.
  - each union member must bind `module_kind` as a unique `Literal[...]` value (generic-string discriminator typing is forbidden).
- Keep v0 contract compiler-agnostic:
  - no parser/pipeline assumptions are embedded into required v0 fields.
  - no schema-evolution hooks are introduced in this arc (`compat_mode`, unknown-module fallback, permissive compatibility parsing are forbidden).

### Locks

- Contract-surface lock is frozen:
  - v38 introduces commitments IR v0 contract only.
- Schema-authority lock is frozen:
  - authoritative schema file is `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`,
  - `spec/adeu_commitments_ir.schema.json` is a deterministic mirror.
  - authority direction is one-way: package schema is source-of-truth; `spec/` mirror must never be manually edited as authority.
- Schema naming/version lock is frozen:
  - v38 commitments contract id is `adeu_commitments_ir@0.1`,
  - authoritative file naming follows repo style `*.v0_1.json`,
  - mirror naming follows repo style `spec/*.schema.json`.
- Union discriminator lock is frozen:
  - module union discriminator key is `module_kind` and is required for every union member.
  - discriminated-union dispatch must be strict `Literal`-key binding per member; fallback duck-typing or left-to-right coercion is forbidden.
- Strictness lock is frozen:
  - unknown fields in commitments IR models fail closed.
- Reason-code namespace lock is frozen:
  - commitments IR reason codes in this arc must follow namespace format `ASC-CIR-[0-9]{4}`.
- Canonicalization lock is frozen:
  - schema export/output canonicalization remains deterministic and profile-consistent with frozen repo baseline.
  - schema export writer format for this arc is frozen to existing repo schema-export profile:
    - `json.dumps(schema, indent=2, sort_keys=True) + "\\n"` written as UTF-8 bytes,
    - compact hash-profile serialization (`separators=(',', ':')`) is non-authoritative for schema-export file bytes in this arc.
  - environment-local absolute path material in exported schema payloads is forbidden.
- No-runtime-mutation lock is frozen:
  - v38 may not modify runtime endpoint behavior/policy semantics.
- No-schema-evolution-hook lock is frozen:
  - v38 may not introduce `compat_mode` flags, `unknown_module_kind` acceptance, or fallback compatibility parsing behavior.
- No-metrics-expansion lock is frozen:
  - v38 may not introduce stop-gate metric-key changes.

### Acceptance

- Commitments IR package is present with typed v0 model contract and deterministic schema export.
- Authoritative (`*.v0_1.json`) and mirror (`*.schema.json`) schemas are byte-parity aligned.
- No regression of v36/v37 continuity guards.

## M2) Commitments IR Determinism/Parity Guard Suite (`V32-A`)

### Goal

Prove commitments IR contract/bootstrap behavior is deterministic, fail-closed, and regression-resistant.

### Scope

- Add/adjust deterministic tests/guards for:
  - schema export determinism (repeat export yields byte-identical output),
  - authoritative/mirror parity assertions,
  - strict discriminated-union rejection assertions:
    - payloads with recognized `module_kind` but mismatched member fields must fail closed without fallback coercion,
  - v0 model strictness assertions (`extra="forbid"` fail-closed),
  - stable schema/version label assertions,
  - deterministic ordering in exported schema artifacts,
  - absolute-path leakage assertions:
    - exported schema payload/bytes must not include repo-root or environment-local absolute paths,
  - generated-schema cleanliness assertion:
    - guard reruns export entrypoint and fails closed if authoritative/mirror generated files differ from committed bytes.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v38 tests/guards may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v37 continuity metrics remain at required values.
- Required-export-determinism lock is frozen:
  - v38 guards fail closed if export reruns drift by bytes.
- Required-mirror-parity lock is frozen:
  - v38 guards fail closed on authoritative/mirror schema mismatch.
- Generated-schema cleanliness lock is frozen:
  - v38 guards fail closed when schema regeneration yields non-committed deltas for `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json` or `spec/adeu_commitments_ir.schema.json`.
- No-absolute-path-leakage lock is frozen:
  - v38 guards fail closed if exported schema content includes environment-local absolute path material.
- Strict-model lock is frozen:
  - v38 guards fail closed when unknown fields are silently accepted.
- Strict-polymorphic-binding lock is frozen:
  - v38 guards fail closed if discriminated union resolution accepts invalid member payload via non-`Literal` fallback behavior.
- Continuity-preservation lock is frozen:
  - v38 guards fail closed if v36/v37 continuity suites regress.
- Deterministic-guard-output lock is frozen:
  - guard outputs are deterministic and machine-checkable under fixed inputs.
- CI lane continuity lock is frozen:
  - in-scope v38 commitments guards must run in default Python CI lane,
  - workflow/job renaming is allowed only if required guard coverage remains equivalent and explicit in CI config.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required export determinism and mirror parity assertions are green.
- Commitments IR strictness behavior is fail-closed and test-covered.
- v36/v37 continuity guard suites remain green under v38 scope.

## Stop-Gate Impact (v38)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v38 closeout must include runtime-observability comparison row against v37 baseline.
- v38 closeout must include commitments schema parity-hash evidence block:
  - block schema is docs-only `v32a_schema_export_parity_evidence@1`,
  - required keys are:
    - `schema`
    - `authoritative_schema_path`
    - `mirror_schema_path`
    - `authoritative_sha256`
    - `mirror_sha256`
    - `byte_equal`
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
  - v38 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS38.md` inside a machine-checkable JSON block.
- Runtime-observability interpretation lock is frozen:
  - v38 runtime-observability comparison row is required evidence and is informational-only for this arc,
  - no new pass/fail threshold is introduced in this arc on elapsed timing deltas.

## Error/Exit Policy (v38)

- No new URM error-code family is introduced in this arc.
- Commitments IR reason-code registry in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V32-A commitments IR v0 package and deterministic schema export`
2. `tests: add v38 commitments schema determinism and mirror parity guard suite`

## Intermediate Preconditions (for v38 start)

1. v37 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v37 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS37.md`
3. Existing schema-export authority pattern remains available at v38 start:
   - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
4. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
5. Existing v31g persistence continuity lint remains enabled:
   - `apps/api/scripts/lint_v31g_persistence_release.py`
6. No additional `L2` boundary release beyond v37 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `M1` and `M2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic commitments IR contract bootstrap (`V32-A`) is closed and test-covered.
- v38 closeout evidence includes runtime-observability comparison row against v37 baseline.
- v36 governance and v37 persistence continuity remain green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
