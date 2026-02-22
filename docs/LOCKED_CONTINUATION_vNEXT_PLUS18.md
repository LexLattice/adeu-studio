# Locked Continuation vNext+18 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS17.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+17` (`E1`-`E4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS17.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` default post-`vNext+17` ordering selects `vNext+18 = Path S5` (tooling consolidation + CI budget sustainability).
- `vNext+16` and `vNext+17` now expose repeated validation/report-builder patterns suitable for behavior-preserving consolidation.
- This arc is reserved for tooling hardening only:
  - deterministic shared validation-module extraction first
  - deterministic stop-gate/transfer-report consolidation second
  - deterministic CI budget observability and bounded optimization third
  - manifest-driven closeout metrics and stop-gate fourth

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md` remain authoritative for policy/proof/explain/runtime/provider-parity/core-ir/depth/integrity baseline semantics.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- Hidden randomness is forbidden in deterministic/replay mode:
  - UUID/random ids must be explicit input, deterministic derivation, or used only behind persisted-artifact determinism boundaries.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)
- Canonical hash/serialization lock is frozen:
  - deterministic artifact hashes use `sha256` over canonical JSON bytes.
  - canonical JSON for hashing follows existing runtime/API hashing helpers:
    - `sort_keys=True`
    - `separators=(",", ":")`
    - `ensure_ascii=False`
    - UTF-8 encoding
  - no pretty-print whitespace is included in hashed canonical payloads.
- Hash-input normalization lock is frozen:
  - manifest hash computation removes embedded `manifest_hash` before canonical hashing.
  - `manifest_hash` stripping must be performed by one shared runtime utility used by both baseline and consolidated paths; stripping order/stage may not diverge by caller.
- Deterministic execution environment lock is frozen:
  - deterministic mode runs with `TZ=UTC` and `LC_ALL=C`.
  - filesystem/glob/path iteration inputs are lexicographically sorted before deterministic aggregation or hashing.
  - deterministic acceptance entrypoints in this arc must set/enforce these env values explicitly (runner/harness), not assume host defaults.
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- `adeu_core_ir@0.1`, `adeu_lane_projection@0.1`, `adeu_lane_report@0.1`, `adeu_projection_alignment@0.1`, `adeu_integrity_dangling_reference@0.1`, `adeu_integrity_cycle_policy@0.1`, `adeu_integrity_deontic_conflict@0.1`, `adeu_integrity_reference_integrity_extended@0.1`, `adeu_integrity_cycle_policy_extended@0.1`, and `adeu_integrity_deontic_conflict_extended@0.1` contracts remain frozen and unchanged in this arc.
- Provider-parity continuity lock is frozen:
  - `vNext+14` provider matrix/manifest semantics remain unchanged in this arc.
  - this arc does not expand proposer provider surface sets.
- Integrity continuity lock from `vNext+16` + `vNext+17` is frozen:
  - v16/v17 integrity artifacts remain authoritative.
  - this arc may refactor validation/building internals only; it must not rewrite integrity artifact contracts or semantics.

## Arc Scope (Draft Lock)

This arc proposes Path S5 thin slice only:

1. `F1` Deterministic shared validation-module extraction (behavior-preserving)
2. `F2` Deterministic stop-gate/transfer-report consolidation (behavior-preserving)
3. `F3` Deterministic CI budget observability + bounded optimization
4. `F4` Manifest-driven tooling parity accountability + stop-gate closeout for `vNext+18 -> vNext+19`

Out-of-scope note:

- Path `S1` follow-on integrity diagnostics expansion is not in this arc.
- Path `S3a` product read-surface activation is not in this arc.
- Schema-family migration to unified `adeu_integrity@...` is not in this arc; only evaluation evidence is allowed.

## F1) Deterministic Shared Validation-Module Extraction

### Goal

Extract duplicated manifest/artifact validation logic into runtime-owned shared helpers without changing external behavior.

### Scope

- Consolidate duplicated validation flows currently mirrored across:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
  - `apps/api/src/adeu_api/integrity_transfer_report_vnext_plus16.py`
  - `apps/api/src/adeu_api/integrity_transfer_report_vnext_plus17.py`
- v17 shared-helper pattern is the canonical migration target for v16 transfer-report validation flow consolidation in this arc.
- canonical migration-target interpretation lock:
  - canonical target applies to code structure and helper topology only.
  - output semantics must remain v16-identical and v17-identical on their respective locked fixture sets.
- Keep contracts additive and behavior-preserving.
- Keep validation deterministic and replay-stable.

### Locks

- Shared-helper ownership lock is frozen:
  - extracted helpers are runtime-owned under `packages/urm_runtime/src/urm_runtime/`.
  - API-layer builders may import these helpers but must not fork equivalent logic again in this arc.
  - explicit extraction targets include duplicated helpers such as:
    - `_resolve_ref`
    - `_build_coverage_summary`
    - `_build_replay_summary`
- Behavior-parity lock is frozen:
  - for locked fixtures, normalized manifest payloads produced by consolidated helpers are canonical-hash identical to baseline behavior.
  - for locked invalid fixtures, error code domain and deterministic context fields remain equivalent for the same failure class.
  - deterministic error-context parity is evaluated over structured fields:
    - `code`
    - `surface_id` (when present)
    - `fixture_id` (when present)
    - `reason` (deterministic enum/code)
  - prose message text is non-authoritative for parity assertions.
- Ordering lock is frozen:
  - fixture ids, coverage entries, and normalized run refs remain lexicographically ordered exactly as before.
- Contract-continuity lock is frozen:
  - `stop_gate.vnext_plus16_manifest@1` and `stop_gate.vnext_plus17_manifest@1` shapes remain unchanged.
  - transfer-report schemas `integrity_transfer_report.vnext_plus16@1` and `integrity_transfer_report.vnext_plus17@1` remain unchanged.
- Non-authoritative refactor lock is frozen:
  - F1 changes implementation structure only; no semantic change to integrity judgments, metric thresholds, or artifact families.
- Legacy-path removal lock is frozen:
  - post-consolidation, API-layer transfer-report modules must not retain shadow copies of manifest normalization/validation helpers already extracted to runtime-owned shared helpers.
  - deterministic tests must assert shared-helper usage and prevent silent reintroduction of duplicated legacy helper paths.

### Acceptance

- Locked parity fixtures confirm byte-identical canonical outputs for consolidated validation flows.
- Invalid-fixture parity cases confirm deterministic error-code/context continuity.

## F2) Deterministic Stop-Gate And Transfer-Report Consolidation

### Goal

Reduce maintenance drift by consolidating repeated stop-gate and transfer-report builder patterns while preserving emitted outputs.

### Scope

- Consolidate repeated family-summary/report-builder code paths for v16/v17 integrity reporting.
- Consolidation boundary for this arc is limited to v16/v17 tooling paths; broad loader rewrites for v7-v15 are out-of-scope unless strictly required for behavior-preserving shared-helper adoption.
- Keep emitted report payloads deterministic and contract-compatible.
- Keep stop-gate metric semantics unchanged except additive v18 tooling keys.

### Locks

- Output-continuity lock is frozen:
  - v16/v17 transfer-report payload structures remain byte-identical for identical inputs (excluding explicitly non-hashed observability fields where allowed).
  - parity hash projection excludes `runtime_observability` only; no other fields are excluded from baseline-vs-candidate parity comparison.
  - existing v16/v17 stop-gate metric definitions remain unchanged.
- Parity-check lock is frozen:
  - consolidation adds deterministic baseline-vs-candidate parity checks over persisted artifacts only.
  - parity checks compare `sha256_canonical_json(load_json(path))` over parsed JSON objects (not raw file bytes and not pretty-printed formatting).
- Loader-parameterization lock is frozen:
  - per-arc manifest differences (surface ids, fixture-list keys, required run keys) must be represented as deterministic data configuration rather than duplicated ad hoc validation branches.
- CLI-manifest consistency lock is frozen:
  - canonical stop-gate CLI manifest-path argument support and runtime loader support must be aligned for active arcs in this repository (`vNext+15` through `vNext+18`) with no hidden hardcoded path divergence.
  - in this arc, required alignment scope is exactly `vNext+15`, `vNext+16`, `vNext+17`, and `vNext+18`.
  - earlier arc CLI/loader harmonization is out-of-scope unless needed for a concrete bugfix.
- Schema-evaluation lock is frozen:
  - this arc may emit a deterministic schema-consolidation assessment artifact.
  - schema-consolidation assessment is decision evidence only and may not replace v16/v17 schema families in this arc.
- Replay boundary lock is frozen:
  - no live provider calls are permitted in deterministic tooling parity acceptance paths.

### Acceptance

- Locked parity fixtures replay to byte-identical transfer-report and stop-gate outputs for baseline vs consolidated builders.
- Schema-consolidation assessment artifact is generated deterministically and marks migration as explicit follow-on work if not selected.

## F3) Deterministic CI Budget Observability + Bounded Optimization

### Goal

Bound closeout execution cost while preserving deterministic guarantees and gate coverage.

### Scope

- Keep deterministic runtime observability evidence machine-checkable and comparable across arcs.
- Add bounded optimization only where it does not alter metric semantics, fixture coverage, replay count, or hash outcomes.
- Freeze a CI runtime ceiling target for closeout tooling execution evidence.

### Locks

- Observability-shape lock is frozen:
  - closeout output includes machine-checkable `runtime_observability` with keys:
    - `total_fixtures`
    - `total_replays`
    - `elapsed_ms`
- Canonical closeout command-path lock is frozen:
  - CI budget ceiling measurement applies to the stop-gate closeout entrypoint:
    - `apps/api/scripts/build_stop_gate_metrics.py`
  - exact CLI args/options for the canonical closeout measurement path are frozen in:
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS18.md`
- Ceiling calibration-evidence lock is frozen:
  - before freeze, `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS18.md` must record baseline `elapsed_ms` from at least two consecutive `main` CI runs of the canonical closeout command path.
  - if the recorded max baseline exceeds `50%` of the frozen ceiling, the ceiling value must be explicitly re-evaluated and amended before freeze.
  - with current ceiling `120000`, this re-evaluation trigger is `> 60000`.
- Non-hash observability lock is frozen:
  - runtime observability evidence is excluded from canonical hash inputs for deterministic artifact parity.
- Budget metric model lock is frozen:
  - `artifact_stop_gate_ci_budget_within_ceiling_pct` is computed as a singleton closeout metric (`total = 1`).
  - singleton pass/fail is derived from canonical closeout output `runtime_observability.elapsed_ms`.
  - `ci_budget_fixtures` entries provide deterministic evidence references for this singleton measurement and do not define denominator units.
- Coverage-preservation lock is frozen:
  - optimization may not reduce fixture lists, replay count, or metric denominator definitions.
  - replay count remains frozen at `N=3` for v18 tooling parity fixtures.
- CI budget ceiling lock is frozen:
  - v18 closeout run must satisfy `runtime_observability.elapsed_ms <= 120000` in CI evidence for the locked closeout command path.
  - ceiling failures fail closed with deterministic tooling-budget error classification.
  - budget ceiling is an operational sustainability gate; ceiling breaches must not alter canonical artifact parity/hash outcomes.
- Budget-counter deferral lock is frozen:
  - deterministic computational-cost counters (for example step-count/operation-count alternatives to wall-clock gating) are deferred from this arc.
  - additive runtime-observability dimensions (for example memory or load-count telemetry) may be emitted as non-gating evidence only in this arc.
- Deterministic optimization lock is frozen:
  - any caching/batching introduced must be keyed only by deterministic artifact inputs.
  - hidden wall-clock/random behavior remains forbidden for gating logic.

### Acceptance

- Runtime observability is present, machine-checkable, and reproducible in shape across reruns.
- Locked closeout evidence satisfies the frozen CI budget ceiling without reducing deterministic coverage guarantees.

## F4) Tooling Parity Accountability + Stop-Gate Metrics + Closeout

### Goal

Make tooling-consolidation parity measurable and reproducible, and add deterministic closeout checks for `vNext+18 -> vNext+19`.

### Scope

- Add manifest-driven parity and budget accountability for F1/F2/F3.
- Extend additive `stop_gate_metrics@1` with v18 tooling keys.
- Emit deterministic tooling transfer report evidence for closeout.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus18_manifest.json`
  - schema:
    - `stop_gate.vnext_plus18_manifest@1`
  - required:
    - `replay_count == 3`
- Surface enumeration completeness lock is frozen:
  - the frozen v18 tooling `surface_id` set is exactly:
    - `adeu.tooling.validation_parity`
    - `adeu.tooling.transfer_report_parity`
    - `adeu.tooling.ci_budget`
  - manifest fixture `surface_id` values must be members of this frozen set only.
  - v18 surface boundary lock:
    - v18 manifest surfaces are tooling-only.
    - ADEU/core-ir/concepts/proposer surfaces are not allowed in v18 manifests.
- Manifest shape continuity lock is frozen:
  - required metric fixture lists are frozen:
    - `validation_parity_fixtures`
    - `transfer_report_parity_fixtures`
    - `ci_budget_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
  - `ci_budget_fixtures` is a singleton evidence list with exactly one fixture and exactly one run entry.
- Run-reference key lock is frozen:
  - required run keys are:
    - `validation_parity_fixtures[].runs[].baseline_path`
    - `validation_parity_fixtures[].runs[].candidate_path`
    - `transfer_report_parity_fixtures[].runs[].baseline_path`
    - `transfer_report_parity_fixtures[].runs[].candidate_path`
    - `ci_budget_fixtures[].runs[].report_path`
  - missing required run keys are fixture-invalid and fail closed.
- Parity computation lock is frozen:
  - validation/transfer parity fixtures pass only when canonical hash(`baseline_path`) equals canonical hash(`candidate_path`) for all replay runs.
  - for parity fixtures, `baseline_path` and `candidate_path` must reference like-for-like artifacts (same schema family and version); schema mismatch is fixture-invalid.
  - parity replay model is frozen:
    - `baseline_path` is treated as a fixed persisted reference.
    - only candidate generation is replayed `N=3`; each replay artifact hash must match the fixed baseline hash.
  - denominator units are fixture units; replay runs are evidence units.
- Budget computation lock is frozen:
  - budget pass/fail uses canonical closeout output `runtime_observability` only.
  - budget passes only when required runtime observability keys are present and `elapsed_ms <= 120000`.
  - budget metric denominator is singleton (`total = 1`) independent of parity fixture counts.
- Determinism metric computation lock is frozen:
  - replay exactly `N=3` times per parity fixture.
  - `pct = 100 * passed / total`.
- Transfer report lock is frozen:
  - output path:
    - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS18.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "tooling_transfer_report.vnext_plus18@1"`
    - `vnext_plus16_manifest_hash`
    - `vnext_plus17_manifest_hash`
    - `vnext_plus18_manifest_hash`
    - `validation_parity_summary`
    - `transfer_report_parity_summary`
    - `ci_budget_summary`
    - `replay_summary`
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_validation_consolidation_parity_pct`
  - `artifact_transfer_report_consolidation_parity_pct`
  - `artifact_stop_gate_ci_budget_within_ceiling_pct`
- Continuity-threshold lock is frozen:
  - v16 and v17 integrity thresholds remain required and unchanged in v18 closeout.
- Threshold lock is frozen for `vNext+18 -> vNext+19`:
  - `artifact_validation_consolidation_parity_pct == 100.0`
  - `artifact_transfer_report_consolidation_parity_pct == 100.0`
  - `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0`
  - canonical closeout command-path budget evidence must satisfy:
    - `runtime_observability.elapsed_ms <= 120000`
  - v16/v17 continuity thresholds remain required and unchanged.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus18_manifest_hash`.
  - mismatch fails closed.

### Acceptance

- Tooling parity accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+18` thresholds and budget checks.
- v18 closeout decision evidence includes explicit baseline-vs-current budget comparison rows for the canonical command path.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_TOOLING_*` additions in this arc are frozen:
  - `URM_ADEU_TOOLING_VALIDATION_PARITY_INVALID`
  - `URM_ADEU_TOOLING_TRANSFER_REPORT_PARITY_INVALID`
  - `URM_ADEU_TOOLING_CI_BUDGET_INVALID`
  - `URM_ADEU_TOOLING_FIXTURE_INVALID`
  - `URM_ADEU_TOOLING_PARITY_DRIFT`
  - `URM_ADEU_TOOLING_RUNTIME_BUDGET_EXCEEDED`
  - `URM_ADEU_TOOLING_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_TOOLING_FIXTURE_INVALID` for manifest/run-key/surface-id/cap violations.
  - use family-specific `*_INVALID` codes for emitted tooling artifact schema/content validation failures.
  - use `URM_ADEU_TOOLING_RUNTIME_BUDGET_EXCEEDED` only when observability evidence is present and exceeds the frozen ceiling.
  - `URM_ADEU_TOOLING_RUNTIME_BUDGET_EXCEEDED` is emitted only from canonical closeout command-path evaluation when output includes `runtime_observability` and `runtime_observability.elapsed_ms` exceeds the frozen ceiling.
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v18 tooling codes are additive and must not remove prior legacy error identifiers.

## Commit Plan (Small Green Commits)

1. `tooling: extract shared deterministic manifest and run-ref validation helpers`
2. `tooling: migrate vnext+16 and vnext+17 transfer-report builders to shared validation helpers`
3. `runtime: consolidate stop-gate tooling parity evaluators with behavior-preserving output parity checks`
4. `metrics: add vnext_plus18 tooling manifest and additive stop-gate parity/budget keys`
5. `runtime: enforce deterministic ci budget observability and frozen ceiling checks`
6. `tests/docs: add vnext_plus18 replay fixtures and tooling transfer report closeout artifacts`

## Intermediate Stage Preconditions And Outputs (Draft)

Before implementation PR1 for `vNext+18`, confirm v17 preconditions are frozen/merged and prepare v18 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS17.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` (precondition post-`vNext+17` baseline refresh; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus18_manifest.json`
4. draft tooling transfer-report schema/renderer for `tooling_transfer_report.vnext_plus18@1`
5. deterministic env helper hook-up for stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
6. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS18.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `F1`-`F4` merged with green CI.
- `artifact_validation_consolidation_parity_pct == 100.0` on locked fixtures.
- `artifact_transfer_report_consolidation_parity_pct == 100.0` on locked fixtures.
- `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0` on locked fixtures.
- `vNext+18 -> vNext+19` frozen thresholds all pass.
- v16 and v17 continuity metrics remain present and at threshold (`100.0`).
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing stop-gate tracked `vNext+6` through `vNext+17` metrics remain at threshold.
- `vNext+15` through `vNext+17` closeout evidence remains green and reproducible.
