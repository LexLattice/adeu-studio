# Locked Continuation vNext+26 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS25.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+25` (`Y1`-`Y4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` post-`vNext+25` sequencing leaves `vNext+26` as a pending lock freeze with `S9` as trigger-based fallback preemption path.
- `S9` hard-precondition metrics from the latest v25 closeout remain at threshold (`100.0`), so fallback preemption is not activated for this arc:
  - `provider_route_contract_parity_pct`
  - `codex_candidate_contract_valid_pct`
  - `provider_parity_replay_determinism_pct`
- This draft selects `vNext+26 = Path S5` follow-on thin slice (tooling consolidation + CI sustainability continuity), scoped to behavior-preserving deterministic tooling improvements only.
- This arc is reserved for deterministic tooling consolidation only:
  - deterministic stop-gate input-contract consolidation first
  - deterministic transfer-report builder consolidation second
  - additive stop-gate parity metrics for tooling consolidation third
  - explicit non-enforcement/no-mutation/provider-boundary continuity fourth

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior in this arc.
- No solver semantic contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS25.md` remain authoritative for baseline semantics.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- Hidden randomness is forbidden in deterministic/replay mode:
  - UUID/random ids must be explicit input, deterministic derivation, or used only behind persisted-artifact determinism boundaries.
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
- Deterministic execution environment lock is frozen:
  - deterministic mode runs with `TZ=UTC` and `LC_ALL=C`.
  - filesystem/glob/path iteration inputs are lexicographically sorted before deterministic aggregation or hashing.
  - deterministic acceptance entrypoints in this arc must set/enforce these env values explicitly (runner/harness), not assume host defaults.
- Stop-gate metrics remain additive on `stop_gate_metrics@1`.
- Provider continuity lock is frozen:
  - v25 proposer/provider surface set remains unchanged in this arc.
  - this arc does not add or reinterpret provider/surface matrix semantics.
- S9 trigger-boundary lock is frozen:
  - provider parity fallback (`S9`) remains trigger-based and preempts expansion work when parity thresholds regress.
- S9 trigger gate lock is frozen (hard precondition for v26 implementation PR1):
  - required baseline metrics and thresholds:
    - `provider_route_contract_parity_pct == 100.0`
    - `codex_candidate_contract_valid_pct == 100.0`
    - `provider_parity_replay_determinism_pct == 100.0`
  - if any required trigger metric is below threshold in the latest closeout evidence:
    - v26 implementation is blocked
    - execute `S9` parity-remediation lock and closeout first.
- S9 executable precondition lock is frozen:
  - v26 implementation PR1 must run deterministic trigger-check script:
    - `apps/api/scripts/check_s9_triggers.py`
  - trigger-check script input source is the closeout artifact referenced by:
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md`
  - script artifact resolution is frozen:
    - resolve the deterministic stop-gate metrics JSON path declared in the decision doc evidence section
      (`artifacts/stop_gate/metrics_v25_closeout.json`).
  - script payload/metric parsing rules are frozen:
    - loaded artifact must declare `schema = "stop_gate_metrics@1"` and include top-level `metrics` object.
    - required metric lookup paths are exactly:
      - `metrics.provider_route_contract_parity_pct`
      - `metrics.codex_candidate_contract_valid_pct`
      - `metrics.provider_parity_replay_determinism_pct`
    - each required metric value is parsed as decimal numeric (`int`, `float`, or numeric string) with no rounding.
    - threshold check is exact equality to `100.0`; missing/invalid/non-equal values fail closed.
  - script checks are fail-closed:
    - missing required metrics OR metric values below frozen thresholds block implementation start.

## Arc Scope (Draft Lock)

This arc proposes Path `S5` follow-on thin slice only:

1. `Z1` Deterministic stop-gate input-contract consolidation (behavior-preserving)
2. `Z2` Deterministic transfer-report builder consolidation for v24/v25 report families
3. `Z3` Additive stop-gate tooling parity metrics for `vNext+26 -> vNext+27`
4. `Z4` Explicit non-enforcement, no-mutation, and provider-boundary continuity for tooling paths

Out-of-scope note:

- Path `S9` remediation is not proactively activated by this arc.
- Provider matrix/surface-set expansion is not in this arc.
- This arc does not add new runtime `/urm/...` API endpoints.
- This arc does not switch default runtime semantics from v3.
- This arc does not introduce automatic policy execution/auto-remediation.
- DB-backed persistence migrations/new SQL tables are not in this arc.
- This arc does not modify proposer candidate-generation semantics or parity fingerprint semantics introduced in v25.
- CI trace-context injection into stop-gate/runtime-observability payloads is out-of-scope in this arc.

## Z1) Stop-Gate Input-Contract Consolidation

### Goal

Reduce call-site drift and maintainability risk by introducing a typed stop-gate input contract while preserving external behavior.

### Scope

- Introduce a typed request/input model for stop-gate metric construction in runtime tooling paths.
- Preserve current CLI/API call semantics through compatibility adapters.
- Keep stop-gate output shapes and metric computations unchanged except additive v26 keys frozen in this arc.

### Locks

- Behavior-parity lock is frozen:
  - for identical v14-v25 fixture inputs, `build_stop_gate_metrics` output remains canonical-hash identical under frozen parity projection rules.
  - Z1 parity comparison scope is evaluated via Z3 frozen projection:
    - `stop_gate_parity.v1`
- Baseline-capture authority lock is frozen:
  - baseline outputs for Z1 parity are precomputed persisted JSON captures checked into the repository before consolidation refactors are applied.
  - baseline captures are authoritative parity references and are not regenerated by consolidated v26 candidate code paths.
- Candidate-capture lock is frozen:
  - candidate outputs are generated by the consolidated v26 code path and compared against frozen baseline captures.
- Parity projection lock is frozen:
  - baseline-vs-candidate tooling parity compares canonical JSON with `runtime_observability` excluded from parity hash inputs.
  - no additional field exclusions are allowed in this arc.
- Compatibility lock is frozen:
  - existing call sites remain accepted (adapter path allowed), with deterministic mapping into the new typed input model.
- Compatibility-ingress permissiveness lock is frozen:
  - compatibility adapters must preserve legacy ingress tolerance for undeclared/extra fields on legacy call paths in this arc.
  - undeclared/extra fields are deterministically stripped/ignored at adapter ingress before typed-model mapping.
  - strict typed-model validation may apply only after adapter normalization and may not create new external request-invalid behavior for previously accepted legacy stop-gate invocations.
- Input-contract boundary lock is frozen:
  - typed stop-gate input contract in this arc is an internal runtime type only.
  - no new serialized artifact schema is introduced for this input model in v26.
  - no schema export/mirror wiring additions are allowed for the internal input model in this arc.
- Metric continuity lock is frozen:
  - existing metric keys and thresholds remain unchanged.

### Acceptance

- Deterministic parity tests prove baseline-vs-candidate stop-gate output continuity on locked fixture suites.

## Z2) Transfer-Report Builder Consolidation (v24/v25)

### Goal

Replace manual transfer-report maintenance for v24/v25 families only with deterministic builder-driven generation.

### Scope

- Add deterministic transfer-report builders for:
  - `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md`
  - `docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md`
- Keep existing schema IDs, key sets, and report contracts unchanged.
- Use persisted fixture/manifests only (no live provider calls) for deterministic acceptance.

### Locks

- Report-path lock is frozen:
  - output paths are exactly:
    - `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md`
    - `docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md`
- Report-data ownership lock is frozen:
  - v26 deterministic transfer-report data builders are runtime-owned under `packages/urm_runtime/src/urm_runtime/`.
  - runtime-owned builders emit machine-checkable JSON payload blocks only (no markdown template/styling rendering responsibilities in this arc).
  - API/docs/CLI layers may format markdown wrappers around runtime-emitted JSON payload blocks, but may not fork equivalent data-builder logic in this arc.
- Report-schema lock is frozen:
  - v24 report schema remains:
    - `extraction_fidelity_transfer_report.vnext_plus24@1`
  - v25 report schema remains:
    - `core_ir_proposer_transfer_report.vnext_plus25@1`
- Baseline report payload-source lock is frozen:
  - baseline payload for transfer-report parity is the checked-in machine-checkable JSON block (or frozen JSON capture extracted from it) at the locked report paths.
  - transfer-report parity baseline may not be derived by executing legacy builder code paths in this arc.
- Markdown JSON-block extractor lock is frozen:
  - for markdown report baselines, parity extraction must select the unique fenced JSON block whose top-level `schema` exactly matches the expected report schema:
    - `extraction_fidelity_transfer_report.vnext_plus24@1` for v24
    - `core_ir_proposer_transfer_report.vnext_plus25@1` for v25
  - missing/non-unique/wrong-schema JSON-block extraction is fixture-invalid and fails closed.
- Output-continuity lock is frozen:
  - generated report JSON blocks are canonical-hash identical to locked baseline payloads for identical fixture/manifests.
- Deterministic-source lock is frozen:
  - report builders must read only frozen manifests and captured fixture payloads declared in this repository.
  - undeclared input discovery and live recomputation paths are out-of-scope.
  - report builders may not depend on git metadata, wall-clock time, or environment-dependent host path values.

### Acceptance

- Builder-generated transfer-report payloads are deterministic and schema-valid.

## Z3) Stop-Gate Tooling Parity Metrics (v26)

### Goal

Make tooling consolidation determinism measurable and reproducible with additive stop-gate metrics.

### Scope

- Add v26 manifest-driven fixture accountability for tooling parity outputs.
- Extend additive `stop_gate_metrics@1` with v26 tooling keys.
- Preserve v14-v25 continuity metrics and thresholds.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`
  - schema:
    - `stop_gate.vnext_plus26_manifest@1`
  - required:
    - `replay_count == 3`
    - `parity_projection = "stop_gate_parity.v1"`
- Parity projection id lock is frozen:
  - v26 tooling parity projection identifier is exactly:
    - `stop_gate_parity.v1`
  - `stop_gate_parity.v1` excludes `runtime_observability` only from parity hash inputs.
  - no additional exclusions are allowed under this projection identifier in this arc.
- Host-path normalization lock is frozen:
  - parity-hash input payloads must not contain host-specific absolute paths.
  - path normalization applies only to this frozen field-key allowlist:
    - `baseline_path`
    - `candidate_path`
    - `report_path`
    - `manifest_path`
  - allowlist path fields are normalized to deterministic repository-relative paths before canonical hashing.
  - path separator normalization for allowlist fields is frozen to `/`.
  - no non-allowlist fields may be path-normalized in this arc.
- Surface enumeration completeness lock is frozen:
  - frozen v26 tooling `surface_id` set is exactly:
    - `adeu.tooling.stop_gate_input_model_parity`
    - `adeu.tooling.transfer_report_builder_parity`
  - manifest fixture `surface_id` values must be members of this frozen set only.
- Manifest shape lock is frozen:
  - required fixture lists are:
    - `stop_gate_input_model_parity_fixtures`
    - `transfer_report_builder_parity_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
- Run-reference key lock is frozen:
  - required run keys are:
    - `stop_gate_input_model_parity_fixtures[].runs[].baseline_path`
    - `stop_gate_input_model_parity_fixtures[].runs[].candidate_path`
    - `transfer_report_builder_parity_fixtures[].runs[].baseline_path`
    - `transfer_report_builder_parity_fixtures[].runs[].candidate_path`
  - missing required run keys are fixture-invalid and fail closed.
- Run-payload format lock is frozen:
  - `baseline_path` and `candidate_path` must reference canonical JSON payload captures (parsed JSON artifacts), not markdown bytes.
  - when source material is markdown (for example transfer reports), parity inputs must be extracted machine-checkable JSON payload blocks before hashing.
- Parity computation lock is frozen:
  - replay exactly `N=3` times per fixture.
  - fixture passes only when all replay hashes match and baseline/candidate canonical parity hash matches under frozen parity projection rules.
  - `pct = 100 * passed / total`.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_stop_gate_input_model_parity_pct`
  - `artifact_transfer_report_builder_parity_pct`
- Metric-key cardinality lock is frozen:
  - v26 adds exactly two tooling parity keys in this arc.
- Continuity-threshold lock is frozen:
  - v14-v25 thresholds remain required and unchanged in v26 closeout.
  - this includes:
    - `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0`
- Threshold lock is frozen for `vNext+26 -> vNext+27`:
  - `artifact_stop_gate_input_model_parity_pct == 100.0`
  - `artifact_transfer_report_builder_parity_pct == 100.0`
  - v14-v25 continuity thresholds remain required and unchanged.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus26_manifest_hash`.
  - mismatch fails closed.
- Transfer report lock is frozen:
  - output path:
    - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "tooling_transfer_report.vnext_plus26@1"`
    - `vnext_plus26_manifest_hash`
    - `coverage_summary`
    - `stop_gate_input_model_parity_summary`
    - `transfer_report_builder_parity_summary`
    - `s9_trigger_check_summary`
    - `replay_summary`
  - `replay_summary.runtime_observability` required keys are:
    - `elapsed_ms`
    - `total_fixtures`
    - `total_replays`
    - `bytes_hashed_per_replay`
    - `bytes_hashed_total`

### Acceptance

- Tooling parity accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+26` thresholds.

## Z4) Non-Enforcement, No-Mutation, and Provider-Boundary Continuity

### Goal

Keep tooling-consolidation activation additive and bounded while preventing drift into mutation, provider dispatch, or policy execution semantics.

### Scope

- Freeze continuity constraints for `vNext+26 -> vNext+27`.
- Preserve trust-lane taxonomy and default solver semantics.

### Locks

- Non-enforcement lock is frozen:
  - tooling/report outputs are evidence/diagnostic artifacts and may not trigger policy enforcement side effects in this arc.
- No-mutation lock is frozen:
  - tooling consolidation paths must not mutate canonical persisted ADEU artifacts.
- Allowed-write boundary lock is frozen:
  - deterministic acceptance writes are limited to exactly:
    - `artifacts/quality_dashboard_v26_closeout.json`
    - `artifacts/stop_gate/metrics_v26_closeout.json`
    - `artifacts/stop_gate/report_v26_closeout.md`
    - `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md`
    - `docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md`
    - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
  - for in-place updates to historical report docs (`v24`/`v25`), deterministic builders may modify only the locked machine-checkable fenced JSON block; surrounding markdown prose/structure remains unchanged in this arc.
  - writes outside explicitly declared output artifacts are out-of-scope for this arc.
- Provider-boundary lock is frozen:
  - deterministic acceptance/report generation paths may not invoke live provider clients.
- Guard lock is frozen:
  - deterministic tests must assert fail-closed behavior for disallowed provider/materialization/policy entrypoints in guarded tooling paths.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.

### Acceptance

- Tests prove guarded tooling acceptance paths do not invoke disallowed provider/materialization/policy flows.
- Tests prove no-mutation boundaries and trust-lane continuity remain intact.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common/tooling error codes where applicable.
- New codes are allowed only when needed, deterministic, and prefixed `URM_`.
- v26 expectation lock:
  - no new error-code family is planned; existing tooling/provider/common error-domain codes remain authoritative.
- v26 fixture-invalid reuse lock is frozen:
  - v26 parity manifest/run-key/JSON-block extractor violations reuse existing tooling fixture-invalid code:
    - `URM_ADEU_TOOLING_FIXTURE_INVALID`
- Compatibility lock is frozen:
  - existing endpoint/tooling error shapes/codes remain accepted for compatibility.
  - if a v26 addition becomes necessary, it must be additive-only and must not remove prior legacy identifiers.

## Commit Plan (Small Green Commits)

1. `runtime: add typed stop-gate input model with compatibility adapters`
2. `tooling: add deterministic builders for v24/v25 transfer-report families`
3. `metrics: add vnext_plus26 tooling parity manifest, additive metric keys, and deterministic S9 trigger-check script`
4. `docs: add vnext_plus26 tooling transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus26 parity fixtures and continuity/guard assertions`

## Intermediate Stage Preconditions and Outputs (Draft)

Before implementation PR1 for `vNext+26`, confirm v25 preconditions are frozen/merged and prepare v26 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md` (precondition transfer baseline; frozen + merged)
3. `docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md` (precondition transfer baseline; frozen + merged)
4. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus26_manifest.json`
5. baseline parity capture inventory for v24/v25 transfer-report payload families
6. draft tooling transfer-report schema/renderer for `tooling_transfer_report.vnext_plus26@1`
7. deterministic env helper hook-up for v26 stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
8. deterministic S9 trigger-check script scaffold at `apps/api/scripts/check_s9_triggers.py`
9. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `Z1`-`Z4` merged with green CI.
- `artifact_stop_gate_input_model_parity_pct == 100.0` on locked fixtures.
- `artifact_transfer_report_builder_parity_pct == 100.0` on locked fixtures.
- `vNext+26 -> vNext+27` frozen thresholds all pass.
- v14-v25 continuity metrics remain present and at threshold (`100.0` where applicable).
- v26 closeout evidence includes runtime-observability comparison rows against v25 canonical baseline.
- no solver semantics contract delta and no trust-lane regression introduced.
- provider-parity continuity lock remains unchanged (no proposer/provider surface expansion).
- S9 fallback trigger remains boundary-controlled and not silently absorbed by v26 tooling scope.
