# Locked Continuation vNext+25 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS24.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS24.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+24` (`X1`-`X4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS24.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` post-`vNext+24` sequencing leaves the planned expansion path as `S3b` with `S9` as parity fallback trigger path.
- `vNext+24` completed extraction-fidelity closure and explicitly deferred `S3b` activation to a separate lock.
- This arc is reserved for deterministic, explicitly bounded core-ir proposer activation only:
  - explicit provider-continuity release and surface-matrix extension first
  - deterministic core-ir proposer surface activation second
  - additive stop-gate determinism/parity metrics for proposer outputs third
  - explicit non-enforcement, no-mutation, and trust-lane continuity fourth

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior in this arc.
- No solver semantic contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS24.md` remain authoritative for baseline semantics.
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
- Endpoint idempotency continuity lock is frozen:
  - new `/urm/...` endpoints introduced in this arc must be idempotent via `client_request_id`.
  - idempotency identity key is composite:
    - `surface_id`
    - `client_request_id`
    - `provider`
  - same `client_request_id` with identical semantic payload must replay byte-identically.
  - same `client_request_id` with a different `provider` for the same `surface_id` is request-invalid and fails closed.
  - same `client_request_id` with different semantic payload must fail closed deterministically.
- Stop-gate metrics remain additive on `stop_gate_metrics@1`.
- New schema-family introduction lock is frozen:
  - this arc adds exactly one new proposer artifact schema family (additive-only):
    - `adeu_core_ir_proposal@0.1`
  - endpoint envelope schemas in this arc:
    - `adeu_core_ir_proposer_request@0.1`
    - `adeu_core_ir_proposer_response@0.1`
    are API contract schemas and do not expand prior persisted artifact families.
- Provider continuity release lock is frozen for this arc:
  - v24 no-provider-expansion continuity is explicitly released for Path `S3b` only.
  - release scope is limited to one new proposer surface and does not authorize broad provider-surface expansion.
- S9 trigger-boundary lock is frozen:
  - provider parity fallback (`S9`) remains trigger-based and preempts this expansion arc when parity thresholds regress.
  - trigger baseline continuity must be evaluated against v24 closeout metrics before v25 implementation PR1.
- S9 trigger gate lock is frozen (hard precondition for v25 implementation PR1):
  - required v24 baseline metrics and thresholds:
    - `provider_route_contract_parity_pct == 100.0`
    - `codex_candidate_contract_valid_pct == 100.0`
    - `provider_parity_replay_determinism_pct == 100.0`
  - if any required trigger metric is below threshold in the latest v24 closeout evidence:
    - v25 implementation is blocked
    - execute `S9` parity-remediation lock and closeout first.

## Arc Scope (Draft Lock)

This arc proposes Path `S3b` thin slice only:

1. `Y1` Provider continuity release + deterministic provider matrix extension for core-ir proposer surface
2. `Y2` Deterministic core-ir proposer surface activation with explicit provider boundaries
3. `Y3` Additive stop-gate determinism/parity metrics for v25 proposer payload stability
4. `Y4` Explicit non-enforcement, no-mutation, and trust-lane continuity for `vNext+25 -> vNext+26`

Out-of-scope note:

- Path `S9` remediation is not proactively activated by this arc.
- Broad provider matrix/surface expansion beyond the locked v25 thin slice is out-of-scope.
- This arc does not switch default runtime semantics from v3.
- This arc does not introduce automatic policy execution/auto-remediation.
- DB-backed proposer persistence migrations/new SQL tables are not in this arc.
- Mandatory frontend build-system expansion is not in this arc.
- Provider cost/SLA telemetry capture (`remote_latency_ms`, token counters) in proposer response envelopes is out-of-scope in this arc.

## Y1) Provider Continuity Release + Matrix Extension

### Goal

Release provider continuity in a controlled way to permit exactly one core-ir proposer surface expansion.

### Scope

- Extend frozen provider matrix semantics with one additive proposer `surface_id` for core-ir.
- Keep existing provider taxonomies and fail-closed behavior from v14 authoritative.

### Locks

- Provider taxonomy lock remains frozen:
  - supported providers remain exactly `mock`, `openai`, `codex`.
- v25 matrix authority lock is frozen:
  - authoritative path:
    - `apps/api/fixtures/provider_parity/vnext_plus25_provider_matrix.json`
  - schema lock:
    - `provider_parity.vnext_plus25_matrix@1`
- Surface-set extension lock is frozen:
  - v25 extends the current proposer matrix by exactly one additive `surface_id`:
    - `adeu_core_ir.propose`
  - all existing proposer `surface_id` entries remain present and unchanged unless explicitly marked additive for compatibility.
- Fail-closed provider lock remains frozen:
  - unsupported provider/surface combinations fail deterministically before provider dispatch.
- Mock-provider strictness lock is frozen:
  - mock proposer outputs used for parity fixtures must be deterministic functions of:
    - `surface_id`
    - `source_text_hash`
    - request mode fields included in the fixture contract
  - static one-payload mock responses that ignore source identity are fixture-invalid for v25 parity coverage.

### Acceptance

- v25 provider matrix validates with deterministic ordering and no ambiguity.
- Existing proposer surfaces retain parity behavior from v14-v24 baselines.

## Y2) Deterministic Core-IR Proposer Surface Activation

### Goal

Activate a bounded core-ir proposer surface with explicit provider boundaries and deterministic fixture-backed acceptance.

### Scope

- Add core-ir proposer surface wiring keyed by `surface_id = "adeu_core_ir.propose"`.
- Ensure proposer responses include core-ir payload plus required lane/integrity evidence linkage fields.
- Keep proposer nondeterminism isolated behind persisted-artifact determinism boundaries.

### Locks

- Endpoint-set lock is frozen:
  - `POST /urm/core-ir/propose`
  - this arc does not add additional proposer endpoints.
- Request-envelope lock is frozen:
  - `schema = "adeu_core_ir_proposer_request@0.1"`
  - route request payload must include:
    - `client_request_id`
    - `provider`
    - `source_text`
  - optional fields are additive-only and must not alter idempotency identity semantics.
- Response-envelope lock is frozen:
  - `schema = "adeu_core_ir_proposer_response@0.1"`
  - response must preserve v14 proposer envelope continuity fields:
    - `provider`
    - `candidates`
    - `proposer_log`
  - response additionally includes:
    - `surface_id = "adeu_core_ir.propose"`
    - `proposal_packet` (`adeu_core_ir_proposal@0.1`)
- Deterministic acceptance boundary lock is frozen:
  - replay/stop-gate acceptance paths use persisted provider fixtures only.
  - live provider calls are forbidden in deterministic acceptance.
- Contract continuity lock is frozen:
  - v14 provider envelope compatibility requirements remain additive and authoritative.
- Proposer packet schema lock is frozen:
  - `schema = "adeu_core_ir_proposal@0.1"`
  - required top-level fields:
    - `client_request_id`
    - `surface_id`
    - `provider`
    - `core_ir_artifact_ref`
    - `lane_artifact_refs`
    - `integrity_artifact_refs`
    - `not_produced_reasons`
    - `summary`
- Proposer packet summary lock is frozen:
  - `summary` required fields:
    - `candidate_count`
    - `assertion_node_count`
    - `relation_edge_count`
    - `logic_tree_max_depth`
    - `lane_ref_count`
    - `integrity_ref_count`
- Evidence linkage lock is frozen:
  - proposer packet must include deterministic evidence refs for produced core-ir + lane + integrity artifacts.
  - when an artifact family is not produced, packet must include deterministic `not_produced_reasons` entries for that family.
- Not-produced-reason lock is frozen:
  - each entry in `not_produced_reasons` includes:
    - `artifact_family`
    - `reason_code`
    - optional `message`
  - entries are sorted lexicographically by:
    - `artifact_family`
    - `reason_code`
- Proposer packet deterministic ordering lock is frozen:
  - `lane_artifact_refs` and `integrity_artifact_refs` are lexicographically sorted.
  - absent optional fields are omitted (no implicit null insertion).
- Schema-export convention lock is frozen:
  - `adeu_core_ir_proposal@0.1` must be exported as authoritative schema JSON.
  - authoritative path:
    - `packages/adeu_core_ir/schema/adeu_core_ir_proposal.v0_1.json`
  - mirror path:
    - `spec/adeu_core_ir_proposal.schema.json`
  - export wiring extends:
    - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- Normalization continuity lock is frozen:
  - codex parse/shape normalization continuity from v14 remains authoritative in this arc.

### Acceptance

- Core-ir proposer fixture replay is deterministic for locked fixtures.
- Existing proposer/provider parity contracts do not regress.

## Y3) Stop-Gate Determinism Metrics for v25 Proposer Surfaces

### Goal

Make v25 proposer determinism and parity measurable with additive stop-gate metrics.

### Scope

- Add v25 manifest-driven fixture accountability for proposer outputs.
- Extend additive `stop_gate_metrics@1` with v25 proposer keys.
- Preserve v14-v24 continuity metrics and thresholds.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus25_manifest.json`
  - schema:
    - `stop_gate.vnext_plus25_manifest@1`
  - required:
    - `replay_count == 3`
- Parity semantics lock is frozen:
  - parity in this arc is deterministic contract parity across providers, not semantic identity of generated candidates.
  - parity comparisons use a normalized contract fingerprint projection; raw candidate free-text equivalence is out-of-scope.
- Contract fingerprint projection lock is frozen:
  - normalized contract parity fingerprint input is canonical JSON over:
    - `surface_id`
    - `candidate_count`
    - `assertion_node_count`
    - `relation_edge_count`
    - `logic_tree_max_depth`
    - `lane_ref_count`
    - `integrity_ref_count`
    - sorted `not_produced_reasons` pairs (`artifact_family`, `reason_code`)
  - parity fingerprint excludes provider-volatile or free-text fields, including:
    - `provider`
    - `raw_prompt`
    - `raw_response`
    - prompt/response hashes
    - narrative/free-text candidate prose.
  - parity hash is `sha256` over canonical JSON bytes of this projection.
- Surface enumeration completeness lock is frozen:
  - frozen v25 proposer `surface_id` set is exactly:
    - `adeu_core_ir.propose`
  - manifest fixture `surface_id` values must be members of this frozen set only.
- Manifest shape lock is frozen:
  - required fixture lists are:
    - `core_ir_proposer_contract_valid_fixtures`
    - `core_ir_proposer_provider_parity_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
  - each fixture entry must declare:
    - `surface_id`
    - `runs`
  - manifest-shape violations are fixture-invalid and fail closed with:
    - `URM_ADEU_CORE_IR_PROPOSER_FIXTURE_INVALID`
- Provider-coverage lock is frozen:
  - each fixture must include exactly one run for each provider:
    - `mock`
    - `openai`
    - `codex`
  - partial provider coverage is fixture-invalid in this arc.
  - provider-coverage violations fail closed with:
    - `URM_ADEU_CORE_IR_PROPOSER_FIXTURE_INVALID`
- Run-reference key lock is frozen:
  - required run keys are:
    - `core_ir_proposer_contract_valid_fixtures[].runs[].provider`
    - `core_ir_proposer_contract_valid_fixtures[].runs[].core_ir_proposer_request_path`
    - `core_ir_proposer_contract_valid_fixtures[].runs[].core_ir_proposer_response_path`
    - `core_ir_proposer_contract_valid_fixtures[].runs[].core_ir_proposal_packet_path`
    - `core_ir_proposer_provider_parity_fixtures[].runs[].provider`
    - `core_ir_proposer_provider_parity_fixtures[].runs[].core_ir_proposer_request_path`
    - `core_ir_proposer_provider_parity_fixtures[].runs[].core_ir_proposer_response_path`
    - `core_ir_proposer_provider_parity_fixtures[].runs[].core_ir_proposal_packet_path`
  - missing required run keys are fixture-invalid and fail closed with:
    - `URM_ADEU_CORE_IR_PROPOSER_FIXTURE_INVALID`
- Fixture-path semantics lock is frozen:
  - `*_path` inputs are captured deterministic JSON artifact payloads from v25 in-process harness, not ad hoc summaries.
  - captured payloads include full JSON body including top-level `schema` where applicable.
  - `core_ir_proposal_packet_path` captures `adeu_core_ir_proposal@0.1` payloads.
  - response headers are excluded from capture envelopes and determinism/parity hash inputs.
- Determinism/parity metric computation lock is frozen:
  - replay exactly `N=3` times per provider run.
  - provider-run replay passes only when all replay hashes match for that provider run.
  - `artifact_core_ir_proposer_contract_valid_pct` denominator is provider-run units from:
    - `core_ir_proposer_contract_valid_fixtures`
  - `artifact_core_ir_proposer_provider_parity_pct` denominator is fixture units from:
    - `core_ir_proposer_provider_parity_fixtures`
  - parity fixture passes only when:
    - every provider run in the fixture is replay-deterministic, and
    - normalized contract fingerprint hashes are equal across `mock|openai|codex`.
  - metric percentage computation remains:
    - `pct = 100 * passed / total`
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_core_ir_proposer_contract_valid_pct`
  - `artifact_core_ir_proposer_provider_parity_pct`
- Metric-key cardinality lock is frozen:
  - v25 adds exactly two proposer determinism/parity keys in this arc.
- Threshold lock is frozen for `vNext+25 -> vNext+26`:
  - `artifact_core_ir_proposer_contract_valid_pct == 100.0`
  - `artifact_core_ir_proposer_provider_parity_pct == 100.0`
  - v14-v24 continuity thresholds remain required and unchanged.
- Transfer report lock is frozen:
  - output path:
    - `docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "core_ir_proposer_transfer_report.vnext_plus25@1"`
    - `vnext_plus25_manifest_hash`
    - `provider_matrix_hash`
    - `coverage_summary`
    - `core_ir_proposer_contract_summary`
    - `core_ir_proposer_parity_summary`
    - `replay_summary`
  - `replay_summary.runtime_observability` required keys are:
    - `elapsed_ms`
    - `total_fixtures`
    - `total_replays`
    - `bytes_hashed_per_replay`
    - `bytes_hashed_total`
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus25_manifest_hash`.
  - mismatch fails closed.

### Acceptance

- Proposer coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+25` thresholds.

## Y4) Non-Enforcement, No-Mutation, and Trust-Lane Continuity

### Goal

Keep v25 proposer activation additive and bounded while preventing policy-execution drift.

### Scope

- Freeze continuity constraints for `vNext+25 -> vNext+26`.
- Preserve trust-lane taxonomy and default solver semantics.

### Locks

- Non-enforcement lock is frozen:
  - proposer outputs are candidate/evidence artifacts and may not trigger policy enforcement side effects in this arc.
- No-mutation lock is frozen:
  - v25 proposer paths must not mutate persisted artifacts outside explicitly declared proposer artifact boundaries.
- Proposer mutation-boundary lock is frozen:
  - runtime proposer endpoints in this arc are read-through with no canonical artifact writes.
  - allowed persisted writes in deterministic acceptance are limited to captured fixture artifacts for:
    - `apps/api/fixtures/stop_gate/vnext_plus25_manifest.json`
    - artifact JSON files referenced by that manifest
  - writes to canonical ADEU artifact families are out-of-scope for this arc.
- Guard lock is frozen:
  - deterministic tests must assert fail-closed behavior for disallowed policy/materialization entrypoints in guarded proposer acceptance paths.
- No-mutation verification lock is frozen:
  - deterministic no-mutation tests must compare pre/post snapshots over:
    - `apps/api/fixtures/provider_parity/vnext_plus25_provider_matrix.json`
    - `apps/api/fixtures/stop_gate/vnext_plus25_manifest.json`
    - all artifact JSON files referenced by that manifest
    - canonical persisted concept/core-ir/lane/integrity/cross-ir/normative-advice/trust/semantics-candidate fixture trees
  - snapshot comparison is hash-based over canonical file contents and must remain byte-identical for proposer read paths.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.

### Acceptance

- Tests prove guarded proposer acceptance paths do not invoke disallowed mutation/policy flows.
- Tests prove trust-lane continuity and non-enforcement boundaries remain intact.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common/provider-parity codes where applicable.
- New codes are deterministic, prefixed `URM_`, and additive-only.
- `URM_ADEU_CORE_IR_PROPOSER_*` additions in this arc are frozen:
  - `URM_ADEU_CORE_IR_PROPOSER_REQUEST_INVALID`
  - `URM_ADEU_CORE_IR_PROPOSER_ARTIFACT_NOT_FOUND`
  - `URM_ADEU_CORE_IR_PROPOSER_PAYLOAD_INVALID`
  - `URM_ADEU_CORE_IR_PROPOSER_PROVIDER_UNSUPPORTED`
  - `URM_ADEU_CORE_IR_PROPOSER_FIXTURE_INVALID`
  - `URM_ADEU_CORE_IR_PROPOSER_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_CORE_IR_PROPOSER_REQUEST_INVALID` for unsupported request modes and idempotency conflicts.
  - use `URM_ADEU_CORE_IR_PROPOSER_PROVIDER_UNSUPPORTED` for provider/surface unsupported combinations.
  - use `URM_ADEU_CORE_IR_PROPOSER_FIXTURE_INVALID` for manifest/run-key/provider-coverage violations.
  - use `URM_ADEU_CORE_IR_PROPOSER_PAYLOAD_INVALID` for emitted response/packet schema content failures.
  - use `URM_ADEU_CORE_IR_PROPOSER_ARTIFACT_NOT_FOUND` for persisted lookup misses in deterministic acceptance inputs.
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v25 proposer codes are additive and must not remove prior legacy error identifiers.

## Commit Plan (Small Green Commits)

1. `provider-parity: extend matrix with additive core-ir proposer surface for v25`
2. `runtime/api: add bounded core-ir proposer surface with deterministic fixture-backed acceptance`
3. `metrics: add vnext_plus25 manifest and additive proposer contract/parity keys`
4. `docs: add vnext_plus25 proposer transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus25 replay fixtures and continuity/guard assertions`

## Intermediate Stage Preconditions and Outputs (Draft)

Before implementation PR1 for `vNext+25`, confirm v24 preconditions are frozen/merged and prepare v25 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS24.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md` (precondition transfer baseline; frozen + merged)
3. initial provider matrix inventory for `apps/api/fixtures/provider_parity/vnext_plus25_provider_matrix.json`
4. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus25_manifest.json`
5. draft proposer fixture scaffold for locked core-ir proposer responses
6. draft transfer-report schema/renderer for `core_ir_proposer_transfer_report.vnext_plus25@1` at `docs/CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md`
7. deterministic env helper hook-up for v25 stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
8. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `Y1`-`Y4` merged with green CI.
- `artifact_core_ir_proposer_contract_valid_pct == 100.0` on locked fixtures.
- `artifact_core_ir_proposer_provider_parity_pct == 100.0` on locked fixtures.
- `vNext+25 -> vNext+26` frozen thresholds all pass.
- v14-v24 continuity metrics remain present and at threshold (`100.0` where applicable).
- v25 closeout evidence includes runtime-observability comparison rows against v24 canonical baseline.
- no solver semantics contract delta and no trust-lane regression introduced.
- S9 parity fallback trigger remains boundary-controlled and not silently absorbed by v25 expansion scope.
