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
- Stop-gate metrics remain additive on `stop_gate_metrics@1`.
- Provider continuity release lock is frozen for this arc:
  - v24 no-provider-expansion continuity is explicitly released for Path `S3b` only.
  - release scope is limited to one new proposer surface and does not authorize broad provider-surface expansion.
- S9 trigger-boundary lock is frozen:
  - provider parity fallback (`S9`) remains trigger-based and preempts this expansion arc when parity thresholds regress.
  - trigger baseline continuity must be evaluated against v24 closeout metrics before v25 implementation PR1.

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

- Deterministic acceptance boundary lock is frozen:
  - replay/stop-gate acceptance paths use persisted provider fixtures only.
  - live provider calls are forbidden in deterministic acceptance.
- Contract continuity lock is frozen:
  - v14 provider envelope compatibility requirements remain additive and authoritative.
- Evidence linkage lock is frozen:
  - proposer outputs must include deterministic evidence refs for produced core-ir + lane + integrity artifacts (or explicit deterministic not-produced reasons when applicable).
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
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_core_ir_proposer_contract_valid_pct`
  - `artifact_core_ir_proposer_replay_determinism_pct`
- Metric-key cardinality lock is frozen:
  - v25 adds exactly two proposer determinism/parity keys in this arc.
- Threshold lock is frozen for `vNext+25 -> vNext+26`:
  - `artifact_core_ir_proposer_contract_valid_pct == 100.0`
  - `artifact_core_ir_proposer_replay_determinism_pct == 100.0`
  - v14-v24 continuity thresholds remain required and unchanged.
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
- Guard lock is frozen:
  - deterministic tests must assert fail-closed behavior for disallowed policy/materialization entrypoints in guarded proposer acceptance paths.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.

### Acceptance

- Tests prove guarded proposer acceptance paths do not invoke disallowed mutation/policy flows.
- Tests prove trust-lane continuity and non-enforcement boundaries remain intact.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common/provider-parity codes where applicable.
- New codes are allowed only when needed, deterministic, and prefixed `URM_`.
- v25 additions (if needed) must be additive and may not remove prior legacy identifiers.

## Commit Plan (Small Green Commits)

1. `provider-parity: extend matrix with additive core-ir proposer surface for v25`
2. `runtime/api: add bounded core-ir proposer surface with deterministic fixture-backed acceptance`
3. `metrics: add vnext_plus25 manifest and additive proposer determinism/parity keys`
4. `docs: add vnext_plus25 proposer transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus25 replay fixtures and continuity/guard assertions`

## Intermediate Stage Preconditions and Outputs (Draft)

Before implementation PR1 for `vNext+25`, confirm v24 preconditions are frozen/merged and prepare v25 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS24.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md` (precondition transfer baseline; frozen + merged)
3. initial provider matrix inventory for `apps/api/fixtures/provider_parity/vnext_plus25_provider_matrix.json`
4. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus25_manifest.json`
5. draft proposer fixture scaffold for locked core-ir proposer responses
6. draft transfer-report schema/renderer for `core_ir_proposer_transfer_report.vnext_plus25@1`
7. deterministic env helper hook-up for v25 stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
8. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS25.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `Y1`-`Y4` merged with green CI.
- `artifact_core_ir_proposer_contract_valid_pct == 100.0` on locked fixtures.
- `artifact_core_ir_proposer_replay_determinism_pct == 100.0` on locked fixtures.
- `vNext+25 -> vNext+26` frozen thresholds all pass.
- v14-v24 continuity metrics remain present and at threshold (`100.0` where applicable).
- v25 closeout evidence includes runtime-observability comparison rows against v24 canonical baseline.
- no solver semantics contract delta and no trust-lane regression introduced.
- S9 parity fallback trigger remains boundary-controlled and not silently absorbed by v25 expansion scope.
