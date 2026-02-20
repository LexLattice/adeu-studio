# Locked Continuation vNext+15 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS14.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+14` (`B1`-`B4`) merged on `main` with green CI and closeout `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` recommends `vNext+15 = Path 7 follow-on thin slice (7b)`.
- This arc is reserved for additive core-ir depth/reporting hardening only:
  - deterministic lane reporting contract first
  - deterministic projection/extraction alignment diagnostics second
  - fixture coverage accountability third
  - stop-gate closeout fourth

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` remain authoritative for policy/proof/explain/runtime/core-ir/provider-parity semantics.
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
  - text-hash fields hash UTF-8 strings after component-defined normalization only.
  - `source_text_hash`-derived artifacts in this arc inherit normalized-text semantics from the existing deterministic source normalization path.
  - manifest hash computation removes embedded `manifest_hash` before canonical hashing.
- Deterministic execution environment lock is frozen:
  - deterministic mode runs with `TZ=UTC` and `LC_ALL=C`.
  - filesystem/glob/path iteration inputs are lexicographically sorted before deterministic aggregation or hashing.
  - deterministic acceptance entrypoints in this arc must set/enforce these env values explicitly (runner/harness), not assume host defaults.
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- `adeu_core_ir@0.1` and `adeu.sbr.v0_1` contracts from `vNext+13` remain frozen and unchanged in this arc.
- Provider-parity continuity lock is frozen:
  - `vNext+14` provider matrix/manifest semantics remain unchanged in this arc.
  - this arc does not expand proposer provider surface sets.

## Arc Scope (Draft Lock)

This arc proposes Path 7 follow-on thin slice only:

1. `C1` Deterministic lane reporting artifact contract
2. `C2` Projection/extraction alignment diagnostics (evidence-only)
3. `C3` Deterministic depth coverage accountability + transfer-report refresh
4. `C4` Stop-gate additive metrics and deterministic closeout for `vNext+15 -> vNext+16`

## C1) Deterministic Lane Reporting Contract

### Goal

Expose deterministic lane reporting artifacts for O/E/D/U core-ir consumption without changing solver contracts.

### Scope

- Add a deterministic lane-report artifact generated from persisted `adeu_core_ir@0.1` inputs.
- Freeze artifact schema and ordering semantics.
- Keep lane reporting strictly additive to existing `adeu_lane_projection@0.1` outputs.
- Define lane report as a summary artifact for reporting/metrics:
  - `adeu_lane_projection@0.1` remains the edge-level structural projection artifact.
  - `adeu_lane_report@0.1` is a deterministic summary view and does not replace projection artifacts in this arc.

### Locks

- Lane-report schema lock is frozen:
  - `schema = "adeu_lane_report@0.1"`
  - required fields:
    - `source_text_hash`
    - `lane_nodes` (`O|E|D|U` -> sorted node ids)
    - `lane_edge_counts` (`O|E|D|U` scoped deterministic counts keyed in canonical lane order)
    - optional additive metadata only.
- Lane-report schema location lock is frozen:
  - authoritative generated schema path:
    - `packages/adeu_core_ir/schema/adeu_lane_report.v0_1.json`
  - optional mirror copy under `spec/` is non-authoritative convenience only.
- Input authority lock is frozen:
  - lane-report generation input is persisted `adeu_core_ir@0.1` only.
  - no live provider dependency in deterministic acceptance paths.
- Deterministic ordering lock is frozen:
  - node-id arrays are lexicographically sorted.
  - lane-key emission order is frozen as `["O", "E", "D", "U"]`.
  - map keys are canonical and stable.
- Edge-count semantics lock is frozen:
  - `lane_edge_counts` are computed from canonical persisted core-ir `edges` only.
  - each edge is counted exactly once by source-node lane.
  - cross-lane edges are counted in the source lane only (no duplicate counting on target lane).
  - edges with missing/unmapped source-node lane are fixture-invalid and fail closed with `URM_ADEU_DEPTH_FIXTURE_INVALID`; they are never silently dropped or bucketed.
- Non-semantic lock is frozen:
  - lane-report generation may not rewrite or infer new semantic claims.

### Acceptance

- Locked lane-report fixtures validate against `adeu_lane_report@0.1`.
- Identical fixture inputs replay to byte-identical lane-report outputs.

## C2) Projection/Extraction Alignment Diagnostics (Evidence-Only)

### Goal

Add deterministic diagnostics for projection/extraction alignment drift without mutating authoritative projected semantics.

### Scope

- Compute deterministic alignment diagnostics between projected and extraction-side candidates.
- Freeze deterministic issue classification and ordering.
- Keep diagnostics additive and non-authoritative.
- Inputs are explicitly dual-path:
  - projection-side: deterministic projection output for the fixture source under the projection-first pipeline.
  - extraction-side: deterministic extraction-side candidate output for the same normalized source text fixture.
  - projection-side parse failures fail closed with `URM_ADEU_DEPTH_PROJECTION_UNPARSEABLE`.

### Locks

- Projection authority lock is frozen:
  - projected semantics remain authoritative in this arc.
  - diagnostics may not alter canonical projected artifacts.
- Diagnostic schema lock is frozen:
  - `schema = "adeu_projection_alignment@0.1"`
  - required fields:
    - `source_text_hash`
    - `summary`
    - `issues` (deterministically ordered)
- Alignment schema location lock is frozen:
  - authoritative generated schema path:
    - `packages/adeu_core_ir/schema/adeu_projection_alignment.v0_1.json`
  - optional mirror copy under `spec/` is non-authoritative convenience only.
- Issue taxonomy lock is frozen:
  - deterministic issue kinds are exactly:
    - `missing_in_projection`
    - `missing_in_extraction`
    - `kind_mismatch`
    - `edge_type_mismatch`
  - `kind_mismatch` uses strict canonical kind-string equality (no subtype relaxation in this arc).
  - deferred (out-of-scope for this arc):
    - `label_text_mismatch`
    - `span_mismatch`
    - `multiplicity_mismatch`
    - `score_mismatch`
- Deterministic ordering lock is frozen:
  - issue ordering key is `(kind, subject_id, related_id)`.
  - missing `related_id` is normalized as `""` for deterministic ordering.
- Issue-identity semantics lock is frozen:
  - `missing_in_projection`:
    - `subject_id` is extraction-side canonical comparison id
    - `related_id = ""`
  - `missing_in_extraction`:
    - `subject_id` is projection-side canonical comparison id
    - `related_id = ""`
  - `kind_mismatch`:
    - `subject_id` is projection-side canonical comparison id
    - `related_id` is extraction-side canonical comparison id
  - `edge_type_mismatch`:
    - `subject_id` is projection-side canonical edge comparison id
    - `related_id` is extraction-side canonical edge comparison id
- Drift-code semantics lock is frozen:
  - `URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_DRIFT` applies only to deterministic replay drift (same locked fixture input yielding different diagnostic artifact hashes).
  - semantic alignment issue presence (`missing_in_projection`, `missing_in_extraction`, `kind_mismatch`, `edge_type_mismatch`) does not trigger `*_DRIFT`.
- Diagnostic hash volatility-exclusion lock is frozen:
  - deterministic alignment diagnostic hash acceptance excludes volatile runner-derived fields (for example timestamps, host-local absolute paths).
  - absolute filesystem paths are forbidden in deterministic diagnostic artifacts for locked fixtures.
- Non-gating semantics lock is frozen:
  - alignment diagnostics are evidence-only for this arc and do not gate canonical artifact generation.

### Acceptance

- Locked fixtures produce stable deterministic diagnostics with byte-identical replay.
- Diagnostics never mutate projected canonical artifacts.

## C3) Coverage Accountability + Transfer Report Refresh

### Goal

Make core-ir depth coverage measurable and reproducible for v15 scope.

### Scope

- Add manifest-driven coverage accounting for lane-report + alignment surfaces.
- Add a deterministic v15 transfer report with machine-checkable evidence references.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus15_manifest.json`
  - schema:
    - `stop_gate.vnext_plus15_manifest@1`
- Manifest shape continuity lock is frozen:
  - manifest follows existing stop-gate list-style fixture pattern used in prior arcs.
  - required metric fixture lists are frozen:
    - `lane_report_replay_fixtures`
    - `projection_alignment_fixtures`
    - `depth_report_replay_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs (for example `fixture_id`, `surface_id`, `runs`/artifact refs).
- Depth-report fixture semantics lock is frozen:
  - `depth_report_replay_fixtures` are replay units for the combined depth-reporting surface (lane report + alignment diagnostics together).
  - no standalone `adeu_depth_report@0.1` schema is introduced in this arc.
- Fixture compactness lock is frozen:
  - fixture inventory remains thin-slice and coverage-justified; avoid unconstrained Cartesian fixture expansion.
- Replay-unit lock is frozen:
  - deterministic replay unit is `(fixture_id, surface_id, run_index)` where `run_index` is in `1..replay_count`.
  - metric denominators and totals derive from explicit replay units only.
- Coverage validity lock is frozen:
  - each declared depth/reporting surface must map to at least one fixture id.
- Non-empty depth evidence lock is frozen:
  - each accepted fixture in `lane_report_replay_fixtures` and `depth_report_replay_fixtures` must produce non-empty lane-node evidence (`sum(len(lane_nodes[lane])) > 0`).
  - empty deterministic outputs are fixture-invalid and fail closed with `URM_ADEU_DEPTH_FIXTURE_INVALID`.
- Transfer report lock is frozen:
  - output path:
    - `docs/CORE_IR_DEPTH_TRANSFER_REPORT_vNEXT_PLUS15.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "core_ir_depth_transfer_report.vnext_plus15@1"`
    - `vnext_plus15_manifest_hash`
    - `coverage_summary`
    - `alignment_summary`
    - `replay_summary`

### Acceptance

- Coverage accounting is reproducible across reruns for identical fixture inputs.
- Transfer report references deterministic evidence artifacts only.

## C4) Stop-Gate Metrics + Core-IR Depth Closeout

### Goal

Add reproducible core-ir depth closeout metrics to decide if `vNext+16` may start.

### Scope

- Extend additive `stop_gate_metrics@1` fields for v15 closeout.
- Add deterministic fixture-based metric computation and report rendering.

### Locks

- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `adeu_lane_report_replay_determinism_pct`
  - `adeu_projection_alignment_determinism_pct`
  - `adeu_depth_report_replay_determinism_pct`
- Determinism metric computation lock is frozen:
  - canonical hash per fixture/output artifact
  - replay exactly `N=3` times per fixture
  - fixture passes only when all replay hashes match
  - `pct = 100 * passed / total`
- Metric denominator lock is frozen:
  - fixture selection is defined by:
    - `apps/api/fixtures/stop_gate/vnext_plus15_manifest.json`
  - denominator units are frozen per metric:
    - lane report and depth replay metrics are computed over replay units defined by the C3 replay-unit lock.
    - alignment determinism metrics are computed over alignment diagnostic replay units defined by the C3 replay-unit lock.
  - `total` for each metric equals the number of frozen replay units derived from that metric's fixture list.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus15_manifest_hash`.
  - mismatch fails closed with `URM_ADEU_DEPTH_MANIFEST_HASH_MISMATCH`.
- Replay boundary lock is frozen:
  - closeout metrics are computed from persisted fixtures/artifacts only.
  - no live provider calls are permitted in deterministic stop-gate acceptance paths.
- Threshold lock is frozen for `vNext+15 -> vNext+16`:
  - `adeu_lane_report_replay_determinism_pct == 100.0`
  - `adeu_projection_alignment_determinism_pct == 100.0`
  - `adeu_depth_report_replay_determinism_pct == 100.0`

### Acceptance

- v15 depth/reporting metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+15` thresholds.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_DEPTH_*` additions in this arc are frozen:
  - `URM_ADEU_DEPTH_LANE_REPORT_INVALID`
  - `URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_INVALID`
  - `URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_DEPTH_PROJECTION_UNPARSEABLE`
  - `URM_ADEU_DEPTH_FIXTURE_INVALID`
  - `URM_ADEU_DEPTH_MANIFEST_HASH_MISMATCH`
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v15 depth codes are additive and must not remove prior legacy error identifiers where already exposed.

## Commit Plan (Small Green Commits)

1. `core-ir-depth: add deterministic lane-report artifact contract and validators`
2. `core-ir-depth: add projection/extraction alignment diagnostics with deterministic ordering`
3. `core-ir-depth: add vnext_plus15 fixture coverage accounting and transfer-report refresh`
4. `metrics: extend stop-gate with vnext_plus15 core-ir-depth manifest-driven keys`
5. `tests: add deterministic lane-report/alignment replay fixtures for closeout`

## Intermediate Stage Preconditions And Outputs (Draft)

Before implementation PR1 for `vNext+15`, confirm v14 preconditions are frozen/merged and prepare v15 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS14.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` (precondition post-`vNext+14` baseline refresh; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus15_manifest.json`
4. draft transfer-report schema/renderer for `core_ir_depth_transfer_report.vnext_plus15@1`
5. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS15.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `C1`-`C4` merged with green CI.
- `adeu_lane_report_replay_determinism_pct == 100.0` on locked fixtures.
- `adeu_projection_alignment_determinism_pct == 100.0` on locked fixtures.
- `adeu_depth_report_replay_determinism_pct == 100.0` on locked fixtures.
- `vNext+15 -> vNext+16` frozen thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing stop-gate tracked `vNext+6` through `vNext+14` metrics remain at threshold.
- `vNext+12`, `vNext+13`, and `vNext+14` closeout evidence remains green and reproducible.
