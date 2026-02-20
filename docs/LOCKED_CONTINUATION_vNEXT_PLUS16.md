# Locked Continuation vNext+16 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS15.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock implemented on `main`; closeout evidence is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md`.

Decision basis:

- `vNext+15` (`C1`-`C4`) merged on `main` with green CI and closeout `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` recommends `vNext+16 = Path 9 thin slice (9a)`.
- `vNext+15` established deterministic depth/reporting artifacts suitable for additive integrity checks.
- This arc is reserved for formal integrity hardening only:
  - deterministic dangling-reference checks first
  - deterministic dependency-cycle policy checks second
  - deterministic minimal deontic conflict checks third
  - manifest-driven closeout metrics and stop-gate fourth

Closeout note (February 20, 2026 UTC):

- `D1`-`D4` merged on `main` with green CI.
- v16 deterministic thresholds are satisfied (`artifact_dangling_reference_determinism_pct`, `artifact_cycle_policy_determinism_pct`, `artifact_deontic_conflict_determinism_pct` all `100.0`).
- deterministic transfer-report evidence is published in `docs/INTEGRITY_TRANSFER_REPORT_vNEXT_PLUS16.md`.

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md` remain authoritative for policy/proof/explain/runtime/provider-parity/core-ir depth semantics.
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
- `adeu_core_ir@0.1`, `adeu_lane_projection@0.1`, `adeu_lane_report@0.1`, and `adeu_projection_alignment@0.1` contracts remain frozen and unchanged in this arc.
- Provider-parity continuity lock is frozen:
  - `vNext+14` provider matrix/manifest semantics remain unchanged in this arc.
  - this arc does not expand proposer provider surface sets.
- Depth-reporting continuity lock is frozen:
  - `vNext+15` depth/reporting outputs remain additive and authoritative in their existing scope.
  - this arc adds integrity diagnostics over persisted artifacts only; it does not rewrite core-ir or depth artifacts.

## Arc Scope (Draft Lock)

This arc proposes Path 9 thin slice only:

1. `D1` Deterministic dangling-reference diagnostics
2. `D2` Deterministic dependency-cycle policy diagnostics
3. `D3` Deterministic minimal deontic conflict diagnostics (evidence-first)
4. `D4` Manifest-driven coverage accountability + stop-gate closeout for `vNext+16 -> vNext+17`

## D1) Deterministic Dangling-Reference Diagnostics

### Goal

Detect unresolved structural references deterministically across frozen persisted integrity graph artifacts.

### Scope

- Compute deterministic dangling-reference diagnostics from persisted fixture artifacts only.
- Freeze deterministic issue taxonomy and ordering semantics.
- Keep diagnostics additive and non-semantic.
- D1 operates as defense-in-depth diagnostics:
  - diagnostics may run on raw fixture payloads before strict `adeu_core_ir@0.1` model-validation rejection paths.
  - this enables deterministic issue capture for intentionally malformed fixture payloads without changing canonical artifact validation behavior.

### Locks

- Diagnostic schema lock is frozen:
  - `schema = "adeu_integrity_dangling_reference@0.1"`
  - required fields:
    - `source_text_hash`
    - `summary`
    - `issues` (deterministically ordered)
  - `summary` shape is frozen:
    - `total_issues`
    - `missing_node_reference`
    - `missing_edge_endpoint`
  - each issue entry includes:
    - `kind`
    - `subject_id`
    - `related_id` (optional in payload; normalized as `""` for deterministic ordering)
    - optional additive `details`
- Input authority lock is frozen:
  - diagnostics consume persisted fixtures/artifacts only.
  - no live provider dependency in deterministic acceptance paths.
- Issue taxonomy lock is frozen:
  - deterministic issue kinds are exactly:
    - `missing_node_reference`
    - `missing_edge_endpoint`
  - deferred (out-of-scope for this arc):
    - artifact-reference integrity beyond structural node/edge reference checks.
- Deterministic ordering lock is frozen:
  - issue ordering key is `(kind, subject_id, related_id)`.
  - missing `related_id` is normalized as `""` for deterministic ordering.
- Issue-identity semantics lock is frozen:
  - `missing_node_reference`:
    - `subject_id = "edge:<type>:<from>-><to>"`
    - `related_id = "<missing_node_id>"`
  - `missing_edge_endpoint`:
    - `subject_id = "edge:<type>:<from>-><to>"`
    - `related_id = "endpoint:from"` or `related_id = "endpoint:to"` for missing source/target endpoint respectively.
  - missing endpoint interpolation lock:
    - when `type` is missing/null in payload interpolation, `subject_id` uses deterministic placeholder `_MISSING_` for the type component.
    - when `from` or `to` is missing/null in payload interpolation, `subject_id` uses deterministic placeholder `_MISSING_` for that endpoint component.
- Summary consistency lock is frozen:
  - `summary.total_issues == len(issues)`.
  - per-kind summary counts equal deterministic counts over `issues.kind`.
- Scope boundary lock is frozen:
  - checks target structural reference integrity only.
  - diagnostics may not infer or rewrite semantic claims.
- Non-authoritative lock is frozen:
  - dangling-reference diagnostics are evidence artifacts and do not mutate canonical artifacts in this arc.
  - canonical `adeu_core_ir@0.1` contract validation behavior remains unchanged and fail-closed.

### Acceptance

- Locked fixtures produce schema-valid dangling-reference diagnostics.
- Identical fixture inputs replay to byte-identical diagnostics.
- At least one locked D1 fixture is a deterministic malformed-payload case that yields non-zero diagnostics through the D1 diagnostic path.

## D2) Deterministic Dependency-Cycle Policy Diagnostics

### Goal

Compute deterministic dependency-cycle policy diagnostics over persisted integrity graphs.

### Scope

- Build deterministic dependency-graph diagnostics from persisted fixtures.
- Freeze cycle canonicalization, taxonomy, and deterministic ordering.
- Keep outputs additive and evidence-oriented in this arc.

### Locks

- Diagnostic schema lock is frozen:
  - `schema = "adeu_integrity_cycle_policy@0.1"`
  - required fields:
    - `source_text_hash`
    - `summary`
    - `cycles` (deterministically ordered)
  - `summary` shape is frozen:
    - `total_cycles`
    - `self_cycle`
    - `multi_node_cycle`
  - each cycle entry includes:
    - `kind`
    - `cycle_signature`
    - `node_ids` (canonical order; first node is not repeated at end)
- Cycle taxonomy lock is frozen:
  - deterministic cycle kinds are exactly:
    - `self_cycle`
    - `multi_node_cycle`
- Dependency-graph scope lock is frozen:
  - cycle analysis node set is exactly `E`-layer nodes.
  - cycle analysis edge set is exactly edges with `type == "depends_on"`.
  - all other edge types are excluded from D2 cycle detection in this arc.
  - under the existing edge typing contract, this constrains cycle sources to `E.Claim`; this arc does not expand dependency typing.
- Cycle canonicalization lock is frozen:
  - cycle node-id paths are normalized to deterministic canonical rotation before hashing/ordering.
  - canonical cycle is the lexicographically smallest node-id sequence among all rotations of the directed cycle path.
  - cycle list ordering is lexicographic on canonical cycle signatures.
- Cycle-signature semantics lock is frozen:
  - `cycle_signature = "cycle:" + "->".join(node_ids)` where `node_ids` are canonicalized by the cycle canonicalization lock.
- Cycle dedup lock is frozen:
  - emit at most one cycle entry per `cycle_signature`.
  - duplicate detections of the same canonical signature are collapsed deterministically before summary counts.
- Diagnostic volume-bound lock is frozen:
  - maximum emitted `cycles` entries per fixture is `1000`.
  - cycle diagnostics must short-circuit once candidate cycle count exceeds the cap and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Summary consistency lock is frozen:
  - `summary.total_cycles == len(cycles)`.
  - per-kind summary counts equal deterministic counts over `cycles.kind`.
- Policy-semantics lock is frozen:
  - cycle diagnostics encode policy evidence only for this arc.
  - cycle presence does not mutate canonical artifacts.
  - `self_cycle` is treated as deterministic policy-evidence output (not automatic artifact mutation or solver policy change).
- Input boundary lock is frozen:
  - deterministic cycle diagnostics are derived from persisted fixture artifacts only.

### Acceptance

- Locked fixtures produce schema-valid deterministic cycle diagnostics.
- Identical fixture inputs replay to byte-identical cycle diagnostics.

## D3) Deterministic Minimal Deontic Conflict Diagnostics (Evidence-First)

### Goal

Add deterministic, minimal deontic conflict diagnostics as additive evidence without changing solver semantics.

### Scope

- Compute deterministic conflict diagnostics over persisted deontic artifacts in fixtures.
- Freeze minimal conflict rule boundary for this arc.
- Keep diagnostics evidence-first and non-gating for canonical artifact generation.

### Locks

- Diagnostic schema lock is frozen:
  - `schema = "adeu_integrity_deontic_conflict@0.1"`
  - required fields:
    - `source_text_hash`
    - `summary`
    - `conflicts` (deterministically ordered)
  - `summary` shape is frozen:
    - `total_conflicts`
    - `deontic_conflict`
  - each conflict entry includes:
    - `kind`
    - `primary_id`
    - `related_id` (optional in payload; normalized as `""` for deterministic ordering)
    - optional additive `details`
- Minimal conflict-rule lock is frozen:
  - this arc evaluates only minimal direct conflicts under shared normalized condition context.
  - no modal hierarchy expansion or conflict-resolution rewriting is allowed.
- Conflict matching-rule lock is frozen:
  - a D3 conflict candidate is a pair of distinct `D`-node records where:
    - both have non-empty normalized target text
    - normalized target text is equal
    - normalized condition text is equal (`None`/missing condition normalizes to `""`)
    - modality pair is exactly `{obligatory, forbidden}` (unordered pair)
  - modality pairs involving `permitted` are deferred in this arc.
- Normalization lock is frozen for D3 matching:
  - normalized text for target/condition is computed deterministically as:
    - Unicode NFC normalization
    - trim leading/trailing whitespace
    - collapse internal whitespace runs to a single ASCII space
    - lowercase ASCII transformation on codepoints `A-Z` only (non-ASCII codepoints unchanged)
    - normalized condition aliases `"always"` and `"none"` map to `""`.
- Conflict resolution-boundary lock is frozen:
  - `priority` is preserved as optional evidence metadata only and is not used to suppress/resolve conflicts in this arc.
  - `excepts`-edge semantics are deferred and do not suppress D3 minimal conflict outputs in this arc.
- Conflict taxonomy lock is frozen:
  - deterministic conflict kind set is exactly:
    - `deontic_conflict`
- Deterministic ordering lock is frozen:
  - conflict ordering key is `(kind, primary_id, related_id)`.
  - missing `related_id` is normalized as `""` for deterministic ordering.
- Conflict-identity semantics lock is frozen:
  - `primary_id` and `related_id` are canonical `D`-node ids from persisted fixture artifacts.
  - deterministic pair orientation is frozen:
    - `primary_id` is lexicographically smaller id
    - `related_id` is lexicographically larger id
  - each unordered node pair is emitted at most once.
- Diagnostic volume-bound lock is frozen:
  - maximum emitted `conflicts` entries per fixture is `1000`.
  - conflict diagnostics must short-circuit once candidate pair count exceeds the cap and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Summary consistency lock is frozen:
  - `summary.total_conflicts == len(conflicts)`.
  - `summary.deontic_conflict` equals deterministic count over `conflicts.kind == "deontic_conflict"`.
- Evidence-first lock is frozen:
  - deontic conflict diagnostics are non-authoritative evidence for this arc.
  - diagnostics may not mutate canonical solver or projection outputs.

### Acceptance

- Locked fixtures produce schema-valid deterministic deontic conflict diagnostics.
- Identical fixture inputs replay to byte-identical deontic diagnostics.

## D4) Coverage Accountability + Stop-Gate Metrics + Integrity Closeout

### Goal

Make integrity coverage measurable and reproducible, and add deterministic closeout metrics for `vNext+16 -> vNext+17`.

### Scope

- Add manifest-driven fixture coverage accounting for D1/D2/D3 surfaces.
- Add deterministic transfer-report evidence for v16 integrity outputs.
- Extend additive `stop_gate_metrics@1` with v16 integrity closeout keys.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus16_manifest.json`
  - schema:
    - `stop_gate.vnext_plus16_manifest@1`
- Surface enumeration completeness lock is frozen:
  - the frozen v16 integrity `surface_id` set is exactly:
    - `adeu.integrity.dangling_reference`
    - `adeu.integrity.cycle_policy`
    - `adeu.integrity.deontic_conflict`
  - manifest fixture `surface_id` values must be members of this frozen set only.
  - surface drift/unknown `surface_id` is fixture-invalid and fails closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Manifest shape continuity lock is frozen:
  - manifest follows existing stop-gate list-style fixture pattern used in prior arcs.
  - required metric fixture lists are frozen:
    - `dangling_reference_fixtures`
    - `cycle_policy_fixtures`
    - `deontic_conflict_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs (for example `fixture_id`, `surface_id`, `runs`/artifact refs).
- Run-reference key lock is frozen:
  - required deterministic run keys are:
    - `dangling_reference_fixtures[].runs[].dangling_reference_path`
    - `cycle_policy_fixtures[].runs[].cycle_policy_path`
    - `deontic_conflict_fixtures[].runs[].deontic_conflict_path`
  - missing required run keys are fixture-invalid and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Replay-run indexing lock is frozen:
  - deterministic replay run identity is `(fixture_id, surface_id, run_index)` where `run_index` is in `1..replay_count`.
  - replay run identities are used for deterministic run-level evidence references and traceability only (not as metric denominator units).
- Coverage validity lock is frozen:
  - each declared integrity surface must map to at least one fixture id.
- Non-empty diagnostic evidence lock is frozen:
  - each metric fixture list must contain at least one fixture that yields non-zero diagnostics for that list's diagnostic family.
  - all-zero diagnostic inventories are fixture-invalid and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Transfer report lock is frozen:
  - output path:
    - `docs/INTEGRITY_TRANSFER_REPORT_vNEXT_PLUS16.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "integrity_transfer_report.vnext_plus16@1"`
    - `vnext_plus16_manifest_hash`
    - `coverage_summary`
    - `dangling_reference_summary`
    - `cycle_policy_summary`
    - `deontic_conflict_summary`
    - `replay_summary`
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_dangling_reference_determinism_pct`
  - `artifact_cycle_policy_determinism_pct`
  - `artifact_deontic_conflict_determinism_pct`
- Determinism metric computation lock is frozen:
  - canonical hash per fixture/output artifact
  - replay exactly `N=3` times per fixture
  - fixture passes only when all replay hashes match
  - `pct = 100 * passed / total`
- Metric denominator lock is frozen:
  - fixture selection is defined by:
    - `apps/api/fixtures/stop_gate/vnext_plus16_manifest.json`
  - denominator units are frozen per metric:
    - dangling-reference, cycle-policy, and deontic-conflict metrics are each computed over fixture units from the corresponding manifest fixture list.
  - `total` for each metric equals the number of fixtures in that metric's frozen fixture list.
  - `passed` for each metric equals the number of fixtures whose run entries are valid and whose replay hashes are all identical across the frozen `replay_count`.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus16_manifest_hash`.
  - mismatch fails closed with `URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH`.
- Replay boundary lock is frozen:
  - closeout metrics are computed from persisted fixtures/artifacts only.
  - no live provider calls are permitted in deterministic stop-gate acceptance paths.
- Deterministic runtime enforcement lock is frozen:
  - stop-gate metric builder entrypoints and integrity transfer-report builders must enforce `TZ=UTC` and `LC_ALL=C` via shared runtime helper before artifact loading/hashing.
- Threshold lock is frozen for `vNext+16 -> vNext+17`:
  - `artifact_dangling_reference_determinism_pct == 100.0`
  - `artifact_cycle_policy_determinism_pct == 100.0`
  - `artifact_deontic_conflict_determinism_pct == 100.0`

### Acceptance

- Integrity coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+16` thresholds.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_INTEGRITY_*` additions in this arc are frozen:
  - `URM_ADEU_INTEGRITY_DANGLING_REFERENCE_INVALID`
  - `URM_ADEU_INTEGRITY_CYCLE_POLICY_INVALID`
  - `URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_INVALID`
  - `URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_INTEGRITY_FIXTURE_INVALID`
  - `URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH`
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v16 integrity codes are additive and must not remove prior legacy error identifiers where already exposed.

## Commit Plan (Small Green Commits)

1. `integrity: add deterministic dangling-reference diagnostics contract and validators`
2. `integrity: add deterministic dependency-cycle policy diagnostics`
3. `integrity: add deterministic minimal deontic conflict diagnostics (evidence-first)`
4. `metrics: extend stop-gate with vnext_plus16 integrity manifest-driven keys and transfer report`
5. `runtime: enforce deterministic env helper in stop-gate/report entrypoints`
6. `tests: add deterministic integrity replay fixtures for closeout`

## Intermediate Stage Preconditions And Outputs (Draft)

Before implementation PR1 for `vNext+16`, confirm v15 preconditions are frozen/merged and prepare v16 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS15.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` (precondition post-`vNext+15` baseline refresh; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus16_manifest.json`
4. draft transfer-report schema/renderer for `integrity_transfer_report.vnext_plus16@1`
5. deterministic env helper hook-up for stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
6. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `D1`-`D4` merged with green CI.
- `artifact_dangling_reference_determinism_pct == 100.0` on locked fixtures.
- `artifact_cycle_policy_determinism_pct == 100.0` on locked fixtures.
- `artifact_deontic_conflict_determinism_pct == 100.0` on locked fixtures.
- `vNext+16 -> vNext+17` frozen thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing stop-gate tracked `vNext+6` through `vNext+15` metrics remain at threshold.
- `vNext+12` through `vNext+15` closeout evidence remains green and reproducible.
