# Locked Continuation vNext+19 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS18.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS18.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+18` (`F1`-`F4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS18.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` default post-`vNext+18` ordering selects `vNext+19 = Path S3a` (read-only product surface activation).
- `vNext+16` and `vNext+17` integrity families are stable and `vNext+18` tooling parity/budget controls are in place for additive product-surface exposure.
- This arc is reserved for read-only product-surface activation only:
  - read-only endpoints for persisted core-ir/lane/integrity artifacts first
  - deterministic render-payload builder (JSON-first, UI-agnostic) + transfer-report refresh second
  - additive stop-gate determinism metrics for read-surface payload stability third
  - explicit no-mutation and no-provider-expansion continuity fourth

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS18.md` remain authoritative for policy/proof/explain/runtime/provider-parity/core-ir/depth/integrity/tooling baseline semantics.
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
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- `adeu_core_ir@0.1`, `adeu_lane_projection@0.1`, `adeu_lane_report@0.1`, `adeu_projection_alignment@0.1`, `adeu_integrity_dangling_reference@0.1`, `adeu_integrity_cycle_policy@0.1`, `adeu_integrity_deontic_conflict@0.1`, `adeu_integrity_reference_integrity_extended@0.1`, `adeu_integrity_cycle_policy_extended@0.1`, and `adeu_integrity_deontic_conflict_extended@0.1` contracts remain frozen and unchanged in this arc.
- Provider-parity continuity lock is frozen:
  - `vNext+14` provider matrix/manifest semantics remain unchanged in this arc.
  - this arc does not expand proposer provider surface sets.
- Integrity continuity lock from `vNext+16` + `vNext+17` is frozen:
  - v16/v17 integrity artifacts remain authoritative.
  - this arc exposes read payloads over persisted artifacts only; it does not rewrite integrity artifacts in place.
- Tooling continuity lock from `vNext+18` is frozen:
  - v18 parity/budget semantics remain authoritative.
  - this arc may reuse v18 shared helpers but may not weaken v18 parity or budget gates.

## Arc Scope (Draft Lock)

This arc proposes Path S3a thin slice only:

1. `R1` Read-only endpoints for persisted core-ir/lane/integrity artifacts
2. `R2` Deterministic render-payload builder (JSON-first, UI-agnostic) + transfer-report refresh
3. `R3` Additive stop-gate determinism metrics for read-surface payload stability
4. `R4` Explicit no-mutation and no-provider-expansion lock continuity for `vNext+19 -> vNext+20`

Out-of-scope note:

- Path `S3b` (core-ir proposer activation) is not in this arc.
- Provider matrix/surface expansion is not in this arc.
- Solver semantics v4 work is not in this arc.
- DB-backed core-ir persistence migrations/new SQL tables are not in this arc.
- payload offloading via blob-store/pre-signed URLs is not in this arc.
- sparse fieldset/query-driven partial payload retrieval is not in this arc.
- Mandatory frontend build-system expansion is not in this arc; optional minimal web rendering is allowed only if it does not introduce a new frontend build-system dependency.

## R1) Read-Only Endpoints For Persisted Artifacts

### Goal

Expose deterministic, read-only API access for persisted core-ir/lane/integrity artifacts without introducing mutation or proposer semantics.

### Scope

- Add read-only endpoints over persisted artifact storage.
- Keep endpoint behavior deterministic for identical persisted inputs.
- Keep endpoint outputs schema-validated and non-authoritative.
- Use fixture-backed persisted artifact catalogs for this arc's read-surface endpoints.

### Locks

- Endpoint-set lock is frozen:
  - `GET /urm/core-ir/artifacts/{artifact_id}`
  - `GET /urm/core-ir/artifacts/{artifact_id}/lane-projection`
  - `GET /urm/core-ir/artifacts/{artifact_id}/lane-report`
  - `GET /urm/core-ir/artifacts/{artifact_id}/integrity/{family}`
- Persistence-model lock is frozen:
  - `R1` endpoints in this arc are fixture-backed over persisted JSON artifacts/capture catalogs.
  - no new SQL storage tables or schema migrations are introduced for core-ir/lane/integrity retrieval in v19.
  - DB-backed core-ir/lane/integrity retrieval is deferred to a later lock.
- Catalog index lock is frozen:
  - endpoint lookup catalog path:
    - `apps/api/fixtures/read_surface/vnext_plus19_catalog.json`
  - catalog schema:
    - `read_surface.vnext_plus19_catalog@1`
  - required entry fields:
    - `core_ir_artifact_id`
    - `source_text_hash`
    - optional `parent_links` map keyed by schema id for lane/integrity artifact refs
    - optional `created_at`
  - catalog entries are deterministically ordered lexicographically by `core_ir_artifact_id`.
  - `{artifact_id}` values accepted by `R1` routes must be members of this frozen catalog.
- Artifact-id authority and resolution-precedence lock is frozen:
  - `{artifact_id}` in `R1` routes denotes the persisted core-ir artifact id.
  - `GET /urm/core-ir/artifacts/{artifact_id}` resolves by exact core-ir artifact id only.
  - `GET /urm/core-ir/artifacts/{artifact_id}/lane-projection` and `.../lane-report` resolve by deterministic precedence:
    - explicit persisted parent-link to `{artifact_id}` when available,
    - fallback lookup by `(source_text_hash(from resolved core-ir), schema)` with unique-match requirement.
  - `GET /urm/core-ir/artifacts/{artifact_id}/integrity/{family}` resolves by deterministic precedence:
    - explicit persisted parent-link to `{artifact_id}` when available,
    - fallback lookup by `(source_text_hash(from resolved core-ir), family_schema)` with unique-match requirement.
  - fallback lookup search domain is frozen to exactly the artifact refs declared in `read_surface.vnext_plus19_catalog@1`; filesystem globs, DB scans, or undeclared directories are out-of-scope for resolution.
  - non-unique fallback matches are endpoint-invalid and fail closed with `URM_ADEU_READ_SURFACE_REQUEST_INVALID`.
- Integrity-family lock is frozen for `R1` endpoint routing:
  - allowed `family` values are exactly:
    - `dangling_reference`
    - `cycle_policy`
    - `deontic_conflict`
    - `reference_integrity_extended`
    - `cycle_policy_extended`
    - `deontic_conflict_extended`
  - family-to-schema mapping is frozen:
    - `dangling_reference -> adeu_integrity_dangling_reference@0.1`
    - `cycle_policy -> adeu_integrity_cycle_policy@0.1`
    - `deontic_conflict -> adeu_integrity_deontic_conflict@0.1`
    - `reference_integrity_extended -> adeu_integrity_reference_integrity_extended@0.1`
    - `cycle_policy_extended -> adeu_integrity_cycle_policy_extended@0.1`
    - `deontic_conflict_extended -> adeu_integrity_deontic_conflict_extended@0.1`
- Read-authority lock is frozen:
  - endpoints may read only persisted artifacts already present in storage.
  - endpoint handlers must not trigger regeneration/materialization/proposer calls on cache miss.
- Mutation lock is frozen:
  - endpoint handlers are read-only and may not write canonical ADEU artifacts.
  - missing artifact paths return deterministic not-found responses.
- Response-envelope lock is frozen:
  - all `R1` endpoint responses include:
    - `artifact_id`
    - `schema`
    - `created_at` (when available in persisted row)
    - artifact payload field (`core_ir`, `lane_projection`, `lane_report`, or `integrity_artifact`)
  - response envelopes are deterministically ordered and schema-validated.
  - `created_at` is read-only persisted metadata and may not be synthesized during response building.
  - read-surface determinism metric hashing excludes `created_at` fields from response-envelope projections in `R3`.
  - consumer-interpretation lock:
    - responses differing only in `created_at` are deterministically equivalent for `R3` metric hashing.
- Response-caching header lock is frozen:
  - `R1` successful responses must emit deterministic immutable-cache headers:
    - `Cache-Control: public, max-age=31536000, immutable`
  - caching headers are metadata and are excluded from read-surface payload determinism hashing.
- Trust-label continuity lock is frozen:
  - read endpoints may expose stored trust labels only.
  - read endpoints may not recompute or mutate trust-lane classifications.
- Error-shape lock is frozen:
  - endpoint error responses remain deterministic with frozen structured fields (`code`, `reason`, context ids).
  - prose message text is non-authoritative.

### Acceptance

- Locked `R1` fixtures return schema-valid read payloads for persisted artifacts.
- Identical persisted inputs replay to byte-identical endpoint payloads.
- Missing-artifact cases produce deterministic not-found error envelopes.

## R2) Deterministic Render-Payload Builder + Transfer Report Refresh

### Goal

Build deterministic render payloads from persisted artifacts for product consumption while remaining JSON-first and UI-agnostic.

### Scope

- Add deterministic render-payload builder fed only by persisted core-ir/lane/integrity artifacts.
- Keep builder independent of UI framework assumptions.
- Refresh transfer-report evidence for read-surface outputs.

### Locks

- Render schema lock is frozen:
  - `schema = "adeu_read_surface_payload@0.1"`
  - required top-level fields:
    - `artifact_id`
    - `source_text_hash`
    - `core_ir`
    - `lane_projection`
    - `lane_report`
    - `integrity`
    - `render_summary`
  - optional additive top-level field:
    - `correlations`
  - when present, `correlations` is deterministic derived evidence only and does not change canonical source artifacts.
- Schema-export convention lock is frozen:
  - `adeu_read_surface_payload@0.1` must be exported as authoritative schema JSON.
  - authoritative path:
    - `packages/adeu_core_ir/schema/adeu_read_surface_payload.v0_1.json`
  - mirror path:
    - `spec/adeu_read_surface_payload.schema.json`
  - export wiring extends:
    - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- Capture-schema classification lock is frozen:
  - `adeu_lane_read_surface_capture@0.1` and `adeu_integrity_read_surface_capture@0.1` are fixture-capture/testing schemas only.
  - capture schemas are not production endpoint artifact schemas and are not included in authoritative schema export wiring for product artifacts.
- Deterministic ordering lock is frozen for render payload sections:
  - `core_ir` field embeds the canonical stored core-ir payload verbatim; render builder may not reorder or recanonicalize this payload.
  - lane items ordered lexicographically by stable identity keys.
  - integrity family blocks ordered by frozen family name list from `R1`.
  - render payload integrity block includes exactly the frozen `R1` family list as stable keys (keys may not be omitted).
  - missing integrity-family artifacts are represented as deterministic placeholders with:
    - `artifact = null`
    - `missing_reason = "ARTIFACT_NOT_FOUND"`
  - `missing_reason` enum is frozen to the single value `ARTIFACT_NOT_FOUND` for v19 render payload placeholders.
  - optional `correlations` block semantics (when emitted):
    - keyed by canonical `node_id`
    - each node entry includes deterministic lists of linked lane/integrity references derived only from persisted payload ids/signatures
    - correlation lists are lexicographically ordered and may not introduce inferred claims beyond persisted evidence linkage.
  - integrity issues/conflicts/cycles preserve family-local canonical ordering rules from v16/v17 artifacts.
- Layout-contract lock is frozen:
  - payload grouping/section order is contract-relevant in this arc.
  - if optional minimal web rendering is added, it must consume this payload ordering directly and may not add nondeterministic client-side reordering heuristics.
- UI-optional lock is frozen:
  - minimal delivery form for `R2` is render-payload JSON + transfer-report evidence.
  - optional web rendering is allowed only if no new frontend build-system dependency is introduced.
  - implementing read-only views inside the existing `apps/web` toolchain is allowed in this arc.
- Transfer report lock is frozen:
  - output path:
    - `docs/READ_SURFACE_TRANSFER_REPORT_vNEXT_PLUS19.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "read_surface_transfer_report.vnext_plus19@1"`
    - `vnext_plus19_manifest_hash`
    - `coverage_summary`
    - `core_ir_read_surface_summary`
    - `lane_read_surface_summary`
    - `integrity_read_surface_summary`
    - `replay_summary`
- Replay boundary lock is frozen:
  - no live provider calls are permitted in deterministic render-payload acceptance paths.

### Acceptance

- Render payload fixtures replay to byte-identical outputs for identical persisted inputs.
- Transfer-report payload is deterministic and schema-valid.

## R3) Stop-Gate Determinism Metrics For Read-Surface Payloads

### Goal

Make read-surface determinism measurable and reproducible, with additive stop-gate metrics for `vNext+19 -> vNext+20`.

### Scope

- Add manifest-driven fixture accountability for read-surface outputs.
- Extend additive `stop_gate_metrics@1` with v19 read-surface keys.
- Preserve v16-v18 continuity metrics and thresholds.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus19_manifest.json`
  - schema:
    - `stop_gate.vnext_plus19_manifest@1`
  - required:
    - `replay_count == 3`
- Surface enumeration completeness lock is frozen:
  - frozen v19 read-surface `surface_id` set is exactly:
    - `adeu.read_surface.core_ir`
    - `adeu.read_surface.lane`
    - `adeu.read_surface.integrity`
  - manifest fixture `surface_id` values must be members of this frozen set only.
- Manifest shape lock is frozen:
  - required fixture lists are:
    - `core_ir_read_surface_fixtures`
    - `lane_read_surface_fixtures`
    - `integrity_read_surface_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
- Run-reference key lock is frozen:
  - required run keys are:
    - `core_ir_read_surface_fixtures[].runs[].core_ir_read_surface_path`
    - `lane_read_surface_fixtures[].runs[].lane_read_surface_path`
    - `integrity_read_surface_fixtures[].runs[].integrity_read_surface_path`
  - missing required run keys are fixture-invalid and fail closed.
- Fixture-path semantics lock is frozen:
  - `*_read_surface_path` inputs are captured HTTP response JSON bodies (or deterministic capture envelopes) from `R1` read endpoints, not ad hoc derived summaries.
  - `core_ir_read_surface_path` captures `GET /urm/core-ir/artifacts/{artifact_id}` response JSON.
  - `lane_read_surface_path` captures a deterministic envelope with schema `adeu_lane_read_surface_capture@0.1` containing both:
    - `GET /urm/core-ir/artifacts/{artifact_id}/lane-projection` response JSON
    - `GET /urm/core-ir/artifacts/{artifact_id}/lane-report` response JSON
  - `integrity_read_surface_path` captures a deterministic envelope with schema `adeu_integrity_read_surface_capture@0.1` containing frozen-family `R1` integrity responses in deterministic family order.
- Capture-harness lock is frozen:
  - captured response fixtures are generated by a deterministic in-process harness (no live-network dependency).
  - capture order is frozen to the endpoint order in `R1` and must be lexicographically stable by `artifact_id`.
  - capture envelope stores only:
    - parsed JSON response body (canonicalized on write),
    - endpoint path/method metadata required for traceability.
  - response headers are not stored in capture envelopes and are excluded from determinism hash inputs.
- Determinism metric computation lock is frozen:
  - determinism hash input is canonical JSON from loaded captured response payloads (`sha256_canonical_json(load_json(path))`), not raw bytes.
  - hash projection excludes `created_at` fields recursively at any depth in captured response JSON; no other fields are excluded.
  - replay exactly `N=3` times per fixture.
  - fixture passes only when all replay hashes match.
  - `pct = 100 * passed / total`.
- Deterministic performance-optimization lock is frozen:
  - v18 bounded-optimization patterns may be applied to v19 read-surface hashing paths.
  - allowed optimization includes deterministic sub-component pre-hashing/caching keyed by canonical input payload hashes.
  - optimization may not alter fixture selection, replay count, hash projection rules, or pass/fail semantics.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_core_ir_read_surface_determinism_pct`
  - `artifact_lane_read_surface_determinism_pct`
  - `artifact_integrity_read_surface_determinism_pct`
- Continuity-threshold lock is frozen:
  - v16/v17/v18 thresholds remain required and unchanged in v19 closeout.
  - this includes v18 tooling budget continuity:
    - `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0`
  - v19 closeout evidence must include an explicit runtime-observability comparison row against v18 canonical closeout baseline.
- Threshold lock is frozen for `vNext+19 -> vNext+20`:
  - `artifact_core_ir_read_surface_determinism_pct == 100.0`
  - `artifact_lane_read_surface_determinism_pct == 100.0`
  - `artifact_integrity_read_surface_determinism_pct == 100.0`
  - v16/v17/v18 continuity thresholds remain required and unchanged.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus19_manifest_hash`.
  - mismatch fails closed.

### Acceptance

- Read-surface coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+19` thresholds.

## R4) No-Mutation And No-Provider-Expansion Continuity

### Goal

Keep v19 product-surface activation strictly read-only and prevent silent drift into proposer/provider or mutation semantics.

### Scope

- Freeze explicit continuity constraints for `vNext+19 -> vNext+20`.
- Separate read-surface activation from proposer activation.
- Preserve v14-v18 operational and trust boundaries.

### Locks

- No-provider-expansion lock is frozen:
  - this arc introduces no proposer/provider surfaces.
  - provider matrix/surface-set continuity from `vNext+14` remains unchanged.
- No-provider-calls guard lock is frozen:
  - read-surface handlers must be covered by deterministic tests using a `NoProviderCallsGuard` runtime helper.
  - guard behavior is fail-closed: any provider client entrypoint invocation in guarded read-surface paths fails the test.
  - guard coverage must also enforce outbound-network denial in test context (socket-level fail-closed boundary) so provider/network calls cannot bypass high-level client patching.
- No-mutation lock is frozen:
  - read-surface entrypoints must not write canonical ADEU artifacts or mutate persisted integrity/core-ir/lane artifacts.
  - canonical artifacts remain generated by existing materialization/closeout flows only.
- No-mutation verification lock is frozen:
  - deterministic no-mutation tests must compare pre/post snapshots over the v19 fixture-backed mutable surface only:
    - `apps/api/fixtures/read_surface/vnext_plus19_catalog.json`
    - all artifact JSON files referenced by that catalog.
  - snapshot comparison is hash-based over canonical file contents (`sha256_canonical_json(load_json(path))`) and must remain byte-identical for read-only calls.
- No-solver-change lock is frozen:
  - solver, validator, and proof semantics are not changed by this arc.
- S3b deferral lock is frozen:
  - any core-ir proposer activation requires a separate lock doc and explicit provider continuity release.
  - S3b work is out-of-scope for v19.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.
  - read surfaces may surface stored trust evidence only.

### Acceptance

- Tests prove read-surface code paths do not invoke provider clients or materialization flows.
- Tests include `NoProviderCallsGuard` coverage that fails closed on provider client entrypoint invocation.
- No mutation side effects are observed for read-surface calls on locked fixtures.
- No-mutation tests include deterministic pre/post storage snapshot hash equality assertions.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_READ_SURFACE_*` additions in this arc are frozen:
  - `URM_ADEU_READ_SURFACE_REQUEST_INVALID`
  - `URM_ADEU_READ_SURFACE_ARTIFACT_NOT_FOUND`
  - `URM_ADEU_READ_SURFACE_PAYLOAD_INVALID`
  - `URM_ADEU_READ_SURFACE_FIXTURE_INVALID`
  - `URM_ADEU_READ_SURFACE_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_READ_SURFACE_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_READ_SURFACE_REQUEST_INVALID` for unsupported family values and ambiguous/non-unique deterministic artifact-resolution cases.
  - use `URM_ADEU_READ_SURFACE_FIXTURE_INVALID` for manifest/run-key/surface-id/cap violations.
  - use `URM_ADEU_READ_SURFACE_PAYLOAD_INVALID` for emitted read-surface artifact schema/content validation failures.
  - use `URM_ADEU_READ_SURFACE_ARTIFACT_NOT_FOUND` for persisted-lookup misses in `R1` endpoints.
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v19 read-surface codes are additive and must not remove prior legacy error identifiers.

## Commit Plan (Small Green Commits)

1. `api: add fixture-backed read-only urm core-ir/lane/integrity endpoints with catalog resolution`
2. `runtime: add deterministic read-surface render payload builder`
3. `metrics: add vnext_plus19 manifest and additive read-surface determinism keys`
4. `docs: add vnext_plus19 read-surface transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus19 replay fixtures, NoProviderCallsGuard coverage, and no-mutation snapshot assertions`

## Intermediate Stage Preconditions And Outputs (Draft)

Before implementation PR1 for `vNext+19`, confirm v18 preconditions are frozen/merged and prepare v19 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS18.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` (precondition post-`vNext+18` baseline refresh; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus19_manifest.json`
4. frozen read-surface catalog scaffold `apps/api/fixtures/read_surface/vnext_plus19_catalog.json` (`read_surface.vnext_plus19_catalog@1`)
5. draft transfer-report schema/renderer for `read_surface_transfer_report.vnext_plus19@1`
6. deterministic env helper hook-up for read-surface stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
7. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS19.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `R1`-`R4` merged with green CI.
- `artifact_core_ir_read_surface_determinism_pct == 100.0` on locked fixtures.
- `artifact_lane_read_surface_determinism_pct == 100.0` on locked fixtures.
- `artifact_integrity_read_surface_determinism_pct == 100.0` on locked fixtures.
- `vNext+19 -> vNext+20` frozen thresholds all pass.
- v16/v17/v18 continuity metrics remain present and at threshold (`100.0`).
- v19 closeout evidence includes runtime-observability comparison rows against v18 canonical baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
- Provider-parity continuity lock remains unchanged (no proposer surface expansion).
- All existing stop-gate tracked `vNext+6` through `vNext+18` metrics remain at threshold.
- `vNext+16` through `vNext+18` closeout evidence remains green and reproducible.
