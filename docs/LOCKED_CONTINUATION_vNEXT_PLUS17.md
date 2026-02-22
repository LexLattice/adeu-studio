# Locked Continuation vNext+17 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock implemented on `main`; closeout evidence is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS17.md`.

Decision basis:

- `vNext+16` (`D1`-`D4`) merged on `main` with green CI and closeout evidence in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` recommends `vNext+17 = Path S1` (Candidate `v17-A`) as the default first slice.
- `vNext+16` established deterministic integrity artifacts, replay controls, and manifest-driven closeout suitable for additive expansion.
- This arc is reserved for integrity diagnostics expansion only:
  - deterministic extended reference-integrity diagnostics first
  - deterministic extended cycle-policy diagnostics second
  - deterministic extended deontic conflict diagnostics third
  - manifest-driven closeout metrics and stop-gate fourth

Closeout note (February 22, 2026 UTC):

- `E1`-`E4` merged on `main` with green CI.
- v17 deterministic thresholds are satisfied:
  - `artifact_reference_integrity_extended_determinism_pct = 100.0`
  - `artifact_cycle_policy_extended_determinism_pct = 100.0`
  - `artifact_deontic_conflict_extended_determinism_pct = 100.0`
- v16 continuity thresholds remain satisfied:
  - `artifact_dangling_reference_determinism_pct = 100.0`
  - `artifact_cycle_policy_determinism_pct = 100.0`
  - `artifact_deontic_conflict_determinism_pct = 100.0`
- deterministic transfer-report evidence is published in `docs/INTEGRITY_TRANSFER_REPORT_vNEXT_PLUS17.md`.

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md` remain authoritative for policy/proof/explain/runtime/provider-parity/core-ir/depth/integrity baseline semantics.
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
  - this arc adds diagnostics over persisted artifacts only; it does not rewrite core-ir or depth artifacts.
- Integrity continuity lock from `vNext+16` is frozen:
  - `adeu_integrity_dangling_reference@0.1`, `adeu_integrity_cycle_policy@0.1`, and `adeu_integrity_deontic_conflict@0.1` remain authoritative for v16 outputs.
  - this arc adds separate extended artifact families and does not rewrite v16 artifacts in place.
- Metric naming continuity lock is frozen:
  - existing v16 keys remain unchanged and must not be replaced or renamed.
  - additive v17 expansion keys must include `_extended_`.

## Arc Scope (Draft Lock)

This arc proposes Path S1 thin slice only:

1. `E1` Deterministic extended reference-integrity diagnostics
2. `E2` Deterministic extended cycle-policy diagnostics
3. `E3` Deterministic extended deontic conflict diagnostics (evidence-first)
4. `E4` Manifest-driven coverage accountability + stop-gate closeout for `vNext+17 -> vNext+18`

Out-of-scope note:

- Path `S2` (extraction fidelity completion) remains deferred in this arc.
- optional pull-forward trigger (placeholder for later freeze): `>= 3` alignment mismatches per fixture replay set OR `>= 5` audit-confirmed span/label drift cases.

## E1) Deterministic Extended Reference-Integrity Diagnostics

### Goal

Capture deterministic reference-integrity issues beyond v16 edge-endpoint checks while preserving canonical fail-closed `adeu_core_ir@0.1` validation behavior.

### Scope

- Compute extended reference-integrity diagnostics from persisted fixture artifacts only.
- Run diagnostics over raw payload structures in deterministic pre-validation paths.
- Keep diagnostics additive and non-authoritative.
- Freeze deferred-edge selection explicitly for this arc.
- Keep selected checks bounded to implementable `adeu_core_ir@0.1` structures in this arc.

### Locks

- Diagnostic schema lock is frozen:
  - `schema = "adeu_integrity_reference_integrity_extended@0.1"`
  - required fields:
    - `source_text_hash`
    - `summary`
    - `issues` (deterministically ordered)
  - `summary` shape is frozen:
    - `total_issues`
    - `edge_type_constraint_violation`
    - `duplicate_edge_identity`
  - each issue entry includes:
    - `kind`
    - `subject_id`
    - `related_id` (optional in payload; normalized as `""` for deterministic ordering)
    - optional additive `details`
- Deferred-edge candidate-set selection lock is frozen:
  - synthesis exhaustive candidate set remains:
    - missing referenced node ids in node-level reference fields (not only edge endpoints)
    - edge endpoint references that exist but violate frozen edge typing constraints
    - duplicate edge identity collisions (`(type, from, to)` duplicates)
  - selected subset for this arc (`E1`) is exactly:
    - edge endpoint references that exist but violate frozen edge typing constraints
    - duplicate edge identity collisions (`(type, from, to)` duplicates)
  - deferred from this arc:
    - `missing_node_reference_field` is deferred because `adeu_core_ir@0.1` node records do not define frozen node-level cross-node reference fields to validate deterministically.
- Issue taxonomy lock is frozen:
  - deterministic issue kinds are exactly:
    - `edge_type_constraint_violation`
    - `duplicate_edge_identity`
- Deterministic ordering lock is frozen:
  - issue ordering key is `(kind, subject_id, related_id)`.
  - missing `related_id` is normalized as `""` for deterministic ordering.
- Issue-identity semantics lock is frozen:
  - `edge_type_constraint_violation`:
    - `subject_id = "edge:<type>:<from>-><to>"`
    - `related_id = "type_constraint"`
    - constraint-evaluation lock:
      - violation means `edge.type` is not allowed for the `(from.layer, from.kind, to.layer, to.kind)` tuple under the frozen `adeu_core_ir@0.1` edge typing matrix.
      - this check is evaluated only when both endpoints resolve to existing nodes in the payload index.
      - when either endpoint is missing, this check is skipped to avoid double-reporting with dangling-reference family diagnostics.
  - `duplicate_edge_identity`:
    - `subject_id = "edge:<type>:<from>-><to>"`
    - `related_id = "duplicate_edge_identity"`
    - duplicate-emission lock:
      - emit exactly one issue entry per duplicate identity key `(type, from, to)` regardless of duplicate multiplicity.
      - optional additive `details.duplicate_count` may be included when deterministic and derived from the raw payload.
  - missing interpolation lock:
    - when `type`, `from`, or `to` is missing/null in payload interpolation, deterministic placeholder `_MISSING_` is used for that component.
- Diagnostic-vs-validation boundary lock is frozen:
  - extended checks may overlap with existing hard validators in `AdeuCoreIR` contract enforcement.
  - diagnostics in this arc are computed from raw payloads for evidence capture and do not replace or weaken canonical validation rejection.
  - canonical `adeu_core_ir@0.1` contract validation behavior remains unchanged and fail-closed.
- Input authority lock is frozen:
  - diagnostics consume persisted fixtures/artifacts only.
  - no live provider dependency in deterministic acceptance paths.
- Diagnostic volume-bound lock is frozen:
  - maximum emitted `issues` entries per fixture is `1000`.
  - cap enforcement applies to deterministically canonicalized, deduplicated emitted entries (not raw pre-dedup candidate enumeration).
  - issue diagnostics must short-circuit once candidate issue count exceeds the cap and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Summary consistency lock is frozen:
  - `summary.total_issues == len(issues)`.
  - per-kind summary counts equal deterministic counts over `issues.kind`.
- Scope boundary lock is frozen:
  - checks target structural/data-contract integrity evidence only.
  - diagnostics may not infer or rewrite semantic claims.
- Non-authoritative lock is frozen:
  - extended reference-integrity diagnostics are evidence artifacts and do not mutate canonical artifacts in this arc.

### Acceptance

- Locked fixtures produce schema-valid extended reference-integrity diagnostics.
- Identical fixture inputs replay to byte-identical diagnostics.
- At least one locked E1 fixture is a deterministic validator-bypass malformed-payload case that yields non-zero diagnostics through the E1 path.

## E2) Deterministic Extended Cycle-Policy Diagnostics

### Goal

Extend deterministic cycle-policy diagnostics while preserving v16 cycle outputs and evidence-first behavior.

### Scope

- Build deterministic cycle-policy diagnostics from persisted fixtures.
- Preserve v16 `E`-layer `depends_on` cycle continuity.
- Add deterministic `D`-layer cycle evidence over `depends_on` and `excepts` edges under separate taxonomy.
- Keep outputs additive and non-authoritative in this arc.
- Keep extended D-layer cycle kinds in deterministic pre-validation diagnostics only (raw/bypass payload path) when they overlap typing-invalid structures under `adeu_core_ir@0.1`.

### Locks

- Diagnostic schema lock is frozen:
  - `schema = "adeu_integrity_cycle_policy_extended@0.1"`
  - required fields:
    - `source_text_hash`
    - `summary`
    - `cycles` (deterministically ordered)
  - `summary` shape is frozen:
    - `total_cycles`
    - `self_cycle`
    - `multi_node_cycle`
    - `dependency_loop`
    - `exception_loop`
  - each cycle entry includes:
    - `kind`
    - `cycle_signature`
    - `node_ids` (canonical order; first node is not repeated at end)
- Cycle taxonomy lock is frozen:
  - deterministic cycle kinds are exactly:
    - `self_cycle`
    - `multi_node_cycle`
    - `dependency_loop`
    - `exception_loop`
  - `exception_loop` in this arc intentionally aggregates both pure `excepts`-only paths and mixed `depends_on` + `excepts` paths.
  - split taxonomy (`pure_exception_loop`, `mixed_normative_loop`) is deferred to a later lock and out-of-scope for this arc.
- Graph-scope lock is frozen:
  - v16 continuity scope:
    - `E`-layer nodes with edges where `type == "depends_on"` remain included with v16 semantics.
  - additive extended scope:
    - `D`-layer nodes with edges where `type in {"depends_on", "excepts"}` are included for extended diagnostics only.
    - only edges whose `from` and `to` both resolve to `D`-layer nodes are in extended D-layer cycle scope.
  - all other edge types are excluded from E2 cycle detection in this arc.
  - cycle detection is over directed adjacency induced by edge direction (`from -> to`) only.
- Diagnostic-vs-validation boundary lock is frozen:
  - under frozen `adeu_core_ir@0.1` edge typing, schema-valid artifacts may yield zero `dependency_loop` and zero `exception_loop`.
  - non-zero evidence for `dependency_loop` and `exception_loop` may be captured only from deterministic validator-bypass fixtures in this arc.
  - canonical `adeu_core_ir@0.1` validation behavior remains unchanged and fail-closed.
- Cycle-kind derivation lock is frozen:
  - cycles in the v16 continuity scope use:
    - `self_cycle` for single-node loops
    - `multi_node_cycle` for length `>= 2`
  - cycles in the additive `D`-layer extended scope use:
    - `exception_loop` when at least one `excepts` edge is present in the cycle path
    - `dependency_loop` otherwise
  - cycle-path capture must include traversed edge types in deterministic candidate construction so kind derivation is based on path evidence (not inferred post hoc from node-only paths).
- Cycle canonicalization lock is frozen:
  - cycle node-id paths are normalized to deterministic canonical rotation before hashing/ordering.
  - canonical cycle is the lexicographically smallest node-id sequence among all rotations of the directed cycle path.
  - cycle list ordering is lexicographic on `(kind, cycle_signature)`.
- Cycle-signature semantics lock is frozen:
  - `cycle_signature = "cycle:" + "->".join(node_ids)` where `node_ids` are canonicalized by the cycle canonicalization lock.
  - signature-namespace lock:
    - node ids are globally unique across layers in `adeu_core_ir@0.1`; `cycle_signature` remains layer-agnostic in this arc.
- Cycle dedup lock is frozen:
  - emit at most one cycle entry per `(kind, cycle_signature)`.
  - duplicate detections of the same canonical signature are collapsed deterministically before summary counts.
- Input boundary lock is frozen:
  - deterministic cycle diagnostics are derived from persisted fixture artifacts only.
  - no live provider calls are permitted.
- Diagnostic volume-bound lock is frozen:
  - maximum emitted `cycles` entries per fixture is `1000`.
  - cap enforcement applies to deterministically canonicalized, deduplicated emitted entries (not raw pre-dedup candidate enumeration).
  - cycle diagnostics must short-circuit once candidate cycle count exceeds the cap and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Summary consistency lock is frozen:
  - `summary.total_cycles == len(cycles)`.
  - per-kind summary counts equal deterministic counts over `cycles.kind`.
- Policy-semantics lock is frozen:
  - cycle diagnostics encode policy evidence only for this arc.
  - cycle presence does not mutate canonical artifacts or solver behavior.

### Acceptance

- Locked fixtures produce schema-valid deterministic extended cycle diagnostics.
- Identical fixture inputs replay to byte-identical extended cycle diagnostics.
- At least one locked E2 fixture is a deterministic validator-bypass case for exercising additive `dependency_loop`/`exception_loop` kinds.

## E3) Deterministic Extended Deontic Conflict Diagnostics (Evidence-First)

### Goal

Extend deterministic deontic diagnostics beyond the v16 minimal pair while preserving solver semantics and evidence-first posture.

### Scope

- Compute deterministic deontic conflict diagnostics over persisted deontic artifacts in fixtures.
- Preserve v16 minimal conflict rule behavior.
- Add one bounded additive deontic tension family in this arc.
- Keep diagnostics non-gating for canonical artifact generation.

### Locks

- Diagnostic schema lock is frozen:
  - `schema = "adeu_integrity_deontic_conflict_extended@0.1"`
  - required fields:
    - `source_text_hash`
    - `summary`
    - `conflicts` (deterministically ordered)
  - `summary` shape is frozen:
    - `total_conflicts`
    - `deontic_conflict`
    - `deontic_tension`
  - each conflict entry includes:
    - `kind`
    - `primary_id`
    - `related_id` (optional in payload; normalized as `""` for deterministic ordering)
    - optional additive `details`
- Conflict taxonomy lock is frozen:
  - deterministic conflict kinds are exactly:
    - `deontic_conflict`
    - `deontic_tension`
- Matching-rule lock is frozen:
  - candidate pairs are distinct `D`-node records where:
    - both have non-empty normalized target text
    - normalized target text is equal
    - normalized condition text is equal (`None`/missing condition normalizes to `""`)
  - modality pair `{obligatory, forbidden}` maps to `deontic_conflict` (v16 continuity).
  - modality pair `{forbidden, permitted}` maps to `deontic_tension` (additive v17 extension).
  - modality pair `{obligatory, permitted}` remains deferred in this arc.
  - each unordered node pair matches at most one kind under the frozen modality mapping.
  - deferral rationale lock:
    - this arc does not introduce normative-resolution semantics for interpreting `permitted` against `obligatory`; it keeps minimal conflict/tension evidence only.
- Normalization lock is frozen for E3 matching:
  - normalized text for target/condition is computed deterministically as:
    - Unicode NFC normalization
    - trim leading/trailing whitespace
    - collapse internal whitespace runs to a single ASCII space
    - lowercase ASCII transformation on codepoints `A-Z` only (non-ASCII codepoints unchanged)
    - normalized condition aliases `"always"` and `"none"` map to `""`.
- Conflict resolution-boundary lock is frozen:
  - `priority` is preserved as optional evidence metadata only and is not used to suppress/resolve conflicts in this arc.
  - `excepts`-edge semantics are not used for suppression in this arc.
  - `deontic_tension` is pure co-occurrence evidence in this arc and is never suppressed by `priority` or `excepts`.
- Deterministic ordering lock is frozen:
  - conflict ordering key is `(kind, primary_id, related_id)`.
  - missing `related_id` is normalized as `""` for deterministic ordering.
- Conflict-identity semantics lock is frozen:
  - `primary_id` and `related_id` are canonical `D`-node ids from persisted fixture artifacts.
  - deterministic pair orientation is frozen:
    - `primary_id` is lexicographically smaller id
    - `related_id` is lexicographically larger id
  - each unordered node pair is emitted at most once per `kind`.
- Input boundary lock is frozen:
  - diagnostics are derived from persisted fixture artifacts only.
  - no live provider calls are permitted.
- Diagnostic volume-bound lock is frozen:
  - maximum emitted `conflicts` entries per fixture is `1000`.
  - cap enforcement applies to deterministically canonicalized, deduplicated emitted entries (not raw pre-dedup candidate enumeration).
  - conflict diagnostics must short-circuit once candidate pair count exceeds the cap and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Summary consistency lock is frozen:
  - `summary.total_conflicts == len(conflicts)`.
  - `summary.deontic_conflict` equals deterministic count over `conflicts.kind == "deontic_conflict"`.
  - `summary.deontic_tension` equals deterministic count over `conflicts.kind == "deontic_tension"`.
- Evidence-first lock is frozen:
  - extended deontic diagnostics are non-authoritative evidence for this arc.
  - diagnostics may not mutate canonical solver or projection outputs.

### Acceptance

- Locked fixtures produce schema-valid deterministic extended deontic diagnostics.
- Identical fixture inputs replay to byte-identical extended deontic diagnostics.

## E4) Coverage Accountability + Stop-Gate Metrics + Integrity Closeout

### Goal

Make v17 integrity expansion coverage measurable and reproducible, and add deterministic closeout metrics for `vNext+17 -> vNext+18`.

### Scope

- Add manifest-driven fixture coverage accounting for E1/E2/E3 surfaces.
- Add deterministic transfer-report evidence for v17 extended integrity outputs.
- Extend additive `stop_gate_metrics@1` with v17 integrity expansion keys.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus17_manifest.json`
  - schema:
    - `stop_gate.vnext_plus17_manifest@1`
  - manifest `replay_count` is frozen to `N=3` for this arc.
- Surface enumeration completeness lock is frozen:
  - the frozen v17 extended integrity `surface_id` set is exactly:
    - `adeu.integrity.reference_integrity_extended`
    - `adeu.integrity.cycle_policy_extended`
    - `adeu.integrity.deontic_conflict_extended`
  - manifest fixture `surface_id` values must be members of this frozen set only.
  - surface drift/unknown `surface_id` is fixture-invalid and fails closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Manifest shape continuity lock is frozen:
  - manifest follows existing stop-gate list-style fixture pattern used in prior arcs.
  - required metric fixture lists are frozen:
    - `reference_integrity_extended_fixtures`
    - `cycle_policy_extended_fixtures`
    - `deontic_conflict_extended_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs (for example `fixture_id`, `surface_id`, `runs`/artifact refs).
- Run-reference key lock is frozen:
  - required deterministic run keys are:
    - `reference_integrity_extended_fixtures[].runs[].reference_integrity_extended_path`
    - `cycle_policy_extended_fixtures[].runs[].cycle_policy_extended_path`
    - `deontic_conflict_extended_fixtures[].runs[].deontic_conflict_extended_path`
  - missing required run keys are fixture-invalid and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Replay-run indexing lock is frozen:
  - deterministic replay run identity is `(fixture_id, surface_id, run_index)` where `run_index` is in `1..replay_count`.
  - replay run identities are used for deterministic run-level evidence references and traceability only (not as metric denominator units).
- Coverage validity lock is frozen:
  - each declared integrity surface must map to at least one fixture id.
- Non-empty diagnostic evidence lock is frozen:
  - each metric fixture list must contain at least one fixture that yields non-zero diagnostics for that list's diagnostic family.
  - at least one E1 fixture must be a validator-bypass malformed-payload case that demonstrates non-empty overlap checks.
  - at least one E2 fixture must be a validator-bypass malformed-payload case that exercises additive `dependency_loop` or `exception_loop`.
  - non-empty evidence lock is family-level (not per-kind); schema-valid artifacts may legitimately yield zero counts for specific additive kinds constrained by frozen typing.
  - all-zero diagnostic inventories are fixture-invalid and fail closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID`.
- Transfer report lock is frozen:
  - output path:
    - `docs/INTEGRITY_TRANSFER_REPORT_vNEXT_PLUS17.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "integrity_transfer_report.vnext_plus17@1"`
    - `vnext_plus17_manifest_hash`
    - `coverage_summary`
    - `reference_integrity_extended_summary`
    - `cycle_policy_extended_summary`
    - `deontic_conflict_extended_summary`
    - `replay_summary`
- Cross-diagnostic linkage lock is frozen:
  - E1/E2/E3 artifacts remain family-isolated in this arc.
  - optional cross-artifact trace ids/causal links are deferred to a later lock to avoid schema-surface expansion in `vNext+17`.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - existing v16 keys remain present and unchanged:
    - `artifact_dangling_reference_determinism_pct`
    - `artifact_cycle_policy_determinism_pct`
    - `artifact_deontic_conflict_determinism_pct`
  - additive v17 keys:
    - `artifact_reference_integrity_extended_determinism_pct`
    - `artifact_cycle_policy_extended_determinism_pct`
    - `artifact_deontic_conflict_extended_determinism_pct`
- Determinism metric computation lock is frozen:
  - canonical hash per fixture/output artifact
  - replay exactly `N=3` times per fixture
  - fixture passes only when all replay hashes match
  - `pct = 100 * passed / total`
- Artifact-hash precedence lock is frozen:
  - manifest hash validates manifest-index integrity only.
  - deterministic metric pass/fail remains driven by per-run canonical artifact hashes for referenced payloads; manifest-hash match alone is insufficient.
- Metric denominator lock is frozen:
  - fixture selection is defined by:
    - `apps/api/fixtures/stop_gate/vnext_plus17_manifest.json`
  - run-entry validity lock:
    - a run entry is valid iff:
      - required run key is present,
      - referenced artifact file exists and is readable,
      - referenced artifact schema/content validates for the corresponding extended family,
      - and if fixture metadata provides optional `expected_source_text_hash`, artifact `source_text_hash` must equal it.
  - denominator units are frozen per metric:
    - reference-integrity-extended, cycle-policy-extended, and deontic-conflict-extended metrics are each computed over fixture units from the corresponding manifest fixture list.
  - `total` for each metric equals the number of fixtures in that metric's frozen fixture list.
  - `passed` for each metric equals the number of fixtures whose run entries are valid and whose replay hashes are all identical across the frozen `replay_count`.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus17_manifest_hash`.
  - mismatch fails closed with `URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH`.
- Replay boundary lock is frozen:
  - closeout metrics are computed from persisted fixtures/artifacts only.
  - no live provider calls are permitted in deterministic stop-gate acceptance paths.
- Deterministic runtime enforcement lock is frozen:
  - stop-gate metric builder entrypoints and integrity transfer-report builders must enforce `TZ=UTC` and `LC_ALL=C` via shared runtime helper before artifact loading/hashing.
- CI budget observability lock is frozen:
  - stop-gate closeout output for this arc must include machine-checkable `runtime_observability` evidence with keys:
    - `total_fixtures`
    - `total_replays`
    - `elapsed_ms`
  - `elapsed_ms` is captured from a monotonic runtime clock in CI execution context for observability only.
  - `runtime_observability` evidence is non-gating and excluded from canonical deterministic hash inputs.
- Threshold lock is frozen for `vNext+17 -> vNext+18`:
  - v16 continuity thresholds remain required:
    - `artifact_dangling_reference_determinism_pct == 100.0`
    - `artifact_cycle_policy_determinism_pct == 100.0`
    - `artifact_deontic_conflict_determinism_pct == 100.0`
  - additive v17 thresholds:
    - `artifact_reference_integrity_extended_determinism_pct == 100.0`
    - `artifact_cycle_policy_extended_determinism_pct == 100.0`
    - `artifact_deontic_conflict_extended_determinism_pct == 100.0`

### Acceptance

- Integrity expansion coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+17` thresholds.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_INTEGRITY_*` additions in this arc are frozen:
  - `URM_ADEU_INTEGRITY_REFERENCE_INTEGRITY_EXTENDED_INVALID`
  - `URM_ADEU_INTEGRITY_CYCLE_POLICY_EXTENDED_INVALID`
  - `URM_ADEU_INTEGRITY_DEONTIC_CONFLICT_EXTENDED_INVALID`
  - `URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_INTEGRITY_FIXTURE_INVALID`
  - `URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_INTEGRITY_FIXTURE_INVALID` for fixture-shape/selection/run-key/surface-id/cap violations.
  - use family-specific `*_EXTENDED_INVALID` codes only for invalid extended diagnostic artifact schema/content validation failures.
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v17 integrity codes are additive and must not remove prior legacy error identifiers where already exposed.

## Commit Plan (Small Green Commits)

1. `integrity: add deterministic reference-integrity extended diagnostics contract and validators`
2. `integrity: add deterministic cycle-policy extended diagnostics`
3. `integrity: add deterministic deontic-conflict extended diagnostics (evidence-first)`
4. `metrics: extend stop-gate with vnext_plus17 manifest-driven extended integrity keys and transfer report`
5. `runtime: enforce deterministic env helper in vnext_plus17 stop-gate/report entrypoints`
6. `tests: add deterministic vnext_plus17 replay fixtures for integrity expansion closeout`

## Intermediate Stage Preconditions And Outputs (Draft)

Before implementation PR1 for `vNext+17`, confirm v16 preconditions are frozen/merged and prepare v17 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` (precondition post-`vNext+16` baseline refresh; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus17_manifest.json`
4. draft transfer-report schema/renderer for `integrity_transfer_report.vnext_plus17@1`
5. deterministic env helper hook-up for stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
6. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS17.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `E1`-`E4` merged with green CI.
- `artifact_reference_integrity_extended_determinism_pct == 100.0` on locked fixtures.
- `artifact_cycle_policy_extended_determinism_pct == 100.0` on locked fixtures.
- `artifact_deontic_conflict_extended_determinism_pct == 100.0` on locked fixtures.
- `vNext+17 -> vNext+18` frozen thresholds all pass.
- v16 continuity metrics remain present and at threshold (`100.0`).
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing stop-gate tracked `vNext+6` through `vNext+16` metrics remain at threshold.
- `vNext+14` through `vNext+16` closeout evidence remains green and reproducible.
