# Locked Continuation vNext+24 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS23.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS23.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+23` (`V1`-`V4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS23.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` post-`vNext+23` sequencing leaves the remaining planned expansion path as `S2 -> S3b` with `S9` as parity fallback; this draft selects `vNext+24 = Path S2` (extraction fidelity completion, deferred from v15).
- `vNext+16` + `vNext+17` integrity families, `vNext+18` tooling continuity, `vNext+19` read-surface activation, `vNext+20` cross-IR coherence bridges, `vNext+21` normative-advice read surfaces, `vNext+22` proof/trust lane starter, and `vNext+23` semantics-v4 candidate lane are stable baselines.
- This arc is reserved for deterministic, read-only, non-enforcing extraction-fidelity diagnostics completion only:
  - deterministic extraction-fidelity packet contract freeze first
  - deterministic extraction-fidelity projection + transfer-report artifact family second
  - additive stop-gate determinism metrics for extraction-fidelity payload stability third
  - explicit non-enforcement and no-mutation/no-provider-expansion continuity fourth

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior in this arc.
- No solver semantic contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS18.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS19.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS20.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS21.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS22.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS23.md` remain authoritative for prior baseline semantics.
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
- Fixture-directory boundary lock is frozen:
  - extraction-fidelity source catalogs for this arc live under:
    - `apps/api/fixtures/extraction_fidelity/`
  - stop-gate replay manifests for this arc live under:
    - `apps/api/fixtures/stop_gate/`
  - introducing additional fixture-root directories in this arc is out-of-scope.
- Existing schema contracts remain frozen and unchanged in this arc, including:
  - `adeu_core_ir@0.1`
  - `adeu_lane_projection@0.1`
  - `adeu_lane_report@0.1`
  - `adeu_projection_alignment@0.1`
  - `adeu_integrity_dangling_reference@0.1`
  - `adeu_integrity_cycle_policy@0.1`
  - `adeu_integrity_deontic_conflict@0.1`
  - `adeu_integrity_reference_integrity_extended@0.1`
  - `adeu_integrity_cycle_policy_extended@0.1`
  - `adeu_integrity_deontic_conflict_extended@0.1`
  - `adeu_read_surface_payload@0.1`
  - `adeu_cross_ir_bridge_manifest@0.1`
  - `adeu_cross_ir_coherence_diagnostics@0.1`
  - `cross_ir_quality_projection.vnext_plus20@1`
  - `adeu_normative_advice_packet@0.1`
  - `normative_advice_projection.vnext_plus21@1`
  - `adeu_trust_invariant_packet@0.1`
  - `trust_invariant_projection.vnext_plus22@1`
  - `semantics_diagnostics@1`
  - `adeu_semantics_v4_candidate_packet@0.1`
  - `semantics_v4_candidate_projection.vnext_plus23@1`
- New schema-family introduction lock is frozen:
  - this arc adds exactly two new extraction-fidelity artifact schema families (additive-only):
    - `adeu_projection_alignment_fidelity_input@0.1`
    - `adeu_projection_alignment_fidelity@0.1`
  - all prior schema contracts remain frozen and unchanged.
- Bridge-version continuity lock is frozen:
  - existing bridge-version contracts remain authoritative:
    - `bridge_mapping_version = "adeu_to_concepts.v1"`
    - `bridge_loss_report.version = "adeu.bridge.loss.v1"`
  - any bridge-version bump is out-of-scope for this arc and requires a separate lock.
- Provider-parity continuity lock is frozen:
  - `vNext+14` provider matrix/manifest semantics remain unchanged in this arc.
  - this arc does not expand proposer provider surface sets.
- Integrity continuity lock from `vNext+16` + `vNext+17` is frozen.
- Tooling continuity lock from `vNext+18` is frozen.
- Read-surface continuity lock from `vNext+19` is frozen.
- Cross-ir continuity lock from `vNext+20` is frozen.
- Normative-advice continuity lock from `vNext+21` is frozen.
- Trust-invariant continuity lock from `vNext+22` is frozen.
- Semantics-v4 candidate continuity lock from `vNext+23` is frozen.
- Upstream dependency continuity lock is frozen:
  - v24 extraction-fidelity generation depends on persisted upstream evidence from:
    - `apps/api/fixtures/extraction_fidelity/vnext_plus24_catalog.json`
    - persisted baseline alignment diagnostics (`adeu_projection_alignment@0.1`) for matched `source_text_hash`
    - persisted extraction-fidelity candidate input payloads (`adeu_projection_alignment_fidelity_input@0.1`) for matched `source_text_hash`
  - missing upstream evidence is artifact-not-found and fails closed.
  - best-effort fallback, live recomputation, and undeclared input substitution are out-of-scope for deterministic acceptance paths.
- Catalog contract lock is frozen:
  - `apps/api/fixtures/extraction_fidelity/vnext_plus24_catalog.json` must declare:
    - `schema = "extraction_fidelity.vnext_plus24_catalog@1"`
  - required per-entry fields:
    - `source_text_hash`
    - `projection_alignment_path`
    - `projection_alignment_fidelity_input_path`
  - optional per-entry fields:
    - `created_at`
    - `domain_id`
    - `document_ref`
  - deterministic entry ordering key is lexicographic `source_text_hash`.
  - uniqueness key is exactly `source_text_hash`; duplicate entries are request-invalid and fail closed.
  - each `source_text_hash` must resolve to exactly one `adeu_projection_alignment@0.1` artifact and exactly one `adeu_projection_alignment_fidelity_input@0.1` artifact.
- Baseline-contract continuity lock is frozen:
  - v24 may consume `adeu_projection_alignment@0.1` persisted artifacts but may not rewrite them in place.
  - deferred v15 diagnostics (`label_text_mismatch`, `span_mismatch`, `score_mismatch`) activate in a new additive artifact family only in this arc.

## Arc Scope (Draft Lock)

This arc proposes Path `S2` thin slice only:

1. `X1` Deterministic extraction-fidelity packet contract freeze
2. `X2` Deterministic extraction-fidelity projection + transfer-report artifact family
3. `X3` Additive stop-gate determinism metrics for extraction-fidelity payload stability
4. `X4` Explicit non-enforcement and no-mutation/no-provider-expansion continuity for `vNext+24 -> vNext+25`

Out-of-scope note:

- Path `S3b` (core-ir proposer activation) is not in this arc.
- Path `S9` (provider parity fallback) remains conditional and trigger-based, and is not proactively activated by this arc.
- Provider matrix/surface expansion is not in this arc.
- This arc does not switch default runtime semantics from v3.
- Automatic policy execution/auto-remediation from extraction-fidelity output is not in this arc.
- DB-backed extraction-fidelity persistence migrations/new SQL tables are not in this arc.
- Payload offloading via blob-store/pre-signed URLs is not in this arc.
- Sparse fieldset/query-driven partial payload retrieval is not in this arc.
- Mandatory frontend build-system expansion is not in this arc; optional minimal rendering is allowed only if it does not introduce a new frontend build-system dependency.
- Extraction-fidelity acknowledgement/dismissal persistence and mutation endpoints are not in this arc.
- Schema-family consolidation/reduction is not in this arc and remains a separate lock decision (continuity with S5-style consolidation work).
- Inline extracted text-snippet transclusion in extraction-fidelity payloads is not in this arc.
- Per-item drift detail expansions (for example `failed_nodes` / `drift_match_ids` arrays) are not in this arc.
- UI-diff-native payload shaping for downstream rendering frameworks is not in this arc.

## X1) Deterministic Extraction-Fidelity Packet Contract Freeze

### Goal

Emit deterministic, read-only, non-enforcing extraction-fidelity packets for deferred v15 diagnostics (`label_text_mismatch`, `span_mismatch`, `score_mismatch`) derived from persisted evidence only.

### Scope

- Add deterministic extraction-fidelity packet generation over persisted alignment/fidelity input evidence.
- Keep output schema-validated and explicitly non-authoritative.
- Resolve source identities from fixture-backed catalogs only in this arc.
- Preserve explicit justification references for every extraction-fidelity item.

### Locks

- Source authority lock is frozen:
  - generation in this arc is fixture-backed only from persisted artifacts:
    - `apps/api/fixtures/extraction_fidelity/vnext_plus24_catalog.json`
    - persisted `adeu_projection_alignment@0.1` payloads
    - persisted `adeu_projection_alignment_fidelity_input@0.1` payloads
  - filesystem scans, DB discovery, and undeclared directories are out-of-scope.
- Dual-input dependency lock is frozen:
  - extraction-fidelity builders must load both:
    - matched baseline alignment diagnostics (`adeu_projection_alignment@0.1`)
    - matched candidate-pair fidelity input payload (`adeu_projection_alignment_fidelity_input@0.1`)
  - operation without either required input is request-invalid and fails closed.
- Fidelity-input generation boundary lock is frozen:
  - persisted `adeu_projection_alignment_fidelity_input@0.1` artifacts are pre-matched evidence inputs for this arc.
  - deterministic acceptance paths do not define or execute live matching between projection and extraction nodes.
  - best-effort regeneration of `matched_nodes` from raw sources or undeclared artifacts is out-of-scope and forbidden.
- Baseline input-authority lock is frozen:
  - baseline alignment artifact (`adeu_projection_alignment@0.1`) is loaded for deterministic provenance/binding evidence (`projection_alignment_hash`) and source evidence linkage.
  - per-node extraction-fidelity comparison inputs are authoritative from persisted `adeu_projection_alignment_fidelity_input@0.1` fields (`projection_*`, `extraction_*`).
  - cross-artifact per-node consistency checks beyond frozen provenance/hash linkage are out-of-scope in this arc.
- Endpoint-set lock is frozen:
  - `GET /urm/extraction-fidelity/sources/{source_text_hash}` (`X1` implementation scope)
  - `GET /urm/extraction-fidelity/projection` (`X2` implementation scope; deferred from this `X1` PR slice)
- Persistence-model lock is frozen:
  - `X1/X2` surfaces in this arc are fixture-backed over persisted JSON artifacts/capture catalogs.
  - no new SQL storage tables or schema migrations are introduced for extraction-fidelity retrieval/projection in v24.
  - DB-backed extraction-fidelity retrieval/projection is deferred to a later lock.
- Source-resolution identity lock is frozen:
  - deterministic source identity key is exactly:
    - `source_text_hash`
  - route resolution is exact-match on this key only.
  - single-key routing by `source_text_hash` is intentional for this arc and supersedes v20-v23 pair-tuple routing patterns.
  - matched catalog entry provides authoritative persisted lookup refs only:
    - `projection_alignment_path`
    - `projection_alignment_fidelity_input_path`
  - path inference, filesystem globbing, and undeclared path fallback are forbidden.
  - non-unique/ambiguous source entries in the fixture-backed catalog are request-invalid and fail closed.
- Source-endpoint miss-mode lock is frozen:
  - when `source_text_hash` is not present in catalog:
    - `URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND`
  - when `source_text_hash` is present but matched baseline alignment or fidelity-input artifact is missing:
    - `URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND`
  - when source and upstream artifacts are present but payload linkage/validation fails:
    - `URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID`
- Route-to-artifact binding lock is frozen:
  - for each request route `source_text_hash`, all loaded artifacts must match exactly:
    - `projection_alignment_payload.source_text_hash == route source_text_hash`
    - `fidelity_input_payload.source_text_hash == route source_text_hash`
  - any mismatch is payload-invalid and fails closed:
    - `URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID`
- Fidelity-input schema lock is frozen:
  - `schema = "adeu_projection_alignment_fidelity_input@0.1"`
  - required top-level fields:
    - `source_text_hash`
    - `matched_nodes`
  - each `matched_nodes[]` entry required fields:
    - `match_id`
    - `projection_label_text`
    - `extraction_label_text`
    - `projection_span` (`start`, `end` integers)
    - `extraction_span` (`start`, `end` integers)
    - `projection_score_milli`
    - `extraction_score_milli`
- Fidelity-input volume-cap lock is frozen:
  - hard cap:
    - `max_matched_nodes_per_source = 5000`
  - cap enforcement is applied on raw list cardinality before any validation/dedup logic.
  - exceeding cap is payload-invalid and fails closed:
    - `URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID`
- Match-id semantics lock is frozen:
  - `matched_nodes[].match_id` is a required non-empty opaque string.
  - `match_id` comparison is exact, case-sensitive, and byte-for-byte.
  - `match_id` values must be unique within each `matched_nodes[]` list; duplicates are payload-invalid.
- Span semantics lock is frozen:
  - `projection_span` and `extraction_span` are half-open intervals `[start, end)` (end-exclusive).
  - each span must satisfy `0 <= start <= end`; negative offsets are payload-invalid.
  - compared projection/extraction spans for a matched node are offsets over the same `source_text_hash`-bound text surface.
  - projection/extraction span offsets must be derived from the same canonical source-text normalization surface bound to `source_text_hash`.
  - if a fixture declares or implies divergent normalization surfaces for projection vs extraction offsets, payload is invalid (`URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID`).
- Extraction-fidelity packet schema lock is frozen:
  - `schema = "adeu_projection_alignment_fidelity@0.1"`
  - required top-level fields:
    - `source_text_hash`
    - `projection_alignment_hash`
    - `fidelity_input_hash`
    - `fidelity_summary`
    - `fidelity_items`
  - `fidelity_summary` required fields:
    - `total_checks`
    - `compatible_checks`
    - `drift_checks`
    - `counts_by_code`
    - `counts_by_status`
    - `counts_by_severity`
- Schema-export convention lock is frozen:
  - `adeu_projection_alignment_fidelity_input@0.1` must be exported as authoritative schema JSON.
  - authoritative path:
    - `packages/adeu_core_ir/schema/adeu_projection_alignment_fidelity_input.v0_1.json`
  - mirror path:
    - `spec/adeu_projection_alignment_fidelity_input.schema.json`
  - `adeu_projection_alignment_fidelity@0.1` must be exported as authoritative schema JSON.
  - authoritative path:
    - `packages/adeu_core_ir/schema/adeu_projection_alignment_fidelity.v0_1.json`
  - mirror path:
    - `spec/adeu_projection_alignment_fidelity.schema.json`
  - export wiring extends:
    - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
  - export cardinality for this arc is frozen:
    - exactly two new extraction-fidelity schema exports are added in `export_schema.py` (`fidelity_input`, `fidelity_packet`).
- Fidelity hash lock is frozen:
  - `projection_alignment_hash = sha256_canonical_json(strip_created_at_recursive(projection_alignment_payload))`
  - `fidelity_input_hash = sha256_canonical_json(strip_created_at_recursive(fidelity_input_payload))`
  - `strip_created_at_recursive(...)` must reuse the shared deterministic helper used by runtime/stop-gate hashing in prior arcs; ad hoc per-call stripping implementations are forbidden.
  - self-hash field handling is frozen:
    - before computing `projection_alignment_hash`, remove top-level fields named:
      - `projection_alignment_hash`
      - `artifact_hash`
    - before computing `fidelity_input_hash`, remove top-level fields named:
      - `fidelity_input_hash`
      - `artifact_hash`
  - all hash fields are lowercase hex `sha256` length `64` and no prefix.
- Fidelity taxonomy lock is frozen:
  - allowed `fidelity_code` values are exactly:
    - `label_text_mismatch`
    - `span_mismatch`
    - `score_mismatch`
  - allowed `status` values are exactly:
    - `compatible`
    - `drift`
  - allowed `severity` values are exactly:
    - `low`
    - `medium`
    - `high`
- Score-bounding lock is frozen:
  - `projection_score_milli` and `extraction_score_milli` must be integers in `[0, 1000]`.
  - score drift threshold is frozen:
    - `score_delta_milli_threshold = 50`
  - `score_mismatch` reports `drift` iff at least one matched node has:
    - `abs(projection_score_milli - extraction_score_milli) > 50`
  - provider/model-specific calibration curves and relative-score thresholds are out-of-scope in this arc.
  - threshold value changes are out-of-scope in this arc.
- Sorted-multiset normalization lock is frozen:
  - each comparison code uses deterministic key lists over `matched_nodes` sorted lexicographically by `match_id`.
  - multiplicity is preserved (no implicit deduplication).
  - string comparisons are exact and case-sensitive unless explicit normalization is stated.
  - unless explicitly stated, no Unicode normalization or case-folding is applied.
  - missing/null values are payload-invalid unless explicitly permitted by schema.
- Fidelity derivation lock is frozen:
  - `label_text_mismatch`:
    - compare ordered key lists of normalized label strings across matched nodes.
    - normalization is frozen:
      - trim outer ASCII whitespace characters in `[ \t\n\r\f\v]`
      - collapse internal ASCII whitespace runs matching `[ \t\n\r\f\v]+` to one literal space (`" "`)
      - no Unicode normalization and no case-folding
      - non-ASCII whitespace and Unicode-canonical equivalents are treated as distinct (intentional in this arc)
    - `status = compatible` iff normalized projection-label list equals normalized extraction-label list; otherwise `drift`.
    - severity mapping is frozen:
      - `compatible -> low`
      - `drift -> medium`
  - `span_mismatch`:
    - compare ordered key lists of two-element tuples `[start, end]` for projection and extraction spans across matched nodes.
    - span comparison uses exact tuple equality only; fuzzy overlap/intersection heuristics are out-of-scope in this arc.
    - `status = compatible` iff lists are equal; otherwise `drift`.
    - severity mapping is frozen:
      - `compatible -> low`
      - `drift -> high`
  - `score_mismatch`:
    - compare ordered key lists of integer `*_score_milli` values across matched nodes with frozen threshold rule.
    - `status = compatible` iff all per-node absolute deltas are `<= 50`; otherwise `drift`.
    - severity mapping is frozen:
      - `compatible -> low`
      - `drift -> medium`
- Fidelity hash-emission lock is frozen:
  - per `fidelity_code`, define `projection_keys` and `extraction_keys` as normalized ordered key lists used by that code's derivation.
  - hash-input key shapes are frozen by code:
    - `label_text_mismatch`:
      - `projection_keys: List[str]`
      - `extraction_keys: List[str]`
    - `span_mismatch`:
      - `projection_keys: List[[int,int]]` (JSON array of 2-int arrays `[start,end]`)
      - `extraction_keys: List[[int,int]]` (JSON array of 2-int arrays `[start,end]`)
    - `score_mismatch`:
      - `projection_keys: List[int]`
      - `extraction_keys: List[int]`
  - when `status == "drift"`:
    - `expected_hash = sha256_canonical_json(projection_keys)`
    - `observed_hash = sha256_canonical_json(extraction_keys)`
  - when `status == "compatible"`:
    - `expected_hash` and `observed_hash` are omitted.
  - emitted hash strings are lowercase hex `sha256` length `64` and no prefix.
- Fidelity aggregation lock is frozen:
  - exactly one fidelity item is emitted per `fidelity_code` for each selected `source_text_hash`.
  - cross-code grouping/deduplication is forbidden in this arc.
  - `fidelity_summary.total_checks` must equal `len(fidelity_items)`.
- Fidelity summary arithmetic lock is frozen:
  - `fidelity_summary.compatible_checks + fidelity_summary.drift_checks == fidelity_summary.total_checks`.
  - `sum(fidelity_summary.counts_by_code.values()) == fidelity_summary.total_checks`.
  - `sum(fidelity_summary.counts_by_status.values()) == fidelity_summary.total_checks`.
  - `sum(fidelity_summary.counts_by_severity.values()) == fidelity_summary.total_checks`.
  - `counts_by_code` keys are frozen to exactly:
    - `label_text_mismatch`
    - `span_mismatch`
    - `score_mismatch`
  - `counts_by_status` keys are frozen to exactly:
    - `compatible`
    - `drift`
  - `counts_by_severity` keys are members of:
    - `low`
    - `medium`
    - `high`
- Fidelity payload lock is frozen:
  - each `fidelity_items[]` item includes:
    - `fidelity_id`
    - `fidelity_code`
    - `status`
    - `severity`
    - `justification_refs` (deterministically ordered non-empty list)
    - optional `expected_hash`
    - optional `observed_hash`
    - `message` (non-authoritative prose)
- Fidelity-id formation lock is frozen:
  - `justification_refs` must be lexicographically sorted before id hash computation.
  - `fidelity_id` must be deterministic and derived from canonical fidelity content only:
    - `fidelity_id = sha256(canonical_json({"fidelity_code": fidelity_code, "status": status, "severity": severity, "justification_refs": justification_refs, "expected_hash": expected_hash, "observed_hash": observed_hash}))[:16]`
  - random IDs, UUIDs, and insertion-order counters are forbidden for `fidelity_id`.
- Justification-reference lock is frozen:
  - `justification_refs` must use stable evidence references only:
    - `artifact:adeu_projection_alignment@0.1:{source_text_hash}`
    - `artifact:adeu_projection_alignment_fidelity_input@0.1:{source_text_hash}`
  - references must resolve to existing persisted artifacts for the selected source.
  - `justification_refs` entries must be unique within each fidelity item.
  - cardinality is frozen per `fidelity_code`:
    - `label_text_mismatch`: exactly two refs
    - `span_mismatch`: exactly two refs
    - `score_mismatch`: exactly two refs
- Deterministic ordering lock is frozen:
  - `fidelity_items[]` are ordered lexicographically by:
    - `fidelity_code`
    - `fidelity_id`
  - `counts_by_code`, `counts_by_status`, and `counts_by_severity` keys are emitted in lexicographic order.
- Read-authority and mutation lock is frozen:
  - generation reads persisted artifacts only.
  - no materialization/proposer/repair execution is allowed on miss.
  - handlers/builders are read-only and may not mutate canonical ADEU artifacts.
- Non-enforcement lock is frozen:
  - output is evidence-only guidance.
  - output may not assert blocking/pass-fail semantics for production solver execution or trigger policy enforcement side effects.
  - `adeu_projection_alignment_fidelity@0.1` does not include enforcement fields; any emitted enforcement-like field is payload-invalid, including:
    - `enforce`
    - `block`
    - `gate`
    - `allow`
    - `deny`

### Acceptance

- Locked v24 fixtures return schema-valid extraction-fidelity packets for persisted sources.
- Identical persisted inputs replay to byte-identical packets.
- Missing/invalid evidence references fail closed with deterministic error envelopes.

## X2) Deterministic Extraction-Fidelity Projection + Transfer Report Artifact Family

### Goal

Expose deterministic aggregate extraction-fidelity summaries and closeout reporting over persisted extraction-fidelity packets.

### Scope

- Add deterministic extraction-fidelity projection over packet outputs.
- Extend transfer-report evidence with packet/projection/replay summaries.

### Locks

- Projection endpoint activation lock is frozen:
  - `GET /urm/extraction-fidelity/projection` is implemented in `X2`, not `X1`.
  - `X1` PRs may ship source-packet endpoint only; projection endpoint activation is deferred to `X2` implementation PR.
- X2 implementation slicing lock is frozen:
  - this `X2` API/runtime slice implements deterministic projection builder + `GET /urm/extraction-fidelity/projection`.
  - transfer-report markdown renderer/script/output generation (`docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md`) may ship in a dedicated `X2` docs slice before `v24` closeout.
- Extraction-fidelity projection schema lock is frozen:
  - `schema = "projection_alignment_fidelity_projection.vnext_plus24@1"`
  - required top-level fields:
    - `source_count`
    - `fidelity_item_count`
    - `fidelity_counts_by_code`
    - `fidelity_counts_by_status`
    - `fidelity_counts_by_severity`
  - projection is reporting-only and may not mutate source artifacts.
- Projection input-set lock is frozen:
  - projection input set is exactly the deterministic `source_text_hash` set from:
    - `apps/api/fixtures/extraction_fidelity/vnext_plus24_catalog.json`
  - projection builders must consume packet outputs for this set only; undeclared source discovery is out-of-scope.
  - projection must invoke the same in-process packet builder contract used by `X1` for each source in lexicographic order; alternate packet-generation paths are forbidden.
  - projection API/runtime may not read precomputed packet fixture files as authoritative inputs; persisted fixture captures are for deterministic stop-gate replay only.
- Projection totality lock is frozen:
  - projection is total over the frozen catalog source set and may not skip sources.
  - any missing upstream artifact for any source fails projection generation closed with:
    - `URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND`
  - any invalid upstream payload for any source fails projection generation closed with:
    - `URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID`
- Projection count-definition lock is frozen:
  - `source_count` equals the count of unique source keys in the projection input set.
  - `fidelity_item_count` equals the deterministic sum of `len(fidelity_items)` across all included packets.
  - `sum(fidelity_counts_by_code.values()) == fidelity_item_count`.
  - `sum(fidelity_counts_by_status.values()) == fidelity_item_count`.
  - `sum(fidelity_counts_by_severity.values()) == fidelity_item_count`.
  - `fidelity_counts_by_code` keys are emitted in lexicographic order.
  - `fidelity_counts_by_status` keys are emitted in lexicographic order.
  - `fidelity_counts_by_severity` keys are emitted in lexicographic order.
- Transfer report lock is frozen:
  - output path:
    - `docs/EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "extraction_fidelity_transfer_report.vnext_plus24@1"`
    - `vnext_plus24_manifest_hash`
    - `coverage_summary`
    - `extraction_fidelity_packet_summary`
    - `extraction_fidelity_projection_summary`
    - `replay_summary`
  - `replay_summary.runtime_observability` required keys are:
    - `elapsed_ms`
    - `total_fixtures`
    - `total_replays`
    - `bytes_hashed_per_replay`
    - `bytes_hashed_total`
- Replay boundary lock is frozen:
  - no live provider calls are permitted in deterministic extraction-fidelity acceptance paths.

### Acceptance

- Extraction-fidelity packet/projection fixtures replay to byte-identical outputs for identical persisted inputs.
- Extraction-fidelity transfer-report payload is deterministic and schema-valid.

## X3) Stop-Gate Determinism Metrics for Extraction-Fidelity Payloads

### Goal

Make extraction-fidelity determinism measurable and reproducible with additive stop-gate metrics for `vNext+24 -> vNext+25`.

### Scope

- Add manifest-driven fixture accountability for extraction-fidelity outputs.
- Extend additive `stop_gate_metrics@1` with v24 extraction-fidelity keys.
- Preserve v16-v23 continuity metrics and thresholds.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus24_manifest.json`
  - schema:
    - `stop_gate.vnext_plus24_manifest@1`
  - required:
    - `replay_count == 3`
- Surface enumeration completeness lock is frozen:
  - frozen v24 extraction-fidelity `surface_id` set is exactly:
    - `adeu.extraction_fidelity.packet`
    - `adeu.extraction_fidelity.projection`
  - manifest fixture `surface_id` values must be members of this frozen set only.
- Manifest shape lock is frozen:
  - required fixture lists are:
    - `extraction_fidelity_packet_fixtures`
    - `extraction_fidelity_projection_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
  - each packet fixture entry must declare explicit upstream refs:
    - `projection_alignment_path`
    - `projection_alignment_fidelity_input_path`
  - missing required upstream refs are fixture-invalid and fail closed.
- Manifest-catalog membership lock is frozen:
  - every packet fixture entry `source_text_hash` must be present in:
    - `apps/api/fixtures/extraction_fidelity/vnext_plus24_catalog.json`
  - fixture entry upstream refs must match catalog refs exactly for that source:
    - `projection_alignment_path`
    - `projection_alignment_fidelity_input_path`
  - mismatched or shadow-catalog fixture wiring is fixture-invalid and fails closed:
    - `URM_ADEU_EXTRACTION_FIDELITY_FIXTURE_INVALID`
- Run-reference key lock is frozen:
  - required run keys are:
    - `extraction_fidelity_packet_fixtures[].runs[].extraction_fidelity_packet_path`
    - `extraction_fidelity_projection_fixtures[].runs[].extraction_fidelity_projection_path`
  - missing required run keys are fixture-invalid and fail closed.
- Fixture-path semantics lock is frozen:
  - `*_path` inputs are captured deterministic JSON artifact payloads from the v24 in-process harness (no live-network dependency), not ad hoc derived summaries.
  - captured payloads include the full artifact JSON body including top-level `schema`.
  - `extraction_fidelity_packet_path` captures `adeu_projection_alignment_fidelity@0.1` payloads.
  - `extraction_fidelity_projection_path` captures `projection_alignment_fidelity_projection.vnext_plus24@1` payloads.
  - capture order is frozen lexicographically by `source_text_hash`.
  - capture envelope stores only:
    - parsed JSON response/artifact payload (canonicalized on write),
    - deterministic harness metadata required for traceability.
  - response headers are excluded from capture envelopes and determinism hash inputs.
- Non-empty evidence floor lock is frozen:
  - at least one locked v24 packet fixture must emit `total_checks > 0`.
  - at least one locked fixture must emit one or more checks in:
    - `label_text_mismatch`
    - `span_mismatch`
    - `score_mismatch`
  - at least one locked fixture must emit one or more items with:
    - `status == "drift"`
  - at least one locked fixture must emit one or more items with:
    - `status == "compatible"`
  - at least one locked fixture must emit one or more `score_mismatch` items with:
    - `status == "drift"`
- Determinism metric computation lock is frozen:
  - determinism hash input is canonical JSON from loaded captured payloads (`sha256_canonical_json(load_json(path))`), not raw bytes.
  - hash projection excludes `created_at` fields recursively at any depth in captured JSON; no other fields are excluded.
  - replay byte observability is computed over canonical hash inputs after `created_at` exclusion only:
    - `bytes_hashed_per_replay = sum(len(canonical_json_bytes(payload_i)))` over all hashed payloads in one replay.
    - `bytes_hashed_total = replay_count * bytes_hashed_per_replay`.
  - replay byte observability surface scope is frozen:
    - for `extraction_fidelity_packet_fixtures`, byte counters include captured packet payload bytes only.
    - for `extraction_fidelity_projection_fixtures`, byte counters include captured projection payload bytes only.
    - upstream dependency payload bytes are excluded from these counters.
  - replay exactly `N=3` times per fixture.
  - fixture passes only when all replay hashes match.
  - `pct = 100 * passed / total`.
- Deterministic performance-optimization lock is frozen:
  - v18 bounded-optimization patterns may be applied to v24 extraction-fidelity hashing paths.
  - allowed optimization includes deterministic sub-component pre-hashing/caching keyed by canonical input payload hashes.
  - allowed optimization includes concurrent replay execution for `N=3` only when:
    - each replay runs in an isolated process with deterministic environment lock enforced (`TZ=UTC`, `LC_ALL=C`),
    - fixture execution order is seeded from frozen lexicographic fixture order,
    - replay result aggregation is reduced in deterministic lexicographic fixture/run order.
  - CI stop-gate entrypoints must default to this concurrent replay mode for v24 extraction-fidelity fixtures to preserve v18 runtime-budget continuity constraints.
  - optimization may not alter fixture selection, replay count, hash projection rules, or pass/fail semantics.
- Reusable deterministic-parallel helper lock is frozen:
  - extracting a shared deterministic concurrent-replay helper is allowed in this arc.
  - helper behavior must preserve deterministic environment isolation, lexicographic ordering, replay cardinality, and pass/fail semantics unchanged.
  - helper reuse across v20/v21/v22/v23/v24 stop-gate deterministic replay paths is allowed.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_extraction_fidelity_packet_determinism_pct`
  - `artifact_extraction_fidelity_projection_determinism_pct`
- Metric-key cardinality lock is frozen:
  - v24 adds exactly two extraction-fidelity determinism keys to `stop_gate_metrics@1` in this arc.
  - additional v24 extraction-fidelity metric-key additions are out-of-scope unless an explicit follow-on lock approves them.
- Continuity-threshold lock is frozen:
  - v16/v17/v18/v19/v20/v21/v22/v23 thresholds remain required and unchanged in v24 closeout.
  - this includes v18 tooling budget continuity:
    - `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0`
  - v24 closeout evidence must include an explicit runtime-observability comparison row against v23 canonical closeout baseline.
- Threshold lock is frozen for `vNext+24 -> vNext+25`:
  - `artifact_extraction_fidelity_packet_determinism_pct == 100.0`
  - `artifact_extraction_fidelity_projection_determinism_pct == 100.0`
  - v16/v17/v18/v19/v20/v21/v22/v23 continuity thresholds remain required and unchanged.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus24_manifest_hash`.
  - mismatch fails closed.

### Acceptance

- Extraction-fidelity coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+24` thresholds.
- Locked fixtures prove non-empty detector behavior (not all-zero extraction-fidelity outputs).

## X4) Non-Enforcement and No-Mutation/No-Provider-Expansion Continuity

### Goal

Keep v24 extraction-fidelity activation strictly read-only and non-enforcing; prevent drift into proposer/provider, mutation, or policy-execution semantics.

### Scope

- Freeze explicit continuity constraints for `vNext+24 -> vNext+25`.
- Keep extraction-fidelity surfaces independent from proposer activation.
- Preserve v14-v23 operational and trust boundaries.

### Locks

- No-provider-expansion lock is frozen:
  - this arc introduces no proposer/provider surfaces.
  - provider matrix/surface-set continuity from `vNext+14` remains unchanged.
- No-provider-calls guard lock is frozen:
  - extraction-fidelity handlers/builders must be covered by deterministic tests using a `NoProviderCallsGuard` runtime helper.
  - guard behavior is fail-closed: any provider client entrypoint invocation in guarded paths fails the test.
  - guard coverage must also enforce outbound-network denial in test context (socket-level fail-closed boundary) so provider/network calls cannot bypass high-level client patching.
- No-materialization-calls guard lock is frozen:
  - extraction-fidelity handlers/builders must be covered by deterministic fail-closed test guards over policy/materialization execution entrypoints.
  - any policy/materialization invocation from guarded extraction-fidelity paths fails the test.
  - this guard requirement is independent of provider-call guards and must be asserted separately.
- Runtime non-enforcement context lock is frozen:
  - extraction-fidelity endpoint handlers/builders must execute inside a runtime non-enforcement context that disables write/policy/materialization dispatch in extraction-fidelity paths.
  - runtime context violations fail closed with deterministic request-invalid errors.
- No-mutation lock is frozen:
  - extraction-fidelity entrypoints/builders must not write canonical ADEU artifacts or mutate persisted concept/core-ir/lane/integrity/cross-ir/normative-advice/trust/semantics-candidate artifacts.
  - canonical artifacts remain generated by existing materialization/closeout flows only.
- No-mutation verification lock is frozen:
  - deterministic no-mutation tests must compare pre/post snapshots over the v24 fixture-backed mutable surface only:
    - `apps/api/fixtures/extraction_fidelity/vnext_plus24_catalog.json`
    - all artifact JSON files referenced by that catalog
    - `apps/api/fixtures/stop_gate/vnext_plus24_manifest.json`
    - all extraction-fidelity artifact JSON files referenced by that manifest
  - snapshot comparison is hash-based over canonical file contents (`sha256_canonical_json(load_json(path))`) and must remain byte-identical for read-only calls.
- Non-enforcement verification lock is frozen:
  - extraction-fidelity generation tests must assert no policy/materialization execution endpoints are invoked.
  - tests must fail closed when guarded policy/materialization entrypoints are invoked.
  - extraction-fidelity payloads may contain evidence recommendations only and no enforcement flags.
- S3b deferral lock is frozen:
  - core-ir proposer activation (`S3b`) requires separate lock docs and explicit continuity releases.
- S9 trigger-boundary lock is frozen:
  - provider parity maintenance path (`S9`) remains trigger-based fallback.
  - v24 extraction-fidelity scope may not silently absorb S9 provider-parity remediation scope.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.
  - extraction-fidelity surfaces may expose stored trust evidence only.

### Acceptance

- Tests prove extraction-fidelity code paths do not invoke provider clients or materialization flows.
- Tests include `NoProviderCallsGuard` coverage that fails closed on provider client entrypoint invocation.
- No mutation side effects are observed for extraction-fidelity calls on locked fixtures.
- No-mutation tests include deterministic pre/post storage snapshot hash equality assertions.
- Tests prove extraction-fidelity output remains non-enforcing.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_EXTRACTION_FIDELITY_*` additions in this arc are frozen:
  - `URM_ADEU_EXTRACTION_FIDELITY_REQUEST_INVALID`
  - `URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND`
  - `URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID`
  - `URM_ADEU_EXTRACTION_FIDELITY_FIXTURE_INVALID`
  - `URM_ADEU_EXTRACTION_FIDELITY_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_EXTRACTION_FIDELITY_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_EXTRACTION_FIDELITY_REQUEST_INVALID` for unsupported source modes and ambiguous/non-unique deterministic source resolution.
  - use `URM_ADEU_EXTRACTION_FIDELITY_REQUEST_INVALID` for runtime non-enforcement-context violations in extraction-fidelity endpoints.
  - use `URM_ADEU_EXTRACTION_FIDELITY_FIXTURE_INVALID` for manifest/run-key/surface-id/cap violations.
  - use `URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID` for emitted extraction-fidelity payload schema/content validation failures.
  - use `URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND` for persisted-lookup misses in extraction-fidelity inputs.
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v24 extraction-fidelity codes are additive and must not remove prior legacy error identifiers.

## Commit Plan (Small Green Commits)

1. `runtime: add deterministic extraction-fidelity packet builder over persisted alignment evidence`
2. `api: add read-only extraction-fidelity surface and deterministic response envelopes`
3. `metrics: add vnext_plus24 manifest and additive extraction-fidelity determinism keys`
4. `docs: add vnext_plus24 extraction-fidelity transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus24 replay fixtures, NoProviderCallsGuard coverage, non-enforcement checks, and no-mutation assertions`

## Intermediate Stage Preconditions and Outputs (Draft)

Before implementation PR1 for `vNext+24`, confirm v23 preconditions are frozen/merged and prepare v24 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS23.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/SEMANTICS_V4_TRANSFER_REPORT_vNEXT_PLUS23.md` (precondition semantics-candidate transfer baseline; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/extraction_fidelity/vnext_plus24_catalog.json`
4. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus24_manifest.json`
5. draft packet fixture scaffold for `adeu_projection_alignment_fidelity@0.1`
6. draft transfer-report schema/renderer for `extraction_fidelity_transfer_report.vnext_plus24@1`
7. deterministic env helper hook-up for v24 stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
8. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS24.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `X1`-`X4` merged with green CI.
- `artifact_extraction_fidelity_packet_determinism_pct == 100.0` on locked fixtures.
- `artifact_extraction_fidelity_projection_determinism_pct == 100.0` on locked fixtures.
- `vNext+24 -> vNext+25` frozen thresholds all pass.
- v16/v17/v18/v19/v20/v21/v22/v23 continuity metrics remain present and at threshold (`100.0`).
- v24 closeout evidence includes runtime-observability comparison rows against v23 canonical baseline.
- no solver semantics contract delta and no trust-lane regression introduced.
- provider-parity continuity lock remains unchanged (no proposer surface expansion).
- all existing stop-gate tracked `vNext+6` through `vNext+23` metrics remain at threshold.
- `vNext+17` through `vNext+23` closeout evidence remains green and reproducible.
