# Locked Continuation vNext+23 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS22.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS22.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+22` (`T1`-`T4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS22.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` post-`vNext+22` progression leaves `vNext+23+` primarily on `S8`; this draft selects `vNext+23 = Path S8` (solver semantics v4 expansion, evidence-first candidate lane).
- `vNext+16` + `vNext+17` integrity families, `vNext+18` tooling continuity, `vNext+19` read-surface activation, `vNext+20` cross-IR coherence bridges, `vNext+21` normative-advice read surfaces, and `vNext+22` proof/trust lane starter are stable baselines.
- This arc is reserved for deterministic, read-only, non-default semantics-v4 candidate activation only:
  - deterministic semantics-v4 candidate comparison packet contract freeze first
  - deterministic candidate projection + transfer-report artifact family second
  - additive stop-gate determinism metrics for candidate payload stability third
  - explicit non-enforcement and no-mutation/no-provider-expansion continuity fourth

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for default runtime behavior in this arc.
- This arc introduces an explicit versioned follow-on candidate contract lane (`SEMANTICS_v4`) but does not switch default production semantics from v3.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS18.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS19.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS20.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS21.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS22.md` remain authoritative for prior baseline semantics.
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
- Upstream dependency continuity lock is frozen:
  - v23 semantics-v4 candidate comparison depends on persisted upstream evidence from:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - persisted `adeu_trust_invariant_packet@0.1` payloads for matched pairs
    - persisted baseline semantics diagnostics captures (`semantics_diagnostics@1`) for matched pairs
    - persisted candidate semantics diagnostics captures (`semantics_diagnostics@1`) for matched pairs
  - missing upstream evidence is artifact-not-found and fails closed.
  - best-effort fallback, live recomputation, and undeclared input substitution are out-of-scope for deterministic acceptance paths.
- Candidate-source provenance lock is frozen:
  - deterministic v23 acceptance paths treat both `semantics_v3_path` and `semantics_v4_candidate_path` as explicit persisted evidence inputs.
  - runtime v23 endpoints/builders may not synthesize, infer, or live-recompute candidate diagnostics captures in deterministic acceptance paths.
  - baseline captures (`semantics_v3_path`) are from existing default v3 semantics diagnostics behavior.
  - candidate captures (`semantics_v4_candidate_path`) are from an explicit v4-candidate fixture capture lane for this arc and are read-only evidence inputs.
  - candidate-source ambiguity for a locked fixture is fixture-invalid and fails closed.
- Default-runtime semantics continuity lock is frozen:
  - existing default runtime semantics behavior remains v3 in this arc.
  - v4 candidate artifacts are read-only evidence and comparison outputs only.

## Arc Scope (Draft Lock)

This arc proposes Path `S8` thin slice only:

1. `V1` Deterministic semantics-v4 candidate comparison packet contract freeze
2. `V2` Deterministic semantics-v4 candidate projection + transfer-report artifact family
3. `V3` Additive stop-gate determinism metrics for semantics-v4 candidate payload stability
4. `V4` Explicit non-enforcement and no-mutation/no-provider-expansion continuity for `vNext+23 -> vNext+24`

Out-of-scope note:

- Path `S3b` (core-ir proposer activation) is not in this arc.
- Provider matrix/surface expansion is not in this arc.
- This arc does not switch default runtime semantics from v3 to v4.
- This arc does not alter v3 `STRICT`/`LAX` mode mapping behavior for production check reports.
- Automatic policy execution/auto-remediation from semantics-v4 candidate output is not in this arc.
- DB-backed semantics-v4 candidate persistence migrations/new SQL tables are not in this arc.
- Payload offloading via blob-store/pre-signed URLs is not in this arc.
- Sparse fieldset/query-driven partial payload retrieval is not in this arc.
- Mandatory frontend build-system expansion is not in this arc; optional minimal rendering is allowed only if it does not introduce a new frontend build-system dependency.
- Semantics-v4 acknowledgement/dismissal persistence and mutation endpoints are not in this arc.
- Theorem-prover integration and proof-checked obligations beyond existing infrastructure evidence are not in this arc.
- Inline formula/body diff snippets in v23 comparison payloads are not in this arc.
- Solver-binary deterministic seed orchestration for out-of-band capture-generation pipelines is not in this arc.
- Shadow-run performance/cost ratio metrics (for example `v4_vs_v3_cpu_ms_ratio`) are not in this arc.
- Drift-acceptance ledger schema/materialization is not in this arc.

## V1) Deterministic Semantics-v4 Candidate Comparison Packet Contract Freeze

### Goal

Emit deterministic, read-only, non-enforcing semantics-v4 candidate comparison packets derived from persisted baseline/candidate diagnostics evidence.

### Scope

- Add deterministic comparison packet generation over persisted dual semantics diagnostics evidence.
- Keep output schema-validated and explicitly non-authoritative.
- Resolve concept/core-ir pairs from fixture-backed catalogs only in this arc.
- Preserve explicit justification references for every comparison item.

### Locks

- Comparison source authority lock is frozen:
  - generation in this arc is fixture-backed only from persisted artifacts:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - persisted `adeu_trust_invariant_packet@0.1` payloads for matched pairs
    - persisted `semantics_diagnostics@1` baseline captures (`semantics_v3_path`) for matched pairs
    - persisted `semantics_diagnostics@1` candidate captures (`semantics_v4_candidate_path`) for matched pairs
  - filesystem scans, DB discovery, and undeclared directories are out-of-scope.
- Dual-diagnostics dependency lock is frozen:
  - comparison builders must load all required inputs:
    - pair context from `cross_ir.vnext_plus20_catalog@1`
    - matched trust-invariant packet from `adeu_trust_invariant_packet@0.1`
    - matched baseline diagnostics from `semantics_v3_path`
    - matched candidate diagnostics from `semantics_v4_candidate_path`
  - operation without any required input is request-invalid and fails closed.
- Candidate-lane generation boundary lock is frozen:
  - `V1/V2` runtime surfaces consume persisted baseline/candidate diagnostics captures only.
  - deterministic acceptance paths do not define or execute the capture-generation mechanism for v4 candidate diagnostics.
  - capture-generation implementation details (flags/backend wiring) are out-of-scope for this arc lock and must not be backfilled by runtime best-effort fallback.
  - solver-binary seed controls (for example `Z3_RANDOM_SEED`) are capture-generation concerns and are out-of-scope for v23 runtime/stop-gate acceptance locks.
- Endpoint-set lock is frozen:
  - `GET /urm/semantics-v4/pairs/{source_text_hash}/{core_ir_artifact_id}/{concept_artifact_id}` (`V1` implementation scope)
  - `GET /urm/semantics-v4/projection` (`V2` implementation scope; deferred from this `V1` PR slice)
- Persistence-model lock is frozen:
  - `V1/V2` surfaces in this arc are fixture-backed over persisted JSON artifacts/capture catalogs.
  - no new SQL storage tables or schema migrations are introduced for semantics-v4 candidate retrieval/projection in v23.
  - DB-backed semantics-v4 candidate retrieval/projection is deferred to a later lock.
- Pair-resolution identity lock is frozen:
  - deterministic pair identity and uniqueness key is exactly:
    - `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`
  - pair route resolution is exact-match on this tuple only.
  - non-unique/ambiguous pair entries in the fixture-backed catalog are request-invalid and fail closed.
- Pair-endpoint miss-mode lock is frozen:
  - when tuple `(source_text_hash, core_ir_artifact_id, concept_artifact_id)` is not present in catalog:
    - `URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND`
  - when tuple is present but matched trust/baseline/candidate artifact is missing:
    - `URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND`
  - when tuple and upstream artifacts are present but payload linkage/validation fails:
    - `URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID`
- Candidate packet schema lock is frozen:
  - `schema = "adeu_semantics_v4_candidate_packet@0.1"`
  - required top-level fields:
    - `source_text_hash`
    - `core_ir_artifact_id`
    - `concept_artifact_id`
    - `trust_invariant_packet_hash`
    - `baseline_semantics_hash`
    - `candidate_semantics_hash`
    - `comparison_summary`
    - `comparison_items`
  - `comparison_summary` required fields:
    - `total_comparisons`
    - `compatible_checks`
    - `drift_checks`
    - `counts_by_code`
    - `counts_by_severity`
    - `counts_by_status`
- Schema-export convention lock is frozen:
  - `adeu_semantics_v4_candidate_packet@0.1` must be exported as authoritative schema JSON.
  - authoritative path:
    - `packages/adeu_core_ir/schema/adeu_semantics_v4_candidate_packet.v0_1.json`
  - mirror path:
    - `spec/adeu_semantics_v4_candidate_packet.schema.json`
  - export wiring extends:
    - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- Semantics hash lock is frozen:
  - `trust_invariant_packet_hash = sha256_canonical_json(strip_created_at_recursive(trust_invariant_packet_payload))`
  - `baseline_semantics_hash = sha256_canonical_json(strip_created_at_recursive(semantics_v3_payload))`
  - `candidate_semantics_hash = sha256_canonical_json(strip_created_at_recursive(semantics_v4_candidate_payload))`
  - all hash fields are lowercase hex `sha256` length `64` and no prefix.
- Baseline/candidate payload shape lock is frozen:
  - both baseline and candidate payloads must satisfy:
    - `schema = "semantics_diagnostics@1"`
    - required top-level fields present (`artifact_ref`, `records`, `semantics_diagnostics_hash`)
    - each `records[]` item satisfies required `semantics_diagnostics@1` keys, including:
      - `status`
      - `assurance`
      - `request_hash`
      - `formula_hash`
      - `witness_refs`
    - `records[]` minimal schema required by v23 comparison logic is frozen:
      - `status`: string member of frozen v3 status set.
      - `assurance`: string member of frozen assurance set.
      - `request_hash`: lowercase hex `sha256` length `64`.
      - `formula_hash`: lowercase hex `sha256` length `64`.
      - `witness_refs`: list (may be empty); each entry requires:
        - `assertion_name`: non-empty string
        - `object_id`: string or `null`
        - `json_path`: string or `null`
    - any deviation from this minimal `records[]` contract is payload-invalid:
      - `URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID`
    - `records` list deterministically ordered per persisted capture
  - baseline and candidate payloads for a selected pair must share identical `artifact_ref` by exact string equality.
  - route-to-artifact binding is fixture-backed only for this arc:
    - selected tuple `(source_text_hash, core_ir_artifact_id, concept_artifact_id)` must resolve to exactly one matched baseline/candidate artifact pair in declared persisted inputs.
    - swapped/mismatched artifact captures for the selected tuple are payload-invalid.
  - `semantics_diagnostics_hash` linkage is strict:
    - for each baseline/candidate payload, recompute `semantics_diagnostics_hash` from canonical JSON after removing the top-level `semantics_diagnostics_hash` field.
    - recomputed value must equal embedded `semantics_diagnostics_hash`; mismatch is payload-invalid.
- Status taxonomy continuity lock is frozen:
  - candidate diagnostics statuses in this arc must remain members of the v3 status set:
    - `SAT`
    - `UNSAT`
    - `UNKNOWN`
    - `TIMEOUT`
    - `INVALID_REQUEST`
    - `ERROR`
  - introducing new status labels is out-of-scope in this arc.
- Assurance taxonomy continuity lock is frozen:
  - candidate diagnostics assurance values in this arc must remain members of the frozen set:
    - `kernel_only`
    - `solver_backed`
    - `proof_checked`
  - introducing new assurance labels is out-of-scope in this arc.
- Comparison taxonomy lock is frozen:
  - allowed `comparison_code` values are exactly:
    - `STATUS_SET_CONTINUITY_REVIEW`
    - `ASSURANCE_SET_CONTINUITY_REVIEW`
    - `REQUEST_FORMULA_HASH_CONTINUITY_REVIEW`
    - `WITNESS_REF_STRUCTURE_REVIEW`
  - allowed `status` values are exactly:
    - `compatible`
    - `drift`
  - allowed `severity` values are exactly:
    - `low`
    - `medium`
    - `high`
- Sorted-multiset normalization lock is frozen:
  - `sorted multiset` means:
    - map each source value to its frozen comparison key tuple for the active `comparison_code`.
    - preserve multiplicity (no deduplication), then sort keys lexicographically and compare ordered list equality.
  - string-key comparisons are exact and case-sensitive (no Unicode normalization or case folding).
  - missing/null values normalize only where explicitly stated by this arc; otherwise payload-invalid.
  - witness duplicate normalization exception is frozen:
    - for `WITNESS_REF_STRUCTURE_REVIEW` only, identical witness tuples are deduplicated within each individual `records[]` item before cross-record multiset aggregation.
    - multiplicity across distinct records remains preserved.
- Comparison derivation lock is frozen:
  - `STATUS_SET_CONTINUITY_REVIEW`:
    - compare sorted multisets of normalized status tokens between baseline and candidate.
    - status-token normalization is frozen:
      - `UNKNOWN -> UNKNOWN_OR_TIMEOUT`
      - `TIMEOUT -> UNKNOWN_OR_TIMEOUT`
      - all other status tokens unchanged.
    - `UNKNOWN_OR_TIMEOUT` is comparison-only normalization state and must never appear in emitted `records[].status` payload values.
    - `status = compatible` iff normalized multisets are equal; otherwise `drift`.
    - severity mapping is deterministic and frozen:
      - `compatible -> low`
      - `drift -> high`
  - `ASSURANCE_SET_CONTINUITY_REVIEW`:
    - compare sorted multisets of `records[].assurance` between baseline and candidate.
    - `records[].assurance` values are exact string members of the frozen assurance set and are compared case-sensitively.
    - `status = compatible` iff multisets are equal; otherwise `drift`.
    - severity mapping:
      - `compatible -> low`
      - `drift -> medium`
  - `REQUEST_FORMULA_HASH_CONTINUITY_REVIEW`:
    - compare sorted multisets of `(record.request_hash, record.formula_hash)` tuples across all records between baseline and candidate.
    - `record.request_hash` and `record.formula_hash` are required lowercase `sha256` hex length `64`; missing/invalid values are payload-invalid.
    - `status = compatible` iff multisets are equal; otherwise `drift`.
    - severity mapping:
      - `compatible -> low`
      - `drift -> high`
  - `WITNESS_REF_STRUCTURE_REVIEW`:
    - compare sorted multisets of witness-ref tuples `(assertion_name, object_id_or_empty, json_path_or_empty)` across all records between baseline and candidate.
    - witness refs are extracted only from `records[].witness_refs[]`; recursive traversal of other evidence fields is forbidden.
    - each witness entry must satisfy `semantics_diagnostics@1` witness shape (`assertion_name`, `object_id`, `json_path`); missing/invalid entries are payload-invalid.
    - tuple mapping is frozen:
      - `assertion_name = witness_ref.assertion_name`
      - `object_id_or_empty = witness_ref.object_id if not null else ""`
      - `json_path_or_empty = witness_ref.json_path if not null else ""`
    - within-record dedup timing is frozen:
      - deduplication occurs after tuple mapping and before appending tuple keys to the per-record witness key list.
    - within each single record, identical tuples are deduplicated before global multiset aggregation.
    - `status = compatible` iff multisets are equal; otherwise `drift`.
    - severity mapping:
      - `compatible -> low`
      - `drift -> medium`
- Comparison hash-emission lock is frozen:
  - per `comparison_code`, define `baseline_keys` and `candidate_keys` as the normalized sorted multiset key lists used by the active derivation check.
  - hash-input structure for `baseline_keys`/`candidate_keys` is frozen:
    - `STATUS_SET_CONTINUITY_REVIEW`: JSON array of strings.
    - `ASSURANCE_SET_CONTINUITY_REVIEW`: JSON array of strings.
    - `REQUEST_FORMULA_HASH_CONTINUITY_REVIEW`: JSON array of 2-element arrays `[request_hash, formula_hash]`.
    - `WITNESS_REF_STRUCTURE_REVIEW`: JSON array of 3-element arrays `[assertion_name, object_id_or_empty, json_path_or_empty]`.
  - when `status == "drift"`:
    - `expected_hash = sha256_canonical_json(baseline_keys)`
    - `observed_hash = sha256_canonical_json(candidate_keys)`
  - when `status == "compatible"`:
    - `expected_hash` and `observed_hash` are omitted.
  - emitted hash strings are lowercase hex `sha256` length `64` with no prefix.
- Comparison aggregation lock is frozen:
  - exactly one comparison item is emitted per `comparison_code` for each selected pair.
  - cross-code grouping/deduplication is forbidden in this arc.
  - `comparison_summary.total_comparisons` must equal `len(comparison_items)`.
- Comparison payload lock is frozen:
  - each `comparison_items[]` item includes:
    - `comparison_id`
    - `comparison_code`
    - `status`
    - `severity`
    - `justification_refs` (deterministically ordered non-empty list)
    - optional `expected_hash`
    - optional `observed_hash`
    - `message` (non-authoritative prose)
- Comparison-id formation lock is frozen:
  - `justification_refs` must be lexicographically sorted before id hash computation.
  - `comparison_id` must be deterministic and derived from canonical comparison content only:
    - `comparison_id = sha256(canonical_json({"comparison_code": comparison_code, "status": status, "severity": severity, "justification_refs": justification_refs, "expected_hash": expected_hash, "observed_hash": observed_hash}))[:16]`
  - random IDs, UUIDs, and insertion-order counters are forbidden for `comparison_id`.
- Comparison-id continuity lock is frozen:
  - `comparison_id` values in this arc are stable foreign-key candidates for future drift-acceptance workflows.
  - v23 introduces no acceptance/dismiss mutation semantics or persistence schema for these ids.
- Justification-reference lock is frozen:
  - `justification_refs` must use stable evidence references only:
    - `artifact:adeu_trust_invariant_packet@0.1:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}`
    - `artifact:semantics_diagnostics@1:v3:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}`
    - `artifact:semantics_diagnostics@1:v4_candidate:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}`
  - references must resolve to existing persisted artifacts for the selected pair.
  - cardinality is frozen per `comparison_code`:
    - `STATUS_SET_CONTINUITY_REVIEW`: exactly two refs (`v3`, `v4_candidate`)
    - `ASSURANCE_SET_CONTINUITY_REVIEW`: exactly two refs (`v3`, `v4_candidate`)
    - `REQUEST_FORMULA_HASH_CONTINUITY_REVIEW`: exactly two refs (`v3`, `v4_candidate`)
    - `WITNESS_REF_STRUCTURE_REVIEW`: exactly three refs (`trust_invariant`, `v3`, `v4_candidate`)
- Deterministic ordering lock is frozen:
  - `comparison_items[]` are ordered lexicographically by:
    - `comparison_code`
    - `comparison_id`
  - `counts_by_code`, `counts_by_severity`, and `counts_by_status` keys are emitted in lexicographic order.
- Read-authority and mutation lock is frozen:
  - generation reads persisted artifacts only.
  - no materialization/proposer/repair execution is allowed on miss.
  - handlers/builders are read-only and may not mutate canonical ADEU artifacts.
- Non-enforcement lock is frozen:
  - output is evidence-only guidance.
  - output may not assert blocking/pass-fail semantics for production solver execution or trigger policy enforcement side effects.
  - `adeu_semantics_v4_candidate_packet@0.1` does not include enforcement fields; any emitted enforcement-like field is payload-invalid, including:
    - `enforce`
    - `block`
    - `gate`
    - `allow`
    - `deny`

### Acceptance

- Locked v23 fixtures return schema-valid semantics-v4 candidate packets for persisted pairs.
- Identical persisted inputs replay to byte-identical candidate packets.
- Missing/invalid evidence references fail closed with deterministic error envelopes.

## V2) Deterministic Semantics-v4 Candidate Projection + Transfer Report Artifact Family

### Goal

Expose deterministic aggregate semantics-v4 candidate summaries and closeout reporting over persisted comparison packets.

### Scope

- Add deterministic semantics-v4 candidate projection over comparison packets.
- Extend transfer-report evidence with packet/projection/replay summaries.

### Locks

- Projection endpoint activation lock is frozen:
  - `GET /urm/semantics-v4/projection` is implemented in `V2`, not `V1`.
  - `V1` PRs may ship pair-packet endpoint only; projection endpoint activation is deferred to `V2` implementation PR.
- V2 implementation slicing lock is frozen:
  - this `V2` API/runtime slice implements deterministic projection builder + `GET /urm/semantics-v4/projection`.
  - transfer-report markdown renderer/script/output generation (`docs/SEMANTICS_V4_TRANSFER_REPORT_vNEXT_PLUS23.md`) may ship in a dedicated `V2` docs slice before `v23` closeout.
- Candidate projection schema lock is frozen:
  - `schema = "semantics_v4_candidate_projection.vnext_plus23@1"`
  - required top-level fields:
    - `bridge_pair_count`
    - `comparison_item_count`
    - `comparison_counts_by_code`
    - `comparison_counts_by_status`
    - `comparison_counts_by_severity`
  - projection is reporting-only and may not mutate source artifacts.
- Projection input-set lock is frozen:
  - projection input set is exactly the deterministic pair-key set from:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
  - projection builders must consume candidate packets for this set only; undeclared pair discovery is out-of-scope.
  - projection must invoke the same in-process packet builder contract used by `V1` for each pair in lexicographic order; alternate packet-generation paths are forbidden.
  - projection API/runtime may not read precomputed packet fixture files as authoritative inputs; persisted fixture captures are for deterministic stop-gate replay only.
- Projection totality lock is frozen:
  - projection is total over the frozen catalog pair-key set and may not skip pairs.
  - any missing upstream candidate artifact for any catalog pair fails projection generation closed with:
    - `URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND`
  - any invalid upstream candidate payload for any catalog pair fails projection generation closed with:
    - `URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID`
- Projection count-definition lock is frozen:
  - `bridge_pair_count` equals the count of unique pair keys in the projection input set.
  - `comparison_item_count` equals the deterministic sum of `len(comparison_items)` across all included packets.
- Transfer report lock is frozen:
  - output path:
    - `docs/SEMANTICS_V4_TRANSFER_REPORT_vNEXT_PLUS23.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "semantics_v4_transfer_report.vnext_plus23@1"`
    - `vnext_plus23_manifest_hash`
    - `coverage_summary`
    - `candidate_packet_summary`
    - `candidate_projection_summary`
    - `replay_summary`
  - `replay_summary.runtime_observability` required keys are:
    - `elapsed_ms`
    - `total_fixtures`
    - `total_replays`
    - `bytes_hashed_per_replay`
    - `bytes_hashed_total`
- Replay boundary lock is frozen:
  - no live provider calls are permitted in deterministic semantics-v4 candidate acceptance paths.

### Acceptance

- Candidate packet/projection fixtures replay to byte-identical outputs for identical persisted inputs.
- Semantics-v4 transfer-report payload is deterministic and schema-valid.

## V3) Stop-Gate Determinism Metrics for Semantics-v4 Candidate Payloads

### Goal

Make semantics-v4 candidate determinism measurable and reproducible with additive stop-gate metrics for `vNext+23 -> vNext+24`.

### Scope

- Add manifest-driven fixture accountability for semantics-v4 candidate outputs.
- Extend additive `stop_gate_metrics@1` with v23 semantics-v4 candidate keys.
- Preserve v16-v22 continuity metrics and thresholds.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus23_manifest.json`
  - schema:
    - `stop_gate.vnext_plus23_manifest@1`
  - required:
    - `replay_count == 3`
- Surface enumeration completeness lock is frozen:
  - frozen v23 semantics-v4 candidate `surface_id` set is exactly:
    - `adeu.semantics_v4_candidate.packet`
    - `adeu.semantics_v4_candidate.projection`
  - manifest fixture `surface_id` values must be members of this frozen set only.
- Manifest shape lock is frozen:
  - required fixture lists are:
    - `semantics_v4_candidate_packet_fixtures`
    - `semantics_v4_candidate_projection_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
  - each packet fixture entry must declare explicit upstream diagnostics refs:
    - `semantics_v3_path`
    - `semantics_v4_candidate_path`
  - each packet fixture entry must declare deterministic capture-lane provenance fields:
    - `semantics_v3_source_lane == "v3_default"`
    - `semantics_v4_candidate_source_lane == "v4_candidate"`
  - required packet-fixture keys are frozen:
    - `semantics_v4_candidate_packet_fixtures[].semantics_v3_path`
    - `semantics_v4_candidate_packet_fixtures[].semantics_v4_candidate_path`
    - `semantics_v4_candidate_packet_fixtures[].semantics_v3_source_lane`
    - `semantics_v4_candidate_packet_fixtures[].semantics_v4_candidate_source_lane`
  - missing, non-matching, or ambiguous lane provenance fields are fixture-invalid and fail closed.
- Run-reference key lock is frozen:
  - required run keys are:
    - `semantics_v4_candidate_packet_fixtures[].runs[].semantics_v4_candidate_packet_path`
    - `semantics_v4_candidate_projection_fixtures[].runs[].semantics_v4_candidate_projection_path`
  - missing required run keys are fixture-invalid and fail closed.
- Fixture-path semantics lock is frozen:
  - `*_path` inputs are captured deterministic JSON artifact payloads from the v23 in-process harness (no live-network dependency), not ad hoc derived summaries.
  - captured payloads include the full artifact JSON body including top-level `schema`.
  - `semantics_v4_candidate_packet_path` captures `adeu_semantics_v4_candidate_packet@0.1` payloads.
  - `semantics_v4_candidate_projection_path` captures `semantics_v4_candidate_projection.vnext_plus23@1` payloads.
  - capture order is frozen lexicographically by `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`.
  - capture envelope stores only:
    - parsed JSON response/artifact payload (canonicalized on write),
    - deterministic harness metadata required for traceability.
  - response headers are excluded from capture envelopes and determinism hash inputs.
- Non-empty evidence floor lock is frozen:
  - at least one locked v23 candidate fixture must emit `total_comparisons > 0`.
  - at least one locked v23 candidate fixture must emit one or more checks in:
    - `REQUEST_FORMULA_HASH_CONTINUITY_REVIEW`
    - `STATUS_SET_CONTINUITY_REVIEW`
  - at least one locked fixture must emit one or more checks in:
    - `WITNESS_REF_STRUCTURE_REVIEW`
  - at least one locked fixture must emit one or more items with:
    - `status == "drift"`
  - at least one locked fixture must emit one or more items with:
    - `status == "compatible"`
  - at least one locked fixture must emit one or more `WITNESS_REF_STRUCTURE_REVIEW` items with:
    - `status == "drift"`
  - at least one locked fixture must source witness-structure drift from the declared v4-candidate lane payload (not from route swapping or cross-pair mismatch).
- Determinism metric computation lock is frozen:
  - determinism hash input is canonical JSON from loaded captured payloads (`sha256_canonical_json(load_json(path))`), not raw bytes.
  - hash projection excludes `created_at` fields recursively at any depth in captured JSON; no other fields are excluded.
  - replay byte observability is computed over canonical hash inputs after `created_at` exclusion only:
    - `bytes_hashed_per_replay = sum(len(canonical_json_bytes(payload_i)))` over all hashed payloads in one replay.
    - `bytes_hashed_total = replay_count * bytes_hashed_per_replay`.
  - replay byte observability surface scope is frozen:
    - for `semantics_v4_candidate_packet_fixtures`, byte counters include captured packet payload bytes only.
    - for `semantics_v4_candidate_projection_fixtures`, byte counters include captured projection payload bytes only.
    - upstream dependency payload bytes are excluded from these counters.
  - replay exactly `N=3` times per fixture.
  - fixture passes only when all replay hashes match.
  - `pct = 100 * passed / total`.
- Deterministic performance-optimization lock is frozen:
  - v18 bounded-optimization patterns may be applied to v23 semantics-v4 candidate hashing paths.
  - allowed optimization includes deterministic sub-component pre-hashing/caching keyed by canonical input payload hashes.
  - allowed optimization includes concurrent replay execution for `N=3` only when:
    - each replay runs in an isolated process with deterministic environment lock enforced (`TZ=UTC`, `LC_ALL=C`),
    - fixture execution order is seeded from frozen lexicographic fixture order,
    - replay result aggregation is reduced in deterministic lexicographic fixture/run order.
  - CI stop-gate entrypoints must default to this concurrent replay mode for v23 semantics-v4 candidate fixtures to preserve v18 runtime-budget continuity constraints.
  - optimization may not alter fixture selection, replay count, hash projection rules, or pass/fail semantics.
- Reusable deterministic-parallel helper lock is frozen:
  - extracting a shared deterministic concurrent-replay helper is allowed in this arc.
  - helper behavior must preserve deterministic environment isolation, lexicographic ordering, replay cardinality, and pass/fail semantics unchanged.
  - helper reuse across v20/v21/v22/v23 stop-gate deterministic replay paths is allowed.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_semantics_v4_candidate_packet_determinism_pct`
  - `artifact_semantics_v4_candidate_projection_determinism_pct`
- Metric-key cardinality lock is frozen:
  - v23 adds exactly two semantics-v4 candidate determinism keys to `stop_gate_metrics@1` in this arc.
  - additional v23 semantics-v4 candidate metric-key additions are out-of-scope unless an explicit follow-on lock approves them.
- Continuity-threshold lock is frozen:
  - v16/v17/v18/v19/v20/v21/v22 thresholds remain required and unchanged in v23 closeout.
  - this includes v18 tooling budget continuity:
    - `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0`
  - v23 closeout evidence must include an explicit runtime-observability comparison row against v22 canonical closeout baseline.
- Threshold lock is frozen for `vNext+23 -> vNext+24`:
  - `artifact_semantics_v4_candidate_packet_determinism_pct == 100.0`
  - `artifact_semantics_v4_candidate_projection_determinism_pct == 100.0`
  - v16/v17/v18/v19/v20/v21/v22 continuity thresholds remain required and unchanged.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus23_manifest_hash`.
  - mismatch fails closed.

### Acceptance

- Semantics-v4 candidate coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+23` thresholds.
- Locked fixtures prove non-empty detector behavior (not all-zero candidate outputs).

## V4) Non-Enforcement and No-Mutation/No-Provider-Expansion Continuity

### Goal

Keep v23 semantics-v4 candidate activation strictly read-only and non-enforcing; prevent drift into proposer/provider, mutation, or policy-execution semantics.

### Scope

- Freeze explicit continuity constraints for `vNext+23 -> vNext+24`.
- Keep semantics-v4 candidate surfaces independent from proposer activation.
- Preserve v14-v22 operational and trust boundaries.

### Locks

- No-provider-expansion lock is frozen:
  - this arc introduces no proposer/provider surfaces.
  - provider matrix/surface-set continuity from `vNext+14` remains unchanged.
- No-provider-calls guard lock is frozen:
  - semantics-v4 candidate handlers/builders must be covered by deterministic tests using a `NoProviderCallsGuard` runtime helper.
  - guard behavior is fail-closed: any provider client entrypoint invocation in guarded paths fails the test.
  - guard coverage must also enforce outbound-network denial in test context (socket-level fail-closed boundary) so provider/network calls cannot bypass high-level client patching.
- No-materialization-calls guard lock is frozen:
  - semantics-v4 candidate handlers/builders must be covered by deterministic fail-closed test guards over policy/materialization execution entrypoints.
  - any policy/materialization invocation from guarded candidate paths fails the test.
  - this guard requirement is independent of provider-call guards and must be asserted separately.
- Runtime non-enforcement context lock is frozen:
  - semantics-v4 candidate endpoint handlers/builders must execute inside a runtime non-enforcement context that disables write/policy/materialization dispatch in candidate paths.
  - runtime context violations fail closed with deterministic request-invalid errors.
- No-mutation lock is frozen:
  - candidate entrypoints/builders must not write canonical ADEU artifacts or mutate persisted concept/core-ir/lane/integrity/cross-ir/normative-advice/trust artifacts.
  - canonical artifacts remain generated by existing materialization/closeout flows only.
- No-mutation verification lock is frozen:
  - deterministic no-mutation tests must compare pre/post snapshots over the v23 fixture-backed mutable surface only:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - all artifact JSON files referenced by that catalog
    - `apps/api/fixtures/stop_gate/vnext_plus22_manifest.json`
    - all trust-invariant artifact JSON files referenced by that manifest
    - `apps/api/fixtures/stop_gate/vnext_plus23_manifest.json`
    - all semantics-v4 candidate artifact JSON files referenced by that manifest
  - snapshot comparison is hash-based over canonical file contents (`sha256_canonical_json(load_json(path))`) and must remain byte-identical for read-only calls.
- Non-enforcement verification lock is frozen:
  - candidate generation tests must assert no policy/materialization execution endpoints are invoked.
  - tests must fail closed when guarded policy/materialization entrypoints are invoked.
  - candidate payloads may contain evidence recommendations only and no enforcement flags.
- Default-v3 continuity lock is frozen:
  - existing default runtime semantics behavior remains v3 after this arc.
  - existing semantics diagnostics endpoints keep existing v3 contract behavior unless an explicit future lock releases this boundary.
  - v4 candidate behavior is isolated to additive v23 endpoints/artifacts only.
  - default-v3 regression evidence is mandatory:
    - deterministic tests rerun locked v3 semantics diagnostics surfaces and assert byte-identical canonical payloads (after frozen `created_at` exclusion rule) versus pre-v23 baseline captures.
    - deterministic tests assert `KernelMode.STRICT`/`KernelMode.LAX` behavior remains unchanged for existing v3 endpoint contracts.
- S3b deferral lock is frozen:
  - core-ir proposer activation (`S3b`) requires separate lock docs and explicit continuity releases.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.
  - semantics-v4 candidate surfaces may expose stored trust evidence only.

### Acceptance

- Tests prove semantics-v4 candidate code paths do not invoke provider clients or materialization flows.
- Tests include `NoProviderCallsGuard` coverage that fails closed on provider client entrypoint invocation.
- No mutation side effects are observed for semantics-v4 candidate calls on locked fixtures.
- No-mutation tests include deterministic pre/post storage snapshot hash equality assertions.
- Tests prove semantics-v4 candidate output remains non-enforcing.
- Tests prove default v3 runtime semantics behavior remains unchanged.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_SEMANTICS_V4_*` additions in this arc are frozen:
  - `URM_ADEU_SEMANTICS_V4_REQUEST_INVALID`
  - `URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND`
  - `URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID`
  - `URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID`
  - `URM_ADEU_SEMANTICS_V4_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_SEMANTICS_V4_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_SEMANTICS_V4_REQUEST_INVALID` for unsupported pairing modes and ambiguous/non-unique deterministic pair resolution.
  - use `URM_ADEU_SEMANTICS_V4_REQUEST_INVALID` for runtime non-enforcement-context violations in candidate endpoints.
  - use `URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID` for manifest/run-key/surface-id/cap violations.
  - use `URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID` for emitted candidate payload schema/content validation failures.
  - use `URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND` for persisted-lookup misses in candidate inputs.
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v23 candidate codes are additive and must not remove prior legacy error identifiers.

## Commit Plan (Small Green Commits)

1. `runtime: add deterministic semantics-v4 candidate packet builder over persisted diagnostics evidence`
2. `api: add read-only semantics-v4 candidate surface and deterministic response envelopes`
3. `metrics: add vnext_plus23 manifest and additive semantics-v4 candidate determinism keys`
4. `docs: add vnext_plus23 semantics-v4 transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus23 replay fixtures, NoProviderCallsGuard coverage, non-enforcement checks, and no-mutation/default-v3 continuity assertions`

## Intermediate Stage Preconditions and Outputs (Draft)

Before implementation PR1 for `vNext+23`, confirm v22 preconditions are frozen/merged and prepare v23 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS22.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/TRUST_INVARIANT_TRANSFER_REPORT_vNEXT_PLUS22.md` (precondition trust transfer baseline; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus23_manifest.json`
4. draft candidate packet fixture scaffold for `adeu_semantics_v4_candidate_packet@0.1`
5. draft transfer-report schema/renderer for `semantics_v4_transfer_report.vnext_plus23@1`
6. deterministic env helper hook-up for v23 stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
7. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS23.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `V1`-`V4` merged with green CI.
- `artifact_semantics_v4_candidate_packet_determinism_pct == 100.0` on locked fixtures.
- `artifact_semantics_v4_candidate_projection_determinism_pct == 100.0` on locked fixtures.
- `vNext+23 -> vNext+24` frozen thresholds all pass.
- v16/v17/v18/v19/v20/v21/v22 continuity metrics remain present and at threshold (`100.0`).
- v23 closeout evidence includes runtime-observability comparison rows against v22 canonical baseline.
- default runtime semantics remains v3 and unchanged by this arc.
- no trust-lane regression introduced.
- provider-parity continuity lock remains unchanged (no proposer surface expansion).
- all existing stop-gate tracked `vNext+6` through `vNext+22` metrics remain at threshold.
- `vNext+17` through `vNext+22` closeout evidence remains green and reproducible.
