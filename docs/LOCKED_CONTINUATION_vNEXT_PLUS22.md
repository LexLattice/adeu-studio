# Locked Continuation vNext+22 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS21.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS21.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+21` (`N1`-`N4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS21.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` post-`vNext+21` sequencing leaves `vNext+22+` on optional `S7/S8`; this draft selects `vNext+22 = Path S7` (proof/trust lane starter) as the next additive continuation.
- `vNext+16` + `vNext+17` integrity families, `vNext+18` tooling continuity, `vNext+19` read-surface activation, `vNext+20` cross-IR coherence bridges, and `vNext+21` normative-advice read surfaces are stable baselines.
- This arc is reserved for deterministic, read-only proof/trust evidence activation only:
  - deterministic trust-invariant packet contract freeze first
  - deterministic trust-invariant projection + transfer-report artifact family second
  - additive stop-gate determinism metrics for trust-invariant payload stability third
  - explicit non-enforcement and no-mutation/no-provider-expansion continuity fourth

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS18.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS19.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS20.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS21.md` remain authoritative for policy/proof/explain/runtime/provider-parity/core-ir/depth/integrity/read-surface/cross-ir/normative-advice baseline semantics.
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
- `adeu_core_ir@0.1`, `adeu_lane_projection@0.1`, `adeu_lane_report@0.1`, `adeu_projection_alignment@0.1`, `adeu_integrity_dangling_reference@0.1`, `adeu_integrity_cycle_policy@0.1`, `adeu_integrity_deontic_conflict@0.1`, `adeu_integrity_reference_integrity_extended@0.1`, `adeu_integrity_cycle_policy_extended@0.1`, `adeu_integrity_deontic_conflict_extended@0.1`, `adeu_read_surface_payload@0.1`, `adeu_cross_ir_bridge_manifest@0.1`, `adeu_cross_ir_coherence_diagnostics@0.1`, `cross_ir_quality_projection.vnext_plus20@1`, `adeu_normative_advice_packet@0.1`, and `normative_advice_projection.vnext_plus21@1` contracts remain frozen and unchanged in this arc.
- Bridge-version continuity lock is frozen:
  - existing bridge-version contracts remain authoritative:
    - `bridge_mapping_version = "adeu_to_concepts.v1"`
    - `bridge_loss_report.version = "adeu.bridge.loss.v1"`
  - any bridge-version bump is out-of-scope for this arc and requires a separate lock.
- Provider-parity continuity lock is frozen:
  - `vNext+14` provider matrix/manifest semantics remain unchanged in this arc.
  - this arc does not expand proposer provider surface sets.
- Integrity continuity lock from `vNext+16` + `vNext+17` is frozen:
  - v16/v17 integrity artifacts remain authoritative and read-only in this arc.
- Tooling continuity lock from `vNext+18` is frozen:
  - v18 parity/budget semantics remain authoritative.
  - this arc may reuse v18 shared helpers but may not weaken v18 parity or budget gates.
- Read-surface continuity lock from `vNext+19` is frozen:
  - v19 read-only endpoint semantics remain authoritative.
- Cross-ir continuity lock from `vNext+20` is frozen:
  - v20 bridge/coherence/quality semantics remain authoritative.
  - this arc consumes persisted cross-ir evidence only and may not rewrite v20 artifacts in place.
- Normative-advice continuity lock from `vNext+21` is frozen:
  - v21 normative-advice packet/projection semantics remain authoritative.
  - this arc consumes persisted v21 normative-advice evidence only and may not rewrite v21 artifacts in place.
- Upstream dependency continuity lock is frozen:
  - v22 trust-invariant proof generation depends on persisted upstream evidence from:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - persisted `adeu_cross_ir_coherence_diagnostics@0.1` payloads
    - persisted `adeu_normative_advice_packet@0.1` payloads for matched pairs
    - persisted bridge/coherence/advice linkage fields (including `bridge_manifest_hash`)
  - missing upstream evidence is artifact-not-found and fails closed.
  - best-effort fallback, live recomputation, and undeclared input substitution are out-of-scope.
- Module-boundary clarity lock is frozen:
  - `apps/api/src/adeu_api/concepts_coherence.py` is concept-level coherence logic and is non-authoritative for v22 proof/trust derivation.
  - v22 proof/trust artifacts derive exclusively from persisted v20/v21 evidence artifacts under this lock.

## Arc Scope (Draft Lock)

This arc proposes Path S7 thin slice only:

1. `T1` Deterministic trust-invariant proof packet contract freeze
2. `T2` Deterministic trust-invariant projection + transfer-report artifact family
3. `T3` Additive stop-gate determinism metrics for trust-invariant payload stability
4. `T4` Explicit non-enforcement and no-mutation/no-provider-expansion continuity for `vNext+22 -> vNext+23`

Out-of-scope note:

- Path `S3b` (core-ir proposer activation) is not in this arc.
- Provider matrix/surface expansion is not in this arc.
- Solver semantics v4 work (`S8`) is not in this arc.
- Automatic policy execution/auto-remediation from trust output is not in this arc.
- DB-backed trust-proof persistence migrations/new SQL tables are not in this arc.
- Payload offloading via blob-store/pre-signed URLs is not in this arc.
- Sparse fieldset/query-driven partial payload retrieval is not in this arc.
- Mandatory frontend build-system expansion is not in this arc; optional minimal rendering is allowed only if it does not introduce a new frontend build-system dependency.
- Proof acknowledgement/dismissal persistence and mutation endpoints are not in this arc.
- Schema-family consolidation/unification is not in this arc and remains a separate lock decision.
- External anchoring/notarization fields (for example ledger block anchors or timestamp-authority anchors) are not in this arc.
- Projection payload dictionary normalization/deduplicated evidence dictionaries are not in this arc.
- Derived trust-tier synthesis fields (for example `suggested_trust_tier`) are not in this arc and remain a separate lock decision.

## T1) Deterministic Trust-Invariant Proof Packet Contract Freeze

### Goal

Emit deterministic, read-only, non-enforcing trust-invariant proof packets derived from persisted evidence artifacts.

### Scope

- Add deterministic trust-invariant packet generation over persisted cross-ir coherence and normative-advice evidence.
- Keep proof output schema-validated and explicitly non-authoritative.
- Resolve concept/core-ir pairs from fixture-backed catalogs only in this arc.
- Preserve explicit justification references for every proof item.

### Locks

- Proof source authority lock is frozen:
  - trust-invariant generation in this arc is fixture-backed only from persisted artifacts:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - persisted `adeu_cross_ir_coherence_diagnostics@0.1` payloads for matched pairs
    - persisted `adeu_normative_advice_packet@0.1` payloads for matched pairs
  - filesystem scans, DB discovery, and undeclared directories are out-of-scope.
- Dual-upstream dependency lock is frozen:
  - proof builders must load all required inputs:
    - pair context from `cross_ir.vnext_plus20_catalog@1`
    - matched coherence diagnostics from `adeu_cross_ir_coherence_diagnostics@0.1`
    - matched normative-advice packet from `adeu_normative_advice_packet@0.1`
  - operation without any required input is request-invalid and fails closed.
- Bridge-manifest resolution lock is frozen:
  - persisted v20 bridge-manifest evidence for a pair is resolved deterministically from exact tuple `(source_text_hash, core_ir_artifact_id, concept_artifact_id)` using fixture-backed pair resolution in `cross_ir.vnext_plus20_catalog@1` plus the v20 bridge-manifest builder/hash lineage.
  - resolution must yield exactly one bridge-manifest payload per pair tuple.
  - filesystem globbing, undeclared path discovery, and best-effort bridge-manifest substitution are out-of-scope.
- Endpoint-set lock is frozen:
  - `GET /urm/proof-trust/pairs/{source_text_hash}/{core_ir_artifact_id}/{concept_artifact_id}` (`T1` implementation scope)
  - `GET /urm/proof-trust/projection` (`T2` implementation scope; deferred from this `T1` PR slice)
- Persistence-model lock is frozen:
  - `T1/T2` surfaces in this arc are fixture-backed over persisted JSON artifacts/capture catalogs.
  - no new SQL storage tables or schema migrations are introduced for trust-invariant retrieval/projection in v22.
  - DB-backed trust-invariant retrieval/projection is deferred to a later lock.
- Pair-resolution identity lock is frozen:
  - deterministic pair identity and uniqueness key is exactly:
    - `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`
  - pair route resolution is exact-match on this tuple only.
  - non-unique/ambiguous pair entries in the fixture-backed catalog are request-invalid and fail closed.
- Pair-endpoint miss-mode lock is frozen:
  - when tuple `(source_text_hash, core_ir_artifact_id, concept_artifact_id)` is not present in catalog:
    - `URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND`
  - when tuple is present but matched normative-advice/coherence artifact is missing:
    - `URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND`
  - when tuple and upstream artifacts are present but payload linkage/validation fails (including `bridge_manifest_hash` mismatch or schema/content invalidity):
    - `URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID`
- Required-input structural-validity lock is frozen:
  - required upstream payloads must be non-empty JSON objects that satisfy their frozen schema-required top-level fields.
  - `null`, empty-object, empty-array, and schema-required-field-missing payload shapes are payload-invalid and fail closed with:
    - `URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID`
- Trust-invariant artifact schema lock is frozen:
  - `schema = "adeu_trust_invariant_packet@0.1"`
  - required top-level fields:
    - `source_text_hash`
    - `core_ir_artifact_id`
    - `concept_artifact_id`
    - `bridge_manifest_hash`
    - `normative_advice_packet_hash`
    - `proof_summary`
    - `proof_items`
  - `proof_summary` required fields:
    - `total_checks`
    - `passed_checks`
    - `failed_checks`
    - `counts_by_invariant_code`
    - `counts_by_status`
- Normative-advice packet hash lock is frozen:
  - `normative_advice_packet_hash` in the emitted v22 packet is authoritative and deterministic:
    - `normative_advice_packet_hash = sha256_canonical_json(strip_created_at_recursive(advice_packet_payload))`
  - `advice_packet_payload` is the full persisted `adeu_normative_advice_packet@0.1` JSON for the selected pair.
  - `strip_created_at_recursive` removes every `created_at` field at any depth and leaves all other fields unchanged.
  - hash value format is lowercase hex `sha256` with length `64` and no prefix.
- Recursive created-at stripping helper lock is frozen:
  - recursive `created_at` exclusion for v22 hashing paths must be implemented by a shared deterministic helper.
  - helper behavior is structural-only:
    - remove keys named exactly `created_at` at any depth,
    - preserve all remaining keys/values unchanged,
    - preserve list element order,
    - preserve deterministic object-key ordering only through canonical serialization, not in-memory mutation side effects.
  - ad hoc per-call custom exclusion logic is forbidden in this arc.
- Schema-export convention lock is frozen:
  - `adeu_trust_invariant_packet@0.1` must be exported as authoritative schema JSON.
  - authoritative path:
    - `packages/adeu_core_ir/schema/adeu_trust_invariant_packet.v0_1.json`
  - mirror path:
    - `spec/adeu_trust_invariant_packet.schema.json`
  - export wiring extends:
    - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- Invariant taxonomy lock is frozen:
  - allowed `invariant_code` values are exactly:
    - `CANONICAL_JSON_CONFORMANCE`
    - `HASH_RECOMPUTE_MATCH`
    - `REPLAY_HASH_STABILITY`
    - `MANIFEST_CHAIN_STABILITY`
  - allowed `status` values are exactly:
    - `pass`
    - `fail`
- Invariant derivation lock is frozen:
  - `CANONICAL_JSON_CONFORMANCE`:
    - inputs: persisted pair-matched `adeu_cross_ir_coherence_diagnostics@0.1` and `adeu_normative_advice_packet@0.1` payloads.
    - check: each payload loads as JSON, validates against its frozen schema contract using the same runtime-owned validator lineage used by stop-gate artifact-family validation (`packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`), and canonical-hash projection (`sha256_canonical_json(strip_created_at_recursive(payload))`) is computable.
    - output fields: `expected_hash` and `observed_hash` are omitted.
  - `HASH_RECOMPUTE_MATCH`:
    - inputs:
      - persisted `adeu_normative_advice_packet@0.1` payload for the pair,
      - persisted v20 bridge-manifest evidence resolved by the frozen bridge-manifest resolution lock.
    - excluded fields:
      - v20 `mapping_hash` remains opaque passthrough continuity evidence and is not a recompute target in this invariant.
    - checks (all required):
      - recompute `normative_advice_packet_hash` from the advice payload and compare to emitted packet `normative_advice_packet_hash`,
      - recompute `bridge_manifest_hash` from the persisted v20 bridge-manifest canonical projection frozen in `vNext+20` and compare to emitted packet `bridge_manifest_hash`.
    - output fields:
      - `expected_hash` is the deterministic recomputed hash for the selected comparison target.
      - `observed_hash` is the compared emitted hash value for the selected comparison target.
      - selected comparison target precedence is frozen:
        - first failing target in order:
          - `normative_advice_packet_hash`,
          - `bridge_manifest_hash`,
        - if both targets pass, use `normative_advice_packet_hash`.
      - `message` is non-authoritative prose and may not reinterpret or override selected comparison target semantics for `expected_hash`/`observed_hash`.
  - `REPLAY_HASH_STABILITY`:
    - inputs: emitted v22 trust-invariant packet payload for the pair.
    - check: replay exactly `N=3` times and compare `sha256_canonical_json(strip_created_at_recursive(packet_payload))`; all three hashes must match.
    - output fields:
      - `observed_hash` is the stable replay hash when all runs match,
      - `expected_hash` is omitted.
  - `MANIFEST_CHAIN_STABILITY`:
    - inputs:
      - pair-matched coherence diagnostics payload,
      - pair-matched normative-advice packet payload,
      - emitted v22 trust-invariant packet payload,
      - pair-matched `cross_ir.vnext_plus20_catalog@1` entry,
      - persisted v20 bridge-manifest evidence resolved by the frozen bridge-manifest resolution lock.
    - pair-binding checks (all required):
      - route tuple `(source_text_hash, core_ir_artifact_id, concept_artifact_id)` matches exactly one catalog entry.
      - coherence/advice/emitted packet tuple fields each equal the route tuple fields exactly.
    - chain checks (all required):
      - `sha256_canonical_json(v20_bridge_manifest_canonical_projection) == coherence.bridge_manifest_hash`,
      - `coherence.bridge_manifest_hash == normative_advice.bridge_manifest_hash`,
      - `normative_advice.bridge_manifest_hash == emitted_packet.bridge_manifest_hash`.
    - output fields:
      - `expected_hash` is `sha256_canonical_json(v20_bridge_manifest_canonical_projection)`,
      - `observed_hash` is the first non-matching downstream chain value in deterministic precedence:
        - `coherence.bridge_manifest_hash`,
        - `normative_advice.bridge_manifest_hash`,
        - `emitted_packet.bridge_manifest_hash`.
      - when all chain edges match, `observed_hash == expected_hash`.
- Proof-boundary lock is frozen:
  - v22 proof/trust output is infrastructure-invariant evidence over persisted artifacts.
  - solver-obligation semantics, theorem-proving claims, and deontic proof obligations are out-of-scope in this arc.
- Proof aggregation lock is frozen:
  - exactly one invariant check item is emitted per `(pair, invariant_code)`.
  - cross-invariant grouping/deduplication is forbidden in this arc.
  - `proof_summary.total_checks` must equal the number of emitted `proof_items` for the selected pair.
- Proof status semantics lock is frozen:
  - `status = "pass"` iff all required checks for that `invariant_code` succeed.
  - `status = "fail"` otherwise.
  - `status` values remain exactly `{pass, fail}`; `skipped` and `indeterminate` are forbidden in this arc.
  - missing required upstream inputs are not represented as `status = "fail"` items:
    - packet generation fails closed with deterministic request-invalid/artifact-not-found/payload-invalid errors.
- Proof payload lock is frozen:
  - each `proof_items[]` item includes:
    - `proof_id`
    - `invariant_code`
    - `status`
    - `justification_refs` (deterministically ordered non-empty list)
    - optional `expected_hash`
    - optional `observed_hash`
    - optional `source_snapshot` (deterministic passthrough projection)
    - `message` (non-authoritative prose)
- Proof-id formation lock is frozen:
  - `justification_refs` must be lexicographically sorted before id hash computation.
  - `proof_id` must be deterministic and derived from canonical proof content only:
    - `proof_id = sha256(canonical_json({"invariant_code": invariant_code, "status": status, "justification_refs": justification_refs, "expected_hash": expected_hash, "observed_hash": observed_hash}))[:16]`
  - random IDs, UUIDs, and insertion-order counters are forbidden for `proof_id`.
- Justification-reference lock is frozen:
  - `justification_refs` must use stable evidence references only:
    - `artifact:adeu_cross_ir_coherence_diagnostics@0.1:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}`
    - `artifact:adeu_normative_advice_packet@0.1:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}`
    - `artifact:adeu_trust_invariant_packet@0.1:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}`
  - references must resolve to existing persisted artifacts for the selected pair.
  - `justification_refs` cardinality and required members are frozen per `invariant_code`:
    - `CANONICAL_JSON_CONFORMANCE`:
      - exactly two refs: coherence diagnostics + normative-advice packet.
    - `HASH_RECOMPUTE_MATCH`:
      - exactly one ref: normative-advice packet.
    - `REPLAY_HASH_STABILITY`:
      - exactly one ref: trust-invariant packet.
    - `MANIFEST_CHAIN_STABILITY`:
      - exactly two refs: coherence diagnostics + normative-advice packet.
- Proof hash-field format lock is frozen:
  - when present, `expected_hash` and `observed_hash` must be lowercase hex `sha256` strings of length `64` with no prefix.
  - when absent, those fields are omitted (not `null` and not empty string).
- Deterministic ordering lock is frozen:
  - `proof_items[]` are ordered lexicographically by:
    - `invariant_code`
    - `proof_id`
  - `counts_by_invariant_code` keys and `counts_by_status` keys are emitted in lexicographic order.
- Read-authority and mutation lock is frozen:
  - proof generation reads persisted artifacts only.
  - no materialization/proposer/repair execution is allowed on miss.
  - proof handlers/builders are read-only and may not mutate canonical ADEU artifacts.
- Non-enforcement lock is frozen:
  - proof output is evidence-only guidance.
  - proof output may not assert blocking/pass-fail semantics for solver execution or trigger policy enforcement side effects.
  - `adeu_trust_invariant_packet@0.1` does not include enforcement fields; any emitted enforcement-like field is payload-invalid, including:
    - `enforce`
    - `block`
    - `gate`
    - `allow`
    - `deny`

### Acceptance

- Locked trust-invariant fixtures return schema-valid proof packets for persisted pairs.
- Identical persisted inputs replay to byte-identical proof packets.
- Missing/invalid evidence references fail closed with deterministic error envelopes.

## T2) Deterministic Trust-Invariant Projection + Transfer Report Artifact Family

### Goal

Expose deterministic aggregate trust-invariant summaries and closeout reporting over persisted proof packets.

### Scope

- Add deterministic trust-invariant projection over proof packets.
- Extend transfer-report evidence with proof packet/projection/replay summaries.

### Locks

- Projection endpoint activation lock is frozen:
  - `GET /urm/proof-trust/projection` is implemented in `T2`, not `T1`.
  - `T1` PRs may ship pair-packet endpoint only; projection endpoint activation is deferred to `T2` implementation PR.
- T2 implementation slicing lock is frozen:
  - this `T2` API/runtime slice implements deterministic projection builder + `GET /urm/proof-trust/projection`.
  - transfer-report markdown renderer/script/output generation (`docs/TRUST_INVARIANT_TRANSFER_REPORT_vNEXT_PLUS22.md`) may ship in a dedicated `T2` docs slice before `v22` closeout.
- Trust-invariant projection schema lock is frozen:
  - `schema = "trust_invariant_projection.vnext_plus22@1"`
  - required top-level fields:
    - `bridge_pair_count`
    - `proof_item_count`
    - `proof_counts_by_invariant_code`
    - `proof_counts_by_status`
  - projection is reporting-only and may not mutate source artifacts.
- Projection input-set lock is frozen:
  - projection input set is exactly the deterministic pair-key set from:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
  - projection builders must consume trust-invariant packets for this set only; undeclared pair discovery is out-of-scope.
  - projection must invoke the same in-process packet builder contract used by `T1` for each pair in lexicographic order; best-effort fallback and alternate packet-generation paths are forbidden.
  - projection API/runtime may not read precomputed packet fixture files as authoritative inputs; persisted fixture captures are for deterministic stop-gate replay only.
  - projection input packets are iterated in lexicographic pair order:
    - `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`
- Projection totality lock is frozen:
  - projection is total over the frozen catalog pair-key set and may not skip pairs.
  - any missing upstream trust-invariant artifact for any catalog pair fails projection generation closed with:
    - `URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND`
  - any invalid upstream trust-invariant payload for any catalog pair fails projection generation closed with:
    - `URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID`
- Projection count-definition lock is frozen:
  - `bridge_pair_count` equals the count of unique pair keys in the projection input set.
  - `proof_item_count` equals the deterministic sum of `len(proof_items)` across all included trust-invariant packets.
- Transfer report lock is frozen:
  - output path:
    - `docs/TRUST_INVARIANT_TRANSFER_REPORT_vNEXT_PLUS22.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "trust_invariant_transfer_report.vnext_plus22@1"`
    - `vnext_plus22_manifest_hash`
    - `coverage_summary`
    - `trust_invariant_packet_summary`
    - `trust_invariant_projection_summary`
    - `replay_summary`
  - `replay_summary.runtime_observability` required keys are:
    - `elapsed_ms`
    - `total_fixtures`
    - `total_replays`
    - `bytes_hashed_per_replay`
    - `bytes_hashed_total`
- Replay boundary lock is frozen:
  - no live provider calls are permitted in deterministic trust-invariant acceptance paths.

### Acceptance

- Trust-invariant packet/projection fixtures replay to byte-identical outputs for identical persisted inputs.
- Trust-invariant transfer-report payload is deterministic and schema-valid.

## T3) Stop-Gate Determinism Metrics for Trust-Invariant Payloads

### Goal

Make trust-invariant determinism measurable and reproducible with additive stop-gate metrics for `vNext+22 -> vNext+23`.

### Scope

- Add manifest-driven fixture accountability for trust-invariant outputs.
- Extend additive `stop_gate_metrics@1` with v22 trust-invariant keys.
- Preserve v16-v21 continuity metrics and thresholds.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus22_manifest.json`
  - schema:
    - `stop_gate.vnext_plus22_manifest@1`
  - required:
    - `replay_count == 3`
- Surface enumeration completeness lock is frozen:
  - frozen v22 trust-invariant `surface_id` set is exactly:
    - `adeu.trust_invariant.packet`
    - `adeu.trust_invariant.projection`
  - manifest fixture `surface_id` values must be members of this frozen set only.
- Manifest shape lock is frozen:
  - required fixture lists are:
    - `trust_invariant_packet_fixtures`
    - `trust_invariant_projection_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
- Run-reference key lock is frozen:
  - required run keys are:
    - `trust_invariant_packet_fixtures[].runs[].trust_invariant_packet_path`
    - `trust_invariant_projection_fixtures[].runs[].trust_invariant_projection_path`
  - missing required run keys are fixture-invalid and fail closed.
- Fixture-path semantics lock is frozen:
  - `*_path` inputs are captured deterministic JSON artifact payloads from the v22 in-process harness (no live-network dependency), not ad hoc derived summaries.
  - captured payloads include the full artifact JSON body including top-level `schema`.
  - `trust_invariant_packet_path` captures `adeu_trust_invariant_packet@0.1` payloads.
  - `trust_invariant_projection_path` captures `trust_invariant_projection.vnext_plus22@1` payloads.
  - capture order is frozen lexicographically by `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`.
  - capture envelope stores only:
    - parsed JSON response/artifact payload (canonicalized on write),
    - deterministic harness metadata required for traceability.
  - response headers are excluded from capture envelopes and determinism hash inputs.
- Non-empty evidence floor lock is frozen:
  - at least one locked trust-invariant fixture must emit `total_checks > 0`.
  - at least one locked trust-invariant fixture must emit one or more checks in:
    - `HASH_RECOMPUTE_MATCH`
    - `REPLAY_HASH_STABILITY`
  - at least one locked trust-invariant fixture must emit one or more items with:
    - `status == "fail"`
- Determinism metric computation lock is frozen:
  - determinism hash input is canonical JSON from loaded captured payloads (`sha256_canonical_json(load_json(path))`), not raw bytes.
  - hash projection excludes `created_at` fields recursively at any depth in captured JSON; no other fields are excluded.
  - replay byte observability is computed over canonical hash inputs after `created_at` exclusion only:
    - `bytes_hashed_per_replay = sum(len(canonical_json_bytes(payload_i)))` over all hashed payloads in one replay.
    - `bytes_hashed_total = replay_count * bytes_hashed_per_replay`.
  - replay byte observability surface scope is frozen:
    - for `trust_invariant_packet_fixtures`, byte counters include captured packet payload bytes only.
    - for `trust_invariant_projection_fixtures`, byte counters include captured projection payload bytes only.
    - upstream dependency payload bytes are excluded from these counters.
  - replay exactly `N=3` times per fixture.
  - fixture passes only when all replay hashes match.
  - `pct = 100 * passed / total`.
- Deterministic performance-optimization lock is frozen:
  - v18 bounded-optimization patterns may be applied to v22 trust-invariant hashing paths.
  - allowed optimization includes deterministic sub-component pre-hashing/caching keyed by canonical input payload hashes.
  - allowed optimization includes concurrent replay execution for `N=3` only when:
    - each replay runs in an isolated process with deterministic environment lock enforced (`TZ=UTC`, `LC_ALL=C`),
    - fixture execution order is seeded from frozen lexicographic fixture order,
    - replay result aggregation is reduced in deterministic lexicographic fixture/run order.
  - CI stop-gate entrypoints must default to this concurrent replay mode for v22 trust-invariant fixtures to preserve v18 runtime-budget continuity constraints.
  - optimization may not alter fixture selection, replay count, hash projection rules, or pass/fail semantics.
- Reusable deterministic-parallel helper lock is frozen:
  - extracting a shared deterministic concurrent-replay helper is allowed in this arc.
  - helper behavior must preserve deterministic environment isolation, lexicographic ordering, replay cardinality, and pass/fail semantics unchanged.
  - helper reuse across v20/v21/v22 stop-gate deterministic replay paths is allowed.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_trust_invariant_packet_determinism_pct`
  - `artifact_trust_invariant_projection_determinism_pct`
- Metric-key cardinality lock is frozen:
  - v22 adds exactly two trust-invariant determinism keys to `stop_gate_metrics@1` in this arc.
  - additional v22 trust-invariant metric-key additions are out-of-scope unless an explicit follow-on lock approves them.
- Continuity-threshold lock is frozen:
  - v16/v17/v18/v19/v20/v21 thresholds remain required and unchanged in v22 closeout.
  - this includes v18 tooling budget continuity:
    - `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0`
  - v22 closeout evidence must include an explicit runtime-observability comparison row against v21 canonical closeout baseline.
- Threshold lock is frozen for `vNext+22 -> vNext+23`:
  - `artifact_trust_invariant_packet_determinism_pct == 100.0`
  - `artifact_trust_invariant_projection_determinism_pct == 100.0`
  - v16/v17/v18/v19/v20/v21 continuity thresholds remain required and unchanged.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus22_manifest_hash`.
  - mismatch fails closed.

### Acceptance

- Trust-invariant coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+22` thresholds.
- Locked fixtures prove non-empty detector behavior (not all-zero trust-invariant outputs).

## T4) Non-Enforcement and No-Mutation/No-Provider-Expansion Continuity

### Goal

Keep v22 trust-invariant activation strictly read-only and non-enforcing; prevent drift into proposer/provider, mutation, or policy-execution semantics.

### Scope

- Freeze explicit continuity constraints for `vNext+22 -> vNext+23`.
- Keep trust-invariant surfaces independent from proposer activation.
- Preserve v14-v21 operational and trust boundaries.

### Locks

- No-provider-expansion lock is frozen:
  - this arc introduces no proposer/provider surfaces.
  - provider matrix/surface-set continuity from `vNext+14` remains unchanged.
- No-provider-calls guard lock is frozen:
  - trust-invariant handlers/builders must be covered by deterministic tests using a `NoProviderCallsGuard` runtime helper.
  - guard behavior is fail-closed: any provider client entrypoint invocation in guarded trust-invariant paths fails the test.
  - guard coverage must also enforce outbound-network denial in test context (socket-level fail-closed boundary) so provider/network calls cannot bypass high-level client patching.
- No-materialization-calls guard lock is frozen:
  - trust-invariant handlers/builders must be covered by deterministic fail-closed test guards over policy/materialization execution entrypoints.
  - any policy/materialization invocation from guarded trust-invariant paths fails the test.
  - this guard requirement is independent of provider-call guards and must be asserted separately.
- Runtime non-enforcement context lock is frozen:
  - trust-invariant endpoint handlers/builders must execute inside a runtime non-enforcement context that disables write/policy/materialization dispatch in trust-invariant paths.
  - runtime context violations fail closed with deterministic request-invalid errors.
  - helper continuity:
    - implementations may reuse `vNext+21` non-enforcement context helper(s) or extract a shared generic helper (for example `urm_non_enforcement_context`).
    - helper extraction/rename may not widen permissions or change fail-closed behavior.
- No-mutation lock is frozen:
  - trust-invariant entrypoints/builders must not write canonical ADEU artifacts or mutate persisted concept/core-ir/lane/integrity/cross-ir/normative-advice artifacts.
  - canonical artifacts remain generated by existing materialization/closeout flows only.
- No-mutation verification lock is frozen:
  - deterministic no-mutation tests must compare pre/post snapshots over the v22 fixture-backed mutable surface only:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - all artifact JSON files referenced by that catalog
    - `apps/api/fixtures/stop_gate/vnext_plus21_manifest.json`
    - all normative-advice artifact JSON files referenced by that manifest
    - `apps/api/fixtures/stop_gate/vnext_plus22_manifest.json`
    - all trust-invariant artifact JSON files referenced by that manifest
  - snapshot comparison is hash-based over canonical file contents (`sha256_canonical_json(load_json(path))`) and must remain byte-identical for read-only calls.
- Non-enforcement verification lock is frozen:
  - trust-invariant generation tests must assert no policy/materialization execution endpoints are invoked.
  - tests must fail closed when guarded policy/materialization entrypoints are invoked.
  - trust-invariant payloads may contain evidence recommendations only and no enforcement flags.
- No-solver-change lock is frozen:
  - solver, validator, and proof semantics are not changed by this arc.
- S3b/S8 deferral lock is frozen:
  - core-ir proposer activation (`S3b`) and solver semantics v4 (`S8`) require separate lock docs and explicit continuity releases.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.
  - trust-invariant surfaces may expose stored trust evidence only.
- Proof-obligation boundary lock is frozen:
  - this arc introduces no solver-obligation proof runtime and no theorem-prover integration.
  - all v22 proofs are deterministic infrastructure-invariant evidence packets only.

### Acceptance

- Tests prove trust-invariant code paths do not invoke provider clients or materialization flows.
- Tests include `NoProviderCallsGuard` coverage that fails closed on provider client entrypoint invocation.
- No mutation side effects are observed for trust-invariant calls on locked fixtures.
- No-mutation tests include deterministic pre/post storage snapshot hash equality assertions.
- Tests prove trust-invariant output remains non-enforcing.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_TRUST_INVARIANT_*` additions in this arc are frozen:
  - `URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID`
  - `URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND`
  - `URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID`
  - `URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID`
  - `URM_ADEU_TRUST_INVARIANT_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_TRUST_INVARIANT_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID` for unsupported pairing modes and ambiguous/non-unique deterministic pair resolution.
  - use `URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID` for runtime non-enforcement-context violations in trust-invariant endpoints.
  - use `URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID` for manifest/run-key/surface-id/cap violations.
  - use `URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID` for emitted trust-invariant payload schema/content validation failures.
  - use `URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND` for persisted-lookup misses in trust-invariant inputs (including pair tuple absent in catalog and missing matched upstream evidence artifacts).
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v22 trust-invariant codes are additive and must not remove prior legacy error identifiers.

## Commit Plan (Small Green Commits)

1. `runtime: add deterministic trust-invariant packet builder over persisted v20/v21 evidence`
2. `api: add read-only proof-trust surface and deterministic response envelopes`
3. `metrics: add vnext_plus22 manifest and additive trust-invariant determinism keys`
4. `docs: add vnext_plus22 trust-invariant transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus22 replay fixtures, NoProviderCallsGuard coverage, non-enforcement checks, and no-mutation snapshot assertions`

## Intermediate Stage Preconditions and Outputs (Draft)

Before implementation PR1 for `vNext+22`, confirm v21 preconditions are frozen/merged and prepare v22 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS21.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/NORMATIVE_ADVICE_TRANSFER_REPORT_vNEXT_PLUS21.md` (precondition normative-advice transfer baseline; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus22_manifest.json`
4. draft trust-invariant fixture scaffold for `adeu_trust_invariant_packet@0.1`
5. draft transfer-report schema/renderer for `trust_invariant_transfer_report.vnext_plus22@1`
6. deterministic env helper hook-up for v22 stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
7. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS22.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `T1`-`T4` merged with green CI.
- `artifact_trust_invariant_packet_determinism_pct == 100.0` on locked fixtures.
- `artifact_trust_invariant_projection_determinism_pct == 100.0` on locked fixtures.
- `vNext+22 -> vNext+23` frozen thresholds all pass.
- v16/v17/v18/v19/v20/v21 continuity metrics remain present and at threshold (`100.0`).
- v22 closeout evidence includes runtime-observability comparison rows against v21 canonical baseline.
- no solver semantics contract delta and no trust-lane regression introduced.
- provider-parity continuity lock remains unchanged (no proposer surface expansion).
- all existing stop-gate tracked `vNext+6` through `vNext+21` metrics remain at threshold.
- `vNext+17` through `vNext+21` closeout evidence remains green and reproducible.
