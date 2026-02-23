# Locked Continuation vNext+21 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS20.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS20.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+20` (`C1`-`C4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS20.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` post-`vNext+20` sequence leaves `vNext+21+` on optional `S6/S7/S8`; this draft selects `vNext+21 = Path S6` (evidence-only normative advice layer) as the lowest-risk additive continuation.
- `vNext+16` + `vNext+17` integrity families, `vNext+18` tooling continuity, `vNext+19` read-surface activation, and `vNext+20` cross-IR coherence bridges are stable baselines.
- This arc is reserved for deterministic, non-enforcing normative advice activation only:
  - deterministic advice-packet contract freeze first
  - deterministic advice projection + transfer-report artifact family second
  - additive stop-gate determinism metrics for advice payload stability third
  - explicit non-enforcement and no-mutation/no-provider-expansion continuity fourth

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS18.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS19.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS20.md` remain authoritative for policy/proof/explain/runtime/provider-parity/core-ir/depth/integrity/read-surface/cross-ir baseline semantics.
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
- `adeu_core_ir@0.1`, `adeu_lane_projection@0.1`, `adeu_lane_report@0.1`, `adeu_projection_alignment@0.1`, `adeu_integrity_dangling_reference@0.1`, `adeu_integrity_cycle_policy@0.1`, `adeu_integrity_deontic_conflict@0.1`, `adeu_integrity_reference_integrity_extended@0.1`, `adeu_integrity_cycle_policy_extended@0.1`, `adeu_integrity_deontic_conflict_extended@0.1`, `adeu_read_surface_payload@0.1`, `adeu_cross_ir_bridge_manifest@0.1`, `adeu_cross_ir_coherence_diagnostics@0.1`, and `cross_ir_quality_projection.vnext_plus20@1` contracts remain frozen and unchanged in this arc.
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
- Upstream dependency continuity lock is frozen:
  - v21 normative advice generation depends on persisted upstream evidence from:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - persisted `adeu_cross_ir_coherence_diagnostics@0.1` payloads
    - persisted bridge/coherence linkage fields (including `bridge_manifest_hash`) referenced by those payloads
  - missing upstream evidence is artifact-not-found and fails closed.
  - best-effort fallback, live recomputation, and undeclared input substitution are out-of-scope.
- Module-boundary clarity lock is frozen:
  - `apps/api/src/adeu_api/concepts_coherence.py` is concept-level coherence logic and is non-authoritative for v21 normative-advice derivation.
  - v21 normative advice derives exclusively from persisted v20 cross-ir coherence artifacts under this lock.

## Arc Scope (Draft Lock)

This arc proposes Path S6 thin slice only:

1. `N1` Deterministic evidence-only normative advice packet contract freeze
2. `N2` Deterministic normative advice projection + transfer-report artifact family
3. `N3` Additive stop-gate determinism metrics for normative advice payload stability
4. `N4` Explicit non-enforcement and no-mutation/no-provider-expansion continuity for `vNext+21 -> vNext+22`

Out-of-scope note:

- Path `S3b` (core-ir proposer activation) is not in this arc.
- Provider matrix/surface expansion is not in this arc.
- Solver semantics v4 work is not in this arc.
- Automatic policy execution/auto-remediation from advice output is not in this arc.
- DB-backed normative advice persistence migrations/new SQL tables are not in this arc.
- Payload offloading via blob-store/pre-signed URLs is not in this arc.
- Sparse fieldset/query-driven partial payload retrieval is not in this arc.
- Mandatory frontend build-system expansion is not in this arc; optional minimal rendering is allowed only if it does not introduce a new frontend build-system dependency.
- Advice acknowledgement/dismissal persistence and mutation endpoints are not in this arc.
- Schema-family consolidation/unification is not in this arc and remains a separate lock decision.

## N1) Deterministic Evidence-Only Normative Advice Packet Contract Freeze

### Goal

Emit deterministic, read-only, non-enforcing normative advice packets derived from persisted evidence artifacts.

### Scope

- Add deterministic advice-packet generation over persisted cross-ir coherence evidence.
- Keep advice output schema-validated and explicitly non-authoritative.
- Resolve concept/core-ir pairs from fixture-backed catalogs only in this arc.
- Preserve explicit justification references for every advice item.

### Locks

- Advice source authority lock is frozen:
  - advice generation in this arc is fixture-backed only from persisted artifacts:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - persisted `adeu_cross_ir_coherence_diagnostics@0.1` payloads for matched pairs
  - filesystem scans, DB discovery, and undeclared directories are out-of-scope.
- Dual-input dependency lock is frozen:
  - advice builders must load both:
    - catalog pair context from `cross_ir.vnext_plus20_catalog@1`
    - matched coherence diagnostics from `adeu_cross_ir_coherence_diagnostics@0.1`
  - coherence-only operation without catalog context is request-invalid and fails closed.
- Endpoint-set lock is frozen:
  - `GET /urm/normative-advice/pairs/{source_text_hash}/{core_ir_artifact_id}/{concept_artifact_id}` (`N1` implementation scope)
  - `GET /urm/normative-advice/projection` (`N2` implementation scope; deferred from this `N1` PR slice)
- Persistence-model lock is frozen:
  - `N1/N2` surfaces in this arc are fixture-backed over persisted JSON artifacts/capture catalogs.
  - no new SQL storage tables or schema migrations are introduced for normative advice retrieval/projection in v21.
  - DB-backed normative advice retrieval/projection is deferred to a later lock.
- Pair-resolution identity lock is frozen:
  - deterministic pair identity and uniqueness key is exactly:
    - `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`
  - pair route resolution is exact-match on this tuple only.
  - non-unique/ambiguous pair entries in the fixture-backed catalog are request-invalid and fail closed.
- Pair-endpoint miss-mode lock is frozen:
  - when tuple `(source_text_hash, core_ir_artifact_id, concept_artifact_id)` is not present in catalog:
    - `URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND`
  - when tuple is present but matched coherence diagnostics artifact is missing:
    - `URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND`
  - when tuple and coherence diagnostics are present but payload linkage/validation fails (including `bridge_manifest_hash` mismatch or schema/content invalidity):
    - `URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID`
- Advice artifact schema lock is frozen:
  - `schema = "adeu_normative_advice_packet@0.1"`
  - required top-level fields:
    - `source_text_hash`
    - `core_ir_artifact_id`
    - `concept_artifact_id`
    - `bridge_manifest_hash`
    - `advice_summary`
    - `advice_items`
  - `advice_summary` required fields:
    - `total_advice`
    - `counts_by_code`
    - `counts_by_priority`
- Schema-export convention lock is frozen:
  - `adeu_normative_advice_packet@0.1` must be exported as authoritative schema JSON.
  - authoritative path:
    - `packages/adeu_core_ir/schema/adeu_normative_advice_packet.v0_1.json`
  - mirror path:
    - `spec/adeu_normative_advice_packet.schema.json`
  - export wiring extends:
    - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- Advice taxonomy lock is frozen:
  - allowed `advice_code` values are exactly:
    - `MAPPING_GAP_REVIEW`
    - `SOURCE_DIVERGENCE_REVIEW`
    - `TOPOLOGY_ALIGNMENT_REVIEW`
    - `CLAIM_PROJECTION_REVIEW`
    - `TRUST_ALIGNMENT_REVIEW`
  - allowed `priority` values are exactly:
    - `low`
    - `medium`
    - `high`
- Advice input-eligibility lock is frozen:
  - advice generation considers only persisted coherence issues from `adeu_cross_ir_coherence_diagnostics@0.1` where:
    - `severity in {"warn","error"}`
    - `issue_code` is a member of the frozen v20 coherence issue taxonomy.
  - issues attributable solely to v20 intentional asymmetry allowlists are ineligible advice inputs in this arc.
  - builders may not synthesize or reintroduce intentionally-suppressed missing-mapping issues.
- Advice derivation lock is frozen:
  - `MISSING_CONCEPT_MAPPING` and `MISSING_CORE_IR_MAPPING` map to `MAPPING_GAP_REVIEW`.
  - `SOURCE_HASH_MISMATCH` maps to `SOURCE_DIVERGENCE_REVIEW`.
  - `TOPOLOGY_DRIFT` and `LINK_KIND_DRIFT` map to `TOPOLOGY_ALIGNMENT_REVIEW`.
  - `CLAIM_PROJECTION_GAP` maps to `CLAIM_PROJECTION_REVIEW`.
  - `TRUST_LABEL_MISMATCH` maps to `TRUST_ALIGNMENT_REVIEW`.
  - priority mapping is deterministic and frozen per advice code:
    - `MAPPING_GAP_REVIEW -> medium`
    - `SOURCE_DIVERGENCE_REVIEW -> high`
    - `TOPOLOGY_ALIGNMENT_REVIEW -> medium`
    - `CLAIM_PROJECTION_REVIEW -> high`
    - `TRUST_ALIGNMENT_REVIEW -> medium`
- Priority-escalation deferral lock is frozen:
  - priority values in this arc are determined only by the frozen `advice_code -> priority` mapping.
  - topology-weight, trust-weight, and graph-centrality based priority escalation are out-of-scope in this arc.
- Advice aggregation lock is frozen:
  - exactly one eligible coherence issue yields exactly one advice item.
  - cross-issue grouping/deduplication is forbidden in this arc.
  - `advice_summary.total_advice` must equal the count of eligible coherence issues for the selected pair.
- Downstream grouping-tuple lock is frozen:
  - while in-arc grouping/deduplication is forbidden, deterministic consumer-side grouping may use:
    - `(advice_code, concept_refs, core_ir_refs)`
  - builders may not mutate this tuple to implicitly collapse multiple source issues into one emitted advice item.
- Advice payload lock is frozen:
  - each `advice_items[]` item includes:
    - `advice_id`
    - `advice_code`
    - `priority`
    - `concept_refs` (deterministically ordered)
    - `core_ir_refs` (deterministically ordered)
    - `justification_refs` (deterministically ordered singleton list)
    - optional `source_issue_snapshot` (deterministic passthrough projection)
    - `message` (non-authoritative prose)
- Advice-reference passthrough lock is frozen:
  - `concept_refs` and `core_ir_refs` in each advice item are copied verbatim from the referenced source coherence issue.
  - builders may not normalize, shorten, expand, or reorder these refs in advice items.
- Advice-id formation lock is frozen:
  - `concept_refs`, `core_ir_refs`, and `justification_refs` must be lexicographically sorted before id hash computation.
  - `advice_id` must be deterministic and derived from canonical advice content only:
    - `advice_id = sha256(canonical_json({"advice_code": advice_code, "concept_refs": concept_refs, "core_ir_refs": core_ir_refs, "justification_refs": justification_refs}))[:16]`
  - random IDs, UUIDs, and insertion-order counters are forbidden for `advice_id`.
- Justification-reference lock is frozen:
  - `justification_refs` must use stable evidence references only:
    - `coherence_issue:{issue_id}`
  - references must resolve to existing persisted coherence issues for the selected pair.
  - each advice item must contain exactly one `justification_refs` entry.
- Advice-id continuity lock is frozen:
  - `advice_id` values in this arc are stable foreign-key candidates for future acknowledgement workflows.
  - v21 introduces no acknowledgement/dismiss mutation semantics.
- Source-issue snapshot transclusion lock is frozen:
  - `source_issue_snapshot` is optional and additive for one-hop rendering over persisted evidence.
  - when present, `source_issue_snapshot` is an exact passthrough projection of the referenced source issue with keys:
    - `issue_id`
    - `issue_code`
    - `severity`
    - `message`
    - `evidence`
  - `source_issue_snapshot.issue_id` must equal the `issue_id` referenced by `justification_refs[0]`.
  - snapshot fields are evidence-only and may not introduce inferred semantics beyond the referenced issue.
  - if snapshot transclusion is enabled for a v21 determinism harness/build mode, it must be enabled for all fixtures/runs in that harness/build mode; mixed inclusion is forbidden.
- Source-issue recoverability lock is frozen:
  - the originating coherence issue for each advice item is authoritative via `justification_refs[0]`.
  - for `TOPOLOGY_ALIGNMENT_REVIEW`, subtype origin (`TOPOLOGY_DRIFT` vs `LINK_KIND_DRIFT`) must be recoverable exclusively from the referenced source issue and may not be dropped/rewritten.
- Deterministic ordering lock is frozen:
  - `advice_items[]` are ordered lexicographically by:
    - `advice_code`
    - first concept ref (or empty string)
    - first core-ir ref (or empty string)
    - `advice_id`
  - `counts_by_code` keys and `counts_by_priority` keys are emitted in lexicographic order.
- Read-authority and mutation lock is frozen:
  - advice generation reads persisted artifacts only.
  - no materialization/proposer/repair execution is allowed on miss.
  - advice handlers/builders are read-only and may not mutate canonical ADEU artifacts.
- Non-enforcement lock is frozen:
  - advice output is evidence-only guidance.
  - advice may not assert blocking/pass-fail semantics or trigger policy enforcement side effects.
  - `adeu_normative_advice_packet@0.1` does not include enforcement fields; any emitted enforcement-like field is payload-invalid, including:
    - `enforce`
    - `block`
    - `gate`
    - `allow`
    - `deny`

### Acceptance

- Locked advice fixtures return schema-valid advice packets for persisted pairs.
- Identical persisted inputs replay to byte-identical advice packets.
- Missing/invalid evidence references fail closed with deterministic error envelopes.

## N2) Deterministic Advice Projection + Transfer Report Artifact Family

### Goal

Expose deterministic aggregate advice summaries and closeout reporting over persisted advice packets.

### Scope

- Add deterministic normative advice projection over advice packets.
- Extend transfer-report evidence with advice packet/projection/replay summaries.

### Locks

- Projection endpoint activation lock is frozen:
  - `GET /urm/normative-advice/projection` is implemented in `N2`, not `N1`.
  - `N1` PRs may ship pair-packet endpoint only; projection endpoint activation is deferred to `N2` implementation PR.
- N2 implementation slicing lock is frozen:
  - this `N2` API/runtime slice implements deterministic projection builder + `GET /urm/normative-advice/projection`.
  - transfer-report markdown renderer/script/output generation (`docs/NORMATIVE_ADVICE_TRANSFER_REPORT_vNEXT_PLUS21.md`) may ship in a dedicated `N2` docs slice before `v21` closeout.

- Advice projection schema lock is frozen:
  - `schema = "normative_advice_projection.vnext_plus21@1"`
  - required top-level fields:
    - `bridge_pair_count`
    - `advice_item_count`
    - `advice_counts_by_code`
    - `advice_counts_by_priority`
  - projection is reporting-only and may not mutate source artifacts.
- Projection input-set lock is frozen:
  - projection input set is exactly the deterministic pair-key set from:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
  - projection builders must consume advice packets for this set only; undeclared pair discovery is out-of-scope.
  - projection input packets are iterated in lexicographic pair order:
    - `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`
- Projection totality lock is frozen:
  - projection is total over the frozen catalog pair-key set and may not skip pairs.
  - any missing upstream coherence/advice artifact for any catalog pair fails projection generation closed with:
    - `URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND`
  - any invalid upstream coherence/advice payload for any catalog pair fails projection generation closed with:
    - `URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID`
- Projection count-definition lock is frozen:
  - `bridge_pair_count` equals the count of unique pair keys in the projection input set.
  - `advice_item_count` equals the deterministic sum of `len(advice_items)` across all included advice packets.
- Transfer report lock is frozen:
  - output path:
    - `docs/NORMATIVE_ADVICE_TRANSFER_REPORT_vNEXT_PLUS21.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "normative_advice_transfer_report.vnext_plus21@1"`
    - `vnext_plus21_manifest_hash`
    - `coverage_summary`
    - `advice_packet_summary`
    - `advice_projection_summary`
    - `replay_summary`
- Replay boundary lock is frozen:
  - no live provider calls are permitted in deterministic normative advice acceptance paths.

### Acceptance

- Advice packet/projection fixtures replay to byte-identical outputs for identical persisted inputs.
- Normative advice transfer-report payload is deterministic and schema-valid.

## N3) Stop-Gate Determinism Metrics for Normative Advice Payloads

### Goal

Make normative advice determinism measurable and reproducible with additive stop-gate metrics for `vNext+21 -> vNext+22`.

### Scope

- Add manifest-driven fixture accountability for normative advice outputs.
- Extend additive `stop_gate_metrics@1` with v21 normative-advice keys.
- Preserve v16-v20 continuity metrics and thresholds.

### Locks

- Snapshot transclusion harness-mode lock is frozen:
  - enforcement of `source_issue_snapshot` inclusion mode is a deterministic harness/build-mode concern in `N3`, not a request-level API toggle in `N1`.
  - when snapshot transclusion is enabled for a `v21` determinism harness/build mode, it must be enabled for all fixtures/runs in that mode; mixed inclusion remains forbidden.

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus21_manifest.json`
  - schema:
    - `stop_gate.vnext_plus21_manifest@1`
  - required:
    - `replay_count == 3`
- Surface enumeration completeness lock is frozen:
  - frozen v21 normative-advice `surface_id` set is exactly:
    - `adeu.normative_advice.packet`
    - `adeu.normative_advice.projection`
  - manifest fixture `surface_id` values must be members of this frozen set only.
- Manifest shape lock is frozen:
  - required fixture lists are:
    - `normative_advice_packet_fixtures`
    - `normative_advice_projection_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
- Run-reference key lock is frozen:
  - required run keys are:
    - `normative_advice_packet_fixtures[].runs[].normative_advice_packet_path`
    - `normative_advice_projection_fixtures[].runs[].normative_advice_projection_path`
  - missing required run keys are fixture-invalid and fail closed.
- Fixture-path semantics lock is frozen:
  - `*_path` inputs are captured deterministic JSON artifact payloads from the v21 in-process harness (no live-network dependency), not ad hoc derived summaries.
  - captured payloads include the full artifact JSON body including top-level `schema`.
  - `normative_advice_packet_path` captures `adeu_normative_advice_packet@0.1` payloads.
  - `normative_advice_projection_path` captures `normative_advice_projection.vnext_plus21@1` payloads.
  - capture order is frozen lexicographically by `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`.
  - capture envelope stores only:
    - parsed JSON response/artifact payload (canonicalized on write),
    - deterministic harness metadata required for traceability.
  - response headers are excluded from capture envelopes and determinism hash inputs.
- Non-empty evidence floor lock is frozen:
  - at least one locked advice fixture must emit `total_advice > 0`.
  - at least one locked advice fixture must emit one or more items in:
    - `MAPPING_GAP_REVIEW`
    - `SOURCE_DIVERGENCE_REVIEW`
- Determinism metric computation lock is frozen:
  - determinism hash input is canonical JSON from loaded captured payloads (`sha256_canonical_json(load_json(path))`), not raw bytes.
  - hash projection excludes `created_at` fields recursively at any depth in captured JSON; no other fields are excluded.
  - replay exactly `N=3` times per fixture.
  - fixture passes only when all replay hashes match.
  - `pct = 100 * passed / total`.
- Deterministic performance-optimization lock is frozen:
  - v18 bounded-optimization patterns may be applied to v21 normative-advice hashing paths.
  - allowed optimization includes deterministic sub-component pre-hashing/caching keyed by canonical input payload hashes.
  - allowed optimization includes concurrent replay execution for `N=3` only when:
    - each replay runs in an isolated process with deterministic environment lock enforced (`TZ=UTC`, `LC_ALL=C`),
    - fixture execution order is seeded from frozen lexicographic fixture order,
    - replay result aggregation is reduced in deterministic lexicographic fixture/run order.
  - CI stop-gate entrypoints must default to this concurrent replay mode for v21 normative-advice fixtures to preserve v18 runtime-budget continuity constraints.
  - optimization may not alter fixture selection, replay count, hash projection rules, or pass/fail semantics.
- Reusable deterministic-parallel helper lock is frozen:
  - extracting a shared deterministic concurrent-replay helper is allowed in this arc.
  - helper behavior must preserve deterministic environment isolation, lexicographic ordering, replay cardinality, and pass/fail semantics unchanged.
  - helper reuse across v20/v21 stop-gate deterministic replay paths is allowed.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_normative_advice_packet_determinism_pct`
  - `artifact_normative_advice_projection_determinism_pct`
- Metric-key cardinality lock is frozen:
  - v21 adds exactly two normative-advice determinism keys to `stop_gate_metrics@1` in this arc.
  - additional v21 normative-advice metric-key additions are out-of-scope unless an explicit follow-on lock approves them.
- Continuity-threshold lock is frozen:
  - v16/v17/v18/v19/v20 thresholds remain required and unchanged in v21 closeout.
  - this includes v18 tooling budget continuity:
    - `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0`
  - v21 closeout evidence must include an explicit runtime-observability comparison row against v20 canonical closeout baseline.
- Threshold lock is frozen for `vNext+21 -> vNext+22`:
  - `artifact_normative_advice_packet_determinism_pct == 100.0`
  - `artifact_normative_advice_projection_determinism_pct == 100.0`
  - v16/v17/v18/v19/v20 continuity thresholds remain required and unchanged.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus21_manifest_hash`.
  - mismatch fails closed.

### Acceptance

- Normative-advice coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+21` thresholds.
- Locked fixtures prove non-empty detector behavior (not all-zero advice outputs).

## N4) Non-Enforcement and No-Mutation/No-Provider-Expansion Continuity

### Goal

Keep v21 normative advice activation strictly read-only and non-enforcing; prevent drift into proposer/provider, mutation, or policy-execution semantics.

### Scope

- Freeze explicit continuity constraints for `vNext+21 -> vNext+22`.
- Keep normative advice independent from proposer activation.
- Preserve v14-v20 operational and trust boundaries.

### Locks

- No-provider-expansion lock is frozen:
  - this arc introduces no proposer/provider surfaces.
  - provider matrix/surface-set continuity from `vNext+14` remains unchanged.
- No-provider-calls guard lock is frozen:
  - advice handlers/builders must be covered by deterministic tests using a `NoProviderCallsGuard` runtime helper.
  - guard behavior is fail-closed: any provider client entrypoint invocation in guarded advice paths fails the test.
  - guard coverage must also enforce outbound-network denial in test context (socket-level fail-closed boundary) so provider/network calls cannot bypass high-level client patching.
- No-materialization-calls guard lock is frozen:
  - advice handlers/builders must be covered by deterministic fail-closed test guards over policy/materialization execution entrypoints.
  - any policy/materialization invocation from guarded advice paths fails the test.
  - this guard requirement is independent of provider-call guards and must be asserted separately.
- Runtime non-enforcement context lock is frozen:
  - normative-advice endpoint handlers/builders must execute inside a runtime non-enforcement context that disables write/policy/materialization dispatch in advice paths.
  - runtime context violations fail closed with deterministic request-invalid errors.
- No-mutation lock is frozen:
  - advice entrypoints/builders must not write canonical ADEU artifacts or mutate persisted concept/core-ir/lane/integrity/cross-ir artifacts.
  - canonical artifacts remain generated by existing materialization/closeout flows only.
- No-mutation verification lock is frozen:
  - deterministic no-mutation tests must compare pre/post snapshots over the v21 fixture-backed mutable surface only:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - all artifact JSON files referenced by that catalog
    - `apps/api/fixtures/stop_gate/vnext_plus21_manifest.json`
    - all normative advice artifact JSON files referenced by that manifest
  - snapshot comparison is hash-based over canonical file contents (`sha256_canonical_json(load_json(path))`) and must remain byte-identical for read-only calls.
- Non-enforcement verification lock is frozen:
  - advice generation tests must assert no policy/materialization execution endpoints are invoked.
  - tests must fail closed when guarded policy/materialization entrypoints are invoked.
  - advice payloads may contain recommendations only and no enforcement flags.
- No-solver-change lock is frozen:
  - solver, validator, and proof semantics are not changed by this arc.
- S3b/S8 deferral lock is frozen:
  - core-ir proposer activation (`S3b`) and solver semantics v4 (`S8`) require separate lock docs and explicit continuity releases.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.
  - advice surfaces may expose stored trust evidence only.

### Acceptance

- Tests prove normative advice code paths do not invoke provider clients or materialization flows.
- Tests include `NoProviderCallsGuard` coverage that fails closed on provider client entrypoint invocation.
- No mutation side effects are observed for normative advice calls on locked fixtures.
- No-mutation tests include deterministic pre/post storage snapshot hash equality assertions.
- Tests prove advice output remains non-enforcing.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_NORMATIVE_ADVICE_*` additions in this arc are frozen:
  - `URM_ADEU_NORMATIVE_ADVICE_REQUEST_INVALID`
  - `URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND`
  - `URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID`
  - `URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID`
  - `URM_ADEU_NORMATIVE_ADVICE_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_NORMATIVE_ADVICE_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_NORMATIVE_ADVICE_REQUEST_INVALID` for unsupported pairing modes and ambiguous/non-unique deterministic pair resolution.
  - use `URM_ADEU_NORMATIVE_ADVICE_REQUEST_INVALID` for runtime non-enforcement-context violations in advice endpoints.
  - use `URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID` for manifest/run-key/surface-id/cap violations.
  - use `URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID` for emitted advice payload schema/content validation failures.
  - use `URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND` for persisted-lookup misses in advice inputs (including pair tuple absent in catalog and missing matched coherence diagnostics).
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v21 normative advice codes are additive and must not remove prior legacy error identifiers.

## Commit Plan (Small Green Commits)

1. `runtime: add deterministic normative advice packet builder over persisted cross-ir evidence`
2. `api: add read-only normative advice surface and deterministic response envelopes`
3. `metrics: add vnext_plus21 manifest and additive normative advice determinism keys`
4. `docs: add vnext_plus21 normative advice transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus21 replay fixtures, NoProviderCallsGuard coverage, non-enforcement checks, and no-mutation snapshot assertions`

## Intermediate Stage Preconditions and Outputs (Draft)

Before implementation PR1 for `vNext+21`, confirm v20 preconditions are frozen/merged and prepare v21 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS20.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/CROSS_IR_COHERENCE_TRANSFER_REPORT_vNEXT_PLUS20.md` (precondition cross-ir transfer baseline; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus21_manifest.json`
4. draft normative advice fixture scaffold for `adeu_normative_advice_packet@0.1`
5. draft transfer-report schema/renderer for `normative_advice_transfer_report.vnext_plus21@1`
6. deterministic env helper hook-up for v21 stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
7. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS21.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `N1`-`N4` merged with green CI.
- `artifact_normative_advice_packet_determinism_pct == 100.0` on locked fixtures.
- `artifact_normative_advice_projection_determinism_pct == 100.0` on locked fixtures.
- `vNext+21 -> vNext+22` frozen thresholds all pass.
- v16/v17/v18/v19/v20 continuity metrics remain present and at threshold (`100.0`).
- v21 closeout evidence includes runtime-observability comparison rows against v20 canonical baseline.
- no solver semantics contract delta and no trust-lane regression introduced.
- provider-parity continuity lock remains unchanged (no proposer surface expansion).
- all existing stop-gate tracked `vNext+6` through `vNext+20` metrics remain at threshold.
- `vNext+17` through `vNext+20` closeout evidence remains green and reproducible.
