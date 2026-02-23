# Locked Continuation vNext+20 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS19.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS19.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+19` (`R1`-`R4`) merged on `main` with green CI and closeout `all_passed = true` in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS19.md`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` default post-`vNext+19` ordering selects `vNext+20 = Path S4` (cross-IR coherence bridge).
- `vNext+16` and `vNext+17` integrity families remain stable, `vNext+18` tooling parity/budget continuity remains in force, and `vNext+19` read-surface activation is stable.
- This arc is reserved for deterministic cross-IR coherence bridge activation only:
  - deterministic concept-to-core-ir bridge mapping contract freeze first
  - deterministic cross-IR coherence diagnostics artifact family second
  - additive stop-gate determinism metrics for coherence payload stability third
  - explicit no-mutation and no-provider-expansion continuity fourth

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS18.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS19.md` remain authoritative for policy/proof/explain/runtime/provider-parity/core-ir/depth/integrity/read-surface baseline semantics.
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
- `adeu_core_ir@0.1`, `adeu_lane_projection@0.1`, `adeu_lane_report@0.1`, `adeu_projection_alignment@0.1`, `adeu_integrity_dangling_reference@0.1`, `adeu_integrity_cycle_policy@0.1`, `adeu_integrity_deontic_conflict@0.1`, `adeu_integrity_reference_integrity_extended@0.1`, `adeu_integrity_cycle_policy_extended@0.1`, `adeu_integrity_deontic_conflict_extended@0.1`, and `adeu_read_surface_payload@0.1` contracts remain frozen and unchanged in this arc.
- Bridge-version continuity lock is frozen:
  - existing bridge-version contracts remain authoritative:
    - `bridge_mapping_version = "adeu_to_concepts.v1"`
    - `bridge_loss_report.version = "adeu.bridge.loss.v1"`
  - any bridge-version bump is out-of-scope for this arc and requires a separate lock.
- Provider-parity continuity lock is frozen:
  - `vNext+14` provider matrix/manifest semantics remain unchanged in this arc.
  - this arc does not expand proposer provider surface sets.
- Integrity continuity lock from `vNext+16` + `vNext+17` is frozen:
  - v16/v17 integrity artifacts remain authoritative.
  - this arc reads persisted artifacts only; it does not rewrite integrity artifacts in place.
- Tooling continuity lock from `vNext+18` is frozen:
  - v18 parity/budget semantics remain authoritative.
  - this arc may reuse v18 shared helpers but may not weaken v18 parity or budget gates.
- Read-surface continuity lock from `vNext+19` is frozen:
  - v19 read-only endpoint semantics remain authoritative.
  - this arc layers deterministic cross-IR diagnostics over persisted artifacts and may not weaken v19 read determinism constraints.

## Arc Scope (Draft Lock)

This arc proposes Path S4 thin slice only:

1. `C1` Deterministic concept-to-core-ir bridge mapping contract freeze (including asymmetric unmappable handling)
2. `C2` Deterministic cross-IR coherence diagnostics artifact family with frozen issue taxonomy
3. `C3` Additive stop-gate determinism metrics for cross-IR coherence payload stability
4. `C4` Explicit no-mutation and no-provider-expansion lock continuity for `vNext+20 -> vNext+21`

Out-of-scope note:

- Path `S3b` (core-ir proposer activation) is not in this arc.
- Provider matrix/surface expansion is not in this arc.
- Solver semantics v4 work is not in this arc.
- DB-backed concept/core-ir coherence persistence migrations/new SQL tables are not in this arc.
- automatic patch/proposal generation from coherence diagnostics is not in this arc.
- payload offloading via blob-store/pre-signed URLs is not in this arc.
- sparse fieldset/query-driven partial payload retrieval is not in this arc.
- Mandatory frontend build-system expansion is not in this arc; optional minimal web rendering is allowed only if it does not introduce a new frontend build-system dependency.
- schema-family consolidation/unification is not in this arc and is deferred to a separate lock after v20 closeout.

## C1) Deterministic Concept-to-Core-IR Bridge Mapping Contract Freeze

### Goal

Freeze a deterministic, read-only mapping contract between persisted concept artifacts and persisted core-ir artifacts as the structural basis for cross-IR coherence diagnostics.

### Scope

- Add deterministic bridge-mapping artifact generation over persisted concept/core-ir inputs.
- Keep mapping output schema-validated and non-authoritative.
- Resolve concept/core-ir pairs from a fixture-backed catalog only in this arc.
- Preserve asymmetric unmappable evidence without implicit inference.

### Locks

- Pair-resolution catalog lock is frozen:
  - catalog path:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
  - catalog schema:
    - `cross_ir.vnext_plus20_catalog@1`
  - required entry fields:
    - `source_text_hash`
    - `core_ir_artifact_id`
    - `concept_artifact_id`
    - optional `created_at`
    - optional `domain_id`
    - optional `document_ref`
    - optional `intentional_concept_only_object_ids`
    - optional `intentional_core_ir_only_object_ids`
  - entries are deterministically ordered lexicographically by `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`.
- Pair-resolution identity lock is frozen:
  - deterministic pair identity and uniqueness key is exactly:
    - `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`
  - optional catalog metadata fields (`domain_id`, `document_ref`) are query/filter metadata only and may not alter pair identity or fallback resolution precedence.
- Pair-resolution authority lock is frozen:
  - cross-IR pairing in this arc is fixture-backed only from `cross_ir.vnext_plus20_catalog@1`.
  - filesystem globs, DB scans, and undeclared directories are out-of-scope for pair resolution.
  - non-unique or ambiguous pair resolution is request-invalid and fails closed.
- Bridge artifact schema lock is frozen:
  - `schema = "adeu_cross_ir_bridge_manifest@0.1"`
  - required top-level fields:
    - `source_text_hash`
    - `core_ir_artifact_id`
    - `concept_artifact_id`
    - `bridge_mapping_version`
    - `mapping_hash`
    - `entries`
    - `unmapped_concept_objects`
    - `unmapped_core_ir_objects`
  - each `entries[]` item includes:
    - `concept_object_id`
    - `concept_kind`
    - `core_ir_object_id`
    - `core_ir_kind`
    - `mapping_status`
    - `confidence_tag`
- Bridge-source continuity lock is frozen:
  - v20 `C1` mapping is a deterministic ConceptIR ↔ AdeuCoreIR pairing/mapping artifact over persisted payloads.
  - existing `adeu_ir -> ConceptIR` bridge outputs (`bridge_mapping_version`, `mapping_hash`) are continuity evidence inputs only and are not the authoritative structural mapping model for C1 pair construction.
- Bridge entry identity-kind lock is frozen:
  - `concept_kind` enum is exactly:
    - `term`
    - `sense`
    - `claim`
    - `link`
    - `ambiguity`
  - `core_ir_kind` enum is exactly:
    - `O.Entity`
    - `O.Concept`
    - `O.RelationType`
    - `E.Claim`
    - `E.Assumption`
    - `E.Question`
    - `E.Evidence`
    - `D.PhysicalConstraint`
    - `D.Norm`
    - `D.Policy`
    - `D.Exception`
    - `U.Goal`
    - `U.Metric`
    - `U.Preference`
    - `edge_signature`
  - `confidence_tag` enum is exactly:
    - `direct`
    - `derived`
    - `missing_provenance`
- Bridge object-id binding lock is frozen:
  - `concept_object_id` must reference a canonical object id from the persisted ConceptIR payload:
    - `terms[].id`, `senses[].id`, `claims[].id`, `links[].id`, or `ambiguity[].id`.
  - when `core_ir_kind != edge_signature`, `core_ir_object_id` must reference a canonical `AdeuCoreIR.nodes[].id` whose node signature exactly matches `core_ir_kind`.
  - when `core_ir_kind = edge_signature`, `core_ir_object_id` must use deterministic form:
    - `edge:{type}:{from}:{to}`
    where `{type}` is a frozen `EdgeType` value from `adeu_core_ir@0.1`.
- Bridge-version continuity lock is frozen for mapping payloads:
  - `bridge_mapping_version` and `mapping_hash` are read-through continuity evidence from persisted bridge inputs.
  - handlers/builders may not synthesize alternate mapping versions or rewrite persisted mapping hashes.
  - mismatched mapping-version/hash evidence is payload-invalid and fails closed.
- Mapping-hash authority lock is frozen:
  - `mapping_hash` in v20 bridge payloads is an authoritative passthrough field from persisted bridge-source artifacts.
  - v20 bridge/coherence builders must not recompute `mapping_hash` from cross-IR payload fields (`entries`, `unmapped_*`, or diagnostic envelopes).
  - `mapping_hash` is opaque continuity evidence and is not the canonical hash of v20 `adeu_cross_ir_bridge_manifest@0.1`.
- Bridge-manifest hash lock is frozen:
  - canonical v20 bridge-manifest hash input is:
    - `{source_text_hash, core_ir_artifact_id, concept_artifact_id, bridge_mapping_version, entries, unmapped_concept_objects, unmapped_core_ir_objects}`
  - excluded from this canonical hash input:
    - `mapping_hash`
    - `created_at`
  - `bridge_manifest_hash` in C2 artifacts must equal `sha256` over this canonical projection.
- Asymmetric unmappable handling lock is frozen:
  - deterministic `mapping_status` enum is exactly:
    - `mapped`
    - `concept_only`
    - `core_ir_only`
  - unmappable evidence must be preserved in `unmapped_concept_objects` and `unmapped_core_ir_objects`; silent dropping is forbidden.
  - no inferred semantic equivalence may be synthesized for unmappable objects.
- Intentional-asymmetry partition lock is frozen:
  - optional catalog allowlists:
    - `intentional_concept_only_object_ids`
    - `intentional_core_ir_only_object_ids`
    declare expected model-boundary asymmetries for a pair.
  - objects listed in these allowlists remain represented with `mapping_status` (`concept_only`/`core_ir_only`) but are treated as intentional asymmetries in coherence defect classification (`C2`) rather than extraction defects.
- Deterministic ordering lock is frozen:
  - `entries[]` are ordered lexicographically by:
    - `concept_object_id`
    - `core_ir_object_id`
    - `concept_kind`
    - `core_ir_kind`
    - `mapping_status`
  - `unmapped_concept_objects` and `unmapped_core_ir_objects` are lexicographically ordered by object id.
- Read-authority and mutation lock is frozen:
  - bridge mapping reads persisted artifacts only.
  - no materialization/proposer/repair execution is allowed on miss.
  - mapping handlers/builders are read-only and may not mutate canonical ADEU artifacts.
- Consumer-interpretation lock is frozen:
  - `created_at` (when present) is metadata only and may not affect mapping equivalence.
  - determinism hashing in `C3` excludes `created_at` recursively.

### Acceptance

- Locked bridge fixtures return schema-valid bridge payloads for persisted concept/core-ir pairs.
- Identical persisted inputs replay to byte-identical bridge payloads.
- Ambiguous pair-resolution cases fail closed with deterministic error envelopes.

## C2) Deterministic Cross-IR Coherence Diagnostics Artifact Family

### Goal

Emit deterministic, read-only coherence diagnostics describing structural divergence between concept and core-ir artifacts.

### Scope

- Add deterministic coherence diagnostics builder over `C1` bridge payloads and persisted artifacts.
- Freeze issue taxonomy and ordering semantics for first-slice structural coherence.
- Extend transfer-report evidence with cross-IR coherence summaries.

### Locks

- Coherence artifact schema lock is frozen:
  - `schema = "adeu_cross_ir_coherence_diagnostics@0.1"`
  - required top-level fields:
    - `source_text_hash`
    - `core_ir_artifact_id`
    - `concept_artifact_id`
    - `bridge_manifest_hash`
    - `issue_summary`
    - `issues`
  - `issue_summary` required fields:
    - `total_issues`
    - `counts_by_code`
    - `counts_by_severity`
- Issue taxonomy lock is frozen:
  - allowed `issue_code` values are exactly:
    - `MISSING_CONCEPT_MAPPING`
    - `MISSING_CORE_IR_MAPPING`
    - `TOPOLOGY_DRIFT`
    - `CLAIM_PROJECTION_GAP`
    - `LINK_KIND_DRIFT`
    - `SOURCE_HASH_MISMATCH`
    - `TRUST_LABEL_MISMATCH`
  - allowed `severity` values are exactly:
    - `warn`
    - `error`
- Issue detection semantics lock is frozen:
  - `MISSING_CONCEPT_MAPPING`:
    - emit when a concept object appears as `mapping_status = concept_only` in the bridge manifest and the object id is not listed in `intentional_concept_only_object_ids`.
  - `MISSING_CORE_IR_MAPPING`:
    - emit when a core-ir object appears as `mapping_status = core_ir_only` in the bridge manifest and the object id is not listed in `intentional_core_ir_only_object_ids`.
  - `TOPOLOGY_DRIFT`:
    - emit when mapped endpoint objects exist on both sides but relation topology diverges:
      - relation/link exists in concept-side structure but corresponding mapped relation/edge is absent in core-ir-side structure, or
      - relation/edge exists in core-ir-side structure but corresponding mapped relation/link is absent in concept-side structure.
  - `CLAIM_PROJECTION_GAP`:
    - emit when a concept claim object exists and no `mapping_status = mapped` bridge entry links that claim to frozen claim-like target set:
      - `E.Claim`
      - `D.Norm`
      - `D.Policy`
    - a claim is considered projected iff there exists at least one bridge entry with:
      - `concept_kind = claim`
      - `mapping_status = mapped`
      - `core_ir_kind in {E.Claim, D.Norm, D.Policy}`
  - `LINK_KIND_DRIFT`:
    - concept-side link kind is sourced from persisted `ConceptIR.links[].kind` (frozen enum).
    - core-ir-side category token is sourced from mapped `edge_signature` relations only when:
      - edge `type = excepts`, and
      - edge `to` endpoint node signature is one of `D.PhysicalConstraint`, `D.Norm`, `D.Policy`.
    - core-ir category derivation is frozen:
      - `excepts -> D.PhysicalConstraint => defeats`
      - `excepts -> D.Norm => narrows`
      - `excepts -> D.Policy => clarifies`
    - emit when a mapped concept link and mapped core-ir exception-edge relation pair disagree under frozen category-to-link mapping:
      - `defeats -> incompatibility`
      - `narrows -> presupposition`
      - `clarifies -> commitment`
  - `SOURCE_HASH_MISMATCH`:
    - emit when concept and core-ir `source_text_hash` values disagree, or either disagrees with catalog `source_text_hash`.
  - `TRUST_LABEL_MISMATCH`:
    - emit only when both mapped sides expose stored trust labels and those labels differ.
    - trust-label sources are frozen:
      - concept-side label comes from persisted concept-side stored trust metadata in the pairing context.
      - core-ir-side label comes from persisted core-ir-side stored trust metadata in the pairing context.
    - trust labels are read-only evidence and may not be recomputed from solver/runtime state in this arc.
- Structural-only coherence lock is frozen:
  - coherence diagnostics in this arc are structural evidence only.
  - diagnostics may not claim semantic equivalence/non-equivalence beyond frozen structural checks.
  - diagnostics may not mutate concept/core-ir/integrity artifacts.
- Issue payload lock is frozen:
  - each `issues[]` item includes:
    - `issue_id`
    - `issue_code`
    - `severity`
    - `concept_refs` (deterministically ordered)
    - `core_ir_refs` (deterministically ordered)
    - `message` (non-authoritative prose)
    - `evidence` (deterministic constrained object per frozen evidence-shape lock)
- Issue-id formation lock is frozen:
  - `concept_refs` and `core_ir_refs` must be lexicographically sorted before issue-id hash computation.
  - `issue_id` must be deterministic and derived from canonical issue content only:
    - `issue_id = sha256(canonical_json({"issue_code": issue_code, "concept_refs": concept_refs, "core_ir_refs": core_ir_refs, "evidence": evidence}))[:16]`
  - random IDs, UUIDs, and insertion-order counters are forbidden for `issue_id`.
- Evidence-shape lock is frozen:
  - `evidence.kind` enum is exactly:
    - `bridge_entry`
    - `unmapped`
    - `topology`
    - `hashes`
    - `trust_labels`
  - allowed `evidence` shapes are:
    - `{"kind":"bridge_entry","entry_ref":"<stable-entry-ref>"}`
    - `{"kind":"unmapped","side":"concept|core_ir","object_id":"<id>"}`
    - `{"kind":"topology","concept_relation_ref":"<id>","core_ir_relation_ref":"<id|null>","relation_key":"<stable-key>"}`
    - `{"kind":"hashes","concept_source_text_hash":"<sha256>","core_ir_source_text_hash":"<sha256>","catalog_source_text_hash":"<sha256>","concept_source_excerpt_prefix":"<optional-prefix>","core_ir_source_excerpt_prefix":"<optional-prefix>"}`
    - `{"kind":"trust_labels","concept_trust":"<label>","core_ir_trust":"<label>"}`
  - additional `evidence.kind` values or keys are out-of-scope for v20.
  - topology relation-key lock:
    - `relation_key = sha256(canonical_json({"concept_relation_ref": concept_relation_ref, "core_ir_relation_ref": core_ir_relation_ref or ""}))[:16]`
    - random IDs, UUIDs, and insertion-order counters are forbidden for `relation_key`.
  - `SOURCE_HASH_MISMATCH` triage lock:
    - when persisted source text is available for both sides, `evidence.kind = "hashes"` may include deterministic prefix snippets:
      - `concept_source_excerpt_prefix`
      - `core_ir_source_excerpt_prefix`
    - each prefix is exactly the first 50 Unicode code points from persisted source text without normalization or trimming.
    - snippets are optional triage fields; when present they are included in canonical determinism hashing and comparison.
- Deterministic ordering lock is frozen:
  - `issues[]` are ordered lexicographically by:
    - `issue_code`
    - first concept ref (or empty string)
    - first core-ir ref (or empty string)
    - `issue_id`
  - `counts_by_code` keys and `counts_by_severity` keys are emitted in lexicographic order.
- Quality projection lock is frozen:
  - additive cross-IR quality projection artifact schema:
    - `schema = "cross_ir_quality_projection.vnext_plus20@1"`
  - required top-level fields:
    - `bridge_pair_count`
    - `coherence_issue_count`
    - `coherence_counts_by_code`
    - `coherence_counts_by_severity`
  - quality projection is reporting-only and may not mutate source artifacts.
- Transfer report lock is frozen:
  - output path:
    - `docs/CROSS_IR_COHERENCE_TRANSFER_REPORT_vNEXT_PLUS20.md`
  - report includes machine-checkable fenced JSON block with top-level keys:
    - `schema = "cross_ir_transfer_report.vnext_plus20@1"`
    - `vnext_plus20_manifest_hash`
    - `coverage_summary`
    - `bridge_mapping_summary`
    - `coherence_diagnostics_summary`
    - `quality_projection_summary`
    - `replay_summary`
- Replay boundary lock is frozen:
  - no live provider calls are permitted in deterministic cross-IR coherence acceptance paths.

### Acceptance

- Coherence diagnostics fixtures replay to byte-identical outputs for identical persisted inputs.
- Coherence transfer-report payload is deterministic and schema-valid.

## C3) Stop-Gate Determinism Metrics For Cross-IR Coherence Payloads

### Goal

Make cross-IR bridge/coherence determinism measurable and reproducible, with additive stop-gate metrics for `vNext+20 -> vNext+21`.

### Scope

- Add manifest-driven fixture accountability for cross-IR coherence outputs.
- Extend additive `stop_gate_metrics@1` with v20 cross-IR keys.
- Preserve v16-v19 continuity metrics and thresholds.

### Locks

- Coverage manifest lock is frozen:
  - path:
    - `apps/api/fixtures/stop_gate/vnext_plus20_manifest.json`
  - schema:
    - `stop_gate.vnext_plus20_manifest@1`
  - required:
    - `replay_count == 3`
- Surface enumeration completeness lock is frozen:
  - frozen v20 cross-IR `surface_id` set is exactly:
    - `adeu.cross_ir.bridge_mapping`
    - `adeu.cross_ir.coherence_diagnostics`
    - `adeu.cross_ir.quality_projection`
  - manifest fixture `surface_id` values must be members of this frozen set only.
- Manifest shape lock is frozen:
  - required fixture lists are:
    - `cross_ir_bridge_mapping_fixtures`
    - `cross_ir_coherence_diagnostics_fixtures`
    - `cross_ir_quality_projection_fixtures`
  - each fixture entry includes deterministic identity and persisted evidence refs.
- Run-reference key lock is frozen:
  - required run keys are:
    - `cross_ir_bridge_mapping_fixtures[].runs[].cross_ir_bridge_mapping_path`
    - `cross_ir_coherence_diagnostics_fixtures[].runs[].cross_ir_coherence_diagnostics_path`
    - `cross_ir_quality_projection_fixtures[].runs[].cross_ir_quality_projection_path`
  - missing required run keys are fixture-invalid and fail closed.
- Fixture-path semantics lock is frozen:
  - `*_path` inputs are captured deterministic JSON artifact payloads from the v20 in-process harness (no live-network dependency), not ad hoc derived summaries.
  - captured payloads include the full artifact JSON body including top-level `schema`.
  - `cross_ir_bridge_mapping_path` captures `adeu_cross_ir_bridge_manifest@0.1` payloads.
  - `cross_ir_coherence_diagnostics_path` captures `adeu_cross_ir_coherence_diagnostics@0.1` payloads.
  - `cross_ir_quality_projection_path` captures `cross_ir_quality_projection.vnext_plus20@1` payloads.
  - capture order is frozen lexicographically by `(source_text_hash, core_ir_artifact_id, concept_artifact_id)`.
  - capture envelope stores only:
    - parsed JSON response/artifact payload (canonicalized on write),
    - deterministic harness metadata required for traceability.
  - response headers are excluded from capture envelopes and determinism hash inputs.
- Non-empty evidence floor lock is frozen:
  - at least one locked coherence fixture must emit `total_issues > 0`.
  - at least one locked coherence fixture must emit one or more issues in:
    - `MISSING_CONCEPT_MAPPING`
    - `MISSING_CORE_IR_MAPPING`
    - `SOURCE_HASH_MISMATCH`
- Determinism metric computation lock is frozen:
  - determinism hash input is canonical JSON from loaded captured payloads (`sha256_canonical_json(load_json(path))`), not raw bytes.
  - hash projection excludes `created_at` fields recursively at any depth in captured JSON; no other fields are excluded.
  - replay exactly `N=3` times per fixture.
  - fixture passes only when all replay hashes match.
  - `pct = 100 * passed / total`.
- Deterministic performance-optimization lock is frozen:
  - v18 bounded-optimization patterns may be applied to v20 cross-IR hashing paths.
  - allowed optimization includes deterministic sub-component pre-hashing/caching keyed by canonical input payload hashes.
  - allowed optimization includes concurrent replay execution for `N=3` only when:
    - each replay runs in an isolated process with deterministic environment lock enforced (`TZ=UTC`, `LC_ALL=C`),
    - fixture execution order is seeded from frozen lexicographic fixture order,
    - replay result aggregation is reduced in deterministic lexicographic fixture/run order.
  - CI stop-gate entrypoints should default to this concurrent replay mode for v20 cross-IR fixtures to preserve v18 runtime-budget continuity constraints.
  - optimization may not alter fixture selection, replay count, hash projection rules, or pass/fail semantics.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `artifact_cross_ir_bridge_mapping_determinism_pct`
  - `artifact_cross_ir_coherence_diagnostics_determinism_pct`
  - `artifact_cross_ir_quality_projection_determinism_pct`
- Continuity-threshold lock is frozen:
  - v16/v17/v18/v19 thresholds remain required and unchanged in v20 closeout.
  - this includes v18 tooling budget continuity:
    - `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0`
  - v20 closeout evidence must include an explicit runtime-observability comparison row against v19 canonical closeout baseline.
- Threshold lock is frozen for `vNext+20 -> vNext+21`:
  - `artifact_cross_ir_bridge_mapping_determinism_pct == 100.0`
  - `artifact_cross_ir_coherence_diagnostics_determinism_pct == 100.0`
  - `artifact_cross_ir_quality_projection_determinism_pct == 100.0`
  - v16/v17/v18/v19 continuity thresholds remain required and unchanged.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus20_manifest_hash`.
  - mismatch fails closed.

### Acceptance

- Cross-IR coverage accounting is reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+20` thresholds.
- Locked fixtures prove non-empty detector behavior (not all-zero issue outputs).

## C4) No-Mutation And No-Provider-Expansion Continuity

### Goal

Keep v20 cross-IR coherence activation strictly read-only and prevent silent drift into proposer/provider or mutation semantics.

### Scope

- Freeze explicit continuity constraints for `vNext+20 -> vNext+21`.
- Separate cross-IR coherence diagnostics from proposer activation.
- Preserve v14-v19 operational and trust boundaries.

### Locks

- No-provider-expansion lock is frozen:
  - this arc introduces no proposer/provider surfaces.
  - provider matrix/surface-set continuity from `vNext+14` remains unchanged.
- No-provider-calls guard lock is frozen:
  - cross-IR bridge/coherence handlers must be covered by deterministic tests using a `NoProviderCallsGuard` runtime helper.
  - guard behavior is fail-closed: any provider client entrypoint invocation in guarded cross-IR paths fails the test.
  - guard coverage must also enforce outbound-network denial in test context (socket-level fail-closed boundary) so provider/network calls cannot bypass high-level client patching.
- No-mutation lock is frozen:
  - cross-IR entrypoints/builders must not write canonical ADEU artifacts or mutate persisted concept/core-ir/lane/integrity artifacts.
  - canonical artifacts remain generated by existing materialization/closeout flows only.
- No-mutation verification lock is frozen:
  - deterministic no-mutation tests must compare pre/post snapshots over the v20 fixture-backed mutable surface only:
    - `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json`
    - all artifact JSON files referenced by that catalog.
  - snapshot comparison is hash-based over canonical file contents (`sha256_canonical_json(load_json(path))`) and must remain byte-identical for read-only calls.
- No-solver-change lock is frozen:
  - solver, validator, and proof semantics are not changed by this arc.
- S3b deferral lock is frozen:
  - any core-ir proposer activation requires a separate lock doc and explicit provider continuity release.
  - S3b work is out-of-scope for v20.
- Trust-lane continuity lock is frozen:
  - this arc does not add or reinterpret trust-lane taxonomy.
  - cross-IR surfaces may expose stored trust evidence only.

### Acceptance

- Tests prove cross-IR bridge/coherence code paths do not invoke provider clients or materialization flows.
- Tests include `NoProviderCallsGuard` coverage that fails closed on provider client entrypoint invocation.
- No mutation side effects are observed for cross-IR calls on locked fixtures.
- No-mutation tests include deterministic pre/post storage snapshot hash equality assertions.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_CROSS_IR_*` additions in this arc are frozen:
  - `URM_ADEU_CROSS_IR_REQUEST_INVALID`
  - `URM_ADEU_CROSS_IR_ARTIFACT_NOT_FOUND`
  - `URM_ADEU_CROSS_IR_PAYLOAD_INVALID`
  - `URM_ADEU_CROSS_IR_FIXTURE_INVALID`
  - `URM_ADEU_CROSS_IR_DIAGNOSTIC_DRIFT`
  - `URM_ADEU_CROSS_IR_MANIFEST_HASH_MISMATCH`
- Error-domain boundary lock is frozen:
  - use `URM_ADEU_CROSS_IR_REQUEST_INVALID` for unsupported pairing modes and ambiguous/non-unique deterministic pair resolution.
  - use `URM_ADEU_CROSS_IR_FIXTURE_INVALID` for manifest/run-key/surface-id/cap violations.
  - use `URM_ADEU_CROSS_IR_PAYLOAD_INVALID` for emitted bridge/coherence payload schema/content validation failures.
  - use `URM_ADEU_CROSS_IR_ARTIFACT_NOT_FOUND` for persisted-lookup misses in cross-IR inputs.
- Compatibility lock is frozen:
  - existing endpoint error shapes/codes remain accepted for compatibility.
  - new v20 cross-IR codes are additive and must not remove prior legacy error identifiers.

## Commit Plan (Small Green Commits)

1. `api: add deterministic cross-ir bridge mapping artifact builder with fixture catalog resolution`
2. `runtime: add deterministic cross-ir coherence diagnostics artifact + quality projection`
3. `metrics: add vnext_plus20 manifest and additive cross-ir determinism keys`
4. `docs: add vnext_plus20 cross-ir coherence transfer report and closeout scaffold`
5. `tests: add deterministic vnext_plus20 replay fixtures, NoProviderCallsGuard coverage, and no-mutation snapshot assertions`

## Intermediate Stage Preconditions And Outputs (Draft)

Before implementation PR1 for `vNext+20`, confirm v19 preconditions are frozen/merged and prepare v20 scaffolding artifacts:

1. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS19.md` (precondition closeout gate artifact; frozen + merged)
2. `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` (precondition post-`vNext+19` baseline refresh; frozen + merged)
3. initial fixture inventory for `apps/api/fixtures/stop_gate/vnext_plus20_manifest.json`
4. frozen cross-IR catalog scaffold `apps/api/fixtures/cross_ir/vnext_plus20_catalog.json` (`cross_ir.vnext_plus20_catalog@1`)
5. draft transfer-report schema/renderer for `cross_ir_transfer_report.vnext_plus20@1`
6. deterministic env helper hook-up for cross-IR stop-gate/report entrypoints (`TZ=UTC`, `LC_ALL=C`)
7. draft closeout skeleton `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS20.md` for end-of-arc evidence capture

## Exit Criteria (Draft)

- `C1`-`C4` merged with green CI.
- `artifact_cross_ir_bridge_mapping_determinism_pct == 100.0` on locked fixtures.
- `artifact_cross_ir_coherence_diagnostics_determinism_pct == 100.0` on locked fixtures.
- `artifact_cross_ir_quality_projection_determinism_pct == 100.0` on locked fixtures.
- `vNext+20 -> vNext+21` frozen thresholds all pass.
- v16/v17/v18/v19 continuity metrics remain present and at threshold (`100.0`).
- v20 closeout evidence includes runtime-observability comparison rows against v19 canonical baseline.
- No solver semantics contract delta and no trust-lane regression introduced.
- Provider-parity continuity lock remains unchanged (no proposer surface expansion).
- All existing stop-gate tracked `vNext+6` through `vNext+19` metrics remain at threshold.
- `vNext+16` through `vNext+19` closeout evidence remains green and reproducible.
