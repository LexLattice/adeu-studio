# Locked Continuation vNext+10 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS9.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS9.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- vNext+9 (`R1`-`R4`) merged on `main` with green CI and stop-gate `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` recommends `vNext+10 = Path 5` (semantic depth v3.1).
- This arc is reserved for semantic-depth quality hardening only:
  - pairwise interaction/conflict surfaces first
  - ranking/provenance and coherence diagnostics second
  - quality stop-gate hardening third

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS7.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS8.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS9.md` remain authoritative for policy/proof/explain/runtime semantics.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- LLM-derived signals are advisory only:
  - they may not override deterministic evidence dimensions in ranking/selection.
- Thin-slice scope boundary is frozen:
  - semantic-depth rollout in this arc is pairwise only (two-document surfaces).
  - no N-way cross-document interaction rollout in this arc.
- Pairwise analysis strategy lock is frozen:
  - strategy for this arc is `compare_and_synthesize_v1`:
    - run single-document concept/coherence analysis independently per input artifact,
    - project both analyses into canonical deterministic signatures,
    - synthesize pairwise conflict items from deterministic signature comparison rules.
  - merged/joint pairwise SMT formula construction is out of scope in this arc.
- Signature projection version lock is frozen:
  - canonical per-document signature projection version is:
    - `signature_projection_version = "semantic_depth.signature.v1"`.
- Cross-document framing lock is frozen:
  - pairwise conflict surfaces are defined for arbitrary two-document inputs.
  - version-delta comparisons are treated as a subset of pairwise inputs, not a separate semantic contract.
- Semantic-depth compute location lock is frozen:
  - pairwise semantic-depth compute logic must live in a dedicated module/package path (for example `packages/adeu_semantic_depth/...`).
  - existing `adeu_concepts` single-document APIs remain authoritative for per-document analysis inputs and are not refactored into pairwise semantics in this arc.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- Hidden randomness is forbidden in deterministic/replay mode:
  - UUID/random ids must be explicit input, deterministic derivation, or be used only behind persisted-artifact determinism boundaries.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Semantic-depth outputs/reports must be reproducible from persisted artifacts only:
  - no live environment/process reads for deterministic replay decisions/reports.
- Semantic-depth derive/materialize boundary is frozen:
  - read/derive semantic-depth calls are pure and do not append events.
  - semantic-depth artifact persistence/event emission is allowed only through explicit materialization flow in this arc.
- Versioned artifacts introduced in this arc must have explicit schemas under `spec/`:
  - `semantic_depth_report@1`
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)

## Arc Scope (Draft Lock)

This arc proposes only Path 5 thin-slice implementation:

1. `D1` Pairwise interaction/conflict surface normalization + `semantic_depth_report@1` hardening
2. `D2` Ranking objective/provenance v1 + deterministic tie-breaks
3. `D3` Coherence diagnostics permutation invariance expansion
4. `D4` Replay metrics + stop-gate hardening for semantic-depth quality gates

## D1) Pairwise Conflict Surface + Report Contract

### Goal

Operationalize deterministic pairwise interaction/conflict reporting on top of semantics-v3 without changing solver semantics.

### Scope

- Introduce/freeze `semantic_depth_report@1` schema under `spec/`.
- Normalize pairwise conflict surfaces for exactly two input artifacts.
- Add deterministic hash and linkage fields for depth reports.
- Add explicit semantic-depth materialization endpoint for evidence capture:
  - `POST /urm/semantic_depth/materialize` (idempotent via `client_request_id`).
- Freeze materialization storage model for semantic-depth reports:
  - persist materialized semantic-depth packets in a dedicated semantic-depth report store keyed by `semantic_depth_report_id`.
  - do not overload IR `artifacts` source-of-truth rows for semantic-depth packet persistence.

### Locks

- Pairwise-only lock is frozen:
  - each report includes exactly two input artifact refs.
  - report materialization fails closed for input cardinality != 2.
- Canonical pair-order lock is frozen:
  - input pair refs are sorted lexicographically before report materialization.
- `semantic_depth_report@1` minimum contract is frozen:
  - `schema = "semantic_depth_report@1"`
  - `input_artifact_refs` (length `2`, sorted)
  - `signature_projection_version`
  - `ranking_objective_version`
  - `ranking_tie_break_version`
  - `conflict_items`
  - `ranked_conflict_ids`
  - `coherence_summary` (optional)
  - `coherence_summary_hash` (optional, required when `coherence_summary` present)
  - `hash_excluded_fields`
  - optional linkage refs (`diff_refs`, `witness_refs`, `semantics_diagnostics_ref`, `explain_diff_ref`)
  - `semantic_depth_hash = sha256(canonical_json(report_without_nonsemantic_fields))`
- Conflict identity lock is frozen:
  - each conflict item must carry deterministic `conflict_id`.
  - `conflict_id` is computed as:
    - `sha256(canonical_json(conflict_key))`
  - `conflict_key` reference fields are typed:
    - `subject_ref`, `object_ref`, optional `predicate_ref`, and optional `locus_ref` must use the frozen typed ref union compatible with `adeu_ir` reference modeling (for example `{entity|def|doc|text}` forms).
    - raw untyped string refs are forbidden in semantic conflict-key payloads.
  - canonical `conflict_key` fields are frozen:
    - `kind`
    - `subject_ref`
    - `object_ref`
    - optional `predicate_ref`
    - optional `locus_ref`
  - `kind` is frozen as an enum in `spec/semantic_depth_report.schema.json`; non-enum `kind` values fail closed deterministically.
  - duplicate `conflict_id` within one report fails closed deterministically.
- Subject/object assignment lock is frozen:
  - after canonical pair ordering, `subject_ref` must point to an entity in lexicographically-first artifact and `object_ref` must point to an entity in lexicographically-second artifact.
  - asymmetric semantic role information may be carried only via explicit role fields (for example `subject_role`, `object_role`) and may not alter canonical subject/object assignment.
- Report ref-format lock is frozen:
  - semantic-depth linkage refs must be canonical `artifact:<...>` or `event:<stream_id>#<seq>` forms only.
  - refs outside frozen forms fail closed in deterministic validation/materialization paths.
- Linkage resolution lock is frozen:
  - optional linkage refs are render/linkage aids and do not alter semantic-depth ranking semantics.
  - when linkage refs are provided on deterministic materialization paths, each ref must resolve from persisted artifact/event stores; unresolved refs fail closed with `URM_SEMANTIC_DEPTH_INVALID_REF`.
  - absent optional linkage refs are omitted (no implicit `null` insertion).
- Canonical ordering lock is frozen:
  - `conflict_items` are canonicalized by `conflict_id ASC` only.
  - ranking order is represented only by `ranked_conflict_ids` from `D2`.
- Nonsemantic exclusion lock is frozen:
  - `semantic_depth_hash` exclusion set is explicit and schema-frozen (for example `client_request_id`, `request_id`, transient timestamps, `*_raw`, operator notes).
- Derive/materialize side-effect lock is frozen:
  - read/derive semantic-depth calls are pure derivations and do not append events.
  - materialized depth artifact/event emission is allowed only through `POST /urm/semantic_depth/materialize`.
- Materialization event lock is frozen:
  - `POST /urm/semantic_depth/materialize` emits exactly one `SEMANTIC_DEPTH_MATERIALIZED` event per idempotency key.
  - materialization idempotency semantic key is frozen:
    - `(schema, signature_projection_version, ranking_objective_version, ranking_tie_break_version, semantic_depth_hash)`.
    - same `client_request_id` + same semantic key replays idempotently.
    - same `client_request_id` + different semantic key fails closed with `URM_SEMANTIC_DEPTH_IDEMPOTENCY_CONFLICT`.
  - event payload must include deterministic linkage fields:
    - `parent_stream_id`
    - `parent_seq`
    - `artifact_ref`
    - `client_request_id`
  - event minima validation is frozen:
    - all required linkage fields above must be present and schema-valid at emit time; missing/invalid required fields fail closed deterministically.
  - event appends to the governed parent stream identified by `parent_stream_id`.

### Acceptance

- `semantic_depth_report@1` payloads validate against schema.
- Identical persisted pairwise inputs replay to byte-identical reports.
- `semantic_depth_hash` recomputation matches embedded hash on deterministic fixtures.
- Materialization idempotency fixtures pass:
  - same `client_request_id` + same semantic payload replays response/event without duplicate materialization.
  - same `client_request_id` + different semantic payload fails closed deterministically.

## D2) Ranking Objective + Provenance v1

### Goal

Freeze deterministic ranking behavior for pairwise conflict surfaces with explicit provenance.

### Scope

- Add frozen ranking objective/tie-break versioning.
- Emit deterministic ranking provenance in report payloads.
- Lock ranking reproducibility for identical persisted inputs.

### Locks

- Ranking version lock is frozen:
  - `ranking_objective_version = "semantic_depth.rank.v1"`
  - `ranking_tie_break_version = "semantic_depth.tie_break.v1"`
- Ranking provenance lock is frozen:
  - each ranked conflict includes deterministic provenance dimensions used by objective evaluation.
  - minimum provenance shape is frozen:
    - `priority`
    - `confidence_milli`
    - `evidence_kind`
    - `source_ref_ids` (sorted canonical refs)
    - optional `solver_status`
- Deterministic objective lock is frozen:
  - ranking dimensions may use persisted deterministic evidence only.
  - advisory LLM signals may be included only in `*_raw` non-semantic provenance and may not change deterministic ordering in any mode.
- Priority derivation lock is frozen:
  - `priority` must be derived from a frozen `kind -> priority` mapping table in `spec/semantic_depth_report.schema.json` (mirrored into runtime constants for implementation).
  - runtime/model heuristics may not mutate priority mapping in this arc.
- Tie-break lock is frozen:
  - ties are resolved deterministically by `(priority DESC, confidence_milli DESC, conflict_id ASC)`.
- Numeric determinism lock is frozen:
  - ranking confidence values in semantic payloads are encoded as deterministic fixed-point integers (`confidence_milli` in `[0, 1000]`).
  - floating-point confidence fields are forbidden in semantic ranking payloads.
  - if confidence is derived from rational quantities, conversion boundary is frozen:
    - `confidence_milli = floor((num * 1000 + denom // 2) / denom)` for `denom > 0`.
  - invalid rational inputs (`denom <= 0`) fail closed deterministically with `URM_SEMANTIC_DEPTH_CONFIDENCE_INVALID`.
- Ranking/output alignment lock is frozen:
  - `ranked_conflict_ids` ordering must be derivable from frozen objective + tie-break versions with no hidden heuristics.

### Acceptance

- Identical persisted inputs replay to byte-identical ranked order.
- Ranking provenance fields are present and schema-valid for all ranked conflicts.

## D3) Coherence Diagnostics Permutation Invariance

### Goal

Expand coherence diagnostics while preserving permutation-invariant behavior.

### Scope

- Add permutation-invariance diagnostics over pairwise equivalent fixture groups.
- Emit deterministic coherence summary and linkage in `semantic_depth_report@1`.

### Locks

- Permutation invariance lock is frozen:
  - for a fixture permutation group with equivalent semantic inputs, coherence summary outputs/hashes must be identical across all permutations.
- Permutation fixture-group definition lock is frozen:
  - fixture groups must include at least one meaning-preserving intra-artifact permutation case (for example ordering of declarations/clauses), not only input-pair swap.
  - input-pair swap alone is insufficient to satisfy D3 fixture coverage.
  - each permutation fixture group must include at least `3` variants:
    - canonical baseline,
    - one input-pair swap,
    - one intra-artifact meaning-preserving permutation.
  - per-group replay cap is frozen to `max_permutations_per_group = 6`.
- Coherence hash lock is frozen:
  - `coherence_summary_hash = sha256(canonical_json(coherence_summary_without_nonsemantic_fields))`.
- Coherence canonicalization boundary lock is frozen:
  - invariance is enforced at canonicalized IR projection boundary before report materialization.
  - canonicalized coherence summary may not depend on raw atom labels, assertion names, or raw JSON path indices that vary under meaning-preserving permutation.
  - canonicalized coherence summary may not depend on raw artifact IDs/refs that are permutation-variant; such linkage values are allowed only in explicitly non-semantic excluded fields.
- Coherence summary scope lock is frozen:
  - `coherence_summary` reports:
    - per-document coherence outcomes for the two inputs,
    - pairwise conflict-surface coherence aggregate for the synthesized pair.
  - it does not introduce a new solver semantic contract.
- Failure handling lock is frozen:
  - permutation mismatch in deterministic fixtures fails closed and emits deterministic validation error.
- No semantic override lock is frozen:
  - coherence diagnostics are quality/reporting signals only and may not mutate solver semantic outcomes.

### Acceptance

- Permutation fixtures pass with invariant coherence hashes.
- Coherence diagnostics remain deterministic across replay reruns.

## D4) Semantic-Depth Replay Metrics + Stop-Gate Hardening

### Goal

Add reproducible semantic-depth closeout metrics to decide if `vNext+11` may start.

### Scope

- Extend additive `stop_gate_metrics@1` fields for semantic-depth quality gates.
- Add deterministic fixture-based metric computation and report rendering.

### Locks

- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `concept_conflict_precision_pct`
  - `concept_conflict_recall_pct`
  - `coherence_permutation_stability_pct`
- Metric computation lock is frozen:
  - precision/recall are computed from locked labeled pairwise fixtures only.
  - matching semantics are frozen:
    - predicted set = `{conflict_id}` emitted by semantic-depth report.
    - locked fixture labels store canonical `conflict_key` entries (not precomputed conflict IDs).
    - expected set = `{sha256(canonical_json(conflict_key))}` derived deterministically from fixture labels.
    - TP/FP/FN are computed per fixture and micro-averaged across manifest fixtures.
  - coherence stability is computed via canonical hash equivalence across permutation groups.
  - replay exactly `N=3` times per fixture group.
- Precision/recall zero-denominator lock is frozen:
  - if `(TP + FP) == 0`, precision is `100.0` when `(TP + FN) == 0`, else `0.0`.
  - if `(TP + FN) == 0`, recall is `100.0`.
- Labeled fixture governance lock is frozen:
  - precision/recall expected-label sets are maintained in locked fixture files under stop-gate manifest control.
  - fixture labels require explicit reviewer sign-off before lock freeze.
  - minimum labeled fixture coverage for gate validity is frozen:
    - at least `5` labeled pairwise fixtures total,
    - at least `3` fixtures with non-empty expected conflict sets.
- Metric denominator and fixture selection are frozen:
  - fixture selection is defined by a locked manifest file:
    - `apps/api/fixtures/stop_gate/vnext_plus10_manifest.json`
  - manifest schema is frozen:
    - `stop_gate.vnext_plus10_manifest@1`
  - `total` for each vNext+10 metric equals number of fixture entries listed for that metric in the manifest.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus10_manifest_hash`.
  - hash is computed as `sha256(canonical_json(manifest_payload))`.
  - metric computation is invalid if runtime manifest hash does not match recomputed canonical hash.
- Improvement lock is frozen:
  - manifest carries frozen baseline references:
    - `baseline_concept_conflict_precision_pct`
    - `baseline_concept_conflict_recall_pct`
  - `vNext+10` closeout requires non-regression on both metrics:
    - `concept_conflict_precision_pct >= baseline_concept_conflict_precision_pct`
    - `concept_conflict_recall_pct >= baseline_concept_conflict_recall_pct`
  - strict-improvement requirement is frozen:
    - strict improvement is required on at least one of precision/recall unless both baseline metrics are already `100.0`.
- Plateau handling lock is frozen:
  - when strict-improvement is not met, gate may still pass only if:
    - both precision and recall are non-regressing,
    - both metrics are already at or above frozen thresholds,
    - absolute deltas vs baseline are within a frozen plateau epsilon (`<= 0.1` percentage points).
- Metric visibility lock is frozen:
  - micro-averaged precision/recall drive gate decisions in this arc.
  - macro-averaged per-fixture precision/recall must be reported as non-gating diagnostics.
- Metric rendering precision lock is frozen:
  - gate computations use full deterministic metric precision before threshold comparisons.
  - human-readable stop-gate report percentages are rendered with fixed one-decimal rounding (half-up).
- Metrics are computed only from locked fixtures/replay artifacts.
- No live-run data may be mixed into deterministic stop-gate deltas.
- `vNext+10 -> vNext+11` thresholds are frozen:
  - `concept_conflict_precision_pct >= 95.0`
  - `concept_conflict_recall_pct >= 95.0`
  - `coherence_permutation_stability_pct == 100.0`
  - precision/recall must satisfy frozen non-regression and strict-improvement rules from the improvement lock.
  - if any fail: continue Path 5 hardening; do not start Path 6.

### Acceptance

- Stop-gate semantic-depth metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen `vNext+10` thresholds.
- No regression on existing `vNext+6`, `vNext+7`, `vNext+8`, and `vNext+9` determinism metrics.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Semantic-depth code family in this arc is explicit/additive:
  - `URM_SEMANTIC_DEPTH_*`
- Frozen additions in this arc:
  - `URM_SEMANTIC_DEPTH_INVALID_CARDINALITY`
  - `URM_SEMANTIC_DEPTH_DUPLICATE_CONFLICT_ID`
  - `URM_SEMANTIC_DEPTH_PERMUTATION_MISMATCH`
  - `URM_SEMANTIC_DEPTH_INVALID_REF`
  - `URM_SEMANTIC_DEPTH_CONFIDENCE_INVALID`
  - `URM_SEMANTIC_DEPTH_IDEMPOTENCY_CONFLICT`
- Endpoint/code mapping remains explicit and additive-only.

## Commit Plan (Small Green Commits)

1. `semantic-depth: add semantic_depth_report@1 schema + pairwise conflict report builder`
2. `semantic-depth: add ranking objective/tie-break v1 + deterministic provenance fixtures`
3. `semantic-depth: add coherence permutation invariance diagnostics + fixture coverage`
4. `metrics: extend stop-gate with vnext_plus10 semantic-depth metric keys and manifest hashing`
5. `tests: add deterministic replay/quality fixtures for semantic-depth gates`

## Exit Criteria (Draft)

- `D1`-`D4` merged with green CI.
- `concept_conflict_precision_pct` meets frozen threshold and satisfies improvement-lock rules (non-regression + strict-improvement conditions).
- `concept_conflict_recall_pct` meets frozen threshold and satisfies improvement-lock rules (non-regression + strict-improvement conditions).
- `coherence_permutation_stability_pct` is `100.0` on locked fixtures.
- `vNext+10 -> vNext+11` frozen stop-gate thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing `vNext+6`, `vNext+7`, `vNext+8`, and `vNext+9` determinism metrics remain at threshold.
