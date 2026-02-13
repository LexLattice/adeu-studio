# Locked Continuation vNext+3 (Frozen)

This document freezes the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS2.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS2.md`

Status: frozen.

Decision basis:

- vNext+2 exit criteria passed on `main` (C1-C4 complete, conformance valid).
- Selected next primary arc: **Semantic Depth v2.1** (Option D).

## Global Locks

- No solver semantic changes in this arc.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none in this arc).
- Determinism and replayability remain mandatory for new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Bridge-loss signals remain informational only (no solver-semantic effect).
- LLM-derived signals cannot override deterministic checker/solver precedence dimensions.
- Hidden wall-clock behavior is forbidden in deterministic mode.
- No randomness is allowed in deterministic mode:
  - no stochastic tie-breaks
  - no sampling-based ranking/scoring
  - any optional stochastic path must be explicitly non-replay and excluded from acceptance tests
- Quality metrics and dashboard deltas must be computed from locked fixture/replay inputs only.
- Ordering vectors are deterministic-only:
  - ranking/scoring objective vectors must be computed from deterministic fields only
  - LLM-derived signals may appear only in rationale/advisory/evidence fields
  - LLM-derived signals must not contribute to ordering/tie-break dimensions

## Frozen Quality Metric Set (v3)

All quality-delta claims in this arc use only this metric set:

- `redundancy_rate`:
  - `1 - (unique_questions / max(total_questions, 1))`
  - lower is better
- `top_k_stability@10`:
  - `|top10_a ∩ top10_b| / 10` on replay reruns for identical inputs
  - higher is better
- `evidence_coverage_rate`:
  - `ranked_items_with_required_evidence / max(ranked_items_total, 1)`
  - higher is better
- `bridge_loss_utilization_rate`:
  - `bridge_loss_referenced_cases / max(bridge_loss_present_cases, 1)`
  - higher is better
- `coherence_alert_count`:
  - integer count of emitted coherence diagnostics per fixture
  - lower is better

Delta-comparison rule versus locked v2 baseline:

- non-negative quality means:
  - `redundancy_rate_delta <= 0`
  - `top_k_stability@10_delta >= 0`
  - `evidence_coverage_rate_delta >= 0`
  - `bridge_loss_utilization_rate_delta >= 0`
  - `coherence_alert_count_delta <= 0`

## Arc Scope (Frozen)

This arc implements only:

1. `D1` Question quality v3 (deterministic dedupe/ranking/rationale tightening)
2. `D2` Tournament scoring v3 (objective/tie-break provenance lock)
3. `D3` Cross-artifact coherence diagnostics v1
4. `D4` Quality dashboard deterministic delta reporting

## D1) Question Quality v3

### Goal

Improve question quality and interpretability with deterministic ranking metadata.

### Scope

- Add deterministic question-ranking refinement slice.
- Introduce explicit question-rank version:
  - `concepts.qrank.v3`
- Expand question metadata with additive rationale fields tied to evidence.

### Locks

- Ranking output order is deterministic for identical replay inputs.
- Candidate-order permutation must not change final ranking.
- Bridge-loss references are included only when applicable.
- New rationale fields are additive-only and evidence-backed.
- Dedupe method is frozen for v3:
  - `dedupe_signature = (question_type, target_entity_ids_canonical, polarity, normalized_text_hash)`
  - `target_entity_ids_canonical` is sorted ascending and joined in canonical order
  - `normalized_text_hash = sha256(normalized_text_utf8)` where `normalized_text` uses:
    - lowercasing
    - whitespace collapse
    - punctuation stripping
    - UTF-8 encoding
- In-cluster representative selection is deterministic:
  - highest deterministic `impact_score` first
  - tie-break by `stable_id` ascending
- `impact_score` inputs are frozen to deterministic features only:
  - bridge-loss signal counts
  - affected artifact count
  - dependency depth features
  - explicit trust-lane metadata (`mapping_trust`, `solver_trust`, `proof_trust`) without lane collapse

### Acceptance

- Replay fixtures produce byte-identical question ranking artifacts for identical inputs.
- Redundancy delta versus v2 baseline is non-negative on locked fixtures.
- All emitted question artifacts include explicit `question_rank_version`.

## D2) Tournament Scoring v3

### Goal

Advance tournament scoring while preserving deterministic ordering guarantees.

### Scope

- Introduce next tournament scoring version:
  - `concepts.tscore.v3`
- Emit explicit score provenance fields per ranking artifact:
  - `objective_vector_version = "concepts.tobjective.v3"`
  - `tie_break_version = "concepts.ttiebreak.v1"`
  - `score_version = "concepts.tscore.v3"`

### Locks

- Tie-break order is frozen:
  - rank by objective vector (lexicographic, descending), then `stable_id` (ascending).
- Score metadata must be emitted on every ranking output.
- Objective vector inputs are frozen to deterministic fields only:
  - deterministic impact/dedupe features from D1
  - checker/solver-backed evidence dimensions
  - trust-lane metadata dimensions (explicit, non-collapsed)
- If LLM-derived score signals conflict with deterministic checker/solver evidence:
  - record LLM signal as evidence only
  - do not alter deterministic precedence dimensions for final order

### Acceptance

- Tournament ranking is replay-deterministic for identical inputs.
- Permuting candidate input order does not change final ranking order.
- Ranking artifacts always include `objective_vector_version`, `tie_break_version`, and `score_version`.

## D3) Cross-Artifact Coherence Diagnostics v1

### Goal

Add deterministic coherence diagnostics across related artifacts without semantic side effects.

### Scope

- Add additive diagnostic artifact:
  - `concepts.coherence.v1`
- Report deterministic coherence signals across this frozen artifact set within same `run_id`:
  - `bridge_loss_report`
  - question ranking artifact (`concepts.qrank.*`)
  - tournament ranking artifact (`concepts.tscore.*`)
  - patch/apply summary artifact (when present)

### Locks

- Diagnostic output is permutation-invariant on fixture artifact ordering.
- Diagnostic logic is replay-safe and must not require network/provider calls.
- Coherence diagnostics are informational only and cannot mutate solver outcomes.
- Coherence checks are frozen to:
  - missing required cross-artifact references
  - contradictory status labels across artifacts
  - inconsistent entity-id references
  - score/rank version mismatches

### Acceptance

- Coherence diagnostics pass permutation-invariance tests on locked fixtures.
- Identical replay inputs produce byte-identical `concepts.coherence.v1` outputs.

## D4) Quality Dashboard Delta Reporting

### Goal

Expose deterministic, evidence-backed quality deltas for v3 semantic slices.

### Scope

- Extend quality dashboard outputs with explicit baseline-vs-current deltas.
- Bind dashboard computation to locked fixture suites and replay artifacts only.

### Locks

- No live-run data may be mixed into deterministic dashboard deltas.
- Reported deltas must be traceable to fixture artifact refs.
- Output schema remains additive-only and versioned.
- Baseline selection is frozen:
  - baseline must come from replay-generated v2 artifacts for the same locked fixture suite
  - dashboard input manifest must pin baseline/current by `artifact_hash`
  - no floating "latest baseline" selection is allowed

### Acceptance

- Dashboard deltas are reproducible across reruns for identical fixture inputs.
- Primary ranking quality metrics show non-negative delta vs locked baseline.
- Dashboard outputs include explicit score/rank version provenance.

## Error-Code Policy (Frozen)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- No fork of URM error envelope or event taxonomy.

## Commit Plan (Small Green Commits)

1. `semantic: add deterministic question quality v3 ranking metadata and fixtures`
2. `semantic: add concepts.tscore.v3 objective/tie-break provenance and tests`
3. `semantic: add concepts.coherence.v1 diagnostics with permutation invariance tests`
4. `quality: extend dashboard with fixture-only deterministic deltas and evidence refs`
5. `docs: add semantic-depth v3 evidence report template`

## PR Sequence (Frozen)

1. **PR1: Question Quality v3**
   - D1 ranking/refinement + versioned metadata + deterministic fixture tests
2. **PR2: Tournament Score v3**
   - D2 scoring objective/tie-break/version metadata + replay/permutation tests
3. **PR3: Coherence Diagnostics**
   - D3 `concepts.coherence.v1` artifact + invariance checks
4. **PR4: Quality Dashboard**
   - D4 fixture-only delta reporting + evidence linkage

## Exit Criteria

- D1-D4 merged with green CI.
- Question/tournament replay determinism is `100%` on locked fixtures.
- Coherence diagnostics are permutation-invariant on locked fixtures.
- Primary quality deltas satisfy the frozen metric-set non-negative rules versus locked v2 baseline.
- No solver-semantics delta and no trust-lane regression introduced.
