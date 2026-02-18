# Locked Continuation vNext+13 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS12.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS12.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+12` (`P1`-`P4`) merged on `main` with green CI and closeout `all_passed = true`.
- post-`vNext+12` planning in `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` recommends `vNext+13 = Path 7 thin slice (7a)`.
- This arc is reserved for first-shippable O/E/D/U core artifact hardening only:
  - canonical core IR contract first
  - deterministic extraction/canonicalization second
  - claim-ledger scoring contract third
  - fixture/stop-gate closeout fourth

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS11.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS12.md` remain authoritative for policy/proof/explain/runtime/conformance semantics.
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
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.

## Arc Scope (Draft Lock)

This arc proposes Path 7 thin slice only:

1. `A1` `adeu_core_ir@0.1` contract freeze (O/E/D/U)
2. `A2` Deterministic extraction + canonicalization pipeline
3. `A3` Deterministic claim-ledger scoring contract (`S/B/R`)
4. `A4` Fixture/metrics closeout for `vNext+13 -> vNext+14` gate

## A1) `adeu_core_ir@0.1` Contract Freeze

### Goal

Introduce a canonical additive layer-interconnected artifact contract for O/E/D/U reasoning surfaces.

### Scope

- Add additive package/module home for this artifact family:
  - `packages/adeu_core_ir`.
- Add generated schema contract under:
  - `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`
- Optional mirror copy under `spec/` is non-authoritative convenience only.
- Freeze node-family and edge-family contracts.
- Freeze deterministic ID and ordering semantics.

### Locks

- `adeu_core_ir@0.1` envelope lock is frozen:
  - `schema = "adeu_core_ir@0.1"`
  - `source_text_hash`
  - optional `source_text` (non-authoritative; hash remains authoritative)
  - `nodes`
  - `edges`
  - optional additive metadata fields only.
- Layer lock is frozen:
  - valid layer set is exactly `O`, `E`, `D`, `U`.
- Node-family lock is frozen:
  - `O`: `Entity`, `Concept`, `RelationType`
  - `E`: `Claim`, `Assumption`, `Question`, `Evidence`
  - `D`: `PhysicalConstraint`, `Norm`, `Policy`, `Exception`
  - `U`: `Goal`, `Metric`, `Preference`
- Edge-family lock is frozen for this arc:
  - `about`, `defines`, `supports`, `refutes`, `depends_on`, `justifies`, `gates`, `serves_goal`, `prioritizes`, `excepts`.
- Edge typing matrix lock is frozen:
  - `about`: `E.Claim|E.Assumption|E.Question|E.Evidence -> O.Entity|O.Concept|O.RelationType`
  - `defines`: `E.Claim|E.Evidence -> O.Concept|O.RelationType`
  - `supports|refutes`: `E.Evidence|E.Claim -> E.Claim`
  - `depends_on`: `E.Claim -> E.Claim|E.Assumption|E.Question|E.Evidence`
  - `justifies`: `E.Claim|E.Evidence -> D.Norm|D.Policy`
  - `gates`: `D.Policy -> E.Claim|E.Assumption|E.Question`
  - `serves_goal`: `D.PhysicalConstraint|D.Norm|D.Policy|E.Claim -> U.Goal|U.Metric`
  - `prioritizes`: `U.Preference -> U.Goal|U.Metric|D.PhysicalConstraint|D.Norm|D.Policy|D.Exception`
  - `excepts`: `D.Exception -> D.PhysicalConstraint|D.Norm|D.Policy`
- Relation single-source lock is frozen:
  - relational truth is carried in `edges` only; node relation duplication is forbidden in this arc.
- Deontic-subkind preservation lock is frozen:
  - projection/extraction may not collapse `PhysicalConstraint` into `Norm|Policy`.
  - exception semantics are explicit through `D.Exception` and `excepts` edges.
- Deterministic ID canonicalization lock is frozen:
  - node ids are deterministic and content-derived via canonical stable-id input tuples.
  - canonical tuple includes `(layer, kind, normalized_primary_text_or_label, canonical_spans, source_text_hash)`.
  - `canonical_spans` in id tuples are the post-merge canonical span union result only.
- Edge uniqueness lock is frozen:
  - canonical edge identity is `(type, from, to)`.
  - duplicate edges with same identity are merged before final ordering/hash.
- Deterministic ordering lock is frozen:
  - `nodes` ordered deterministically by `(layer, kind, id)`.
  - `edges` ordered deterministically by `(type, from, to)`.
- Non-breaking bridge lock is frozen:
  - `adeu_core_ir@0.1` is additive and may not replace `adeu.ir.v0` authority in this arc.
- Projection authority lock is frozen:
  - `adeu_core_ir@0.1` is a projection artifact.
  - `adeu.ir.v0` and `adeu.concepts.v0` remain authoritative source semantics in this arc.
- Projection precedence lock is frozen:
  - when authoritative upstream artifacts are present, `adeu_core_ir@0.1` is produced by deterministic projection first.
  - raw-text extraction is fallback-only for missing authoritative upstream surfaces.
- Divergence handling lock is frozen:
  - if projected and extracted candidates disagree, projected semantics remain authoritative in this arc.
  - divergence emits deterministic diagnostics (`URM_ADEU_CORE_PROJECTION_DIVERGENCE`) and does not silently mutate projected semantics.
- Span contract lock is frozen:
  - spans use existing `SourceSpan` semantics (`start` inclusive, `end` exclusive, `0 <= start < end`).

### Acceptance

- Locked fixtures validate against `adeu_core_ir@0.1` schema.
- Identical fixture inputs replay to byte-identical canonical artifact output.

## A2) Deterministic Extraction + Canonicalization

### Goal

Generate `adeu_core_ir@0.1` from source text with deterministic extraction and merge behavior.

### Scope

- Stage 0: deterministic text normalization + span anchoring.
- Stage 1: candidate harvesting for O/E/D/U node candidates.
- Stage 2: deterministic canonicalization/merge/ref-resolution.

### Locks

- Extraction offset lock is frozen:
  - extracted units must preserve deterministic span references into normalized source text.
- Source-hash authority lock is frozen:
  - `source_text_hash` is computed from normalized Stage-0 text.
  - identical normalized text yields identical `source_text_hash` regardless of pre-normalization formatting noise.
- Candidate-source boundary lock is frozen:
  - live candidate harvesting may be provider-backed and/or rule-based.
  - deterministic acceptance fixtures in this arc consume persisted candidate payloads only.
- Canonicalization lock is frozen:
  - duplicate merge policy is deterministic and order-independent.
  - canonical node duplicate identity uses `(layer, kind, normalized_primary_text_or_label, source_text_hash)` (span-insensitive).
  - duplicate merges must union spans deterministically before canonical stable-id recomputation.
  - when duplicates merge, retained id is deterministic by lexicographic minimal canonical stable-id.
  - unresolved references fail closed in deterministic acceptance paths.
- Deterministic tie-break lock is frozen:
  - candidate tie-breaks are deterministic and explicit; no hidden provider-order dependence.
- Offline deterministic lock is frozen:
  - acceptance fixtures/replay paths may not require remote network dependency.
- Provider nondeterminism boundary lock is frozen:
  - provider generation may be nondeterministic.
  - deterministic acceptance claims in this arc are measured on persisted candidate/artifact fixtures and deterministic transforms only.

### Acceptance

- Identical persisted source+candidate fixture inputs replay to byte-identical canonical `nodes`/`edges`.
- No dangling node/edge references in accepted fixtures.

## A3) Claim-Ledger Scoring Contract (`S/B/R`)

### Goal

Expose deterministic epistemic closure-risk metrics on claims.

### Scope

- Add deterministic claim ledger fields:
  - `confidence`
  - authoritative `S_milli`, `B_milli`, `R_milli`
  - optional display-only `S`, `B`, `R` derived from milli fields
- Freeze deterministic derivation of evidence/dependency inputs from `edges[]` only.
- Freeze deterministic scoring computation inputs and ordering.

### Locks

- Score definition lock is frozen:
  - raw closure delta is `B(c) - S(c)`.
  - stored risk score uses the clamped fixed-point form defined below.
- Ledger version lock is frozen:
  - `ledger_version = "adeu.sbr.v0_1"` for claim-ledger computations in this arc.
- Structural grounding lock is frozen:
  - `S` uses only persisted structural/evidence/dependency features.
  - ratio-term definitions are frozen:
    - `evidence_support_ratio = supports_to_claim / max(1, supports_to_claim + refutes_to_claim)`
    - `dependency_resolution_ratio = resolved_dependencies / max(1, total_dependencies)`
    - `resolved_dependencies` are `depends_on` targets with kind in `{Claim, Evidence}`
    - `provenance_anchor_ratio = 1.0` iff claim has at least one valid span, else `0.0`
  - deterministic fixed-point (`milli`) scoring is frozen:
    - `ratio_milli = round(1000 * ratio)`
    - `S_milli = clamp_0_1000((500*evidence_support_ratio_milli + 300*dependency_resolution_ratio_milli + 200*provenance_anchor_ratio_milli + 500) // 1000)`
    - authoritative stored value is `S_milli` (integer).
    - optional display `S` is derived as decimal with exactly 3 fractional digits.
- Behavioral authority lock is frozen:
  - `B` uses only persisted claim `confidence` value from canonical artifact input.
  - missing `confidence` defaults deterministically to `0.0`.
  - deterministic fixed-point formula is frozen:
    - `B_milli = clamp_0_1000(round(1000 * clamp01(confidence)))`
    - authoritative stored value is `B_milli` (integer).
    - optional display `B` is derived as decimal with exactly 3 fractional digits.
- Risk lock is frozen:
  - deterministic fixed-point formula is frozen:
    - `R_milli = clamp_0_1000(B_milli - S_milli)`
    - authoritative stored value is `R_milli` (integer).
    - optional display `R` is derived as decimal with exactly 3 fractional digits.
- Recompute lock is frozen:
  - `S/B/R` recomputation from persisted artifact inputs must match stored values exactly on locked fixtures.
- Intervention-hint lock is frozen:
  - optional intervention hints are additive and deterministic only; they may not alter `S/B/R` values.

### Acceptance

- `S/B/R` recomputation is deterministic and exact on locked fixtures.
- Highest-risk claims ranking by `R` is deterministic on identical inputs.

## A4) Fixture + Stop-Gate Closeout

### Goal

Add deterministic fixture coverage and additive stop-gate metrics for this arc.

### Scope

- Add manifest-driven fixture accounting for new core-IR and claim-ledger checks.
- Extend stop-gate metrics additively for `vNext+13` closeout.

### Locks

- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `adeu_core_ir_replay_determinism_pct`
  - `adeu_claim_ledger_recompute_match_pct`
  - `adeu_lane_projection_determinism_pct`
- Lane projection definition lock is frozen:
  - lane projection input is persisted `adeu_core_ir@0.1`.
  - lane projection output artifact shape is frozen:
    - `schema = "adeu_lane_projection@0.1"`
    - `source_text_hash`
    - `lanes = { O: string[], E: string[], D: string[], U: string[] }`
    - `edges = { type: string, from: string, to: string }[]`
  - lane arrays and edges are deterministically ordered.
  - `adeu_lane_projection_determinism_pct` replays this projection artifact hash only (no UI runtime data).
- Determinism metric computation lock is frozen:
  - canonical hash per artifact/fixture
  - replay exactly `N=3` times per fixture
  - fixture passes only when all replay hashes match
  - `pct = 100 * passed / total`
- Fixture-manifest lock is frozen:
  - fixture selection is defined by:
    - `apps/api/fixtures/stop_gate/vnext_plus13_manifest.json`
  - manifest envelope is frozen:
    - `schema = "stop_gate.vnext_plus13_manifest@1"`
    - `replay_count = 3`
  - required top-level keys for this arc are frozen:
    - `core_ir_replay_fixtures`
    - `ledger_recompute_fixtures`
    - `lane_projection_fixtures`
- Manifest-hash lock is frozen:
  - closeout output must include `vnext_plus13_manifest_hash`.
  - mismatch fails closed with `URM_ADEU_CORE_MANIFEST_HASH_MISMATCH`.
- Threshold lock is frozen for `vNext+13 -> vNext+14`:
  - `adeu_core_ir_replay_determinism_pct == 100.0`
  - `adeu_claim_ledger_recompute_match_pct == 100.0`
  - `adeu_lane_projection_determinism_pct == 100.0`

### Acceptance

- New v13 metrics are reproducible across reruns for identical fixture inputs.
- All frozen thresholds pass with deterministic closeout output.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- `URM_ADEU_CORE_*` additions in this arc are frozen:
  - `URM_ADEU_CORE_INVALID_LAYER`
  - `URM_ADEU_CORE_INVALID_EDGE_TYPE`
  - `URM_ADEU_CORE_EDGE_TYPING_VIOLATION`
  - `URM_ADEU_CORE_DANGLING_REF`
  - `URM_ADEU_CORE_DUPLICATE_NODE_ID`
  - `URM_ADEU_CORE_LEDGER_RECOMPUTE_MISMATCH`
  - `URM_ADEU_CORE_PROJECTION_DIVERGENCE`
  - `URM_ADEU_CORE_MANIFEST_HASH_MISMATCH`

## Commit Plan (Small Green Commits)

1. `core-ir: add adeu_core_ir@0.1 schema and deterministic ordering/validation contracts`
2. `core-ir: implement deterministic O/E/D/U extraction and canonicalization pipeline`
3. `ledger: add deterministic claim S/B/R scoring and recompute fixtures`
4. `metrics: extend stop-gate with vnext_plus13 core-ir/ledger deterministic keys`
5. `tests: add fixture-driven replay and projection determinism coverage for v13 closeout`

## Exit Criteria (Draft)

- `A1`-`A4` merged with green CI.
- `adeu_core_ir@0.1` replay determinism is `100%` on locked fixtures.
- claim-ledger recomputation match is `100%` on locked fixtures.
- lane projection determinism is `100%` on locked fixtures.
- `vNext+13 -> vNext+14` frozen stop-gate thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing stop-gate tracked `vNext+6` through `vNext+11` determinism metrics remain at threshold.
- `vNext+12` closeout evidence remains green and reproducible.
