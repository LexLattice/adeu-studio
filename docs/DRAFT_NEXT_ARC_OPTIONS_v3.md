# Draft Next Arc Options v3 (Interconnected Layers)

This document is the next continuation-planning draft after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS12.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS12.md`
- `docs/SEMANTICS_v3.md`
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`

Status: draft only (not frozen).
Goal: define larger-scale next-arc options and identify a concrete first slice for `vNext+13`.

## Consolidation Note

For the post-`vNext+12` stage, planning should use this file as the working source of truth.
`docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` remains historical context but is no longer the primary planning draft for next-arc selection.

## Baseline Snapshot (Post vNext+12)

Current baseline includes:

- `vNext+12` (`P1`-`P4`) practical paper-pipeline hardening complete:
  - raw-PDF abstract extraction robustness
  - deterministic flow selection contract (`paper_pipeline_summary@1`)
  - worker provider-log normalization for known rollout noise
  - deterministic fixture/test closeout with green CI
- deterministic stop-gate closeout remains green (`all_passed = true`) with existing `vNext+6` through `vNext+11` metrics at threshold.
- post-lock additive intermezzo merged (PR `#131`):
  - codex surfaced as module proposer provider
  - approval-backed write-mode controls for copilot
  - provider wiring refactor with policy gating retained

Net: platform is stable enough to start a larger conceptual/product arc centered on layer-interconnected reasoning artifacts.

## Repo-Grounded Clarifications

1. Existing canonical IRs remain authoritative in their domains:
   - `adeu.ir.v0` (packages/adeu_ir) and `adeu.concepts.v0` (packages/adeu_concepts) already exist and are in active use.
2. Path 7 should be framed as a projection artifact, not a replacement:
   - `adeu_core_ir@0.1` is a normalized cross-lane view-model over persisted ADEU/Concept artifacts and extracted text units.
3. Determinism boundary must stay consistent with current provider architecture:
   - provider generation may be nondeterministic;
   - deterministic guarantees apply to canonicalization, ledger scoring, projection, and replay over persisted fixtures/artifacts.
4. Deontic subdomain semantics must not be collapsed away:
   - lane rendering stays four-lane (`O/E/D/U`) for UX,
   - but `D` must preserve at least `PhysicalConstraint` vs `Norm/Policy` and exception semantics in artifact kinds.
5. Existing span/provenance contracts should be reused:
   - `SourceSpan`/provenance semantics stay aligned with `adeu.ir.v0` contracts to avoid dual span dialects.

## Shared Locks For Any Next Arc

- No solver semantic contract changes unless explicitly versioned and locked.
- `docs/SEMANTICS_v3.md` remains authoritative unless a versioned follow-on lock says otherwise.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- New behavior is additive-only unless explicitly marked breaking.
- Replay determinism is mandatory for acceptance paths.
- Runtime behavior must emit evidence events in `urm-events@1`.
- New `/urm/...` endpoints must be idempotent via `client_request_id`.
- New artifacts must be schema-versioned under `spec/` and canonically serialized.
- Stop-gate metrics schema continuity remains additive on `stop_gate_metrics@1` unless explicitly re-locked.

## Path 7: ADEU Interconnected Layers Core (O/E/D/U)

### Goal

Introduce a first shippable, canonical layer-interconnected IR that supports:

1. reliable extraction from source text,
2. deterministic rendering into O/E/D/U lanes,
3. epistemic-ledger scoring (`S`, `B`, `R`) and future formal checks.

### Scope

1. Define and freeze `adeu_core_ir@0.1` (new additive artifact family) with node and edge contracts.
2. Implement deterministic projection/extraction + canonicalization pipeline to `adeu_core_ir@0.1`:
   - projection-first when authoritative IR artifacts exist,
   - extraction path when no authoritative IR is available.
3. Implement initial epistemic-ledger metrics on claims:
   - `S(c)` structural grounding
   - `B(c)` behavioral authority
   - `R(c) = B(c) - S(c)` closure risk
4. Provide minimal read-only lane projection contract for O/E/D/U UX rendering.

### Locks

- Layer model lock is frozen:
  - lanes: `O`, `E`, `D`, `U`
  - node families:
    - `O`: `Entity`, `Concept`, `RelationType`
    - `E`: `Claim`, `Assumption`, `Question`, `Evidence`
    - `D`: `PhysicalConstraint`, `Norm`, `Policy`, `Exception`
    - `U`: `Goal`, `Metric`, `Preference`
- Cross-lane edge lock is frozen for thin slice:
  - `about`, `defines`, `supports`, `refutes`, `depends_on`, `justifies`, `gates`, `serves_goal`, `prioritizes`, `excepts`.
- Extraction determinism lock is frozen:
  - source offsets/spans persisted per extracted unit
  - deterministic candidate ordering and ID canonicalization via stable-id rules
  - no nondeterministic tie-breaks.
- Canonicalization lock is frozen:
  - duplicate merge is deterministic and explainable
  - concept-level duplicate identity is span-insensitive:
    - canonical duplicate key is `(layer, kind, normalized_primary_text_or_label, source_text_hash)`.
    - duplicates union span anchors deterministically before final id/hash.
  - duplicate edges collapse to a single canonical `(type, from, to)` tuple
  - no dangling node references in final IR.
- Epistemic-ledger lock is frozen:
  - `Claim` includes `confidence`, authoritative `S_milli/B_milli/R_milli`, and derived display `S/B/R`
  - evidence/dependency relation inputs are derived from authoritative `edges[]` only
  - derived `S`, `B`, `R` fields are computed deterministically from persisted IR/evidence only.
- Non-breaking bridge lock is frozen:
  - `adeu_core_ir@0.1` is additive and does not replace existing `adeu.ir.v0` in first slice.
  - existing policy/proof/semantic-depth artifacts remain authoritative in their current lanes.
- Projection-boundary lock is frozen:
  - `adeu_core_ir@0.1` is derived/projection-oriented.
  - source-of-truth semantics remain on existing authoritative artifacts (`adeu.ir.v0`, `adeu.concepts.v0`) in this stage.
- Projection precedence lock is frozen:
  - when authoritative `adeu.ir.v0`/`adeu.concepts.v0` artifacts exist for a source, `adeu_core_ir@0.1` must be produced from deterministic projection first.
  - raw-text extraction is fallback-only for missing authoritative upstream artifacts.
- Divergence handling lock is frozen:
  - when both projected and extracted candidates are available, projected semantics are authoritative in this arc.
  - divergence is surfaced as deterministic diagnostics and may not silently overwrite authoritative projected semantics.
- Relation single-source lock is frozen:
  - cross-node relations are represented in `edges[]` only.
  - nodes may not duplicate relational truth in parallel relation fields.
- Source-span reuse lock is frozen:
  - span fields align with existing `SourceSpan` semantics (`start` inclusive, `end` exclusive, `0 <= start < end`).
- Determinism boundary lock is frozen:
  - acceptance determinism is measured over persisted candidate/artifact fixtures and deterministic transforms.
  - provider raw generation nondeterminism is isolated outside deterministic replay acceptance paths.

### Draft Data Model (v0.1 Reference)

```ts
type Layer = "O" | "E" | "D" | "U";

type Node =
  | { id: string; layer: "O"; kind: "Entity" | "Concept" | "RelationType"; label: string; aliases?: string[] }
  | {
      id: string;
      layer: "E";
      kind: "Claim" | "Assumption" | "Question" | "Evidence";
      text: string;
      spans?: { start: number; end: number }[];
      confidence?: number;
      S_milli?: number;
      B_milli?: number;
      R_milli?: number;
      S?: number;
      B?: number;
      R?: number;
      ledger_version?: "adeu.sbr.v0_1";
    }
  | {
      id: string;
      layer: "D";
      kind: "PhysicalConstraint" | "Norm" | "Policy" | "Exception";
      constraint_kind?: "mechanism" | "resource_limit" | "invariant" | "law" | "assumption";
      modality?: "obligatory" | "forbidden" | "permitted";
      condition?: string;
      target?: string;
      priority?: number;
    }
  | { id: string; layer: "U"; kind: "Goal" | "Metric" | "Preference"; label: string; weight?: number };

type Edge = { from: string; to: string; type: string };
type ADEUCoreIR = {
  schema: "adeu_core_ir@0.1";
  source_text_hash: string;
  source_text?: string; // optional for portability; hash remains authoritative
  nodes: Node[];
  edges: Edge[];
};
```

### Edge Typing Matrix (Frozen For Thin Slice)

- `about`: `E.Claim|E.Assumption|E.Question|E.Evidence -> O.Entity|O.Concept|O.RelationType`
- `defines`: `E.Claim|E.Evidence -> O.Concept|O.RelationType`
- `supports|refutes`: `E.Evidence|E.Claim -> E.Claim`
- `depends_on`: `E.Claim -> E.Claim|E.Assumption|E.Question|E.Evidence`
- `justifies`: `E.Claim|E.Evidence -> D.Norm|D.Policy`
- `gates`: `D.Policy -> E.Claim|E.Assumption|E.Question`
- `serves_goal`: `D.PhysicalConstraint|D.Norm|D.Policy|E.Claim -> U.Goal|U.Metric`
- `prioritizes`: `U.Preference -> U.Goal|U.Metric|D.PhysicalConstraint|D.Norm|D.Policy|D.Exception`
- `excepts`: `D.Exception -> D.PhysicalConstraint|D.Norm|D.Policy`

### Pipeline Outline (Deterministic Where It Matters)

1. Stage 0: text normalization and stable span mapping.
2. Stage 1: projection-first candidate harvesting:
   - deterministic projection from authoritative IR artifacts when available,
   - provider/rule extraction fallback when not available.
3. Stage 2: deterministic canonicalization (dedupe, typing constraints, ref integrity).
4. Stage 3: deterministic claim-ledger scoring (`S`, `B`, `R`) + intervention hints.
5. Stage 4 (optional first-slice tail): integrity checks (dangling refs, dependency cycles, basic deontic conflicts).

Numerics portability note:

- fixed-point milli values (`S_milli/B_milli/R_milli`) are authoritative for canonical hashing/replay.
- floating `S/B/R` fields are optional display projections derived from milli values.

### Acceptance

- identical persisted fixture inputs produce byte-identical `adeu_core_ir@0.1` outputs.
- O/E/D/U projection renders deterministically from stored IR (no UI-only inference drift).
- claim-level `S`, `B`, `R` recomputation matches stored values on locked fixtures.

### Risk

- schema overreach in first slice can delay shipping; keep v13 focused on core IR + extraction + ledger baseline only.

## Path 8: Codex-Provider Reliability + Module Parity

### Goal

Complete codex provider parity and reliability for existing modules before deeper model-layer expansion.

### Scope

1. ensure all proposer endpoints that accept `mock|openai` also deterministically accept `codex`.
2. harden codex parse/repair normalization for concept/paper/puzzle flows.
3. add deterministic provider parity fixtures for concept/paper/puzzle propose flows.

### Locks

- provider taxonomy lock is frozen:
  - `mock`, `openai`, `codex` remain explicit and additive.
- codex normalization lock is frozen:
  - schema-shape normalization may repair transport noise only; it may not silently rewrite semantic content.
- parity reporting lock is frozen:
  - attempts/reasons/candidate rank logging remains explicit and deterministic.

### Acceptance

- codex provider can successfully produce candidates across all proposer modules in locked fixtures.
- no endpoint returns provider literal validation errors when `provider=codex` is selected on supported routes.

### Risk

- runtime/provider heterogeneity can leak flaky behavior without tight fixture boundaries.

## Path 9: Formal Sanity Checks For Layer Graphs

### Goal

Add minimal formal integrity checks for the new layer graph without broad solver-contract change.

### Scope

1. add deterministic graph sanity checks:
   - no dangling refs
   - `depends_on` cycle policy (either forbidden or explicitly marked)
   - basic deontic conflict checks under same condition (`must X` + `must not X`)
2. expose check reports as additive artifacts.

### Locks

- checks are integrity-only in first slice; no expansion into new solver semantics.
- failures are deterministic and fail-closed in validation paths.

### Acceptance

- locked fixtures deterministically pass/fail with stable reason-code ordering.

### Risk

- if this enters v13 too early it may block core IR shipping velocity.

## Decision Matrix

### If priority is foundational architecture for layered reasoning

- Start with Path 7.

### If priority is immediate codex production reliability across existing modules

- Start with Path 8.

### If priority is early formal graph integrity guarantees

- Start with Path 9.

## Recommended Arc Order (v13+)

1. `vNext+13`: Path 7 thin slice (`7a`) — core IR + deterministic extraction + initial `S/B/R`
2. `vNext+14`: Path 8 thin slice (`8a`) — codex module parity/hardening closeout
3. `vNext+15`: Path 7 thin slice (`7b`) + Path 9 thin slice (`9a`) — lane UX deepening + formal sanity checks

Why this order:

- it ships the new conceptual spine first,
- stabilizes provider execution reliability second,
- then expands formal/UX depth on a stable canonical artifact.

Fallback sequencing rule:

- if codex/openai provider reliability regresses during early Path 7 execution, Path 8 may be pulled forward before expanding Path 7 scope.

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md` with Path 7 thin slice (`7a`) only:

1. `7a-1` Freeze `adeu_core_ir@0.1` schema and deterministic serialization profile.
2. `7a-2` Implement deterministic extraction/canonicalization pipeline from source text.
3. `7a-3` Implement deterministic claim-ledger scoring (`S/B/R`) and report contract.
4. `7a-4` Add locked fixtures and additive stop-gate checks for replay determinism.

Suggested measured outcomes for `vNext+13 -> vNext+14` gate:

- `adeu_core_ir_replay_determinism_pct == 100.0`
- `adeu_claim_ledger_recompute_match_pct == 100.0`
- `adeu_lane_projection_determinism_pct == 100.0`
- no solver-semantics delta and no trust-lane regression.
- all existing stop-gate tracked `vNext+6` through `vNext+11` determinism metrics remain at threshold.
- `vNext+12` closeout evidence remains green and reproducible.
