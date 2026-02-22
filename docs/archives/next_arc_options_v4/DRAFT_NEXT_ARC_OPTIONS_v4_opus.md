# Draft Next Arc Options v4 (Post vNext+16 Planning)

This document is the continuation-planning draft after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md`
- `docs/SEMANTICS_v3.md`

Status: active planning draft for `vNext+17` selection.
Goal: identify post-`vNext+16` development paths for the next 2–3 arcs given current repo state.

## Baseline Snapshot (Post vNext+16)

Current baseline includes:

- `vNext+16` (`D1`-`D4`) complete and merged on `main`:
  - deterministic dangling-reference diagnostics (`adeu_integrity_dangling_reference@0.1`)
  - deterministic dependency-cycle policy diagnostics (`adeu_integrity_cycle_policy@0.1`)
  - deterministic minimal deontic conflict diagnostics (`adeu_integrity_deontic_conflict@0.1`)
  - deterministic env enforcement (`TZ=UTC`, `LC_ALL=C`) in stop-gate/report entrypoints
  - manifest-driven integrity coverage + transfer report
  - additive stop-gate metrics for integrity closeout
- v16 closeout is green:
  - `valid=true`
  - `all_passed=true`
  - `artifact_dangling_reference_determinism_pct=100.0`
  - `artifact_cycle_policy_determinism_pct=100.0`
  - `artifact_deontic_conflict_determinism_pct=100.0`
- prior arc guarantees remain green:
  - all stop-gate tracked `vNext+6` through `vNext+15` metrics remain at threshold
  - `vNext+12` through `vNext+15` closeout evidence remain reproducible
- `FUTURE_CLEANUPS.md` tracks 10 deferred items from v16 arc

Net: infrastructure, integrity, and determinism layers are mature. The backend pipeline (source text → core-ir → scoring → lane reporting → integrity diagnostics) is complete and deterministic. But this pipeline has **no consumer-facing output** — no rendering, no API exposure of core-ir artifacts, and no cross-IR coherence checks. The product layer is the primary frontier.

## Repo-Grounded Clarifications

1. Artifact schema inventory is substantial (7 `adeu_*` schemas, 30+ stop-gate metrics):
   - `adeu_core_ir@0.1` (canonical core-ir graph)
   - `adeu_lane_projection@0.1` (lane-scoped projection)
   - `adeu_lane_report@0.1` (lane report)
   - `adeu_projection_alignment@0.1` (alignment diagnostics)
   - `adeu_integrity_dangling_reference@0.1` (dangling refs)
   - `adeu_integrity_cycle_policy@0.1` (dependency cycles)
   - `adeu_integrity_deontic_conflict@0.1` (deontic conflicts)
2. Two IR families coexist without a unified consumer surface:
   - `adeu.ir.v0` (structured channel model — powers existing concept/puzzle proposers)
   - `adeu_core_ir@0.1` (flat graph model — powers lane reports, integrity diagnostics, S/B/R)
3. Existing web app (`apps/web`) has 6 page groups (artifacts, concepts, copilot, explain, papers, puzzles) but **none** expose core-ir, lane, or integrity outputs.
4. Quality dashboard (`quality_dashboard.py`, 578 lines) evaluates concept-level quality metrics but is disconnected from core-ir/integrity metrics.
5. Explain system (`adeu_explain`) produces structured causal explanations but doesn't reference core-ir nodes or integrity diagnostics.
6. Lean proof system (`adeu_lean`) runs obligation checks but isn't integrated with integrity diagnostic outputs.
7. `FUTURE_CLEANUPS.md` includes: schema consolidation evaluation, CI budget assessment (30 metrics), D-lane cycle expansion, hostile fixture generation, and shared validation module extraction.

## Shared Locks For Any Next Arc

- No solver semantic contract changes unless explicitly versioned and locked.
- `docs/SEMANTICS_v3.md` remains authoritative unless a versioned follow-on lock says otherwise.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- New behavior is additive-only unless explicitly marked breaking.
- Replay determinism is mandatory for acceptance paths.
- Runtime behavior must emit evidence events in `urm-events@1`.
- New `/urm/...` endpoints must be idempotent via `client_request_id`.
- New artifacts must be schema-versioned and canonically serialized.
- Stop-gate schema continuity remains additive on `stop_gate_metrics@1` unless explicitly re-locked.
- Deterministic execution environment lock (`TZ=UTC`, `LC_ALL=C`) carries forward.

## Path 10: Core-IR Rendering + API Exposure (Product Surface)

### Goal

Expose deterministic core-ir outputs to the web application and API consumers — making the infrastructure pipeline visible and usable at the product layer.

### Scope

1. Deterministic API endpoints for core-ir graph retrieval and lane-report retrieval from persisted artifacts.
2. Core-ir rendering contract: typed response models for web consumption (node/edge data, lane summaries, integrity status).
3. Integrity summary exposure: deterministic S/B/R scores, deontic conflicts, and dangling-reference counts exposed as first-class API fields.
4. Web app integration: new core-ir visualization page or panel showing O/E/D/U graph structure, lane distribution, and integrity heatmap.

### Locks

- rendering-only lock:
  - core-ir rendering surfaces persisted artifacts read-only; no mutation or re-extraction on read paths.
- schema-continuity lock:
  - rendering response models reference frozen `adeu_core_ir@0.1`, `adeu_lane_report@0.1`, and `adeu_integrity_*@0.1` schemas only.
- determinism lock:
  - rendering outputs are deterministic for identical persisted inputs.
- additive lock:
  - rendering endpoints do not change existing proposer/concept/puzzle API contracts.

### Acceptance

- API endpoints return deterministic, schema-valid core-ir rendering payloads from persisted fixtures.
- Web app renders core-ir graph with lane distribution and integrity overlay.

### Risk

- Web app scope can expand rapidly; thin-slice to read-only rendering first.
- Rendering may expose internal-only content — review trust/privacy boundaries before exposing.

## Path 11: Cross-IR Coherence Bridge (Concept ↔ Core-IR Alignment)

### Goal

Bridge the `adeu_concepts.ConceptIR` and `adeu_core_ir@0.1` models with deterministic coherence checks — answering "do the concept-level analysis and the core-ir graph agree?"

### Scope

1. Deterministic concept-to-core-ir projection: frozen mapping from `ConceptIR` claims/terms/links to core-ir O/E/D/U nodes and edges.
2. Coherence diagnostics: deterministic issue taxonomy for concept/core-ir divergence (missing concepts, unmapped claims, link-type drift).
3. Quality dashboard unification: extend `quality_dashboard.py` with core-ir/integrity metrics alongside existing concept metrics.
4. Transfer-report evidence for coherence closeout.

### Locks

- projection-authority lock:
  - `adeu_core_ir@0.1` remains the structural authority; concept-level projections are additive evidence.
- non-mutation lock:
  - coherence checks are read-only diagnostics; no modification to either IR family.
- determinism lock:
  - coherence diagnostics are deterministic and fixture-replayable.

### Acceptance

- Locked fixtures produce deterministic coherence diagnostics between concept-IR and core-IR.
- Quality dashboard includes core-ir and integrity metrics.

### Risk

- Mapping semantics between two IR families is complex — keep first slice to structural matching (same entities, same claims) without semantic equivalence.
- `ConceptIR` and `adeu_core_ir@0.1` have different granularity (concept has `Term`, `TermSense`, `InferentialLink`; core-ir has `O.Entity`, `O.Concept`, edges). Exact mapping may not be 1:1.

## Path 12: Infrastructure Consolidation + CI Sustainability

### Goal

Address accumulated technical debt from the 10-arc infrastructure build: schema consolidation, stop-gate CI budget, shared validation extraction, and fixture quality improvements.

### Scope

1. Schema consolidation: evaluate and optionally unify `adeu_integrity_*@0.1` into `adeu_integrity@0.1` with discriminator.
2. Stop-gate CI budget: implement fixture scheduling, selective lane execution, or deterministic parallelization to keep CI within reasonable runtime while maintaining gate guarantees (30 metrics × N=3 replays).
3. Shared validation module: extract duplicated manifest/artifact validation from `stop_gate_tools.py` and `integrity_transfer_report_vnext_plus16.py` into shared runtime helpers.
4. Hostile fixture generation: add deterministic procedural generation of malformed/dangling/cyclic payloads for defense-in-depth integrity coverage.
5. Drift error granularity: optionally split `URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT` into per-family codes.

### Locks

- behavior-preservation lock:
  - consolidation changes must be behavior-identical for existing acceptance paths.
- backward-compatibility lock:
  - schema consolidation must preserve existing fixture/artifact validity or provide explicit migration.
- CI-budget lock:
  - proposed CI optimizations may not reduce gate coverage guarantees.

### Acceptance

- All existing stop-gate metrics remain green and reproducible.
- CI runtime stays within defined budget after consolidation.
- `FUTURE_CLEANUPS.md` items addressed in scope are closed.

### Risk

- Schema consolidation is a breaking change if existing persisted artifacts use old schema family names — careful migration needed.
- CI parallelization must preserve replay determinism.

## Path 8b: Provider Parity Maintenance (Standing Fallback)

### Goal

Reserve a constrained fallback slice if provider parity regressions appear during v17+ execution.

### Scope

1. Fixture/matrix drift remediation only.
2. No expansion of proposer surface set.
3. Additive tests + stop-gate evidence only.

### Acceptance

- Parity closeout metrics return to frozen thresholds without broad scope expansion.

## Decision Matrix

### If priority is making the infrastructure investment visible to users and product stakeholders

- Start with Path 10 (thin slice: read-only API + minimal web rendering).

### If priority is ensuring the two IR families evolve coherently

- Start with Path 11 (thin slice: structural coherence diagnostics + quality dashboard extension).

### If priority is sustainability and technical debt before further feature expansion

- Start with Path 12 (thin slice: schema consolidation + CI budget optimization).

### If provider parity regresses

- Invoke Path 8b fallback and defer other paths.

## Recommended Arc Order (v17+)

1. `vNext+17`: Path 12 thin slice (`12a`) — infrastructure consolidation + CI sustainability
2. `vNext+18`: Path 10 thin slice (`10a`) — core-ir rendering API + minimal web exposure
3. `vNext+19`: Path 11 thin slice (`11a`) — concept ↔ core-ir coherence bridge

Why this order:

- Path 12 first: 30 metrics and 7 schemas create growing maintenance drag. Consolidating now prevents compounding overhead. The CI budget concern (raised in `FUTURE_CLEANUPS.md` and all assessments since vNext+14) becomes a blocker if left unaddressed — each future arc adds ~3 more metrics. Schema consolidation reduces the number of artifact families and simplifies the fixture inventory for subsequent arcs.
- Path 10 second: after consolidation, the infrastructure is leaner and ready for product exposure. API exposure is the highest-impact change for demonstrating value from the 10-arc build. But exposing messy internals before consolidation risks locking in un-consolidated schemas at the API boundary.
- Path 11 third: cross-IR coherence is the most conceptually complex path and benefits from both the consolidation (fewer schema families to bridge) and the API exposure (coherence diagnostics need a rendering surface to be meaningful).

Fallback sequencing rule:

- If provider parity metrics regress below threshold during any v17+ arc, hold current expansion and run Path 8b maintenance first.

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md` with Path 12 thin slice (`12a`) only:

1. `E1` schema consolidation evaluation and optional unification for `adeu_integrity_*@0.1`
2. `E2` shared validation module extraction from duplicated stop-gate/transfer-report code
3. `E3` stop-gate CI budget optimization (deterministic fixture scheduling or selective parallelization)
4. `E4` deterministic closeout metrics and stop-gate for `vNext+17 -> vNext+18`

Suggested measured outcomes for `vNext+17 -> vNext+18` gate:

- all existing 30 stop-gate metrics remain at `== 100.0` threshold
- CI runtime for full stop-gate suite is within defined budget target
- no solver-semantics delta and no trust-lane regression
- schema consolidation evaluation documented (even if deferred)
- shared validation module extracted without behavior changes
- `FUTURE_CLEANUPS.md` closure evidence for addressed items
