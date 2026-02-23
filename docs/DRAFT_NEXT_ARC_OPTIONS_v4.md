# Draft Next Arc Options v4 (Cross-Draft Consolidation)

This document consolidates the four independent v4 planning drafts:

- `docs/archives/next_arc_options_v4/DRAFT_NEXT_ARC_OPTIONS_v4_codex.md`
- `docs/archives/next_arc_options_v4/DRAFT_NEXT_ARC_OPTIONS_v4_gpt.md`
- `docs/archives/next_arc_options_v4/DRAFT_NEXT_ARC_OPTIONS_v4_opus.md`
- `docs/archives/next_arc_options_v4/DRAFT_NEXT_ARC_OPTIONS_v4_gemini.md`

Status: active planning draft (v17 through v23 baselines executed; active for `vNext+24+` selection).
Goal: capture all high-level next-arc path families raised across drafts, then provide a single planning map for post-`vNext+23` sequencing.

## Baseline Agreement (Shared Across Drafts)

All four drafts converge on these baseline points:

- `vNext+16` (`D1`-`D4`) is complete and green.
- `vNext+17` Path S1 (`E1`-`E4`) is complete and green (`docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS17.md`).
- `vNext+18` Path S5 (`F1`-`F4`) is complete and green (`docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS18.md`).
- `vNext+19` Path S3a (`R1`-`R4`) is complete and green (`docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS19.md`).
- `vNext+20` Path S4 (`C1`-`C4`) is complete and green (`docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS20.md`).
- `vNext+21` Path S6 (`N1`-`N4`) is complete and green (`docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS21.md`).
- `vNext+22` Path S7 (`T1`-`T4`) is complete and green (`docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS22.md`).
- `vNext+23` Path S8 (`V1`-`V4`) is complete and green (`docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS23.md`).
- Determinism/manifest/stop-gate closeout discipline is now mature and must carry forward.
- Next work should remain additive-first and explicitly locked.
- Provider parity maintenance remains a fallback path, not the default next arc.
- S9 is treated as an operational fallback mode that may preempt planned arcs when
  parity thresholds regress.

## Consolidated Path Families

The four drafts collectively define nine high-level path families.
This section preserves all of them in one normalized option set.

## Path S1: Integrity Diagnostics Expansion (Follow-On)

### Goal

Deepen the v16 integrity diagnostics along deferred edges while preserving evidence-first behavior.

### Source Convergence

- `v4_codex`: Path `9b`
- `v4_gemini`: Path `11a` (normative-resolution follow-on)
- `v4_opus`: partial overlap (cycle/deontic expansion ideas appear in clarifications/risks)

### Typical Scope

1. Extend reference-integrity checks beyond D1 structural endpoint checks.
2. Extend cycle policy scope beyond current D2 E-layer `depends_on` boundary where justified.
   If D-layer cycle checks are added, they must freeze a separate taxonomy for
   `dependency_loop` vs `exception_loop` and may not reuse E-layer cycle semantics by default.
3. Expand deontic conflict scope beyond current D3 `{obligatory, forbidden}` minimum.
4. Keep outputs additive and deterministic with explicit identity/ordering/cap locks.

### Acceptance Shape

- new integrity expansion fixtures are deterministic under replay
- additive v17 integrity metrics pass at `100.0`
- no solver semantics contract delta
- lock diagnostic-vs-validation boundary explicitly:
  - expanded checks are diagnostics over persisted/raw payloads and do not change canonical
    `adeu_core_ir@0.1` fail-closed validation behavior.
  - non-empty diagnostic fixtures must include intentional validator-bypass payloads when a
    check overlaps existing hard validators.

## Path S2: Extraction Fidelity Completion (v15 Deferred Diagnostics)

### Goal

Close deferred projection-alignment fidelity gaps from v15 (span/label/score diagnostics).

### Source Convergence

- `v4_gemini`: Path `10a`
- partial relation to `v4_codex`/`v4_opus` via quality/coherence themes

### Typical Scope

1. Add deterministic `span_mismatch`, `label_text_mismatch`, and bounded score diagnostics.
2. Keep diagnostics non-authoritative evidence-only.
3. Preserve existing alignment determinism contracts and thresholds.

### Acceptance Shape

- alignment fixtures expose deterministic drift taxonomy
- alignment determinism metric remains `100.0`

## Path S3: Product Surface Activation (Core-IR API/Rendering/Proposer)

### Goal

Turn the now-stable core-ir/integrity pipeline into an explicit product-visible surface.

### Source Convergence

- `v4_gpt`: Option A (core-ir proposer thin slice), Option B (quality report)
- `v4_opus`: Path `10` (core-ir rendering + API exposure)

### S3a: Product Surface Read-Only (Thin Slice)

#### Typical Scope

1. Read-only API exposure of persisted core-ir/lane/integrity artifacts.
2. Deterministic render payload builders for product consumption (JSON-first, UI-agnostic).
3. Optional minimal web rendering over persisted read payloads only.
4. If layout/grouping becomes contract-relevant, freeze a deterministic layout schema/version
   instead of leaving ordering to ad hoc frontend heuristics.
5. Minimal-form lock: S3a may ship as read-only endpoints + render-payload JSON only;
   web UI is optional and only if it does not require adding a new frontend build-system
   dependency.

#### Acceptance Shape

- API/CLI/UI parity over persisted artifacts
- deterministic render payload replay stability
- no mutation semantics on read surfaces

### S3b: Core-IR Proposer Activation (Separate Thin Slice)

#### Typical Scope

1. Activate a core-ir proposer surface with explicit provider boundaries.
2. Ensure outputs include core-ir + lane + integrity evidence artifacts.
3. Keep proposer nondeterminism isolated behind persisted artifact determinism boundaries.

#### Acceptance Shape

- proposer contract validity and replay determinism metrics are green on locked fixtures
- no regression to existing proposer/provider parity contracts
- explicit provider continuity release is approved in the lock doc before implementation
  (S3b expands proposer surface sets and cannot rely on vNext+14 continuity lock unchanged)

## Path S4: Cross-IR Coherence Bridge (Concept IR ↔ Core-IR)

### Goal

Add deterministic diagnostics and reporting for alignment between concept-level and core-ir representations.

### Source Convergence

- `v4_opus`: Path `11`
- related motivation in `v4_gpt` Option B

### Typical Scope

1. Freeze deterministic mapping/projection from concept structures to core-ir structures.
2. Emit deterministic coherence issue taxonomy.
3. Extend quality reporting/dashboard with cross-IR coherence signals.
4. Freeze asymmetric bridge behavior for unmappable entities (drop, roll-up, or placeholder)
   so Concept IR-only and Core-IR-only structures do not create nondeterministic drift.

### Acceptance Shape

- coherence diagnostics replay determinism `100.0`
- additive reporting without mutating canonical artifacts

## Path S5: Tooling Consolidation + CI Budget Sustainability

### Goal

Reduce maintenance drift and execution cost as metric/schema surface area grows.

### Source Convergence

- `v4_codex`: Path `10a`
- `v4_opus`: Path `12`
- ties directly to `docs/FUTURE_CLEANUPS.md`

### Typical Scope

1. Extract shared manifest/artifact validation modules.
2. Add deterministic CI/runtime budget observability and bounded optimization.
3. Evaluate schema-family consolidation strategy with compatibility constraints.
4. Preserve behavior while reducing duplication and operational drag.

### Acceptance Shape

- behavior-preserving refactors (no hash/contract regressions)
- deterministic budget reporting
- all existing gates remain green
- migration determinism checks prove exact historical hash parity for locked v14-v16 fixtures
- stop-gate runtime budget ceiling is explicitly frozen (for example full closeout under a
  bounded wall-clock target in CI)

## Path S6: Normative Advice Layer (Evidence-Only Policy Guidance)

### Goal

Derive deterministic non-authoritative gating/advice from integrity + lane outputs without solver mutation.

### Source Convergence

- `v4_gpt`: Option C

### Typical Scope

1. Define additive advice artifact family and frozen ruleset version.
2. Bind advice to existing evidence refs, with mandatory `justification_refs` to D/E evidence.
3. Keep advisory output explicitly non-enforcing.

### Acceptance Shape

- deterministic advice replay and rule coverage
- no trust-lane/solver-lane semantics mutation
- advice generation contract explicitly depends on mature D3/S1 evidence outputs

## Path S7: Proof/Trust Lane Starter

### Goal

Begin proving key deterministic invariants as explicit trust-lane evidence.

### Source Convergence

- `v4_gpt`: Option D

### Typical Scope

1. Select a narrow invariant set (canonicalization, replay invariants, ledger recompute).
2. Emit deterministic proof evidence packets for persisted checks.
3. Keep scope narrow and additive.
4. Distinguish solver-obligation proofs from infrastructure-invariant checks explicitly
   (the latter may use deterministic property-test evidence rather than Lean obligations).

### Acceptance Shape

- locked invariant set checked reproducibly
- proof evidence replay stability

## Path S8: Solver Semantics v4 Expansion (Future Heavy Arc)

### Goal

Introduce a new semantics generation (for example soft constraints/optimization) only behind explicit versioned locks.
This path is explicitly out of default `vNext+17`-`vNext+20` sequencing.

### Source Convergence

- `v4_gemini`: Path `12a`

### Typical Scope

1. Draft/freeze `SEMANTICS_v4` contract.
2. Define compatibility and migration boundaries from v3.
3. Bind to deterministic tests/metrics.
4. If soft constraints/objectives are introduced, freeze their mapping to U-layer constructs
   so D-layer deontic semantics remain non-probabilistic.

### Acceptance Shape

- strict backward compatibility or explicit migration lock
- new v4-specific deterministic metrics and fixtures

## Path S9: Provider Parity Maintenance (Fallback)

### Goal

Preserve a constrained maintenance branch if parity regresses.

### Source Convergence

- present in `v4_codex`, `v4_opus`, and `v4_gemini` directly
- compatible with `v4_gpt` risk framing

### Scope

1. matrix/fixture drift remediation only
2. no surface-set expansion
3. additive tests + stop-gate evidence only

## Synthesis Decision Matrix

### If priority is maximum continuity from v16 deferred work

- choose Path S1 first (integrity diagnostics expansion)

### If priority is immediate user-visible product value

- choose Path S3a first (read-only product surface activation)

### If priority is early workflow/product feedback without proposer nondeterminism

- choose Path S3a first, then choose S1 or S5 based on observed usage pain points

### If priority is maintainability and CI sustainability

- choose Path S5 first (tooling consolidation)

### If priority is conceptual coherence between IR stacks

- choose Path S4 first (cross-IR coherence bridge)

### If priority is long-horizon semantics capability

- defer to Path S8 only after at least one of S1/S5 lands cleanly

### If provider parity regresses below thresholds

- execute Path S9 fallback before any expansion path

## Cross-Path Dependencies (Explicit)

| Path | Depends On / Constraint |
|---|---|
| S1 | overlaps existing hard validators; requires explicit diagnostic-vs-validation lock and bypass fixtures for non-empty evidence |
| S2 | can run independently; practically benefits from S1 lock clarity on issue-taxonomy naming and ordering |
| S3a | independent of proposer matrix; read-only persisted-artifact exposure only |
| S3b | requires explicit provider-surface lock release and provider-matrix refresh semantics |
| S4 | strongly benefits from S3a payload surfaces and frozen asymmetric bridge-mapping contract |
| S5 | independent and can/should precede metric growth arcs if CI budget pressure is high |
| S6 | depends on stable D3/S1 evidence outputs and explicit evidence linkage (`justification_refs`) |
| S7 | independent but operationally easier after S5 CI/runtime hardening |
| S8 | depends on stable outcomes from S1/S5 and explicit semantics versioning strategy |
| S9 | fallback path that preempts expansion paths when parity thresholds regress |

## Consolidated Recommended Order (v17+)

Default balanced sequence from synthesis:

1. `vNext+17`: Path S1 thin slice (integrity diagnostics expansion)
2. `vNext+18`: Path S5 thin slice (tooling consolidation + CI sustainability)
3. `vNext+19`: Path S3a thin slice (read-only product surface activation)
4. `vNext+20`: Path S4 thin slice (cross-IR coherence bridge)
5. `vNext+21+`: optional S6/S7/S8 progression based on risk appetite

Rationale:

- S1 closes explicit deferred diagnostic edges while v16 contracts are fresh.
- S5 controls complexity before further surface expansion.
- S3a and S4 maximize product/system value once integrity and maintainability are stabilized.
- S8 (solver semantics v4) remains intentionally deferred until preconditions are stronger.

Alternative balanced sequence (earlier product stress-test):

1. `vNext+17`: Path S3a thin slice (read-only product surface activation)
2. `vNext+18`: Path S1 thin slice (integrity diagnostics expansion)
3. `vNext+19`: Path S5 thin slice (tooling consolidation + CI sustainability)
4. `vNext+20`: Path S3b or S4 based on S3a evidence and user workflow pain points

Rationale for alternative:

- it preserves additive/read-only safety,
- gives earlier feedback on real payload/UX usefulness,
- and can tighten S1 scope based on observed gaps instead of purely speculative deferred edges.

Stability-first sequence (CI pressure first):

1. `vNext+17`: Path S5 thin slice (tooling consolidation + CI sustainability)
2. `vNext+18`: Path S1 thin slice (integrity diagnostics expansion)
3. `vNext+19`: Path S3a thin slice (read-only product surface activation)
4. `vNext+20`: Path S4 thin slice (cross-IR coherence bridge)

Rationale for stability-first:

- addresses metric-growth cost before adding new determinism metrics,
- reduces migration/refactor risk before product exposure,
- keeps expansion arcs operating on a cleaner runtime/validation base.

S2 prioritization note:

- S2 is intentionally not in the default top sequence; treat it as conditional and pull it
  forward only if alignment fidelity defects are observed in active usage or audits.
- S2 trigger definition (to be frozen before lock):
  - trigger when projection-alignment defects exceed `>= X` mismatches per fixture replay set
    or manual audits detect span/label drift in `>= N` reviewed cases.
- recommended placeholders for planning: `X=3`, `N=5` (freeze concrete values in lock doc).

Execution checkpoint (current state):

- completed:
  - `vNext+17 = S1` (closed out)
  - `vNext+18 = S5` (closed out)
  - `vNext+19 = S3a` (closed out)
  - `vNext+20 = S4` (closed out)
  - `vNext+21 = S6` (closed out)
  - `vNext+22 = S7` (closed out)
  - `vNext+23 = S8` (closed out)
- active default next selection:
  - `vNext+24 = pending lock selection` (post-S8 follow-on scope to be explicitly frozen)

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS24.md` with one thin-slice continuation only (exact path to be selected and explicitly frozen):

1. freeze deterministic contract deltas for the selected post-v23 scope.
2. keep additive-only stop-gate metric extension on `stop_gate_metrics@1`.
3. preserve v14-v23 continuity locks unless an explicit release is approved.
4. keep non-enforcement/no-mutation/no-provider-expansion boundaries explicit where applicable.

## Historical Freeze Candidate (v19 Reference)

Implemented lock doc:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS19.md` (Path S3a, `R1`-`R4`)

Merged implementation sequence:

1. PR `#158` (`R1`): fixture-backed read-only `/urm` core-ir/lane/integrity endpoints
2. PR `#159` (`R2`): deterministic read-surface render payload builder
3. PR `#160` (`R3`): additive v19 read-surface stop-gate determinism metrics
4. PR `#161` (`R4`): provider/network guard coverage + deterministic no-mutation snapshot checks

## Historical Freeze Candidate (v17 Reference)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md` with Path S1 thin slice only:

1. `E1` deterministic extended reference-integrity diagnostics
2. `E2` deterministic extended cycle-policy diagnostics
3. `E3` deterministic deontic conflict expansion (still evidence-first)
4. `E4` manifest-driven coverage accountability + additive stop-gate metrics for `vNext+17 -> vNext+18`

Deferred-edge lock candidate for S1 (`E1`-`E3`):

- S1 deferred-edge candidate set (exhaustive for this synthesis):
  - missing referenced node ids in node-level reference fields (not only edge endpoints),
  - edge endpoint references that exist but violate frozen edge typing constraints,
  - duplicate edge identity collisions (`(type, from, to)` duplicates).
- the lock doc must select and freeze an explicit subset from this exhaustive set as the full
  `E1`-`E3` scope; no additional deferred-edge kinds may be introduced without updating this
  synthesis first.

Metric naming rule for S1 expansion:

- v16 metric keys remain unchanged and must not be reused/overwritten by expansion work.
- additive v17 S1 metrics must use `_extended_` in key names (not `_expanded_`).

Suggested measured outcomes for `vNext+17 -> vNext+18` gate:

- existing v16 family metrics remain present and at threshold:
  - `artifact_dangling_reference_determinism_pct == 100.0`
  - `artifact_cycle_policy_determinism_pct == 100.0`
  - `artifact_deontic_conflict_determinism_pct == 100.0`
- additive expansion metrics use explicit non-replacement naming:
  - `artifact_reference_integrity_extended_determinism_pct == 100.0`
- `artifact_cycle_policy_extended_determinism_pct == 100.0`
- `artifact_deontic_conflict_extended_determinism_pct == 100.0`
- no solver-semantics delta and no trust-lane regression
- all existing stop-gate tracked `vNext+6` through `vNext+16` metrics remain at threshold
- closeout evidence from prior arcs remains green and reproducible

## Candidate v17 Locks (Mutually Exclusive)

Candidate v17-A (default in this synthesis):

- `vNext+17 = Path S1` (`E1`-`E4`) integrity diagnostics expansion.
- choose this if the priority is tightening evidence/contracts before expanding product surfaces.

Candidate v17-B (read-only product stress-test):

- `vNext+17 = Path S3a` with:
  - `R1` read-only endpoints for persisted core-ir/lane/integrity artifacts,
  - `R2` deterministic render-payload builder + transfer-report refresh,
  - `R3` additive stop-gate determinism metrics for read-surface payloads.
- choose this if the priority is early product/workflow learning while keeping proposer nondeterminism out of scope.
