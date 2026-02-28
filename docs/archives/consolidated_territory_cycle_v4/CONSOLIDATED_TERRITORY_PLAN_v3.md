# Consolidated Territory Plan v3 (Draft Planning, Not Frozen)

Inputs:

- `docs/CONSOLIDATED_TERRITORY_PLAN_v2.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v2_FACT_CHECKS.md`
- `docs/reviewv2.md`
- `docs/leanv2.md`
- `docs/next arcv2.md`

This is a planning doc only. It is not a lock doc and does not authorize behavior changes.

## 1) Repo Truth Snapshot (Grounded, Fact-Checked)

### 1.1 Repo anchors (minimal, operational)

- Baseline lock and closeout are `vNext+26`:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
  - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
  - `artifacts/stop_gate/metrics_v26_closeout.json`
- Active `/urm` evidence surfaces exist in API:
  - `apps/api/src/adeu_api/main.py`
- Primary hotspots by centrality/LOC:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (~15179 LOC)
  - `apps/api/src/adeu_api/main.py` (~7424 LOC)

### 1.2 Mechanical verification status

- `VERIFIED`: baseline v26 lock + closeout artifacts exist (see anchors above).
- `VERIFIED`: evidence routes (`/urm/core-ir/*`, `/urm/normative-advice/*`, `/urm/proof-trust/*`, `/urm/semantics-v4/*`, `/urm/extraction-fidelity/*`) exist in `apps/api/src/adeu_api/main.py`.
- `VERIFIED`: ODEU Lean prep files exist:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`
- `MISSING`: `apps/api/scripts/check_s9_triggers.py`.
- `MISSING`: v27 lock artifacts are not yet created:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
  - `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`

## 2) Two-tier Plan

## Tier A: Gate-0 pre-lock preconditions (must complete before expansion lock)

1. S9 trigger checker script is missing.
- Gap: `apps/api/scripts/check_s9_triggers.py` absent.
- Lock class: `L1`.
- Why it blocks: v26 declares executable S9 precondition.
- Lowest-lock fix: add deterministic checker script, fail-closed on missing/below-threshold metrics.
- Acceptance check: deterministic script test coverage over pass/fail/missing-key cases.

2. v26 path normalization implementation exceeds lock allowlist.
- Gap: code normalizes generic `*_path/*_paths` keys.
- Lock class: `L1`.
- Why it blocks: lock freezes allowlist-only normalization (`baseline_path`, `candidate_path`, `report_path`, `manifest_path`).
- Lowest-lock fix: enforce allowlist-only normalization path.
- Acceptance check: parity projection tests prove non-allowlist fields are untouched.

3. deterministic env lock is not enforced by tooling entrypoints.
- Gap: no entrypoint-level enforcement in build scripts.
- Lock class: `L0`.
- Why it blocks: determinism remains caller-environment dependent.
- Lowest-lock fix: shared helper invoked at entrypoint start.
- Acceptance check: helper fail-closed behavior tests plus unchanged fixture outputs.

4. v26 tooling transfer-report regeneration path is not explicit.
- Gap: v24/v25 have dedicated transfer-report builder modules; v26 lacks dedicated module/script counterpart.
- Lock class: `L0`.
- Why it blocks: higher risk of report maintenance drift.
- Lowest-lock fix: add deterministic v26 builder module/script + parity tests.
- Acceptance check: generated v26 report payload parity against locked baseline.

## Tier B: Forward territory (planning-only multi-workstream map)

- W1: Determinism/lock-alignment baseline
- W2: Stop-gate tooling sustainability
- W3: Read-only product evidence UX
- W4: Formal ODEU additive lane

## 3) Rule of Engagement (Lock-class Steering)

- L1 items are scheduled first and treated as gate-opening corrections.
- L0 items may ship as behavior-preserving hardening within current lock boundaries.
- L2 items are deferred unless a new continuation lock explicitly releases the boundary.
- No L2 work enters an arc unless the lock doc explicitly releases that boundary.

## 4) Ranked Risk Register (Evidence + Lock Class)

| Rank | Risk | Evidence | Lock class |
|---|---|---|---|
| 1 | v26 path normalization lock mismatch | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`, `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (`_normalize_vnext_plus26_parity_paths`) | `L1` |
| 2 | Missing executable S9 trigger checker | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`, missing `apps/api/scripts/check_s9_triggers.py` | `L1` |
| 3 | Deterministic env lock not enforced by tooling entrypoints | `apps/api/scripts/build_stop_gate_metrics.py`, `apps/api/scripts/build_quality_dashboard.py` | `L0` |
| 4 | Canonical JSON/hash helper duplication across layers | `apps/api/src/adeu_api/hashing.py`, `packages/urm_runtime/src/urm_runtime/hashing.py`, `packages/adeu_kernel/src/adeu_kernel/validator_evidence.py`, `packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py`, `packages/adeu_explain/src/adeu_explain/explain_diff.py`, `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py` | `L0` |
| 5 | stop-gate tooling monolith risk | `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` | `L0` |
| 6 | API main monolith risk | `apps/api/src/adeu_api/main.py` | `L0` |
| 7 | stop-gate manifest version declaration duplication | `apps/api/scripts/build_stop_gate_metrics.py`, `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` | `L0` |
| 8 | `/urm/worker/run` governance path divergence | `apps/api/src/adeu_api/urm_routes.py` | `L2` |
| 9 | proposer idempotency process-local cache | `apps/api/src/adeu_api/main.py` (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`) | `L2` |
| 10 | Lean temp filename nondeterminism | `packages/adeu_lean/src/adeu_lean/runner.py` | `L0` |
| 11 | v26 transfer-report builder path not explicit | dedicated v24/v25 modules exist, no dedicated v26 counterpart | `L0` |

## 5) Cross-stream Shared Primitives (Actionable)

| Primitive | Requirement | Location target | Test contract |
|---|---|---|---|
| Deterministic env enforcement | One shared helper; entrypoints must invoke it before computation | `packages/urm_runtime/src/urm_runtime/` helper + calls from `apps/api/scripts/build_stop_gate_metrics.py` and `apps/api/scripts/build_quality_dashboard.py` | pass/fail tests for correct env and conflicting env; fixture output parity unchanged |
| Canonical JSON conformance | One conformance suite across API/runtime/kernel implementations | test layer under `apps/api/tests/` (or runtime equivalent) | same canonical output/hash across all helpers on fixed corpus |
| Recursive `created_at` stripping | One canonical helper; no ad hoc variants | runtime shared utility module | parity hash equivalence tests vs current locked behavior |
| Shared active-manifest registry | Single source of truth for active vnext manifest versions | runtime shared registry consumed by scripts/tests | script and runtime use same version set; no duplicate tuples |
| v26 allowlist normalization | Normalize only frozen allowlist keys | v26 parity projection helpers in stop-gate tooling | test that non-allowlist path fields are not normalized |
| S9 trigger checker | Deterministic fail-closed metric gate script | `apps/api/scripts/check_s9_triggers.py` | parse/threshold tests: missing key fails, below threshold fails, all pass succeeds |
| Formal oracle boundary | Structural proofs hard; hashing/canonical-json oracle-bounded | formal lane docs + ODEU modules | agreement tests explicitly separate structural proof and oracle fields |

## 6) Standard Arc Template (single form)

Use this exact planning template for each thin slice:

- Goal
- Scope
- Locks
- Acceptance
- Stop-gate impact
- Commit plan (small-green)

## 7) Arc Instantiations (vNext+27 to vNext+30)

## Arc vNext+27 (Workstream W1, Path A)

Readiness: **Draft lock candidate**.

Goal:
- Complete gate-0 lock-alignment and determinism baseline fixes.

Scope:
- S9 checker script.
- v26 allowlist normalization correction.
- deterministic env helper and wiring.
- canonical-json conformance tests.

Locks:
- No schema changes.
- No new metric keys.
- Preserve `stop_gate_parity.v1` behavior on locked fixtures.

Acceptance:
- deterministic checker script exists and is tested.
- parity projection behavior matches lock allowlist.
- entrypoint env enforcement tests pass.
- canonical-json conformance tests pass.

Stop-gate impact:
- No new keys and no schema fork.
- Runtime observability is still reported and compared against prior closeout baseline.

Commit plan:
1. Add S9 checker script + tests.
2. Implement allowlist normalization correction + tests.
3. Add deterministic env helper + wire entrypoints.
4. Add canonical-json conformance tests.

## Arc vNext+28 (Workstream W2, Path A)

Readiness: **Draft lock candidate**.

Goal:
- Improve stop-gate tooling sustainability without behavior change.

Scope:
- modularize `stop_gate_tools.py` internals.
- centralize active manifest registry.
- add explicit deterministic v26 tooling transfer-report builder path.

Locks:
- Preserve output payload shapes and ordering.
- Preserve existing metric definitions and semantics.

Acceptance:
- baseline-vs-candidate parity hash identity on locked fixtures.
- shared manifest registry consumed by runtime/scripts/tests.
- v26 tooling transfer-report regeneration path deterministic and tested.

Stop-gate impact:
- No new keys and no schema fork.
- Runtime observability rows remain present in closeout evidence.

Commit plan:
1. Extract manifest registry.
2. Internal modularization with compatibility façade.
3. Add v26 transfer-report builder path.
4. Add parity regression tests.

## Arc vNext+29 (Workstream W3, Path B)

Readiness: **Draft lock candidate**.

Goal:
- Expose existing evidence families through read-only product UX.

Scope:
- deterministic catalog/list endpoints.
- read-only evidence explorer pages.
- explicit trust-lane and non-enforcement labels.

Locks:
- no enforcement behavior.
- no provider expansion.
- fixture-first authority remains unchanged.

Acceptance:
- deterministic sorted list outputs.
- no-provider/no-mutation guard tests for new read surfaces.
- UI labels candidate/advisory outputs as non-enforcing.

Stop-gate impact:
- No new keys and no schema fork.
- Runtime observability comparison still required in closeout.

Commit plan:
1. Add deterministic listing endpoints.
2. Add explorer UI shell.
3. Add packet/projection readers + labeling.
4. Add guard and deterministic ordering tests.

## Arc vNext+30 (Workstream W4, Path C)

Readiness: **Planning-only research arc** (needs additional agreement evidence before lock drafting).

Goal:
- Advance additive formal ODEU lane with deterministic agreement checks.

Scope:
- stabilize ODEU module compile path.
- structural invariant proofs aligned with existing validators.
- Python canonicalization -> Lean typed-constant agreement checks on fixtures.

Locks:
- `SEMANTICS_v3` remains runtime authority.
- no enforcement semantics from formal outputs.
- hashing/canonical-json remain oracle-bounded unless explicitly released.

Acceptance:
- deterministic compile + agreement runs on selected fixtures.
- no runtime behavior changes in API/kernel paths.

Stop-gate impact:
- No new keys by default.
- Any new key requires explicit new evidence-family justification and lock release.

Commit plan:
1. stabilize ODEU module wiring.
2. add fixture-backed agreement test harness.
3. prove first structural invariant set.
4. document oracle boundary in evidence output path.

## 8) Deferred L2 Bucket (Explicit lock release required)

- Default capability-policy enforcement for `/urm/worker/run`.
- Persistent/shared proposer idempotency storage replacing process-local cache.

These are intentionally excluded from vNext+27..vNext+30 default sequence.

## 9) Recommended Sequence + Dependency Edges

Recommended sequence:

1. `vNext+27` (W1 / Path A)
2. `vNext+28` (W2 / Path A)
3. `vNext+29` (W3 / Path B)
4. `vNext+30` (W4 / Path C)

Dependencies:

- `vNext+28` depends on `vNext+27`.
- `vNext+29` depends on `vNext+27`.
- `vNext+30` depends on `vNext+27` and partially on `vNext+28`.
- Any L2 activation depends on a separate explicit lock release.

## 10) Planning Boundaries

- Planning-only; not a lock.
- No implementation changes authorized here.
- No metric-key additions claimed here.
- New metric keys remain tied to explicit new evidence-family introduction and lock approval.
