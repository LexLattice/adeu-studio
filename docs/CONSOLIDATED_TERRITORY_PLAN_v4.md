# Consolidated Territory Plan v4 (Draft Planning, Not Frozen)

Inputs:

- `docs/CONSOLIDATED_TERRITORY_PLAN_v3.md`
- `docs/CONSOLIDATED_TERRITORY_PLAN_v3_FACT_CHECKS.md`
- `docs/reviewv2.md`
- `docs/leanv2.md`
- `docs/next arcv2.md`

This is a planning doc only. It is not a lock doc and does not authorize behavior changes.

## 1) Repo Truth Snapshot (Grounded)

Repo anchors:

- Current lock baseline is v26:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS26.md`
  - `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`
  - `artifacts/stop_gate/metrics_v26_closeout.json`
- Active `/urm` evidence surfaces are present in:
  - `apps/api/src/adeu_api/main.py`
- Primary operational hotspots:
  - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` (~15179 LOC)
  - `apps/api/src/adeu_api/main.py` (~7424 LOC)

Mechanical status:

- `VERIFIED`: v26 baseline artifacts exist.
- `VERIFIED`: active evidence routes exist in API.
- `VERIFIED`: ODEU Lean prep files exist:
  - `packages/adeu_lean/AdeuODEU/Artifacts.lean`
  - `packages/adeu_lean/AdeuODEU/Invariants.lean`
- `MISSING`: `apps/api/scripts/check_s9_triggers.py`.
- `MISSING`: v27 lock artifacts are not created yet:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
  - `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`

## 2) Lock-class Glossary (Canonical for this Plan)

- `L0`:
  behavior-preserving hardening/refactor; output/hash/order parity must hold for locked fixtures.
- `L1`:
  lock-alignment correction; behavior may change only where current code violates a frozen lock, and acceptance must prove the change is bounded to the violating region.
- `L2`:
  boundary release; requires a new continuation lock that explicitly widens capability, semantics, or persistence authority.

## 3) Two-tier Execution Model

Decision for this plan:

- **Option A selected**:
  Gate-0 preconditions are implemented as the first scope inside `vNext+27` and block all other expansion work until green.

Implication:

- There is no separate `v26.x` hotfix storyline in this plan.
- `vNext+27` is the gate-opening arc.

## 4) Tier A Gate-0 Preconditions (Executable Contracts)

## G0.1 S9 trigger checker contract

Gap:

- `apps/api/scripts/check_s9_triggers.py` is missing.

Contract:

- Input:
  - `--metrics-path` (defaults to locked v25 closeout metrics artifact used by precondition checks).
  - optional `--required-threshold` default `100.0`.
- Rationale for v25 default:
  - v26 lock defines S9 precondition over v25 closeout evidence; checker default must mirror that lock reference until a later lock explicitly updates it.
- Required metric keys:
  - `provider_route_contract_parity_pct`
  - `codex_candidate_contract_valid_pct`
  - `provider_parity_replay_determinism_pct`
- Comparator:
  - fail if any required metric `< required_threshold`.
- Output:
  - deterministic JSON summary to stdout.
  - deterministic error summary to stderr on failure.
- Exit codes:
  - `0` when all required keys exist and meet threshold.
  - `1` on missing key, parse error, or threshold failure.

Acceptance:

- tests cover: all-pass, missing-key, below-threshold, malformed-json.

Lock class:

- `L1`.

## G0.2 v26 normalization allowlist contract

Gap:

- current normalization in `stop_gate_tools.py` applies to generic suffix keys (`*_path`, `*_paths`).
- frozen lock allowlist is explicit and narrower.

Contract:

- Given input keys `{baseline_path, candidate_path, report_path, manifest_path, extra_path, extra_paths}`:
  - only allowlist keys may be normalized.
  - `extra_path` and `extra_paths` must remain byte-identical.
- Synthetic fixture clarifier:
  - `extra_path` and `extra_paths` are representative adversarial stand-ins for any non-allowlisted path-like keys; tests must assert that no non-allowlisted keys are normalized, even if names end with `_path` or `_paths`.

Acceptance:

- parity projection tests assert exact key-level behavior above.
- locked fixture parity/hash outputs remain unchanged.

Lock class:

- `L1`.

## G0.3 deterministic env enforcement contract

Gap:

- entrypoint scripts do not enforce deterministic env internally.

Policy selected for this plan:

- **Set-then-assert**:
  - if `TZ` or `LC_ALL` are missing, set to frozen defaults (`UTC`, `C`).
  - if present with conflicting values, fail closed deterministically.

Entry points covered in vNext+27:

- `apps/api/scripts/build_stop_gate_metrics.py`
- `apps/api/scripts/build_quality_dashboard.py`

Acceptance:

- tests cover missing-env (auto-set), correct-env (pass), conflicting-env (fail).
- locked fixture outputs remain unchanged.

Lock class:

- `L0`.

## G0.4 v26 transfer-report regeneration contract

Gap:

- v24/v25 have dedicated builder modules; v26 does not have a dedicated counterpart.

Contract:

- Ownership:
  - runtime-owned builder in `packages/urm_runtime/src/urm_runtime/`.
  - script entrypoint in `apps/api/scripts/`.
- Canonical target:
  - machine-checkable fenced JSON block in `docs/TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md`.
- Extraction algorithm:
  - parse markdown, locate the first fenced block labeled `json` under the report’s machine-checkable section, parse JSON payload, canonicalize with existing canonical-json helper before parity comparison.
- Parity basis:
  - compare parsed machine-checkable JSON block payloads, not raw markdown bytes.
  - rebuilt JSON must be canonical-hash identical to extracted JSON unless a lock explicitly defines parity-field exclusions.
- Markdown policy:
  - markdown wrapper text may differ.
  - fenced JSON block content must be canonical-hash identical.

Acceptance:

- deterministic regeneration test for v26 JSON block parity.

Lock class:

- `L0`.

## 5) Rule of Engagement

- L1 items are first and blocking.
- L0 items may proceed only within current boundaries.
- L2 items stay deferred unless explicitly released by a new lock doc.
- No L2 work enters implementation without explicit release text.

## 6) Ranked Risk Register (with ownership)

| Rank | Risk | Evidence | Class | Owner arc |
|---|---|---|---|---|
| 1 | v26 normalization lock mismatch | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`, `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` | `L1` | vNext+27 |
| 2 | missing S9 checker script | `docs/LOCKED_CONTINUATION_vNEXT_PLUS26.md`, missing `apps/api/scripts/check_s9_triggers.py` | `L1` | vNext+27 |
| 3 | deterministic env not enforced by entrypoints | `apps/api/scripts/build_stop_gate_metrics.py`, `apps/api/scripts/build_quality_dashboard.py` | `L0` | vNext+27 |
| 4 | canonical json/hash helper duplication | API/runtime/kernel/explain/core-ir helper paths | `L0` | vNext+27 (conformance), vNext+28 (consolidation) |
| 5 | stop-gate tooling monolith | `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` | `L0` | vNext+28 |
| 6 | API main monolith | `apps/api/src/adeu_api/main.py` | `L0` | deferred maintenance track |
| 7 | manifest version declaration duplication | script + runtime duplicated version sets | `L0` | vNext+28 |
| 8 | `/urm/worker/run` governance divergence | `apps/api/src/adeu_api/urm_routes.py` | `L2` | deferred |
| 9 | proposer idempotency process-local cache | `apps/api/src/adeu_api/main.py` | `L2` | deferred |
| 10 | Lean temp filename nondeterminism | `packages/adeu_lean/src/adeu_lean/runner.py` | `L0` | vNext+30 |
| 11 | v26 transfer-report regen path implicit | v24/v25 dedicated modules only | `L0` | vNext+28 |

## 7) Cross-stream Shared Primitives (Actionable)

| Primitive | Requirement | Location target | Test contract |
|---|---|---|---|
| Deterministic env helper | one helper + entrypoint invocation | runtime helper + API scripts | missing/correct/conflict env tests |
| Canonical-json conformance | one cross-layer suite | API/runtime test layer | identical canonical bytes + hashes |
| Recursive `created_at` stripper | one canonical helper only | runtime shared utility | parity-hash equivalence tests |
| Active-manifest registry | one source of truth | runtime registry used by scripts/tests | no duplicated hard-coded version tuples |
| v26 allowlist normalization | normalize allowlist keys only | v26 parity projection helper path | key-level normalization boundary tests |
| S9 checker | deterministic fail-closed script | `apps/api/scripts/check_s9_triggers.py` | 0/1 exit-code + deterministic output tests |
| Formal oracle boundary | separate structural proofs from hash-oracle checks | formal lane modules/docs | agreement tests with explicit oracle fields |
| Naming consistency | one canonical filename reference per artifact | docs planning/lock chain | path-lint check or review checklist item |

## 8) Standard Arc Template (required in future drafting)

For every arc draft in this territory:

- Goal
- Scope
- Locks
- Acceptance
- Stop-gate impact
- Commit plan (small-green)
- Closeout observability clause:
  include runtime-observability comparison row against prior canonical baseline.

## 9) Arc Instantiations (vNext+27 to vNext+30)

## Arc vNext+27 (W1 / Path A)

Readiness:
- draft lock candidate.

Goal:
- complete Tier A Gate-0 preconditions.

Scope:
- implement G0.1, G0.2, G0.3.
- add canonical-json conformance tests.

Locks:
- no schema changes.
- no new metric keys.
- preserve `stop_gate_parity.v1` fixture behavior.

Acceptance:
- Gate-0 contracts all pass.
- locked v26 fixture outputs remain unchanged.

Stop-gate impact:
- no new keys / no schema fork.
- listing endpoints are non-gated convenience surfaces in this arc (covered by deterministic and guard tests, but not introduced as new stop-gate metric families).
- closeout includes runtime-observability comparison row.

Commit plan:
1. S9 checker script + tests.
2. v26 allowlist normalization correction + tests.
3. deterministic env helper + script wiring + tests.
4. canonical-json conformance tests.

## Arc vNext+28 (W2 / Path A)

Readiness:
- draft lock candidate.

Goal:
- improve tooling sustainability while preserving behavior.

Scope:
- modularize stop-gate internals.
- centralize active-manifest registry.
- implement explicit v26 transfer-report regen path (G0.4).

Locks:
- preserve output payload and ordering.
- preserve existing metric semantics.

Acceptance:
- baseline-vs-candidate parity hash identity on locked fixtures.
- v26 regen path deterministic over parsed JSON block parity.

Stop-gate impact:
- no new keys / no schema fork.
- closeout includes runtime-observability comparison row.

Commit plan:
1. manifest registry extraction.
2. internal modularization with compatibility façade.
3. v26 transfer-report builder + script entrypoint.
4. parity regression tests.

## Arc vNext+29 (W3 / Path B)

Readiness:
- draft lock candidate.

Goal:
- ship read-only evidence UX over existing evidence families.

Scope:
- deterministic catalog/list endpoints.
- explorer UI for existing packet/projection families.
- explicit trust-lane and non-enforcement labels.

Locks:
- no enforcement behavior.
- no provider expansion.
- fixture-first authority preserved.

Acceptance:
- deterministic sorted outputs.
- no-provider/no-mutation guard coverage.
- non-enforcement messaging present in UI surfaces.

Stop-gate impact:
- no new keys / no schema fork.
- closeout includes runtime-observability comparison row.

Commit plan:
1. deterministic listing endpoints.
2. explorer UI shell.
3. packet/projection renderers + labels.
4. guard and deterministic ordering tests.

## Arc vNext+30 (W4 / Path C)

Readiness:
- planning-only research arc; requires pre-lock evidence before freezing.

Goal:
- advance additive formal ODEU lane with deterministic agreement checks.

Scope:
- stabilize ODEU compile path.
- prove first structural invariants.
- add fixture-backed Python->Lean agreement harness.
- include Lean temp filename determinism hardening.
- deterministic temp-path strategy:
  - temp filenames must be derived from stable artifact/request hash inputs, created under a deterministic workdir, and cleaned deterministically.

Locks:
- `SEMANTICS_v3` remains runtime authority.
- no enforcement semantics from formal outputs.
- hashing/canonical-json remain oracle-bounded unless explicitly released.

Acceptance:
- deterministic compile and agreement runs.
- no runtime API/kernel behavior changes.

Stop-gate impact:
- no new keys by default.
- closeout includes runtime-observability comparison row.

Commit plan:
1. ODEU module/stability pass.
2. fixture-backed agreement harness.
3. first structural theorem set.
4. deterministic Lean runner temp-path behavior.

## 10) Deferred L2 Bucket

Deferred until explicit lock release:

- default capability-policy enforcement for `/urm/worker/run`.
- persistent/shared proposer idempotency store replacing process-local cache.

## 11) Recommended Sequence + Dependency Edges

Recommended sequence:

1. vNext+27 (W1 / Path A)
2. vNext+28 (W2 / Path A)
3. vNext+29 (W3 / Path B)
4. vNext+30 (W4 / Path C)

Dependencies:

- vNext+28 depends on vNext+27.
- vNext+29 depends on vNext+27.
- vNext+30 depends on vNext+27 and partially on vNext+28.
- Any L2 activation depends on explicit lock release.

## 12) Planning Boundaries

- planning-only, not lock text.
- no code implementation performed by this doc.
- no metric-key additions claimed here.
- metric additions require explicit new evidence-family justification in a future lock.
