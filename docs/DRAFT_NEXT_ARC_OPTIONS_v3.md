# Draft Next Arc Options v3 (Interconnected Layers + Provider Reliability)

This document is the continuation-planning draft after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS13.md`
- `docs/SEMANTICS_v3.md`
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`

Status: draft only (not frozen).
Goal: define post-`vNext+13` options and identify the concrete first slice for `vNext+14`.

## Consolidation Note

For post-`vNext+13` planning, this file remains the working source of truth.
`docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` remains historical context only.

## Baseline Snapshot (Post vNext+13)

Current baseline includes:

- `vNext+13` (`A1`-`A4`) complete and merged on `main`:
  - `adeu_core_ir@0.1` schema + deterministic ordering/validation
  - deterministic projection/extraction canonicalization path
  - deterministic claim ledger scoring (`S_milli/B_milli/R_milli`) via `adeu.sbr.v0_1`
  - additive stop-gate metrics and fixture closeout
- v13 closeout is green:
  - `valid=true`
  - `all_passed=true`
  - `adeu_core_ir_replay_determinism_pct=100.0`
  - `adeu_claim_ledger_recompute_match_pct=100.0`
  - `adeu_lane_projection_determinism_pct=100.0`
- prior arc guarantees remain green:
  - stop-gate tracked `vNext+6` through `vNext+11` metrics remain at threshold
  - `vNext+12` closeout evidence remains green/reproducible

Net: the core O/E/D/U artifact spine is stable enough to shift focus to provider reliability and cross-module parity hardening.

## Repo-Grounded Clarifications

1. `adeu_core_ir@0.1` remains additive/projection-oriented:
   - authoritative upstream semantics remain on `adeu.ir.v0` and `adeu.concepts.v0`.
2. Determinism boundary remains unchanged:
   - provider generation may be nondeterministic,
   - deterministic claims are enforced on persisted fixtures + canonical transforms.
3. Provider parity remains a practical product risk surface:
   - route-level provider acceptance drift,
   - codex candidate parse/repair drift,
   - module action/gating drift after provider selection.
4. Formal integrity expansion should wait until provider parity is stable:
   - keep solver semantics untouched.

## Shared Locks For Any Next Arc

- No solver semantic contract changes unless explicitly versioned and locked.
- `docs/SEMANTICS_v3.md` remains authoritative unless a versioned follow-on lock says otherwise.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- New behavior is additive-only unless explicitly marked breaking.
- Replay determinism is mandatory for acceptance paths.
- Runtime behavior must emit evidence events in `urm-events@1`.
- New `/urm/...` endpoints must be idempotent via `client_request_id`.
- New artifacts must be schema-versioned under `spec/` and canonically serialized.
- Stop-gate schema continuity remains additive on `stop_gate_metrics@1` unless explicitly re-locked.

## Path 8: Provider Reliability + Module Parity (Recommended for vNext+14)

### Goal

Complete deterministic provider parity and codex reliability across module proposer surfaces.

### Scope

1. Normalize route/provider contract acceptance for supported module endpoints.
2. Harden codex candidate normalization/repair and deterministic diagnostics.
3. Add deterministic fixture parity coverage and transfer-report evidence.
4. Close out with additive `vNext+14` stop-gate metrics.

### Locks

- provider taxonomy lock:
  - `mock`, `openai`, `codex` remain explicit and additive.
- scope boundary lock:
  - Path 8 targets parity on existing proposer families (`adeu.ir.v0`, `adeu.concepts.v0`, puzzles) and does not introduce a new `adeu_core_ir` proposer surface.
- surface model lock:
  - parity is frozen by `surface_id` (route + mode variant when needed), not by route path string alone.
- provider matrix authority lock:
  - supported route/provider matrix is fixture-backed and deterministic.
- normalization boundary lock:
  - repair schema-shape noise only; no semantic rewrites.
- replay boundary lock:
  - deterministic acceptance/replay uses persisted fixtures only; no live provider dependency.

### Acceptance

- No supported route fails with provider-literal mismatch for `provider=codex`.
- Codex normalized outputs are contract-valid across targeted module proposer flows.
- Deterministic parity metrics pass at frozen thresholds on locked fixtures.

### Risk

- provider/runtime heterogeneity can reintroduce flaky behavior unless matrix + fixtures are strict.

## Path 7b: Core-IR Follow-On (Post-Provider Stabilization)

### Goal

Expand core-IR depth after provider reliability hardening.

### Scope

1. Lane UX/reporting refinement with deterministic lane projection artifacts.
2. Additional core-ir surface coverage and pressure fixtures.
3. Optional additive diagnostics around projection/extraction divergence trends.

### Locks

- `adeu_core_ir@0.1` contract remains authoritative in this expansion.
- no replacement of existing authoritative upstream IR contracts.

### Acceptance

- Added depth remains additive and replay-deterministic on persisted fixtures.

## Path 9: Formal Sanity Checks (Deferred Integrity Slice)

### Goal

Add deterministic integrity checks over layer graphs without broad solver-contract change.

### Scope

1. dangling reference enforcement
2. dependency cycle policy checks
3. minimal deontic conflict checks under shared conditions

### Locks

- integrity-only scope in first slice; no solver-semantics expansion.
- deterministic fail-closed reason-code ordering.

### Acceptance

- locked fixtures produce stable deterministic pass/fail artifacts.

## Decision Matrix

### If priority is immediate production reliability of provider-backed module flows

- Start with Path 8.

### If priority is deeper O/E/D/U UX/reporting capabilities after reliability stabilization

- Continue with Path 7b.

### If priority is formal graph integrity hardening

- Start Path 9 only after Path 8 reliability closeout.

## Recommended Arc Order (v14+)

1. `vNext+14`: Path 8 thin slice (`8a`) — provider contract parity + codex normalization closeout
2. `vNext+15`: Path 7 follow-on (`7b`) — lane/core-ir depth expansion on stable provider base
3. `vNext+16`: Path 9 thin slice (`9a`) — formal integrity checks

Why this order:

- it stabilizes provider execution reliability before broader UX/formal expansion,
- reduces noisy operational regressions while core-ir adoption scales,
- keeps deterministic closeout discipline consistent with prior arcs.

Fallback sequencing rule:

- if provider reliability regresses during `vNext+15` planning, keep Path 8 hardening active and defer further expansion.

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` with Path 8 thin slice (`8a`) only:

1. `B1` provider contract parity normalization for supported routes
2. `B2` codex candidate normalization/repair hardening with deterministic parity diagnostics
3. `B3` deterministic fixture coverage accounting + transfer-report refresh
4. `B4` additive stop-gate metrics for `vNext+14 -> vNext+15` closeout

Suggested measured outcomes for `vNext+14 -> vNext+15` gate:

- `provider_route_contract_parity_pct == 100.0`
- `codex_candidate_contract_valid_pct == 100.0`
- `provider_parity_replay_determinism_pct == 100.0`
- no solver-semantics delta and no trust-lane regression
- all existing stop-gate tracked `vNext+6` through `vNext+13` metrics remain at threshold
- `vNext+12` closeout evidence remains green and reproducible
- `vNext+13` closeout evidence remains green and reproducible
