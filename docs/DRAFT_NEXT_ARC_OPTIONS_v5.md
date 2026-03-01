# Draft Next Arc Options v5 (Post vNext+30)

This document is the fresh consolidated planning baseline for post-`vNext+30` sequencing.

Status: active planning draft (v17 through v30 baselines executed; active for `vNext+31+` selection).
Goal: define thin-slice, lock-respecting candidate paths for `vNext+31` and onward, while preserving the standard multi-implementation review sequence before lock freeze.

## Naming Convention (Paths vs Bundles)

- `V31-*` identifiers are reserved for single path families only.
- `B31-*` identifiers are reserved for explicit multi-path bundles only.
- Any selected arc must reference either one `V31-*` path or one `B31-*` bundle identifier; mixed shorthand is forbidden.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS27.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS28.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS29.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS30.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS28.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`
- archived GPT Pro snapshot inputs:
  - `docs/archives/next_arc_options_v5/DRAFT_NEXT_ARC_OPTIONS_v5_gpt_pro_snapshot.md`
  - `docs/archives/next_arc_options_v5/REVIEW_v5_gpt_pro_snapshot.md`

This is a planning document only. It is not a lock doc and does not authorize runtime behavior changes.

## Baseline Agreement (Current Ground Truth)

- Locked continuation baseline is `vNext+30` (W4 / Path C, `D1`-`D4`) and is closed on `main`.
- Latest closeout decision is `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`.
- Stop-gate schema family remains `stop_gate_metrics@1`.
- v29 and v30 closeout artifacts are present and committed:
  - `artifacts/quality_dashboard_v29_closeout.json`
  - `artifacts/stop_gate/metrics_v29_closeout.json`
  - `artifacts/stop_gate/report_v29_closeout.md`
  - `artifacts/quality_dashboard_v30_closeout.json`
  - `artifacts/stop_gate/metrics_v30_closeout.json`
  - `artifacts/stop_gate/report_v30_closeout.md`

## Lock Class Semantics (Operational)

- `L0`: internal hardening/tooling/guard-rail work with no externally visible contract change.
- `L1`: externally visible contract closure/behavior change on an existing surface (API/web/CLI/artifact contract), without boundary release.
- `L2`: boundary release (governance authority, persistence authority, provider/proposer surface expansion).

## Confirmed Post-v30 Gaps (Worth Addressing)

1. Evidence Explorer API/web contract mismatch:
   - API returns template `"/urm/evidence-explorer/catalog/{family}"`.
   - web validator currently expects expanded `"/urm/evidence-explorer/catalog/${family}"`.
2. `/urm/worker/run` and `/urm/worker/{worker_id}/cancel` are not policy-gated via `authorize_action`.
3. Repo-root discovery remains duplicated and `.git`-dependent in several scripts/tests/runtime helpers.
4. Worker CLI handling is compatibility-first, not fail-closed, when `--ask-for-approval` is unsupported.
5. Proposer idempotency remains process-local in-memory cache for one API path.

## Gap-to-Path Mapping (Total)

- Gap 1 -> `V31-A`
- Gap 2 -> `V31-F`
- Gap 3 -> `V31-D`
- Gap 4 -> `V31-E`
- Gap 5 -> `V31-G`

## Consolidated Path Families (v31+ Candidate Menu)

### Path V31-A: Evidence Explorer Contract Closure

Lock class: `L1`

Goal:
- Align web contract validation with the frozen API catalog contract so v29 explorer surface is operational.

Scope:
- Freeze contract interpretation: `families[].list_ref.path` is a URI template string using literal `{family}` placeholder.
- Update web validator/expander to support the frozen template form deterministically.
- Expansion rules are frozen:
  - replace exact substring `{family}` only;
  - fail closed if placeholder is missing or appears more than once;
  - fail closed if expanded path does not preserve expected endpoint prefix.
- Add frontend contract fixture test for catalog payload shape.

Locks:
- Do not change API payload contract already covered by v29 endpoint tests.
- No new evidence families or persistence authority.

Acceptance:
- Evidence Explorer page loads family list and family entries using live API payload.
- Fail-closed behavior remains deterministic for malformed payloads.

### Path V31-B: Closeout Consistency Guard Rail

Lock class: `L0`

Goal:
- Prevent closeout-doc drift between referenced artifacts and committed evidence.

Scope:
- Add deterministic docs-reference lint over `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS*.md`.
- Assert referenced `artifacts/...` files exist.
- Optionally assert declared metric-key continuity claims against referenced metrics artifacts.

Locks:
- No new stop-gate metric keys.
- No schema-family changes.

Acceptance:
- Guard fails closed on missing referenced artifact paths.
- Guard passes on current v29/v30 closeout chain.

### Path V31-C: Formal ODEU Template Activation v0.2 (Evidence-Only)

Lock class: `L1`

Goal:
- Start a deterministic artifact-to-Lean proof-packet flow for core contract checks without enforcement release.

Scope:
- Fix ODEU prep compile issues (for example, `CoreNode` accessor usage).
- Add minimal deterministic JSON->Lean codegen bridge for frozen fixtures.
- Emit evidence-only proof packet artifact(s) under real Lean lane.

Locks:
- Runtime validator remains enforcement authority.
- No policy mutation and no stop-gate schema/key expansion in this slice.

Acceptance:
- Deterministic generated Lean inputs and deterministic proof packet identity.
- Real Lean CI lane executes packet check and remains fail-closed.

### Path V31-D: Repo-root Resolution Consolidation

Lock class: `L0`

Goal:
- Replace fragmented repo-root discovery logic with one shared resolver path.

Scope:
- Consolidate script/test/runtime root discovery to shared helper behavior.
- Preserve deterministic env override semantics.

Locks:
- No behavior changes to business logic outputs.

Acceptance:
- Scripts/tests remain deterministic in normal checkouts and exported source layouts.

### Path V31-E: Worker CLI Safety Tightening

Lock class: `L1`

Goal:
- Decide and lock explicit behavior when required `codex exec` flags are unsupported.

Scope:
- Define fail-closed vs compatibility-mode policy for `--ask-for-approval` and related execution flags.
- Add explicit tests for chosen policy path.

Locks:
- No silent behavior ambiguity after lock freeze.

Acceptance:
- Unsupported-flag behavior is deterministic, explicit, and test-covered.

### Path V31-F: `/urm/worker/run` Governance Alignment

Lock class: `L2` (boundary release)

Goal:
- Route worker execution endpoints through capability policy with explicit authorization semantics.

Scope:
- Apply `authorize_action` to worker run/cancel surfaces.
- Add audit events and deterministic denial payloads.

Locks:
- Requires explicit lock text authorizing boundary expansion.

Acceptance:
- Unauthorized requests fail closed deterministically.
- Authorized behavior remains compatible.

### Path V31-G: Proposer Idempotency Persistence Alignment

Lock class: `L2` (boundary release)

Goal:
- Replace process-local proposer idempotency cache with persisted, deterministic idempotency storage.

Scope:
- Persist proposer idempotency records.
- Preserve existing response semantics under replay/conflict.

Locks:
- Requires explicit boundary-release lock text.

Acceptance:
- Multi-process behavior is deterministic and conflict-safe.

## L2 Precondition Hygiene (Invariant)

- No `L2` path is selectable until a dedicated boundary lock doc enumerates:
  - newly authorized surface(s),
  - persistence-authority change(s),
  - rollback and deterministic denial semantics.

## Decision Matrix (Thin-slice Selection)

| Option ID | Includes | Max lock class | Benefit | Risk |
|---|---|---:|---|---|
| `V31-A` | `V31-A` | `L1` | Restores v29 explorer usability | low |
| `V31-B` | `V31-B` | `L0` | Prevents closeout drift regressions | low |
| `B31-AB` | `V31-A + V31-B` | `L1` | Product + operational hardening together | low/med |
| `V31-C` | `V31-C` | `L1` | Extends formal lane evidence value | med/high |
| `V31-D` | `V31-D` | `L0` | Reduces portability/tooling drift | low |
| `V31-E` | `V31-E` | `L1` | Clarifies worker safety policy | med |
| `V31-F` | `V31-F` | `L2` | Closes governance gap | high |
| `V31-G` | `V31-G` | `L2` | Closes proposer idempotency boundary | high |

## Recommended Sequencing (Default)

1. `vNext+31`: `B31-AB` (`V31-A + V31-B`)
   - fixes active explorer usability gap and adds closeout consistency guard rails.
2. `vNext+32`: `V31-C` (formal lane) or `V31-D` (repo-root consolidation), based on active velocity blocker.
3. `vNext+33`: complete whichever of `V31-C`/`V31-D` remains, then `V31-E`.
4. `vNext+34+`: evaluate `L2` releases (`V31-F`, `V31-G`) only via explicit boundary lock.

## Standard Multi-Implementation Sequence (Required)

For each selected arc candidate (starting with `vNext+31`):

1. Draft parallel implementation briefs for multiple implementers (`codex`, `gpt`, `gemini`, `opus`) with identical locks/acceptance.
2. Run independent implementations and collect deterministic evidence bundles.
3. Produce comparative assessment (risk, lock adherence, determinism evidence, CI impact).
4. Consolidate into one lock candidate (`docs/LOCKED_CONTINUATION_vNEXT_PLUS31.md`).
5. Execute small-green PR sequence and close out with stop-gate decision note.

## Proposed Freeze Candidate (Next Step)

Finalize `docs/LOCKED_CONTINUATION_vNEXT_PLUS31.md` for selected `B31-AB` (default) unless reprioritized:

1. Freeze deterministic contract deltas for selected v31 scope.
2. Preserve v14-v30 continuity locks unless explicit release is approved.
3. Keep non-enforcement/no-mutation/no-provider-expansion boundaries explicit.
4. Include closeout consistency guard clause (`V31-B`) and explicit template-path interpretation clause (`V31-A`) in the lock text.
