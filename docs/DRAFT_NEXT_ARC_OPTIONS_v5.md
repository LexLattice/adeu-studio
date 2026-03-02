# Draft Next Arc Options v5 (Post vNext+32)

This document is the fresh consolidated planning baseline for post-`vNext+32` sequencing.

Status: active planning draft (v17 through v32 baselines executed; active for `vNext+33+` selection).
Goal: define thin-slice, lock-respecting candidate paths for `vNext+33` and onward, while preserving the standard multi-implementation review sequence before lock freeze.

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
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS31.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS32.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS27.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS28.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md`
- archived GPT Pro snapshot inputs:
  - `docs/archives/next_arc_options_v5/DRAFT_NEXT_ARC_OPTIONS_v5_gpt_pro_snapshot.md`
  - `docs/archives/next_arc_options_v5/REVIEW_v5_gpt_pro_snapshot.md`

This is a planning document only. It is not a lock doc and does not authorize runtime behavior changes.

## Baseline Agreement (Current Ground Truth)

- Locked continuation implementation baseline is `vNext+32` (`V31-D`, `F1`-`F2`) and is merged on `main`.
- Latest closeout decision remains `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md` (`vNext+32` closeout decision doc is pending).
- Stop-gate schema family remains `stop_gate_metrics@1`.
- v29 through v31 closeout artifacts are present and committed:
  - `artifacts/quality_dashboard_v29_closeout.json`
  - `artifacts/stop_gate/metrics_v29_closeout.json`
  - `artifacts/stop_gate/report_v29_closeout.md`
  - `artifacts/quality_dashboard_v30_closeout.json`
  - `artifacts/stop_gate/metrics_v30_closeout.json`
  - `artifacts/stop_gate/report_v30_closeout.md`
  - `artifacts/quality_dashboard_v31_closeout.json`
  - `artifacts/stop_gate/metrics_v31_closeout.json`
  - `artifacts/stop_gate/report_v31_closeout.md`

## Lock Class Semantics (Operational)

- `L0`: internal hardening/tooling/guard-rail work with no externally visible contract change.
- `L1`: externally visible contract closure/behavior change on an existing surface (API/web/CLI/artifact contract), without boundary release.
- `L2`: boundary release (governance authority, persistence authority, provider/proposer surface expansion).

## v32 Completion Checkpoint

- `V31-D` is complete on `main` via `F1` and `F2`:
  - PR `#210` (`F1`) and PR `#211` (`F2`) merged with green CI.
- `vNext+32` closeout decision doc remains pending.
- Planning default now advances to `vNext+33` candidate selection.

## Confirmed Post-v32 Remaining Gaps (Worth Addressing)

1. `/urm/worker/run` and `/urm/worker/{worker_id}/cancel` are not policy-gated via `authorize_action`.
   - evidence anchors:
     - `apps/api/src/adeu_api/urm_routes.py` (`@router.post("/worker/run")`, `@router.post("/worker/{worker_id}/cancel")`)
2. Worker CLI handling is compatibility-first, not fail-closed, when `--ask-for-approval` is unsupported.
   - evidence anchors:
     - `packages/urm_runtime/src/urm_runtime/worker.py` (`_supports_exec_flag`, conditional `include_ask_for_approval_flag`)
3. Proposer idempotency remains process-local in-memory cache for one API path.
   - evidence anchor:
     - `apps/api/src/adeu_api/main.py` (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`)

## Gap-to-Path Mapping (Total)

- Gap 1 -> `V31-F`
- Gap 2 -> `V31-E`
- Gap 3 -> `V31-G`

## Consolidated Path Families (v33+ Candidate Menu)

### Path V31-A: Evidence Explorer Contract Closure

Lock class: `L1`

Goal:
- Align web contract validation with the frozen API catalog contract so v29 explorer surface is operational.

Scope:
- Freeze contract interpretation: `families[].list_ref.path` is a URI template string using literal `{family}` placeholder.
- Freeze authoritative family enum for this path to exactly:
  - `read_surface`
  - `normative_advice`
  - `proof_trust`
  - `semantics_v4_candidate`
  - `extraction_fidelity`
- Authoritative enum source for this path is API-side `_EVIDENCE_EXPLORER_FAMILIES`; web-side family typing must be value-identical to that frozen set.
- Update web validator/expander to support the frozen template form deterministically.
- Expansion authority boundary is frozen:
  - API continues returning template form only;
  - frontend performs expansion for request dispatch;
  - dual-contract acceptance (`{family}` and pre-expanded forms) is out-of-scope for this path.
- Expansion rules are frozen:
  - accept only frozen family enum values as expansion inputs;
  - replace exact substring `{family}` only;
  - fail closed if placeholder is missing or appears more than once;
  - fail closed if template contains any placeholder token other than exact `{family}`;
  - URL-encode expanded family token before insertion;
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
- Parse referenced JSON artifacts and fail closed on invalid JSON.
- Validate referenced stop-gate metrics artifacts have `schema == "stop_gate_metrics@1"`.
- Validate declared metric-key continuity claims against referenced metrics artifacts.
- Normalize v29/v30 closeout docs by adding the frozen continuity-assertion block (same content, machine-checkable form) so current baseline docs remain guard-compatible.
- Metric-key continuity claim extraction grammar is frozen:
  - claim source is one fenced JSON block under heading `## Metric-Key Continuity Assertion`;
  - required block schema is docs-only `metric_key_continuity_assertion@1`;
  - required keys:
    - `schema`
    - `baseline_metrics_path`
    - `current_metrics_path`
    - `expected_relation`
  - allowed `expected_relation` value in this path:
    - `exact_keyset_equality`
  - this grammar is docs-validation-only and is not a runtime/public schema-family addition.

Locks:
- No new stop-gate metric keys.
- No schema-family changes.

Acceptance:
- Guard fails closed on missing referenced artifact paths.
- Guard fails closed when required continuity-assertion block is missing or schema-invalid.
- Guard passes on current v29/v30 closeout chain.

### Path V31-C: Formal ODEU Template Activation v0.2 (Evidence-Only)

Lock class: `L1`

Goal:
- Start a deterministic artifact-to-Lean proof-packet flow for core contract checks without enforcement release.
- Lock-class rationale:
  - path is treated as `L1` because it introduces a new committed proof-packet evidence contract surface (artifact schema/shape), even while runtime enforcement remains unchanged.

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
- Consolidate script/test/runtime root discovery to one canonical helper path.
- Preferred canonical helper: `packages/adeu_ir/src/adeu_ir/repo.py` (`repo_root`), with consistent marker fallback behavior and env override support.
- Root-resolution precedence is frozen:
  - `ADEU_REPO_ROOT` when set and valid,
  - otherwise nearest ancestor satisfying `pyproject.toml` + `packages/`,
  - otherwise nearest ancestor containing `.git/`,
  - otherwise fail closed.
- Marker disagreement behavior is frozen:
  - if `ADEU_REPO_ROOT` is set but does not satisfy required markers, fail closed;
  - no silent fallback away from an explicitly configured env root.
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
- Freeze worker CLI safety policy to fail-closed:
  - when execution requires `--ask-for-approval` and support probe reports unsupported, worker run fails deterministically before spawn.
- Freeze support-detection mechanism to explicit `codex exec --help` flag probing via `_supports_exec_flag`.
- Compatibility-mode fallback for unsupported required flags is out-of-scope for this path.
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
- Remove process-local proposer idempotency memory cache in the same boundary-release slice (no dual-source operation).

Locks:
- Requires explicit boundary-release lock text.
- Lock text must define one source of truth for idempotency state during and after migration.

Acceptance:
- Multi-process behavior is deterministic and conflict-safe.

## L2 Precondition Hygiene (Invariant)

- No `L2` path is selectable until a dedicated boundary lock doc enumerates:
  - newly authorized surface(s),
  - persistence-authority change(s),
  - rollback and deterministic denial semantics.
- `L2` scaffolding prohibition is frozen:
  - no partial implementation of `L2` authority/persistence surfaces may land under `L0/L1` arcs prior to boundary lock approval.

## Decision Matrix (Thin-slice Selection)

| Option ID | Includes | Max lock class | Status | Benefit | Risk |
|---|---|---:|---|---|---|
| `V31-A` | `V31-A` | `L1` | closed in v31 | Restored v29 explorer usability | low |
| `V31-B` | `V31-B` | `L0` | closed in v31 | Added closeout drift guard rail | low |
| `B31-AB` | `V31-A + V31-B` | `L1` | closed in v31 | Product + operational hardening together | low/med |
| `V31-C` | `V31-C` | `L1` | candidate | Extends formal lane evidence value | med/high |
| `V31-D` | `V31-D` | `L0` | closed in v32 | Consolidated repo-root resolution and added determinism guards | low |
| `V31-E` | `V31-E` | `L1` | candidate | Clarifies worker safety policy | med |
| `V31-F` | `V31-F` | `L2` | deferred boundary | Closes governance gap | high |
| `V31-G` | `V31-G` | `L2` | deferred boundary | Closes proposer idempotency boundary | high |

## Recommended Sequencing (Default)

1. `vNext+33`: `V31-C` (formal lane evidence) or `V31-E` (worker CLI safety), based on active velocity blocker.
2. `vNext+34`: complete whichever of `V31-C`/`V31-E` remains.
3. `vNext+35+`: evaluate `L2` releases (`V31-F`, `V31-G`) only via explicit boundary lock.

## Standard Multi-Implementation Sequence (Required)

For each selected arc candidate (starting with `vNext+33`):

1. Draft parallel implementation briefs for multiple implementers (`codex`, `gpt`, `gemini`, `opus`) with identical locks/acceptance.
2. Run independent implementations and collect deterministic evidence bundles.
3. Produce comparative assessment (risk, lock adherence, determinism evidence, CI impact).
4. Consolidate into one lock candidate (next default: `docs/LOCKED_CONTINUATION_vNEXT_PLUS33.md`).
5. Execute small-green PR sequence and close out with stop-gate decision note.

## Proposed Freeze Candidate (Next Step)

Finalize `docs/LOCKED_CONTINUATION_vNEXT_PLUS33.md` for selected post-v32 candidate (`V31-C` or `V31-E` by priority) unless reprioritized:

1. Freeze deterministic contract deltas for selected v33 scope.
2. Preserve v14-v32 continuity locks unless explicit release is approved.
3. Keep non-enforcement/no-mutation/no-provider-expansion boundaries explicit.
4. Preserve v31 continuity clauses for template-path contract closure (`V31-A`) and closeout consistency lint guards (`V31-B`), plus v32 repo-root consolidation continuity (`V31-D`).
