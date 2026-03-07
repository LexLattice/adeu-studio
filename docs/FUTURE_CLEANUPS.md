# Future Cleanups and Open Edges

This tracker is the current-state cleanup and open-edge view for the repo.

It supersedes the older mixed backlog format. The goal is to keep only items that are
still open in the current implementation, or still intentionally deferred as explicit
future-path work.

## Audit Basis

This rewrite was produced by auditing:

- `docs/ASSESSMENT_vNEXT_PLUS34_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS35_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS37_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS38_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS39_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS40_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS41_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS42_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS43_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS44_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS45_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS46_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS47_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS49_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS50_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS51_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS53_EDGES.md`
- the prior version of this file
- current implementation under `apps/` and `packages/`

Notes:

- `docs/ASSESSMENT_vNEXT_PLUS36_EDGES.md` is not present in the repository, so there was
  no v36 assessment file to audit directly.
- Many edge docs in this range are historical or post-closeout and no longer describe
  active blocking issues. This file tracks only the still-open residue.

## 1. Active Open Edges

### 1.1 P1: Trust-Boundary and Correctness Gaps

- `EDGE-P1-01` logic-tree cycle handling is still sentinel-based rather than fail-closed.
  - Source: prior `FUTURE_CLEANUPS.md`
  - Current evidence:
    - `_core_ir_proposer_logic_tree_max_depth` in
      `apps/api/src/adeu_api/main.py` returns `1` when revisiting a node.
  - Why it is still open:
    - cycle presence is collapsed into a depth value instead of being surfaced as a
      policy/contract decision.
  - Next action:
    - either freeze the current sentinel behavior explicitly, or add a fail-closed cycle
      policy under future lock text.

### 1.2 P2: Governance and Operational Hardening

- `EDGE-P2-01` runtime observability is still informational-only.
  - Source:
    - `docs/ASSESSMENT_vNEXT_PLUS43_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS44_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS45_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS46_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS47_EDGES.md`
  - Current evidence:
    - closeout decision docs in this family continue to state that
      `runtime_observability_comparison@1` is required evidence but non-gating.
  - Why it is still open:
    - runtime regressions are visible, but not promoted to pass/fail policy.
  - Next action:
    - either keep this explicitly non-gating, or introduce bounded thresholds in a future
      lock rather than leaving it implicit.

- `EDGE-P2-02` closeout artifact regeneration and command hygiene still depend on operator discipline.
  - Source:
    - `docs/ASSESSMENT_vNEXT_PLUS43_EDGES.md`
    - prior `FUTURE_CLEANUPS.md`
  - Current evidence:
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS46.md` and
      `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS47.md` still embed long inline `python -c`
      commands.
  - Why it is still open:
    - stale artifacts and inline-script drift remain possible even under deterministic env
      requirements.
  - Next action:
    - extract closeout helper scripts into `apps/api/scripts/` and lint for oversized
      embedded commands in future decision docs.

- `EDGE-P2-03` signing verification is portable only where `openssl` CLI behavior matches the frozen contract.
  - Source: `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md`
  - Current evidence:
    - `_verify_with_openssl(...)` in
      `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`
    - emitted verifier field `verification_library = "openssl_cli"`
    - signing tests skip when `openssl` is unavailable.
  - Why it is still open:
    - the current v48 trust lane is deterministic, but its portability and provider
      behavior are pinned to one CLI toolchain.
  - Next action:
    - either explicitly pin and document the required OpenSSL contract more tightly, or
      add a deterministic library-backed verifier under future lock text.

- `EDGE-P2-04` policy CLI strictness defaults are inconsistent.
  - Source: prior `FUTURE_CLEANUPS.md`
  - Current evidence:
    - `policy validate` exposes opt-in `--strict`
    - `policy eval`, `policy explain`, `policy diff`, and `policy materialize` default to
      strict mode and expose `--lax`
    - implementation lives in `packages/urm_runtime/src/urm_runtime/policy_tools.py`
  - Why it is still open:
    - CLI behavior is harder to reason about and easier to misuse across subcommands.
  - Next action:
    - align defaults and keep explicit compatibility flags where needed.

### 1.3 P3: Maintainability Backlog With Ongoing Value

- `EDGE-P3-01` shared validation logic is still duplicated across older tooling paths.
  - Source: prior `FUTURE_CLEANUPS.md`
  - Current evidence:
    - the old tracker item for shared extraction between
      `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
      and
      `apps/api/src/adeu_api/integrity_transfer_report_vnext_plus16.py`
      has not been retired by later lock docs.
  - Why it is still open:
    - this is mainly maintenance drift risk, not a current correctness break.
  - Next action:
    - extract shared runtime-owned helpers only if those older tool paths still need active
      maintenance.

- `EDGE-P3-02` read-surface guard scaffolding remains repetitive.
  - Source: prior `FUTURE_CLEANUPS.md`
  - Current evidence:
    - the repo still carries many family-specific guard harness tests rather than one shared
      helper layer.
  - Why it is still open:
    - maintenance cost is higher than necessary, but this is not a release-blocking issue.
  - Next action:
    - consolidate common guard-test helper patterns when that area is touched next.

- `EDGE-P3-03` legacy core-IR proposer cache residue still exists after the persistence release.
  - Source:
    - `docs/ASSESSMENT_vNEXT_PLUS37_EDGES.md`
    - current audit
  - Current evidence:
    - `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` still exists in
      `apps/api/src/adeu_api/main.py`
    - the live `/urm/core-ir/propose` endpoint now uses
      `get_core_ir_proposer_idempotency_by_client_request_id(...)` and
      `create_core_ir_proposer_idempotency_if_absent(...)`
    - several tests still clear or mutate the old in-memory symbol.
  - Why it is still open:
    - the runtime authority path is persisted, but the leftover cache symbol makes the
      authority model look less clear than it really is.
  - Next action:
    - remove or quarantine the legacy cache symbol and trim tests that still treat it as a
      meaningful surface unless it is intentionally retained as a non-authoritative sentinel.

## 2. Explicitly Deferred Follow-On Paths

These are intentionally deferred capabilities, not regressions. They remain open only in
the sense that the roadmap still names them and current code does not implement them.

### 2.1 Harness and Trust Roadmap

- broader policy recomputation beyond the current runner validator and verifier-lane
  comparison
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS46_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS47_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS51_EDGES.md`
- cross-adapter and matrix-lane parity beyond current released adapter/mode sets
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS45_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS47_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS50_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- verifier/package rejection-diagnostic aggregation beyond the current runner surface
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- automatic retry prompt assembly or execution orchestration
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- richer retry-context excerpt families beyond rejection diagnostics and canonical
  candidate-plan hunks
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- live provider adapters beyond the frozen singleton test-provider surface
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS53_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- network transport and remote job dispatch for attested verifier lanes
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS53_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- attested verifier ingestion without exact local-equivalence fallback
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS53_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- additive trust-anchor registry extension only if the existing V34-A registry contract
  proves insufficient
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS53_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- multi-signer or quorum signature policy
  - Source:
    - `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md`

### 2.2 Semantic Compiler and CI Depth

- compiler partial-run ergonomics such as `--stop-after` and intermediate IR dumps
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS40_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- resolver namespace aliasing and workspace-scoped bindings
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS40_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS41_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS42_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- semantic-equivalency and deep-path keyset semantics for structured surfaces
  - Sources:
    - `docs/ASSESSMENT_vNEXT_PLUS41_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS42_EDGES.md`
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- optional cross-OS required-check or coverage-signature matrix validation
  - Source:
    - `docs/ASSESSMENT_vNEXT_PLUS42_EDGES.md`

## 3. Archived Low-Priority Legacy Evaluations

These items came from the prior cleanup tracker, but the v34-v48 audit does not support
keeping them as active current-state edges. They are not closed by proof, but they should
not compete with the active backlog unless a future lock or incident revives them.

- integrity-diagnostics schema-family consolidation evaluation
  - old theme:
    - unify older integrity packet families under one discriminator-driven schema
  - current status:
    - archived unless a new lock explicitly reopens that contract family

- integrity drift-error granularity expansion
  - old theme:
    - split older shared drift codes into per-family codes
  - current status:
    - archived unless debugging signal proves insufficient in production

- D-lane cycle expansion and condition-alias policy review
  - old theme:
    - expand older integrity cycle semantics and revisit normalized condition aliases
  - current status:
    - archived as semantic-evolution work, not a current implementation edge

- hostile fixture generation and additive diagnostic-delta tracking
  - old theme:
    - broaden deterministic adversarial coverage and delta triage tooling
  - current status:
    - archived as optional hardening work

- provider telemetry capture, parity topology strengthening, and surface-id naming normalization
  - old theme:
    - older proposer-family observability and naming improvements from the v25 era
  - current status:
    - archived unless that proposer family becomes the active frontier again

- stop-gate registry externalization and generic transfer-report pipeline
  - old theme:
    - external consumer support and multi-arc pipeline consolidation
  - current status:
    - archived as strategic tooling work, not current edge closure

## 4. Items Retired or Superseded by Current Repo State

These older tracker items were removed from the active backlog because the current repo
state no longer supports them as open work items.

- `cleanup-copilot-child-queue-method-extraction`
  - retired: `URMCopilotManager` now delegates `_run_child_workflow_v2` and
    `_spawn_child_v2` through extracted implementation helpers in
    `packages/urm_runtime/src/urm_runtime/copilot.py`.

- v42-v48 follow-on slices that were deferred in earlier assessments and later shipped
  - retired from the cleanup tracker:
    - v42 deferred stop-gate metric-key extension was realized in v43
    - v44 deferred runner work was realized in v45
    - v45 deferred verifier/evidence work was realized in v46
    - v46 deferred packaging work was realized in v47
    - v47 deferred signing/trust-anchor work was realized in v48
    - v37 persistence release was realized; only cache-residue cleanup remains

- old speculative or arc-local naming/finalization items that are no longer useful as
  current-state tracker entries
  - examples:
    - v25 metric-key finalization naming cleanup
    - tiny test-only cache micro-optimization items
    - already-closed planning-rollover bookkeeping tied to older arc drafts

## 5. Summary

After auditing `v34` through `v48`, the repo does not appear to have an unresolved
historical blocking edge carried directly from those assessment docs. What remains is a
smaller set of current-state issues:

- one real v48 trust-boundary adoption gap,
- one cycle-policy ambiguity in proposer summary handling,
- one weak continuity sentinel test,
- several governance and portability hardening items,
- and a separate bucket of intentionally deferred future-path work.

That is the set this tracker should carry forward.
