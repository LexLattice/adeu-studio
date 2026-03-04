# Assessment vNext+45 Edges (V33-B Draft)

This document captures draft edge analysis for `vNext+45` (`V33-B` constrained runner path).

Status: draft assessment (pre-implementation, March 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS45_EDGES.md",
  "phase": "draft_assessment",
  "authoritative": false,
  "required_in_freeze_review": true,
  "required_in_closeout": true,
  "notes": "Draft edge set for V33-B planning/freeze review before implementation."
}
```

## Scope

- In scope: `V33-B` planning (`T1` constrained runner wiring, `T2` determinism/fail-closed guard design).
- Out of scope: `V33-C` auditor/evidence-writer lane, `V33-D` packaging lane, stop-gate metric expansion, and runtime/provider/proposer boundary changes.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS44.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS44.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/compile.py`
- `packages/adeu_agent_harness/tests/test_taskpack_compile.py`

## Draft Edge Set (V33-B)

1. Taskpack authority bypass risk (runner accepts undeclared/mutated taskpack components).
2. Candidate-change-plan ambiguity risk (policy checks free-form prose instead of canonical artifact/AST).
3. Pre-write validation ordering risk (workspace mutations occur before policy validation).
4. Validation/apply divergence risk (validator approves canonicalized plan but patcher applies raw/fuzzy diff).
5. Candidate-plan file-operation ordering drift risk (canonicalizers disagree on deterministic ordering).
6. Allowlist drift risk (path normalization or glob semantics diverge between compiler and runner).
7. Forbidden-effect under-detection risk (runner must enforce forbidden touches/operation kinds explicitly in v45 scope).
8. Forbidden-operation-kind enum drift risk (closed enum behavior drifts into open/custom values).
9. Adapter-boundary coupling risk (`packages/adeu_agent_harness` directly imports `apps/api` runtime modules).
10. Adapter-resolution ambiguity risk (missing/malformed registry or ambiguous/unknown adapter selection).
11. Adapter-match looseness risk (prefix/partial/case-insensitive matching bypasses exact id lock).
12. Dry-run determinism-domain drift risk (determinism claims become invalid if dry-run invokes model generation).
13. Dry-run network-guard scope leak risk (subprocesses bypass Python-level HTTP/socket patching).
14. Command-authority bypass risk (runner executes model-suggested or undeclared commands).
15. Rejection-diagnostics opacity risk (policy failures lack structured path/hunk diagnostics for remediation loops).
16. Rejection-diagnostics ordering drift risk (`hunk_index` tie-break not deterministic).
17. Provenance incompleteness risk (missing manifest hash, adapter id, or candidate plan hash).
18. Severity downgrade risk (required policy failures emitted as warning-only outcomes).
19. Continuity regression risk (v36-v44 frozen suites regress while adding runner surface).

## Planning Guardrail Evaluation (Expected)

- Authority model clarity: pass (taskpack-driven authority, non-authoritative repo prose/model claims).
- Candidate-plan canonicalization requirement: pass in lock intent; implementation verifier required in `T2`.
- Candidate-plan AST coupling requirement: pass in lock intent; validator/apply same-AST proof required in `T2`.
- Candidate-plan file-operation ordering requirement: pass in lock intent; ordering determinism proof required in `T2`.
- Pre-write fail-closed requirement: pass in lock intent; no-bypass control-flow proof required in `T2`.
- Adapter boundary portability requirement: pass in lock intent; exact-match adapter-registry selection and import-boundary tests required in `T2`.
- Dry-run determinism and side-effect prohibition: pass in lock intent (model-free dry-run, no subprocess execution, no outbound network, no workspace mutation outside preview root except preview-root directory creation/file writes); network-guard initialization and deterministic artifact checks required in `T2`.
- Stop-gate continuity posture: pass (schema family `stop_gate_metrics@1`, keyset/cardinality frozen `80`).

## Recommended Hardening Focus (v45)

1. Freeze canonical candidate-change-plan schema and normalization rules in code and tests before adapter integration.
2. Enforce canonical candidate-plan `file_operations` ordering (`path`, then `operation_kind`) and fail closed on ordering drift.
3. Enforce validator/apply coupling to the same canonical AST and prohibit raw/fuzzy patch-application paths.
4. Enforce deterministic pre-write policy-validation ordering via explicit state-machine checks with exception-path no-bypass coverage.
5. Add adapter-registry/adapter-resolution tests for missing, malformed, ambiguous, and unknown adapter id outcomes.
6. Add exact adapter-id match tests (case-sensitive equality; no prefix/partial matching).
7. Add static import-boundary guard test that fails if harness kernel imports `apps/api` directly.
8. Add dry-run negative tests proving model-invocation prohibition, subprocess-execution prohibition, no outbound network execution, and no workspace mutation outside preview root.
9. Require deterministic structured rejection-diagnostic artifacts for policy failures (path/hunk/line-range context) with integer-ascending `hunk_index` ordering.
10. Require command-authority enforcement tests (`COMMANDS.json` only; model-suggested/undeclared commands fail closed via subprocess interception).
11. Require deterministic provenance hash-subject tests that exclude non-deterministic fields.

## Residual Planning Risks

1. Runner adapters can reintroduce hidden authority channels if adapter interfaces or adapter registry contracts are underspecified.
2. Equivalent behavior across future integrated/standalone modes (`V33-D`) can drift if provenance schema is not fixed early.
3. Runtime observability deltas remain informational-only unless a later arc introduces explicit thresholds.
4. Cross-adapter deterministic matrix parity remains deferred; lock posture should keep adapter contracts strict ahead of v49 parity work.

## Follow-on Recommendation

1. Freeze `vNext+45` lock and planning decision bundle for `V33-B` (`T1`/`T2`) only.
2. Implement constrained runner and guard suite in two small green PRs with deterministic provenance artifacts.
3. Keep `V33-C`/`V33-D` deferred until v45 closeout confirms runner boundary integrity and continuity preservation.
