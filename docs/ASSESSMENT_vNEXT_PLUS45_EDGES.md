# Assessment vNext+45 Edges (V33-B Post-Hoc)

This document records post-implementation edge analysis for `vNext+45` (`V33-B` constrained runner + deterministic fail-closed guard suite).

Status: post-hoc assessment (March 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS45_EDGES.md",
  "phase": "post_hoc_assessment",
  "authoritative": true,
  "authoritative_scope": "v45_closeout_edge_analysis",
  "required_in_closeout": true,
  "notes": "Post-hoc assessment refreshed against merged v45 implementation and closeout artifacts."
}
```

## Scope

- In scope: `V33-B` constrained runner implementation (`T1`) and determinism/fail-closed guard suite (`T2`).
- Out of scope: `V33-C` auditor/evidence-writer lane, `V33-D` packaging lane, stop-gate metric-key expansion, and runtime/provider/proposer boundary changes.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md`
- PR `#238` (`contracts: add V33-B constrained taskpack runner + candidate-change-plan policy validation`)
- PR `#239` (`tests: add v45 runner determinism and fail-closed guard suite`)
- `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
- `packages/adeu_agent_harness/tests/test_taskpack_runner.py`
- `artifacts/quality_dashboard_v45_closeout.json`
- `artifacts/stop_gate/metrics_v45_closeout.json`
- `artifacts/stop_gate/report_v45_closeout.md`
- `artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json`
- `artifacts/agent_harness/v45/candidate_change_plan_closeout.json`
- `artifacts/agent_harness/v45/closeout_runner_result_run1.json`
- `artifacts/agent_harness/v45/closeout_runner_result_run2.json`

## Post-Hoc Edge Set (V33-B)

1. Taskpack authority bypass risk.
2. Adapter-registry schema/order/uniqueness drift risk.
3. Non-exact adapter-id matching risk.
4. Candidate-plan schema/canonicalization drift risk.
5. Candidate-plan AST malformed/overlap risk.
6. Candidate-plan apply/validate divergence risk.
7. Pre-write no-bypass failure risk under exception paths.
8. COMMANDS authority bypass risk.
9. Dry-run subprocess/network side-effect risk.
10. Dry-run guard initialization failure risk.
11. Rejection-diagnostic missing/malformed ordering drift risk.
12. Provenance hash-subject nondeterminism risk.
13. Stop-gate continuity/keyset regression risk.

## Guardrail Evaluation (Observed)

- Taskpack component and manifest integrity lock: pass.
  - runner verifies bundle via `verify_taskpack_bundle(...)` before policy/apply execution.
- Adapter-registry lock: pass.
  - schema/entry grammar, uniqueness, and lexicographic `adapter_id` ordering are enforced fail-closed (`AHK1003`/`AHK1005`/`AHK1007`).
- Exact adapter-id match lock: pass.
  - adapter resolution uses exact case-sensitive equality and rejects unknown id (`AHK1006`).
- Candidate-plan canonicalization + ordering lock: pass.
  - canonical payload hash and deterministic `file_operations` ordering stability are covered by runner tests.
- Candidate-plan AST coupling lock: pass.
  - malformed/overlapping hunk structures fail closed (`AHK1017`); apply path consumes parsed canonical AST only.
- Pre-write no-bypass lock: pass.
  - policy validation executes before apply/commands; forced pre-apply exception path confirms no command execution bypass.
- Command-authority lock: pass.
  - undeclared/model-suggested commands fail closed; interception unavailability fails closed (`AHK1011`).
- Dry-run lock: pass.
  - dry-run forbids subprocess execution and outbound socket/HTTP calls, with explicit guard initialization and fail-closed behavior (`AHK1012`/`AHK1015`).
- Rejection diagnostics lock: pass.
  - policy failures emit deterministic structured diagnostics with stable `(issue_code, target_path, hunk_index)` ordering.
- Provenance hash-subject lock: pass.
  - deterministic provenance excludes nondeterministic fields and validates stored `provenance_hash` round-trip.
- Continuity lock: pass.
  - stop-gate schema family remains `stop_gate_metrics@1`; v44-v45 metric keysets are exact-set equal with cardinality `80`.

## Coverage Snapshot

- v45 runner guard file covers 19 deterministic/fail-closed cases.
- v44/v45 compiler guard file remains green at 20 deterministic/fail-closed cases.
- Closeout verification run executed `39` tests total across:
  - `packages/adeu_agent_harness/tests/test_taskpack_runner.py`
  - `packages/adeu_agent_harness/tests/test_taskpack_compile.py`

## Known Limits (Accepted in v45)

- Auditor/verifier/evidence-writer release remains deferred to `V33-C`.
- Integrated/standalone UX packaging release remains deferred to `V33-D`.
- Semantic-inference forbidden-effect lane remains deferred; v45 keeps closed-enum forbidden operation kinds only.
- Stop-gate metric-key set remains frozen; no key expansion was introduced.

## Residual Risks

1. Future adapter kinds can re-open authority boundaries if registry semantics are loosened.
2. Cross-adapter parity checks are deferred; deterministic behavior remains validated on the currently released adapter kind.
3. Runtime-observability deltas remain informational unless a later arc introduces threshold enforcement.

## Follow-on Recommendation

1. Start `vNext+46` planning for `V33-C` with explicit lock text for deterministic auditor/verifier and evidence-writer artifacts.
2. Preserve v45 runner closeout artifacts as baseline fixtures for adapter-parity work.
3. Keep v45 deterministic env contract (`TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`) mandatory for all closeout regeneration paths.
