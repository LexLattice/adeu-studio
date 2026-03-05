# Assessment vNext+47 Edges (V33-D Draft)

This document records pre-implementation edge analysis for `vNext+47` (`V33-D` deterministic integrated + standalone UX surface packaging).

Status: draft assessment (March 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS47_EDGES.md",
  "phase": "draft_assessment",
  "authoritative": true,
  "authoritative_scope": "v47_planning_edge_analysis",
  "required_in_closeout": true,
  "notes": "Pre-implementation edge assessment for V33-D packaging scope and fail-closed planning posture."
}
```

## Scope

- In scope: `V33-D` integrated+standalone packaging implementation (`W1`) and determinism/policy-equivalence guard suite (`W2`).
- Out of scope: stop-gate metric-key expansion, schema-family changes, verifier trust-model expansion, and runtime/provider/proposer boundary changes.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS46.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
- `packages/adeu_agent_harness/tests/test_taskpack_verifier.py`
- `apps/api/scripts/lint_closeout_consistency.py`
- `artifacts/quality_dashboard_v46_closeout.json`
- `artifacts/stop_gate/metrics_v46_closeout.json`
- `artifacts/stop_gate/report_v46_closeout.md`

## Draft Edge Set (V33-D)

1. Packaging-authority drift risk (non-artifact input accepted as authority).
2. Deployment-mode selection drift risk (unknown/ambiguous/non-exact mode resolution allowed).
3. Mode-adapter policy-override risk (adapter redefining kernel policy semantics).
4. Integrated vs standalone canonical artifact parity drift risk.
5. Integrated vs standalone policy-equivalence drift risk.
6. Packaging manifest schema/ordering drift risk.
7. Pre-package validation no-bypass failure risk (emit path reachable after failed checks).
8. Rejection-diagnostic missing or unstable ordering risk.
9. Diagnostics namespace/registry drift risk (`AHK47xx` mapping drift).
10. Diagnostics `policy_source` freeform drift risk (non-enum payloads reducing machine-joinability).
11. Required violation severity downgrade risk (error reclassified as warning).
12. Harness kernel import-boundary regression risk (`apps/api` leakage).
13. Deterministic env contract drift risk in packaging commands.
14. Packaging provenance hash-subject nondeterminism risk.
15. Stop-gate keyset/cardinality continuity regression risk.
16. Runtime-observability comparison row omission/staleness risk in closeout evidence.

## Planned Guardrail Strategy

- Freeze packaging authority to canonical artifacts only; reject natural-language authority inputs fail closed.
- Freeze deployment-mode resolution to exact case-sensitive `deployment_mode` equality only.
- Freeze mode contract identity:
  - integrated and standalone modes must consume identical kernel contracts,
  - adapters cannot redefine policy semantics.
- Require deterministic pre-package validation gate before any packaging emission.
- Couple packaging emission to parity + policy-equivalence pass state via single no-bypass gate.
- Enforce strict schema/version checks for packaging manifest/provenance/diagnostic artifacts.
- Enforce deterministic cross-mode parity checks for canonical artifact subjects.
- Enforce deterministic policy-equivalence checks for frozen subject set:
  - `issue_code_set`,
  - `required_evidence_slots_filled`,
  - `allowlist_violations`,
  - `forbidden_effects_detected`.
- Emit deterministic structured rejection diagnostics with stable ordering.
- Enforce diagnostics code namespace/prefix and authoritative registry use.
- Enforce required-violation error channel (non-zero exit) without warning downgrade.
- Preserve stop-gate continuity (`stop_gate_metrics@1`, exact keyset equality, cardinality `80` computed from `metrics` keys).

## Planned Validation Signals for Closeout

- deterministic integrated/standalone packaging rerun parity:
  - `artifacts/agent_harness/v47/packaging/integrated/closeout_package_result_run1.json`
  - `artifacts/agent_harness/v47/packaging/integrated/closeout_package_result_run2.json`
  - `artifacts/agent_harness/v47/packaging/standalone/closeout_package_result_run1.json`
  - `artifacts/agent_harness/v47/packaging/standalone/closeout_package_result_run2.json`
- deterministic cross-mode artifact parity evidence:
  - `artifacts/agent_harness/v47/packaging/parity/closeout_artifact_parity.json`
- deterministic policy-equivalence evidence:
  - `artifacts/agent_harness/v47/packaging/parity/closeout_policy_equivalence.json`
- deterministic packaging provenance parity:
  - `artifacts/agent_harness/v47/packaging/provenance/closeout_packaging_provenance_integrated.json`
  - `artifacts/agent_harness/v47/packaging/provenance/closeout_packaging_provenance_standalone.json`
- stop-gate continuity evidence:
  - `artifacts/quality_dashboard_v47_closeout.json`
  - `artifacts/stop_gate/metrics_v47_closeout.json`
  - `artifacts/stop_gate/report_v47_closeout.md`

## Residual Risks (Pre-Implementation)

1. Mode-adapter drift can silently weaken parity guarantees if mode surfaces are allowed to diverge from kernel contracts.
2. Packaging parity checks can become too narrow if artifact subject list is reduced in implementation.
3. Runtime-observability comparison remains informational-only unless future lock text converts it to thresholded gating.

## Feedback Carryover (from v46 closeout)

1. Closeout command readability concerns (long inline script commands) remain a maintainability-only follow-up.
   - disposition: deferred to tracker item `cleanup-vnext-plus46-closeout-command-script-extraction`.
2. Transitional verifier trust model concerns remain deferred and out of v47 scope.
   - disposition: continue deferral to non-v47 lock text.

## Follow-on Recommendation

1. Implement `W1` first with strict mode-selection + no-bypass packaging validation gate wiring.
2. Implement `W2` immediately after `W1` with explicit parity/policy-equivalence fail-closed tests for each locked condition.
3. Keep all v47 closeout regeneration commands under frozen deterministic env contract (`TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`).
