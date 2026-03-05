# Assessment vNext+46 Edges (V33-C Draft)

This document records pre-implementation edge analysis for `vNext+46` (`V33-C` deterministic auditor/verifier + evidence writer).

Status: draft assessment (March 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS46_EDGES.md",
  "phase": "draft_assessment",
  "authoritative": true,
  "authoritative_scope": "v46_planning_edge_analysis",
  "required_in_closeout": true,
  "notes": "Pre-implementation edge assessment for V33-C scope and fail-closed planning posture."
}
```

## Scope

- In scope: `V33-C` verifier/evidence implementation (`U1`) and determinism/fail-closed guard suite (`U2`).
- Out of scope: `V33-D` packaging lane, stop-gate metric-key expansion, schema-family changes, and runtime/provider/proposer boundary changes.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS45.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
- `packages/adeu_agent_harness/tests/test_taskpack_runner.py`
- `apps/api/scripts/lint_closeout_consistency.py`
- `artifacts/quality_dashboard_v45_closeout.json`
- `artifacts/stop_gate/metrics_v45_closeout.json`
- `artifacts/stop_gate/report_v45_closeout.md`

## Draft Edge Set (V33-C)

1. Verifier-input authority drift risk (non-artifact input accepted as authority).
2. Verifier input schema drift risk across runner result/provenance/candidate plan artifacts.
3. Cross-artifact hash mismatch acceptance risk.
4. Verification-no-bypass failure risk (evidence emitted despite failed verification).
5. Verifier policy-validation recomputation scope-creep risk (auditor lane violating v46 boundary).
6. Evidence-schema allowlist drift risk (writer emits non-allowlisted schemas).
7. Evidence bundle hash-subject drift risk across implementations.
8. Diagnostics code namespace/registry drift risk in verifier lane.
9. Diagnostics `policy_source` freeform drift risk (non-enum payloads reducing machine-joinability).
10. Required-evidence-slot missing or malformed acceptance risk.
11. Evidence payload ordering/hash nondeterminism risk.
12. Rejection-diagnostic missing or unstable ordering risk.
13. Required violation severity downgrade risk (error reclassified as warning).
14. Stop-gate keyset/cardinality continuity regression risk.
15. Harness kernel import-boundary regression risk (`apps/api` leakage).
16. Deterministic env contract drift risk in verification/evidence commands.
17. Dual-entrypoint orchestration drift risk (evidence writer invoked independently without prior verified-result artifact).
18. Arc-scoped diagnostic prefix drift risk (`AHK46xx`) from parent namespace contract (`AHK[0-9]{4}`).

## Planned Guardrail Strategy

- Freeze verifier authority to canonical artifacts only; reject natural-language authority inputs fail closed.
- Freeze verifier role to auditor-only behavior; policy validation recomputation is forbidden in v46.
- Freeze dual-entrypoint control flow:
  - default path is deterministic `verify -> evidence_write`,
  - independent evidence-writer reruns are allowed only with prior verified-result artifact.
- Enforce strict schema/version checks for runner output and provenance artifacts.
- Require deterministic cross-hash checks before evidence write path is reachable.
- Enforce cross-hash semantics as recomputation from canonical artifact payloads (recorded hash strings alone are non-authoritative).
- Couple evidence emission to verifier pass state via single no-bypass gate (no partial closeout blocks on verification failure).
- Enforce evidence-slot authority from `EVIDENCE_SLOTS.json` only with required-slot completeness checks.
- Enforce writable evidence schema allowlist to v46 closeout block set only.
- Freeze `evidence_bundle_hash` subject definition and ordering semantics.
- Enforce canonical JSON serialization (`canonical_json`) for each evidence block and each rejection diagnostic before bundle-hash subject assembly.
- Emit deterministic structured rejection diagnostics with stable key ordering.
- Enforce verifier diagnostics code namespace/prefix and authoritative code registry use.
- Enforce explicit `AHK46xx` subset mapping under global `AHK[0-9]{4}` namespace.
- Enforce `policy_source` closed-enum typing in verifier rejection diagnostics for machine-joinable downstream evidence analysis.
- Enforce required-violation error channel (non-zero exit) without warning downgrade.
- Preserve stop-gate continuity (`stop_gate_metrics@1`, exact keyset equality, cardinality `80` computed from `metrics` keys).

## Planned Validation Signals for Closeout

- deterministic verifier output rerun parity:
  - `artifacts/agent_harness/v46/verification/closeout_verify_result_run1.json`
  - `artifacts/agent_harness/v46/verification/closeout_verify_result_run2.json`
- deterministic evidence bundle hash parity:
  - `artifacts/agent_harness/v46/evidence/closeout_evidence_bundle.json`
  - `artifacts/agent_harness/v46/evidence/closeout_evidence_bundle.sha256`
- verification-failure no-evidence emission invariant:
  - failed verify fixture emits no closeout blocks under `artifacts/agent_harness/v46/evidence` (rejection diagnostics only)
- deterministic provenance parity:
  - `artifacts/agent_harness/v46/evidence/provenance/closeout_verifier_provenance.json`
- stop-gate continuity evidence:
  - `artifacts/quality_dashboard_v46_closeout.json`
  - `artifacts/stop_gate/metrics_v46_closeout.json`
  - `artifacts/stop_gate/report_v46_closeout.md`

## Residual Risks (Pre-Implementation)

1. Adapter evolution can silently alter verifier semantics if adapter-boundary contracts are not kept strict.
2. v46 verifier is auditor-only and does not independently recompute policy validation; a compromised runner that emits internally consistent but incorrect policy results remains a deferred trust-model risk.
3. Runtime-observability comparison remains informational-only unless future lock text converts it to thresholded gating.

## Feedback Disposition (Gemini)

1. Independent policy recomputation in verifier: deferred (non-v46) to preserve frozen v46 scope and avoid runner-policy-engine duplication in this arc.
2. Canonical JSON bundle-hash input enforcement: accepted and locked in v46 contract text.
3. Rejection-diagnostic retry-context feeder: deferred follow-on candidate (non-v46).
4. Multi-party attested verifier execution: deferred follow-on candidate (non-v46).

## Feedback Disposition (Opus)

1. Dual-entrypoint sequencing ambiguity: accepted and locked with deterministic default `verify -> evidence_write`, plus guarded independent rerun semantics.
2. Transitional trust model risk: accepted as explicit v46 tradeoff; independent zero-trust recompute remains deferred to non-v46 lock.
3. AHK46 namespace mapping ambiguity: accepted and locked as `AHK46xx` subset of global `AHK[0-9]{4}` with registry authority.

## Follow-on Recommendation

1. Implement `U1` first with strict no-bypass verification-to-evidence control flow and deterministic provenance subject.
2. Implement `U2` immediately after `U1` with explicit fail-closed tests for each locked condition.
3. Keep all v46 closeout regeneration commands under frozen deterministic env contract (`TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`).
