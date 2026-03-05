# Assessment vNext+48 Edges (Post Closeout)

This document records edge disposition for `vNext+48` (`V34-A` deterministic signing + trust-anchor pre-flight hardening) after arc closeout.

Status: post-closeout assessment (March 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v48_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: `V34-A` signing/trust-anchor pre-flight implementation (`X1`) and guard-suite implementation (`X2`).
- Out of scope: `V34-B` through `V34-G`, stop-gate schema-family fork, metric-key expansion, and `L2` boundary release.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/_v48_signing_common.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`
- `packages/adeu_agent_harness/tests/test_taskpack_signature.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v48.json`
- `artifacts/quality_dashboard_v48_closeout.json`
- `artifacts/stop_gate/metrics_v48_closeout.json`
- `artifacts/agent_harness/v48/evidence_inputs/runtime_observability_comparison_v48.json`
- `artifacts/agent_harness/v48/evidence_inputs/metric_key_continuity_assertion_v48.json`
- `artifacts/agent_harness/v48/evidence_inputs/v34a_signing_wiring_evidence_v48.json`
- merged PRs: `#245`, `#246`

## Pre-Lock Edge Set Outcome (v48 Closeout)

1. Signature subject drift risk: `resolved`.
   - `taskpack_bundle_hash` enforced as signed subject; mismatches fail closed.
2. Trust-anchor split-brain risk: `resolved`.
   - single registry artifact input and strict schema/key constraints.
3. Algorithm downgrade risk: `resolved`.
   - exact key-id + algorithm binding checks enforced.
4. Single-signature scope creep risk: `resolved`.
   - envelope grammar is strict; multi-signature-shaped payloads fail closed.
5. Pre-flight verification bypass risk: `resolved` (for v48 lane scope).
   - downstream validator requires pre-flight artifact and binding checks.
6. Cross-component verification-policy drift risk: `resolved` (v48 lane scope).
   - shared downstream validator captures fixed-field and binding invariants.
7. Envelope/registry schema drift risk: `resolved`.
   - strict keyset/schema validation with fail-closed behavior.
8. Deterministic diagnostics ordering/namespace drift risk: `resolved`.
   - `AHK48xx` registry contract enforced.
9. Required violation severity downgrade risk: `resolved`.
   - CLI failure path emits error payload on stderr with non-zero exit.
10. Canonical hash profile drift risk: `resolved`.
   - canonical JSON hashing retained for authoritative comparisons.
11. Deterministic environment drift risk: `resolved`.
   - deterministic env contract required in signing path/tests.
12. Verification-result spoofing risk: `resolved`.
   - downstream binding validator enforces preflight binding hash + authority fields.
13. Trust-anchor lifecycle drift risk: `resolved`.
   - revoked/expired keys fail closed under explicit reference time.
14. Stop-gate keyset/cardinality continuity regression risk: `resolved`.
   - keyset equality with v47 and cardinality `80` verified.

## Post-Merge Review Feedback Disposition

1. `Codex` (`P1`): downstream validator accepted altered fixed contract fields (`contract_schema`, `verification_library`).
   - disposition: `resolved`.
   - change: downstream validator now enforces fixed values for both fields before downstream acceptance.
2. `Gemini`: authority-field subset check was redundant/unreachable.
   - disposition: `resolved`.
   - change: redundant authority-field subset block removed.
3. `Gemini`: `verified` check duplicated in `expected_bindings`.
   - disposition: `resolved`.
   - change: explicit `verified is True` check retained; duplicate binding removed.
4. `Gemini`: test repo-root resolution via `parents[3]` is fragile.
   - disposition: `resolved`.
   - change: tests now use `project_repo_root(anchor=Path(__file__))`.
5. `Gemini`: duplicate repo-root fragility finding in second test.
   - disposition: `resolved`.
   - change: same fix applied to both stop-gate continuity tests.

## Guard Coverage Outcome

- implemented guard suite includes all required v48 checks listed in pre-lock planning set.
- closeout test signal:
  - `packages/adeu_agent_harness/tests/test_taskpack_signature.py`: `18` passing tests
  - `packages/adeu_agent_harness/tests`: `98` passing tests

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v48_edge_closeout_summary@1",
  "arc": "vNext+48",
  "target_path": "V34-A",
  "prelock_edge_count": 14,
  "resolved_edge_count": 14,
  "open_blocking_edges": 0,
  "review_feedback_items_resolved": 5,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v47": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v48)

1. Multi-signer policy/quorum remains intentionally deferred and requires explicit future lock text.
2. Downstream adoption risk remains if future lanes bypass the shared validator helper instead of consuming it.
3. Crypto-provider portability remains deferred; v48 verifier implementation is pinned to deterministic OpenSSL CLI behavior.

## Recommendation (Post Closeout)

1. Mark v48 edge set as closed with no blocking issues.
2. Carry residual risks as explicit inputs into `vNext+49` edge planning.
3. Keep `V34-A` constraints frozen while evaluating `V34-B` selection in the next lock.
