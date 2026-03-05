# Assessment vNext+48 Edges (V34-A Pre-Lock)

This document records pre-implementation edge analysis for `vNext+48` (`V34-A` deterministic signing + trust-anchor pre-flight hardening).

Status: pre-lock assessment (March 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": true,
  "authoritative_scope": "v48_prelock_edge_analysis",
  "required_in_lock": true,
  "notes": "Pre-lock assessment aligned to V34-A scope from DRAFT_NEXT_ARC_OPTIONS_v8.md."
}
```

## Scope

- In scope: `V34-A` signing/trust-anchor pre-flight implementation planning (`X1`) and guard-suite planning (`X2`).
- Out of scope: `V34-B` through `V34-G`, stop-gate schema-family fork, metric-key expansion, and `L2` boundary release.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS47.md`
- `docs/ASSESSMENT_vNEXT_PLUS47_EDGES.md`
- `docs/SEMANTICS_v3.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
- `packages/adeu_agent_harness/tests/test_taskpack_packaging.py`
- `artifacts/quality_dashboard_v47_closeout.json`
- `artifacts/stop_gate/metrics_v47_closeout.json`

## Pre-Lock Edge Set (V34-A)

1. Signature subject drift risk (`taskpack_bundle_hash` substituted or recomputed from non-authoritative bytes).
2. Trust-anchor split-brain risk (multiple registries or non-authoritative key sources).
3. Algorithm downgrade risk (envelope algorithm differs from key-pinned algorithm in registry).
4. Single-signature scope creep risk (implicit multi-signature behavior appears without lock authorization).
5. Pre-flight verification bypass risk (runner/verifier/packaging invoked without `signature_verification_result@1`).
6. Cross-component verification-policy drift risk (runner/verifier/packaging each re-interpret signature validity).
7. Envelope/registry schema drift risk (weak parsing or permissive extras accepted).
8. Deterministic diagnostics ordering/namespace drift risk (`AHK48xx` policy drift).
9. Required violation severity downgrade risk (errors emitted as warnings).
10. Canonical hash profile drift risk (non-frozen JSON serializer introduced in signing path).
11. Deterministic environment drift risk (`TZ`, `LC_ALL`, `PYTHONHASHSEED` not enforced in guard lanes).
12. Stop-gate keyset/cardinality continuity regression risk.

## Guardrail Evaluation (Planned)

- Signature subject lock: planned.
  - enforce `taskpack_bundle_hash` exact-match subject verification.
- Trust-anchor single-source lock: planned.
  - accept trust anchors from canonical registry artifact only.
- Algorithm/key pinning lock: planned.
  - key-id lookup must enforce exact allowed algorithm; mismatch fails closed.
- Single-signature lock: planned.
  - envelope cardinality > 1 fails closed.
- Pre-flight no-bypass lock: planned.
  - signature verification artifact required before downstream execution.
- Cross-lane policy identity lock: planned.
  - downstream components consume `signature_verification_result@1` rather than redefining policy.
- Schema + canonicalization lock: planned.
  - strict schema validation + frozen canonical JSON hash profile.
- Diagnostic namespace/severity lock: planned.
  - `AHK48xx` registry mapping and error-only channel for required violations.
- Stop-gate continuity lock: planned.
  - exact keyset equality with v47 and derived cardinality `80`.

## Required Guard Additions (v48)

1. `test_signature_envelope_requires_single_signature`
2. `test_signature_subject_must_equal_taskpack_bundle_hash`
3. `test_signature_manifest_hash_redundant_binding_must_match`
4. `test_algorithm_key_binding_mismatch_fails_closed`
5. `test_unknown_signer_key_id_fails_closed`
6. `test_preflight_signature_verification_is_required_before_runner`
7. `test_signature_verification_result_schema_required_for_downstream`
8. `test_signing_diagnostics_enforce_AHK48_registry`
9. `test_signing_required_violations_are_error_channel_only`
10. `test_stop_gate_metric_keyset_exact_equal_v47`
11. `test_stop_gate_metric_cardinality_equals_80_from_metrics_keys_only`

## Residual Risks (Post-Lock, Pre-Implementation)

1. Registry migration risk if key-id format is underspecified in `taskpack_trust_anchor_registry@1`.
2. Tooling adoption risk if downstream callers do not uniformly require pre-flight artifact consumption.
3. Future multi-signer pressure risk unless explicitly deferred in v48 lock and tests.

## Recommendation (Pre-Lock)

1. Proceed with `V34-A` lock drafting for `vNext+48`.
2. Freeze single-signature semantics and key-algorithm pinning in lock JSON before implementation.
3. Treat all `V34-B` through `V34-G` proposals as deferred and non-authoritative for v48 implementation scope.
