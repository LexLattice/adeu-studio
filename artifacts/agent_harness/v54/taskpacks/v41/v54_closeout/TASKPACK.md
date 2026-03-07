# TaskPack

Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=e1f3f817e2cfbba0f9e3d508513f8d20059e258002a46c86eba0067dbafb4a0b -->

## Task Scope

- `profile_id`: `v54_closeout_default`
- `source_semantic_arc`: `v41`
- `title`: V54 C1+C2 Standalone Integrity Closeout
- `summary`: Deterministic closeout compile for standalone bundle integrity verification baseline plus canonical v34f evidence integration.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=e1f3f817e2cfbba0f9e3d508513f8d20059e258002a46c86eba0067dbafb4a0b -->

## Acceptance

1. Standalone integrity checker emits deterministic standalone_integrity_verification_result@1 on success and fail-closed paths.
2. Standalone bundle inventory is verified against manifest-authoritative emitted-file rows and recomputed bundle-hash subject.
3. Evidence writer emits deterministic canonical closeout bundle with v34a, v34b, v34c, v34d, v34e, and v34f blocks.

<!-- adeu:source_schema_id=taskpack/acceptance@1;source_component_hash=42054b4ab596ce941b6dc08436e8a1fa3af8d847a5b6d83743456b9e73380db3 -->

## Allowlist

- `artifacts/stop_gate`
- `packages/adeu_agent_harness/src/adeu_agent_harness`
- `packages/adeu_agent_harness/tests`

<!-- adeu:source_schema_id=taskpack/allowlist@1;source_component_hash=898209a71e58adf6642fb970ce1dd6232af0cca25977b8e39c9c8f4fdff5e591 -->

## Forbidden

Paths:

- `apps/api`

Effects:

- `network_calls`

<!-- adeu:source_schema_id=taskpack/forbidden@1;source_component_hash=8bb67e38535217f78352c110327f35f6528ed47488853907db5718056c9d1062 -->

## Commands

```text
[noop] true
```

<!-- adeu:source_schema_id=taskpack/commands@1;source_component_hash=fcd22f1ae7bc690b87319790bc4a7c63216cc8a943ba3a4f810e12f1d7502076 -->

## Evidence Slots

- `metric_key_continuity_assertion` (required): Stop-gate metric-key continuity assertion block.
- `runtime_observability_comparison` (required): Runtime observability comparison row against v53 baseline.
- `v34a_handoff_completion_evidence` (required): Signing handoff completion evidence block.
- `v34b_matrix_parity_evidence` (required): Matrix parity evidence block.
- `v34c_policy_recompute_evidence` (required): Policy recompute evidence block.
- `v34d_retry_context_evidence` (required): Retry-context feeder evidence block.
- `v34e_attestation_evidence` (required): Attestation evidence block.
- `v34f_standalone_integrity_evidence` (required): Standalone integrity evidence block.

<!-- adeu:source_schema_id=taskpack/evidence_slots@1;source_component_hash=6a9856d33fbc8b22dcba36769218e8b6a9bcc76a83e2de4be9d24872adecba17 -->

## Attribution

Attribution markers bind each semantic section to authoritative source schema + hash.

<!-- adeu:source_schema_id=taskpack/manifest@1;source_component_hash=ea37cfe4d6b615e8b7afcf06d94564a4a743e0d4c131c11b2cb74244de000172 -->

