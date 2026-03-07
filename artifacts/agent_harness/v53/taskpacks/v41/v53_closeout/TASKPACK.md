# TaskPack

Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=bdbf4f6c274cdbb678400071475d1fdac7ab3e58daaf0e251786c3f492f825da -->

## Task Scope

- `profile_id`: `v53_closeout_default`
- `source_semantic_arc`: `v41`
- `title`: V53 B1+B2 Attestation Closeout
- `summary`: Deterministic closeout compile for provider-neutral attestation validation baseline plus canonical v34e evidence integration.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=bdbf4f6c274cdbb678400071475d1fdac7ab3e58daaf0e251786c3f492f825da -->

## Acceptance

1. Attestation validator emits deterministic remote_enclave_attestation@1 and attestation_verification_result@1.
2. Current local verifier result is recomputed and exact local equivalence is required.
3. Evidence writer emits deterministic canonical closeout bundle with v34a, v34b, v34c, v34d, and v34e blocks.

<!-- adeu:source_schema_id=taskpack/acceptance@1;source_component_hash=ef0e6692432c185dd9ced97c1cc6051738c80ad82b3fc23d9cab821f2fc60004 -->

## Allowlist

- `artifacts/stop_gate`
- `packages/adeu_agent_harness/src/adeu_agent_harness`
- `packages/adeu_agent_harness/tests`

<!-- adeu:source_schema_id=taskpack/allowlist@1;source_component_hash=0e53b7df3d8617267e872ac57be80d3efc152bb4309dc032088e73be0b694c66 -->

## Forbidden

Paths:

- `apps/api`

Effects:

- `network_calls`

<!-- adeu:source_schema_id=taskpack/forbidden@1;source_component_hash=c8d2e86a58c0f67e7215b907252c8f5f48ab2f602092dea33e04f20c37c63e92 -->

## Commands

```text
[noop] true
```

<!-- adeu:source_schema_id=taskpack/commands@1;source_component_hash=96a3be0db343c75cae424bd5c5d26d7a197003e849b7f52e1ad6bb3dcd542353 -->

## Evidence Slots

- `metric_key_continuity_assertion` (required): Stop-gate metric-key continuity assertion block.
- `runtime_observability_comparison` (required): Runtime observability comparison row against v52 baseline.
- `v34a_handoff_completion_evidence` (required): Signing handoff completion evidence block.
- `v34b_matrix_parity_evidence` (required): Matrix parity evidence block.
- `v34c_policy_recompute_evidence` (required): Policy recompute evidence block.
- `v34d_retry_context_evidence` (required): Retry-context feeder evidence block.
- `v34e_attestation_evidence` (required): Attestation evidence block.

<!-- adeu:source_schema_id=taskpack/evidence_slots@1;source_component_hash=71e14c642371aeabf6995d7288f28729f79a220a0302d224b753fff8ead04d64 -->

## Attribution

Attribution markers bind each semantic section to authoritative source schema + hash.

<!-- adeu:source_schema_id=taskpack/manifest@1;source_component_hash=ea37cfe4d6b615e8b7afcf06d94564a4a743e0d4c131c11b2cb74244de000172 -->

