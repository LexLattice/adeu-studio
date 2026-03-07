# TaskPack

Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=a25bb18109eb57bd4cc465164f30dc90c95969c8ddac500a81d450ddf4a2720c -->

## Task Scope

- `profile_id`: `v55_closeout_default`
- `source_semantic_arc`: `v41`
- `title`: V55 D1+D2 Remote Enclave Closeout
- `summary`: Deterministic closeout compile for remote_enclave deployment-mode baseline plus canonical v34g evidence integration.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=a25bb18109eb57bd4cc465164f30dc90c95969c8ddac500a81d450ddf4a2720c -->

## Acceptance

1. Remote-enclave deployment mode emits deterministic packaging artifacts and fails closed without attestation-bound prerequisites.
2. Three-mode matrix parity remains exact for canonical subtree and policy-equivalence subjects under the singleton runtime.
3. Evidence writer emits deterministic canonical closeout bundle with v34a through v34g blocks.

<!-- adeu:source_schema_id=taskpack/acceptance@1;source_component_hash=951908d38e70754400180c4a6ac030d325367890cb881600b84cac768e49ac55 -->

## Allowlist

- `artifacts/stop_gate`
- `packages/adeu_agent_harness/src/adeu_agent_harness`
- `packages/adeu_agent_harness/tests`

<!-- adeu:source_schema_id=taskpack/allowlist@1;source_component_hash=a33e094d5c57f70989e05e05e5f71cdd84f26aa6dcd6f222839c699cd708a9db -->

## Forbidden

Paths:

- `apps/api`

Effects:

- `network_calls`

<!-- adeu:source_schema_id=taskpack/forbidden@1;source_component_hash=d8015c9d1b6274376b5dfb836bea0467c65bd54e825ba537e6b749195ebd1ad4 -->

## Commands

```text
[noop] true
```

<!-- adeu:source_schema_id=taskpack/commands@1;source_component_hash=509091aea3799b17f0f9d8b8399134dbe45609c9276b3942901995f0ff305b52 -->

## Evidence Slots

- `metric_key_continuity_assertion` (required): Stop-gate metric-key continuity assertion block.
- `runtime_observability_comparison` (required): Runtime observability comparison row against v54 baseline.
- `v34a_handoff_completion_evidence` (required): Signing handoff completion evidence block.
- `v34b_matrix_parity_evidence` (required): Matrix parity evidence block.
- `v34c_policy_recompute_evidence` (required): Policy recompute evidence block.
- `v34d_retry_context_evidence` (required): Retry-context feeder evidence block.
- `v34e_attestation_evidence` (required): Attestation evidence block.
- `v34f_standalone_integrity_evidence` (required): Standalone integrity evidence block.
- `v34g_remote_enclave_mode_evidence` (required): Remote-enclave deployment-mode evidence block.

<!-- adeu:source_schema_id=taskpack/evidence_slots@1;source_component_hash=47b6f4aebf368ff3d598d9d80f61f22575ee269e3ee65287865c8509ec27a302 -->

## Attribution

Attribution markers bind each semantic section to authoritative source schema + hash.

<!-- adeu:source_schema_id=taskpack/manifest@1;source_component_hash=ea37cfe4d6b615e8b7afcf06d94564a4a743e0d4c131c11b2cb74244de000172 -->

