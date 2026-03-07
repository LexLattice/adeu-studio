# TaskPack

Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=299a622bcfc365e0bbf95684df1ba5b9ecaffbc638f001e58e1826caf673eb9c -->

## Task Scope

- `profile_id`: `v52_closeout_default`
- `source_semantic_arc`: `v41`
- `title`: V52 A1+A2 Retry Context Closeout
- `summary`: Deterministic closeout compile for advisory retry-context feeder baseline plus canonical v34d evidence integration.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=299a622bcfc365e0bbf95684df1ba5b9ecaffbc638f001e58e1826caf673eb9c -->

## Acceptance

1. Retry context feeder emits deterministic retry_context_feeder_result@1 from runner rejection diagnostics.
2. Retry context sanitization profile remains frozen and deterministic.
3. Evidence writer emits deterministic canonical closeout bundle with v34a, v34b, v34c, and v34d blocks.

<!-- adeu:source_schema_id=taskpack/acceptance@1;source_component_hash=d4da9e31db948f4e772a106be8082cb7fe63a01a9047dc2c1f58011a979ed8c9 -->

## Allowlist

- `artifacts/stop_gate`
- `packages/adeu_agent_harness/src/adeu_agent_harness`
- `packages/adeu_agent_harness/tests`

<!-- adeu:source_schema_id=taskpack/allowlist@1;source_component_hash=4c5eb74d8e3bec17cd3392d98a33c6edd8f845e96c367267e7d58a09bdd05bd2 -->

## Forbidden

Paths:

- `apps/api`

Effects:

- `network_calls`

<!-- adeu:source_schema_id=taskpack/forbidden@1;source_component_hash=7483505b5966004240f5b1372fb5e01433de22751c771a65f3ca5d3eba535a41 -->

## Commands

```text
[noop] true
```

<!-- adeu:source_schema_id=taskpack/commands@1;source_component_hash=33cb11574aaed7c4ed72a64a156ce9c02c507ce9cdf9045cbce9b3f580095d3a -->

## Evidence Slots

- `metric_key_continuity_assertion` (required): Stop-gate metric-key continuity assertion block.
- `runtime_observability_comparison` (required): Runtime observability comparison row against v51 baseline.
- `v34a_handoff_completion_evidence` (required): Signing handoff completion evidence block.
- `v34b_matrix_parity_evidence` (required): Matrix parity evidence block.
- `v34c_policy_recompute_evidence` (required): Policy recompute evidence block.
- `v34d_retry_context_evidence` (required): Retry-context feeder evidence block.

<!-- adeu:source_schema_id=taskpack/evidence_slots@1;source_component_hash=1168d2ee578a450d1f0780754d66483579812079a436cdd98e7828bf9335877b -->

## Attribution

Attribution markers bind each semantic section to authoritative source schema + hash.

<!-- adeu:source_schema_id=taskpack/manifest@1;source_component_hash=ea37cfe4d6b615e8b7afcf06d94564a4a743e0d4c131c11b2cb74244de000172 -->

