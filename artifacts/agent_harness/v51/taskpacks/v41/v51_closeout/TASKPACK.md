# TaskPack

Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=680f0567e66c55670f1c7a097570db507e747864cdbcb0afe710c4957cd87c6d -->

## Task Scope

- `profile_id`: `v51_closeout_default`
- `source_semantic_arc`: `v41`
- `title`: V51 Z1+Z2 Policy Recompute Closeout
- `summary`: Deterministic closeout compile for verifier-lane policy recompute baseline plus mismatch fail-closed evidence integration.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=680f0567e66c55670f1c7a097570db507e747864cdbcb0afe710c4957cd87c6d -->

## Acceptance

1. Verifier emits deterministic policy_recompute_result@1 for the frozen runner policy subject.
2. Verifier fails closed on recompute mismatch before any success-class verification result survives.
3. Evidence writer emits deterministic canonical closeout bundle with v34a, v34b, and v34c blocks.

<!-- adeu:source_schema_id=taskpack/acceptance@1;source_component_hash=c3393a5792bf231544517b53fc8cc25837e252a1fb81a4d96bcedb6db3bc68e1 -->

## Allowlist

- `artifacts/stop_gate`
- `packages/adeu_agent_harness/src/adeu_agent_harness`
- `packages/adeu_agent_harness/tests`

<!-- adeu:source_schema_id=taskpack/allowlist@1;source_component_hash=f2e9b84249143b4a823f93f16eba9f98b360c47cf11092797509ef6557eda41c -->

## Forbidden

Paths:

- `apps/api`

Effects:

- `network_calls`

<!-- adeu:source_schema_id=taskpack/forbidden@1;source_component_hash=c275012133c449c3d6a8f7ef6c06fe641079a3971f259cc6e49441cd7d93bfad -->

## Commands

```text
[noop] true
```

<!-- adeu:source_schema_id=taskpack/commands@1;source_component_hash=ffb3ad74be7010f9eb7f56be0d2649dd8580c563a4bbe90b4e5f9032364c7dc2 -->

## Evidence Slots

- `metric_key_continuity_assertion` (required): Stop-gate metric-key continuity assertion block.
- `runtime_observability_comparison` (required): Runtime observability comparison row against v50 baseline.
- `v34a_handoff_completion_evidence` (required): Signing handoff completion evidence block.
- `v34b_matrix_parity_evidence` (required): Matrix parity evidence block.
- `v34c_policy_recompute_evidence` (required): Policy recompute evidence block.

<!-- adeu:source_schema_id=taskpack/evidence_slots@1;source_component_hash=96e67244ac30c1e129c3e80e44ab648b411c136be46628fa3fb34c22791abec4 -->

## Attribution

Attribution markers bind each semantic section to authoritative source schema + hash.

<!-- adeu:source_schema_id=taskpack/manifest@1;source_component_hash=ea37cfe4d6b615e8b7afcf06d94564a4a743e0d4c131c11b2cb74244de000172 -->

