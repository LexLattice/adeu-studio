# TaskPack

Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=fd16c2521a77cea5c070f4f2ac17d81afd14ba997c4ccc54042c930cd8046627 -->

## Task Scope

- `profile_id`: `v46_closeout_default`
- `source_semantic_arc`: `v41`
- `title`: V46 U1+U2 Verifier/Evidence Closeout
- `summary`: Deterministic closeout compile for V33-C verifier/evidence wiring.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=fd16c2521a77cea5c070f4f2ac17d81afd14ba997c4ccc54042c930cd8046627 -->

## Acceptance

1. Verifier cross-checks runner artifacts before evidence emission.
2. Evidence writer emits deterministic canonical bundle and provenance for verified inputs.

<!-- adeu:source_schema_id=taskpack/acceptance@1;source_component_hash=51e112c72ce762a14458d21c12fdbb0aa73693772f573094c20a48437b0ab20a -->

## Allowlist

- `artifacts/stop_gate`
- `packages/adeu_agent_harness/src/adeu_agent_harness`
- `packages/adeu_agent_harness/tests`

<!-- adeu:source_schema_id=taskpack/allowlist@1;source_component_hash=78129c55c231e4112ecf72742334e356101801976dc6b64824a331b4094b92b5 -->

## Forbidden

Paths:

- `apps/api`

Effects:

- `network_calls`

<!-- adeu:source_schema_id=taskpack/forbidden@1;source_component_hash=de9e3377ce5f2441f50485d69d136444b755a1fc449d961ee2ae7914bfa0620c -->

## Commands

```text
[noop] true
```

<!-- adeu:source_schema_id=taskpack/commands@1;source_component_hash=eda15bb76052aa92e205b2f0d241939c6f8ce07de5d8de3100a7856268a2b1b7 -->

## Evidence Slots

- `metric_key_continuity_assertion` (required): Stop-gate metric-key continuity assertion block.
- `runtime_observability_comparison` (required): Runtime observability comparison row against v45 baseline.
- `v33c_verifier_wiring_evidence` (required): Verifier/evidence writer wiring evidence block.

<!-- adeu:source_schema_id=taskpack/evidence_slots@1;source_component_hash=385ff9b370f2b2b48b9dfecd66c6d885d7d666aaff5edd26749f795388696895 -->

## Attribution

Attribution markers bind each semantic section to authoritative source schema + hash.

<!-- adeu:source_schema_id=taskpack/manifest@1;source_component_hash=ea37cfe4d6b615e8b7afcf06d94564a4a743e0d4c131c11b2cb74244de000172 -->

