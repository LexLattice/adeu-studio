# TaskPack

Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=c0b17f1d97013e4b7ea28be7fc5fc732d7d8044cd4ebfd6eb69aaceed5cfc444 -->

## Task Scope

- `profile_id`: `v48b_a35a24d7f420`
- `source_semantic_arc`: `v41`
- `title`: Compiled taskpack binding hot_mode_v48_prompt_boundary_binding_profile for task:hot_mode:v48_prompt_boundary:run
- `summary`: Bind one released V47-E consumer row and one admitted V45 scope surface into a single-file hot-mode boundary that keeps prompt prose projection-only.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=c0b17f1d97013e4b7ea28be7fc5fc732d7d8044cd4ebfd6eb69aaceed5cfc444 -->

## Acceptance

1. Stay inside the allowlist projection carried by hot_mode_v48_prompt_boundary_binding_profile.
2. Avoid forbidden paths and forbidden effects carried by hot_mode_v48_prompt_boundary_binding_profile.
3. Use only the declared commands mapped from hot_mode_v48_prompt_boundary_binding_profile.
4. Populate the required evidence slots mapped from hot_mode_v48_prompt_boundary_binding_profile for task:hot_mode:v48_prompt_boundary:run.

<!-- adeu:source_schema_id=taskpack/acceptance@1;source_component_hash=a6d5f92ee30810d37e44bd3ea0ae6259904dd501a3cef445c72c5df485206bf2 -->

## Allowlist

- `packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology.json`

<!-- adeu:source_schema_id=taskpack/allowlist@1;source_component_hash=742905ab57ca73be8f4a5024406c587ce4eb99bfe68cb0e6915d07d12b8082ea -->

## Forbidden

Paths:

- `packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology_rejected_compiled_boundary_mismatch.json`

Effects:

- `network_calls`

<!-- adeu:source_schema_id=taskpack/forbidden@1;source_component_hash=f2a8043ce74b2d5cd81fc1b2e577d01b997092c53a14429c77dd4d33257ca013 -->

## Commands

```text
[pytest_topology] .venv/bin/python -m pytest packages/adeu_agent_harness/tests/test_worker_delegation_topology.py -q
```

<!-- adeu:source_schema_id=taskpack/commands@1;source_component_hash=0f0483ad1c66641fa6b79c14ef9f2638cedb62d9e36526da66b7c059fd1b2e5a -->

## Evidence Slots

- `hot_mode_summary` (required): Capture the hot-mode summary JSON for the boundary experiment.

<!-- adeu:source_schema_id=taskpack/evidence_slots@1;source_component_hash=7c8189fa560da9e30cb5417bf959957d1b04e06b0032eadb698715f102b8babf -->

## Attribution

Attribution markers bind each semantic section to authoritative source schema + hash.

<!-- adeu:source_schema_id=taskpack/manifest@1;source_component_hash=ea37cfe4d6b615e8b7afcf06d94564a4a743e0d4c131c11b2cb74244de000172 -->

