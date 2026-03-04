# TaskPack

Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=9160826e61c156b913bf3153a1ee73de1710a8bcf99d8ff1de556ab6b0b52ab2 -->

## Task Scope

- `profile_id`: `v44_closeout_default`
- `source_semantic_arc`: `v41`
- `title`: V44 S1+S2 TaskPack Closeout Evidence
- `summary`: Deterministic closeout compile for V33-A evidence wiring.

<!-- adeu:source_schema_id=taskpack/pipeline_profile@1;source_component_hash=9160826e61c156b913bf3153a1ee73de1710a8bcf99d8ff1de556ab6b0b52ab2 -->

## Acceptance

1. Emit deterministic taskpack bundle artifacts for v44 closeout evidence.
2. Verify fail-closed bundle integrity via manifest and component hash checks.

<!-- adeu:source_schema_id=taskpack/acceptance@1;source_component_hash=9f7612b3fdd61a23f9557f33802998450e1b8071d12a171c08a4613f04bc5cad -->

## Allowlist

- `packages/adeu_agent_harness/src/adeu_agent_harness`
- `packages/adeu_agent_harness/tests`

<!-- adeu:source_schema_id=taskpack/allowlist@1;source_component_hash=cfa01041d97c85bd4a32bcd33e168cda8474b0b834e7056091645cab220b5319 -->

## Forbidden

Paths:

- `apps/api`
- `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`

Effects:

- `network_calls`
- `provider_expansion`

<!-- adeu:source_schema_id=taskpack/forbidden@1;source_component_hash=47a923c19e60f26db9372cc35e65ac4cd4688ebb7fe23d958ddd975eadffb097 -->

## Commands

```text
[lint] PYTHONPATH=packages/adeu_agent_harness/src .venv/bin/ruff check packages/adeu_agent_harness/src/adeu_agent_harness packages/adeu_agent_harness/tests
[test] PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/pytest -q packages/adeu_agent_harness/tests/test_taskpack_compile.py
```

<!-- adeu:source_schema_id=taskpack/commands@1;source_component_hash=c3f2bdee5fe0efb1243ed00dcc8a2969613ec6a1d67a81453d12d4794d88c367 -->

## Evidence Slots

- `taskpack_bundle_verify_status` (required): Capture deterministic bundle verification status.
- `taskpack_manifest_sha256` (required): Capture canonical taskpack manifest hash.

<!-- adeu:source_schema_id=taskpack/evidence_slots@1;source_component_hash=4ad968ae6827cf964f06a86c85bf634df6aeeb9eec1ed09ef55452564b314306 -->

## Attribution

Attribution markers bind each semantic section to authoritative source schema + hash.

<!-- adeu:source_schema_id=taskpack/manifest@1;source_component_hash=ea37cfe4d6b615e8b7afcf06d94564a4a743e0d4c131c11b2cb74244de000172 -->

