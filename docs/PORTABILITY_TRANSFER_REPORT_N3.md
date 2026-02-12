# Portability Transfer Report (N3 Thin Slice)

This report documents the N3 portability proof implementation for the frozen pilot domain `paper.abstract`.

## Evidence Refs

- `artifact:apps/api/tests/test_urm_domain_tools.py::test_urm_tool_call_paper_domain_closed_world_flow`
- `artifact:apps/api/tests/test_urm_runtime_import_audit.py::test_urm_runtime_has_no_domain_pack_imports`
- `artifact:policy/urm.capability.lattice.v1.json`
- `artifact:packages/urm_runtime/src/urm_runtime/domain_registry.py`

## Touched Runtime Primitives

- Added domain registry/protocol for runtime tool dispatch:
  - `packages/urm_runtime/src/urm_runtime/domain_registry.py`
- API runtime composition now registers multiple domain packs through the registry:
  - `apps/api/src/adeu_api/urm_routes.py`

## ADEU Coupling Changes

- Removed ADEU-only tool dispatch assumption in `/urm/tools/call` route:
  - before: direct `ADEUDomainTools` call path
  - after: `DomainToolRegistry` resolves pack by supported tool set
  - file: `apps/api/src/adeu_api/urm_routes.py`

## Domain-Only Additions

- New paper domain pack package:
  - `packages/urm_domain_paper/pyproject.toml`
  - `packages/urm_domain_paper/src/urm_domain_paper/adapters.py`
  - `packages/urm_domain_paper/src/urm_domain_paper/models.py`
  - `packages/urm_domain_paper/src/urm_domain_paper/__init__.py`
- Added paper capability actions:
  - `paper.ingest_text`
  - `paper.extract_abstract_candidate`
  - `paper.check_constraints`
  - `paper.emit_artifact`

## Boundary Confirmation

- `paper.abstract` flow remains closed-world:
  - tools operate only on provided local text payloads
  - no web retrieval and no citation oracle usage
- Runtime import-audit test confirms no domain-pack import from `urm_runtime` modules.

## Reproduction Commands

```bash
.venv/bin/python -m pytest apps/api/tests/test_urm_domain_tools.py::test_urm_tool_call_paper_domain_closed_world_flow -q
.venv/bin/python -m pytest apps/api/tests/test_urm_runtime_import_audit.py -q
```
