# Portability Transfer Report (N+2)

This report documents C1-C3 outcomes for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS2.md`

Status: evidence-backed, scoped portability confirmation.

## Evidence Refs

- CI run:
  - `https://github.com/LexLattice/adeu-studio/actions/runs/21969750279`
  - head SHA: `054af33227f245b638edf2c6cd825c5b2b053cb6`
- Domain conformance artifact:
  - artifact name: `domain-conformance`
  - artifact id: `5492312403`
  - digest: `sha256:1fc7988f9e27ca063d5daa712cd439b598071da58a3cfab6261c1d9d3fa895c7`
  - contents: `domain_conformance.json` (`domain_conformance@1`)
- Code + test refs:
  - `apps/api/src/adeu_api/urm_domain_conformance.py`
  - `apps/api/scripts/build_domain_conformance.py`
  - `apps/api/tests/test_urm_domain_conformance.py`
  - `apps/api/tests/test_urm_runtime_import_audit.py`
  - `packages/urm_runtime/src/urm_runtime/domain_registry.py`
  - `packages/urm_domain_digest/src/urm_domain_digest/adapters.py`

## Outcome Summary

- Portability conformance result: `valid = true`
- Registry-order determinism: `valid = true`
  - pack count: `2` (`urm_domain_digest`, `urm_domain_paper`)
  - tool count: `8`
- Import-audit result: `valid = true`, `offenders = []`
- Domain checks:
  - `digest`: all checks valid
  - `paper`: all checks valid
- Reported issues: `[]`

## Reused Runtime Components (Unchanged Contracts)

- URM event envelope + validators/replay:
  - `packages/urm_runtime/src/urm_runtime/models.py` (`urm-events@1`)
  - `packages/urm_runtime/src/urm_runtime/events_tools.py`
- Capability/policy authorization surface:
  - `packages/urm_runtime/src/urm_runtime/capability_policy.py`
- Tool call response envelope:
  - `packages/urm_runtime/src/urm_runtime/models.py` (`ToolCallResponse`)

These components were reused without introducing domain-specific forks.

## Coupling Points Removed/Avoided

- Runtime-to-domain import coupling avoided in core runtime:
  - conformance import-audit confirms no `urm_domain_*` imports under `packages/urm_runtime/src/urm_runtime/`.
- Domain routing remains registry-driven at API boundary:
  - `apps/api/src/adeu_api/urm_routes.py` composes domain packs via `DomainToolRegistry`.
- No domain-specific event or error taxonomy forks introduced for `digest`.

## Domain-Only Additions (Boundary Confirmation)

- Added domain pack:
  - `packages/urm_domain_digest/pyproject.toml`
  - `packages/urm_domain_digest/src/urm_domain_digest/__init__.py`
  - `packages/urm_domain_digest/src/urm_domain_digest/models.py`
  - `packages/urm_domain_digest/src/urm_domain_digest/adapters.py`
- Added digest capability actions:
  - `digest.ingest_text`
  - `digest.extract_digest_candidate`
  - `digest.check_constraints`
  - `digest.emit_artifact`
  - policy refs:
    - `policy/urm.capability.lattice.v1.json`
    - `packages/urm_runtime/src/urm_runtime/policy/urm.capability.lattice.v1.json`

Domain-specific semantics remain confined to the digest pack boundary.

## Generic Runtime Primitive Justification

New/expanded generic registry primitives in this arc are justified by at least two domains:

- `DomainToolPack.list_tools` + deterministic registry metadata surfaces
  - used by `urm_domain_paper`
  - used by `urm_domain_digest`
- `DomainToolRegistry.list_pack_metadata` / `list_tool_metadata`
  - consumed by conformance checks across both non-ADEU domains.

## Tested Scope Boundaries

This report claims portability only for tested scope:

- offline, fixture/snapshot-driven execution
- local provided inputs only (closed-world domain behavior)
- no network, browsing, or external retrieval
- conformance dimensions:
  - event envelope validity
  - replay determinism
  - policy gating behavior
  - error envelope/taxonomy conformance
  - runtime import audit

No claim is made here for semantic portability beyond this scope.

## Reproduction

Generate local conformance artifact:

```bash
.venv/bin/python apps/api/scripts/build_domain_conformance.py \
  --out artifacts/domain_conformance.json \
  --events-dir artifacts/domain_conformance_events
```

Download CI evidence artifact:

```bash
gh run download 21969750279 --name domain-conformance --dir /tmp/domain-conformance
cat /tmp/domain-conformance/domain_conformance.json
```

Validate report invariants in tests:

```bash
.venv/bin/pytest apps/api/tests/test_urm_domain_conformance.py -q
.venv/bin/pytest apps/api/tests/test_urm_runtime_import_audit.py -q
```
