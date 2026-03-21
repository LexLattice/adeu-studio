# PR293 Poetry Utility Claimed Scope Snapshot

Reference fixture: `pr293_poetry_utility`
Materialized on: `2026-03-21`

This file localizes the imported scope claim for `V39-A` using only the
committed local evidence bundle.

## Claim Basis

- Arrival commit:
  `9f1fff04eeda52300d52abe47463214e854a2b29`
- Arrival commit subject:
  `Add LLM-backed poetry generation with codex execution option`
- Changed files in the imported contribution:
  - `apps/api/src/adeu_api/openai_backends.py`
  - `apps/api/src/adeu_api/poetry.py`
  - `apps/api/tests/test_openai_backends.py`
  - `apps/api/tests/test_poetry.py`

## Materialized Claimed Scope

- `declared_surface_kind`: `internal_only_utility`
- `surface_refs`:
  - `apps/api/src/adeu_api/openai_backends.py:888:build_codex_exec_backend`
  - `apps/api/src/adeu_api/poetry.py:286:write_poem`
- Summary:
  The imported contribution claimed a new internal poem-generation utility with
  Codex execution support. The localized evidence bundle does not support a
  stronger claim about a reachable API, URM, or web surface.
