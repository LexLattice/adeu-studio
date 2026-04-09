# Draft Post-Merge Lint Guard v0

Status: support.

Authority layer: support.

## Purpose

Ensure local merge results are lint-checked before they are pushed, so clean
branch heads do not create a dirty merge commit that only fails after `push`
CI.

## Problem Shape

Some merge failures are not visible on either branch head alone. A classic case
is duplicate imports created by clean three-way merge union:

- parent A adds an import in one position;
- parent B adds the same import in a different position;
- Git preserves both because it sees two non-overlapping additions;
- Ruff then fails on the merge commit even though both parent heads were green.

## Guard

- the repo-managed hooks path is `.githooks`
- `make bootstrap` installs that hooks path with:
  - `git config core.hooksPath .githooks`
- `.githooks/post-merge` runs:
  - `make merge-post-check`
- `merge-post-check` currently runs:
  - `make lint`

## Scope

This guard is local merge-result verification. It does not replace:

- PR CI
- push CI on `main`
- `make check` for ordinary Python lane work

It exists because merge-result failures can be minted after the last green
branch-head check.

## Operational Notes

- if `.venv` is missing, the hook exits without blocking and tells the operator
  to run `make bootstrap`
- the hook should stay fast and fail-closed for import-order / Ruff regressions
- if later needed, `merge-post-check` can widen to `make check`, but the first
  priority is catching merge-only lint artifacts immediately
