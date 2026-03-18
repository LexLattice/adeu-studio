# Repo Local Guidance

## Python Environment

- Treat `.venv` as the authoritative Python environment for this repo.
- Prefer `make bootstrap`, `make check`, `make test`, `make lint`, and `make format` over raw `python`, `pytest`, or `ruff` commands.
- If you need to run Python directly, use `.venv/bin/python` and `.venv/bin/pip`.
- Do not create alternate virtual environments unless `.venv` is missing or broken.

## Pre-PR Gate

- Before opening or updating a Python PR, run `make check`.
- `make check` is the default local gate for the Python lane and includes:
  - Ruff lint
  - pytest
  - closeout consistency lint
  - semantic compiler closeout lint
  - generated instruction policy doc check
- If you intentionally run a narrower subset instead of `make check`, state what was skipped.

## Docs-Only Arc Bundles

- For docs-only arc starting-bundle work, use `make arc-start-check ARC=<n>`.
- For docs/artifacts-only arc closeout bundle work, use `make arc-closeout-check ARC=<n>`.
- These shortcuts are only for diffs limited to arc planning/closeout docs and committed
  closeout artifacts; they are not a replacement for `make check` when Python source,
  tests, `Makefile`, CI, or lint scripts change.
- `make arc-start-check` runs the arc-bundle scaffold lint plus the generated instruction
  policy doc check.
- `make arc-closeout-check` runs the arc-bundle closeout lint, closeout consistency lint,
  semantic closeout lint, committed URM event-stream validation for that arc bundle, and
  the generated instruction policy doc check.
- If you intentionally use an arc-bundle shortcut instead of `make check`, say that the
  full Python lane was skipped because the change was docs/artifacts only.

## Reflexive Orchestration Experiments

- When a task is explicitly framed as a repo-internal orchestration experiment,
  prefer compiling the high-level intent into typed ADEU artifacts before
  widening implementation scope.
- If sub-agents are used for such an experiment, keep recommended child models
  within:
  - `gpt-5.4`
  - `gpt-5.3-codex`
  - `gpt-5.4-mini`
- Recommended child reasoning effort for that workflow should remain `xhigh`.
- Treat adversarial feedback and code review as explicit delegated phases, not
  optional commentary.
