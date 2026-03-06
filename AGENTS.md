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
