.PHONY: bootstrap test lint format

VENV ?= .venv
PY := $(VENV)/bin/python
PIP := $(VENV)/bin/pip

bootstrap:
	python -m venv $(VENV)
	$(PIP) install -U pip
	$(PIP) install -e packages/adeu_ir -e packages/adeu_patch_core -e packages/adeu_lean -e "packages/adeu_kernel[dev]" -e packages/adeu_concepts -e packages/adeu_puzzles -e "packages/adeu_explain[dev]" -e packages/urm_runtime -e packages/urm_domain_adeu -e packages/urm_domain_paper -e apps/api

test:
	$(PY) -m pytest

lint:
	$(PY) -m ruff check .

format:
	$(PY) -m ruff format .
