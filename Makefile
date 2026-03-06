.PHONY: bootstrap test lint format check closeout-lint semantic-closeout-lint instruction-policy-check

VENV ?= .venv
PY := $(VENV)/bin/python
PIP := $(VENV)/bin/pip
CLOSEOUT_LINT_PYTHONPATH := apps/api/src:packages/urm_runtime/src

bootstrap:
	python -m venv $(VENV)
	$(PIP) install -U pip
	$(PIP) install \
		-e packages/adeu_ir \
		-e packages/adeu_patch_core \
		-e packages/adeu_lean \
		-e "packages/adeu_kernel[dev]" \
		-e packages/adeu_concepts \
		-e packages/adeu_puzzles \
		-e "packages/adeu_explain[dev]" \
		-e "packages/adeu_semantic_depth[dev]" \
		-e "packages/adeu_core_ir[dev]" \
		-e "packages/adeu_commitments_ir[dev]" \
		-e "packages/adeu_semantic_source[dev]" \
		-e "packages/adeu_semantic_compiler[dev]" \
		-e "packages/adeu_agent_harness[dev]" \
		-e packages/urm_runtime \
		-e packages/urm_domain_adeu \
		-e packages/urm_domain_digest \
		-e packages/urm_domain_paper \
		-e apps/api

test:
	$(PY) -m pytest

lint:
	$(PY) -m ruff check .

format:
	$(PY) -m ruff format .

closeout-lint:
	TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=$(CLOSEOUT_LINT_PYTHONPATH) \
		$(PY) apps/api/scripts/lint_closeout_consistency.py

semantic-closeout-lint:
	TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=$(CLOSEOUT_LINT_PYTHONPATH) \
		$(PY) apps/api/scripts/lint_semantic_compiler_closeout.py

instruction-policy-check:
	$(PY) apps/api/scripts/generate_instruction_policy_views.py --check

check: lint test closeout-lint semantic-closeout-lint instruction-policy-check
