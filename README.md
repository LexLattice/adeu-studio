# ADEU Studio

ADEU Studio is an interactive workflow for turning legal clauses into **typed ADEU IR variants** (with first-class ambiguity), validating them with an authoritative kernel, and storing accepted artifacts.

This repo is a monorepo:

- `packages/adeu_ir`: Pydantic ADEU IR + JSON Schema export (single source of truth)
- `packages/adeu_kernel`: Deterministic checker/kernel + golden fixture harness
- `apps/api`: FastAPI service (scaffolded after kernel is green)
- `apps/web`: Next.js UI (scaffolded after kernel is green)

## Quickstart

```bash
make bootstrap
make test
make lint
```

## Run API (mock proposer)

```bash
make bootstrap
.venv/bin/pip install -e apps/api
.venv/bin/python -m uvicorn adeu_api.main:app --reload --port 8000
```

`POST /propose` returns fixture-backed candidates when the input clause text matches one of
`examples/fixtures/*/clause.txt`.

## Run API (OpenAI proposer)

Set `provider: "openai"` in `POST /propose` and configure:

- `OPENAI_API_KEY` (or `ADEU_OPENAI_API_KEY`) for auth
- optional `ADEU_OPENAI_MODEL` (default: `gpt-5.2`)
- optional `ADEU_OPENAI_BASE_URL` (default: `https://api.openai.com/v1`)
- optional `ADEU_LOG_RAW_LLM=1` to include raw prompt/response in proposer logs (off by default)

Request-level overrides:

- `max_candidates` (default `5`)
- `max_repairs` (default `3`)

## Run Web

```bash
cd apps/web
npm install
NEXT_PUBLIC_ADEU_API_URL=http://localhost:8000 npm run dev
```
