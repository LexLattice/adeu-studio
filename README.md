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
- `ADEU_OPENAI_API` backend selector (`responses` default, `chat` fallback backend)
- optional `ADEU_OPENAI_MODEL` (default: `gpt-5.2`)
- optional `ADEU_OPENAI_BASE_URL` (default: `https://api.openai.com/v1`)
- optional `ADEU_LOG_RAW_LLM=1` to include raw prompt/response in proposer logs (off by default)
- optional `ADEU_Z3_TIMEOUT_MS` (default: `3000`) for SMT validator timeout
- optional `ADEU_PERSIST_VALIDATOR_RUNS=1` to persist solver runs for `/check` (off by default)

Request-level overrides:

- `max_candidates` (default `5`)
- `max_repairs` (default `3`)

Behavior notes:

- The `responses` backend uses strict `json_schema` structured outputs.
- The `chat` backend attempts `json_schema` first and only falls back to `json_object` when schema
  formatting is unsupported by that API mode.
- Validation is fail-closed: output must parse as `AdeuIR`, then pass kernel checks.
- Repair attempts use a strict gate: first valid attempt sets baseline; later attempts are accepted
  only on strict score improvement (`status_rank`, `#ERROR`, `#WARN`, total reasons).
- Kernel conflict checks emit SMT `ValidatorRequest` obligations and execute the Z3 backend
  (`z3-solver==4.13.3.0`) with deterministic assertion naming
  `a:<object_id>:<sha256(json_path)[:12]>`.
- SMT output is treated as **solver evidence** (model / unsat core / stats), not as proof
  certificates. Certificates are reserved for future proof-checked backends.
- `UNKNOWN` and `TIMEOUT` map to `REFUSE` in `STRICT` mode, `WARN` in `LAX`. `INVALID_REQUEST`
  remains `ERROR` severity in both modes.

## Run Web

```bash
cd apps/web
npm install
NEXT_PUBLIC_ADEU_API_URL=http://localhost:8000 npm run dev
```
