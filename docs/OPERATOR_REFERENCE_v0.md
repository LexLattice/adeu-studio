# ADEU Studio Operator Reference v0

**Status:** working reference
**Scope:** local operation, provider modes, runtime surfaces, and practical commands that are too detailed for the front-page README

## Local Bootstrap

```bash
make bootstrap
```

Core local gates:

```bash
make test
make lint
make check
```

Deterministic eval fixture inputs used by roadmap quality checks live under:

- `examples/eval/questions/**`
- `examples/eval/tournament/**`

## Useful Diagnostics

Build the same quality dashboard artifact used by CI:

```bash
.venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard.json
```

Run deterministic oracle checks and emit a machine-readable report:

```bash
.venv/bin/python apps/api/scripts/run_determinism_oracles.py --out artifacts/determinism_oracles.json
```

URM event stream diagnostics:

```bash
.venv/bin/events validate --in apps/api/tests/fixtures/urm_events/sample_valid.ndjson --strict
.venv/bin/events replay --in apps/api/tests/fixtures/urm_events/sample_valid.ndjson --out artifacts/urm_events/replay.ndjson
.venv/bin/events summary --in apps/api/tests/fixtures/urm_events/sample_valid.ndjson --out-json artifacts/urm_events/summary.json --out-md artifacts/urm_events/summary.md
```

## Run API

```bash
.venv/bin/pip install -e apps/api
.venv/bin/python -m uvicorn adeu_api.main:app --reload --port 8000
```

The API supports three provider modes:

- `fixture` for deterministic fixture-backed responses
- `openai` for remote OpenAI-backed proposer flows
- `codex` for local Codex CLI-backed proposer flows

### Fixture Mode

- `POST /propose` returns fixture-backed candidates when the input clause text matches `examples/fixtures/*/clause.txt`.
- `POST /concepts/propose` returns fixture-backed concept composition candidates when `source_text` matches `examples/concepts/fixtures/*/source.txt`.

### Selected API Surfaces

Concept workflows:

- `POST /documents` ingests immutable source documents.
- `GET /documents` and `GET /documents/{doc_id}` list and retrieve stored documents.
- `POST /concepts/check` validates `ConceptIR` and returns a shared `CheckReport`.
- `POST /concepts/analyze` returns a `CheckReport` plus structured SAT/UNSAT analysis.
- `POST /concepts/apply_patch` applies a sandboxed patch and rechecks the result.
- `POST /concepts/questions` generates deterministic question and answer actions from analysis signals.
- `POST /concepts/tournament` ranks patch candidates in advisory mode with deterministic scoring.
- `POST /concepts/align` returns deterministic cross-artifact vocabulary suggestions.
- `POST /concepts/diff` returns a structural and solver-aware causal diff.
- `POST /concepts/artifacts` stores accepted concept artifacts and linked validator runs.

Cross-domain explainability:

- `POST /explain_flip` returns a deterministic flip narrative plus the underlying `diff_report`.

Puzzles:

- `POST /puzzles/solve` accepts a strict `KnightsKnavesPuzzle` payload and returns solver status, role assignments, and underlying `ValidatorResult` evidence.
- `POST /puzzles/propose` supports proposer-backed puzzle generation.

URM runtime:

- `POST /urm/copilot/start`
- `POST /urm/copilot/send`
- `POST /urm/copilot/stop`
- `POST /urm/copilot/mode`
- `GET /urm/copilot/events`
- `POST /urm/worker/run`
- `POST /urm/tools/call`

Proof and artifact retrieval:

- `GET /artifacts/{artifact_id}/proofs`
- `GET /artifacts/{artifact_id}/validator-runs`

### API Notes

- For concept endpoints that accept source text, `doc_id` can be provided instead of `source_text`.
- If both are provided, `doc_id` is authoritative and mismatched text returns `400 DOC_TEXT_MISMATCH`.
- `POST /concepts/apply_patch` accepts `ir_hash` as a precondition; mismatches return `409 STALE_IR`.
- `POST /concepts/align` caps effective scope at 200 artifacts after normalization; larger requests return `400 ALIGNMENT_SCOPE_TOO_LARGE`.

## Provider Configuration

### OpenAI Provider

Set `provider: "openai"` in `POST /propose`, `POST /concepts/propose`, and `POST /puzzles/propose`.

Important environment variables:

- `OPENAI_API_KEY` or `ADEU_OPENAI_API_KEY`
- `ADEU_OPENAI_API` with `responses` as default and `chat` as fallback backend
- `ADEU_OPENAI_MODEL`
- `ADEU_OPENAI_TEMPERATURE`
- `ADEU_OPENAI_DEFAULT_MAX_CANDIDATES`
- `ADEU_OPENAI_DEFAULT_MAX_REPAIRS`
- `ADEU_OPENAI_BASE_URL`
- `ADEU_OPENAI_HTTP_TIMEOUT_SECONDS`
- `ADEU_LOG_RAW_LLM=1` for raw proposer logging
- `ADEU_Z3_TIMEOUT_MS`
- `ADEU_PERSIST_VALIDATOR_RUNS=1`
- `ADEU_PROOF_BACKEND`
- `ADEU_LEAN_BIN` or `LEAN_BIN`
- `ADEU_LEAN_TIMEOUT_MS`
- `ADEU_MAX_SOURCE_TEXT_BYTES`
- `ADEU_MAX_QUESTION_DRY_RUN_EVALS_TOTAL`
- `ADEU_MAX_QUESTION_SOLVER_CALLS_TOTAL`
- `ADEU_MAX_ALIGNMENT_SCOPE_ARTIFACTS`
- `ADEU_ALIGNMENT_MAX_SUGGESTIONS_DEFAULT`
- `ADEU_EXPLAIN_ANALYSIS_BUDGET_DEFAULT`
- `ADEU_QUESTION_FORCED_BUDGET_MAX`
- `ADEU_QUESTION_FORCED_BUDGET_DIVISOR`
- `ADEU_QUESTION_MIC_SHRINK_ITERS_MAX`
- `ADEU_MAX_TOURNAMENT_DRY_RUN_EVALS_TOTAL`
- `ADEU_MAX_TOURNAMENT_SOLVER_CALLS_TOTAL`
- `ADEU_MAX_TOURNAMENT_REPLAY_CANDIDATES`
- `ADEU_MAX_TOURNAMENT_PATCH_OPS_PER_CANDIDATE`
- `ADEU_MAX_TOURNAMENT_TOTAL_PATCH_OPS`
- `ADEU_MAX_TOURNAMENT_REPLAY_PAYLOAD_BYTES`
- `ADEU_MAX_TOURNAMENT_TOP_K`

### Codex Provider

Set `provider: "codex"` in `POST /propose`, `POST /concepts/propose`, and `POST /puzzles/propose`.

Important environment variables:

- `ADEU_CODEX_BIN`
- `ADEU_CODEX_MODEL`
- `ADEU_CODEX_EXEC_TIMEOUT_SECONDS`

### Request-Level Overrides

- `max_candidates`
- `max_repairs`

## Validation and Trust Notes

- The `responses` backend uses strict `json_schema` structured outputs.
- The `chat` backend attempts `json_schema` first and falls back to `json_object` only when schema formatting is unsupported.
- The `codex` backend uses `codex exec --json --output-schema` in `read-only` sandbox mode.
- Validation is fail-closed: proposer output must parse as `AdeuIR` and then pass kernel checks.
- Repair attempts use a strict gate: the first valid attempt sets baseline, and later attempts must improve strictly on score.
- Kernel conflict checks execute the Z3 backend with deterministic assertion naming `a:<object_id>:<sha256(json_path)[:12]>`.
- SMT output is treated as solver evidence, not as proof certificates.
- `UNKNOWN` and `TIMEOUT` map to `REFUSE` in `STRICT` mode and `WARN` in `LAX`.
- Accepted artifacts persist one `ProofArtifact` per theorem obligation via the v3.1 proof-check pipeline:
  - `pred_closed_world`
  - `exception_gating`
  - `conflict_soundness`

## Run Web

```bash
cd apps/web
npm install
NEXT_PUBLIC_ADEU_API_URL=http://localhost:8000 npm run dev
```

Selected routes:

- `/`
- `/concepts`
- `/puzzles`
- `/papers`
- `/artifacts`
- `/copilot`

Web notes:

- `apps/web/next-env.d.ts` is generated by Next.js and may flip between dev and build route type paths.
- If it appears as a local-only diff during unrelated work, restore it before committing unrelated changes.
- If the API runs on a non-default port, update `NEXT_PUBLIC_ADEU_API_URL` and use a matching web origin that is allowed by API CORS settings.

## Read Together With

- [README.md](../README.md) for the human-facing repo front page
- [ARCHITECTURE_ADEU_STUDIO_v0.md](./ARCHITECTURE_ADEU_STUDIO_v0.md) for system structure
- [REPO_ATLAS.md](../REPO_ATLAS.md) for repo navigation
