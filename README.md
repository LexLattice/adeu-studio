# ADEU Studio

ADEU Studio is an interactive workflow for turning legal clauses into **typed ADEU IR variants** (with first-class ambiguity), validating them with an authoritative kernel, and storing accepted artifacts.

This repo is a monorepo:

- `packages/adeu_ir`: Pydantic ADEU IR + JSON Schema export (single source of truth)
- `packages/adeu_kernel`: Deterministic checker/kernel + golden fixture harness
- `packages/adeu_lean`: Lean core semantics + theorem runner helpers (v3.1 theorem obligations)
- `packages/adeu_concepts`: Typed concept composition IR + coherence checker (v3.x concepts)
- `packages/adeu_puzzles`: Typed puzzle IR + solver translation (v3.2: Knights/Knaves)
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

`POST /concepts/propose` returns fixture-backed concept composition candidates when the input
`source_text` matches one of `examples/concepts/fixtures/*/source.txt`.

Concept composition endpoints:

- `POST /documents` ingests immutable source documents (`doc_id`, `domain`, `source_text`).
- `GET /documents` and `GET /documents/{doc_id}` list/retrieve stored documents.
- `POST /concepts/check` validates a `ConceptIR` and returns a shared `CheckReport`.
- `POST /concepts/analyze` returns `CheckReport` plus structured analysis:
  - SAT: model-conditional closure edges
  - UNSAT: one subset-minimal MIC (or `PARTIAL`/`UNAVAILABLE`)
  - SAT: forced-edge analysis via entailment checks (`base_constraints ∧ ¬edge`)
    with optional countermodel witnesses for non-forced edges
- `POST /concepts/apply_patch` applies a sandboxed patch to `ConceptIR`, rechecks it, and returns
  the same response shape as `POST /concepts/apply_ambiguity_option`.
  - `ir_hash` may be provided as a precondition; mismatches return `409 STALE_IR`.
- `POST /concepts/questions` generates deterministic, capped question/answer actions from concept
  analysis signals (MIC, forced-edge countermodels, disconnected clusters).
- `POST /concepts/tournament` ranks patch candidates in advisory mode (`replay_candidates` or
  `live_generation`) with deterministic scoring (`concepts.tscore.v1`), strict dry-run/solver
  budgets, and evidence bundles for top-ranked candidates.
- `POST /concepts/align` returns deterministic cross-artifact vocabulary suggestions
  (`merge_candidate` / `conflict_candidate`) across selected concept artifacts, with
  per-suggestion fingerprints and `alignment_stats` counts by kind.
  - Effective scope is capped at 200 artifacts after normalization; larger requests return
    `400 ALIGNMENT_SCOPE_TOO_LARGE`.
- `POST /concepts/diff` returns structural + solver-aware causal diff for two concept variants.
- `POST /explain_flip` returns a deterministic flip narrative (`check_status_flip`,
  `solver_status_flip`, cause chain, repair hints) plus the underlying `diff_report`.
  It supports `domain: "adeu" | "concepts" | "puzzles"` and inline validator-run overrides.
- `POST /concepts/artifacts` stores accepted concept artifacts (strict check on create) and persists
  linked validator runs by default.
- `GET /concepts/artifacts` and `GET /concepts/artifacts/{artifact_id}` retrieve concept artifacts.
- `GET /concepts/artifacts/{artifact_id}/validator-runs` retrieves linked solver runs.

For concept endpoints that accept source text, `doc_id` can be provided instead of `source_text`.
If both are provided, `doc_id` is authoritative and mismatched text returns `400 DOC_TEXT_MISMATCH`.

`POST /puzzles/solve` accepts a strict `KnightsKnavesPuzzle` payload and returns:

- solver status (`SAT`/`UNSAT`/`UNKNOWN`/...)
- per-person role assignments (`knight`/`knave`/`unknown`)
- underlying `ValidatorResult` evidence (model / unsat core / stats)

## Run API (OpenAI proposer)

Set `provider: "openai"` in `POST /propose` and configure:

- `OPENAI_API_KEY` (or `ADEU_OPENAI_API_KEY`) for auth
- `ADEU_OPENAI_API` backend selector (`responses` default, `chat` fallback backend)
- optional `ADEU_OPENAI_MODEL` (default: `gpt-5.2`)
- optional `ADEU_OPENAI_TEMPERATURE` (default: `0.3`, bounded `0.0..2.0`)
- optional `ADEU_OPENAI_DEFAULT_MAX_CANDIDATES` (default: `5`, bounded `1..20`)
- optional `ADEU_OPENAI_DEFAULT_MAX_REPAIRS` (default: `3`, bounded `0..10`)
- optional `ADEU_OPENAI_BASE_URL` (default: `https://api.openai.com/v1`)
- optional `ADEU_OPENAI_HTTP_TIMEOUT_SECONDS` (default: `60.0`)
- optional `ADEU_LOG_RAW_LLM=1` to include raw prompt/response in proposer logs (off by default)
- optional `ADEU_Z3_TIMEOUT_MS` (default: `3000`) for SMT validator timeout
- optional `ADEU_PERSIST_VALIDATOR_RUNS=1` to persist solver runs for `/check` (off by default)
- optional `ADEU_PROOF_BACKEND` (`mock` default, `lean` for CLI proof-check)
- optional `ADEU_LEAN_BIN` (default: `lean`, canonical)
- optional `LEAN_BIN` (alias fallback when `ADEU_LEAN_BIN` is unset)
- optional `ADEU_LEAN_TIMEOUT_MS` (default: `5000`)
- optional `ADEU_MAX_SOURCE_TEXT_BYTES` (default: `200000`)
- optional `ADEU_MAX_QUESTION_DRY_RUN_EVALS_TOTAL` (default: `20`)
- optional `ADEU_MAX_QUESTION_SOLVER_CALLS_TOTAL` (default: `40`)
- optional `ADEU_MAX_ALIGNMENT_SCOPE_ARTIFACTS` (default: `200`)
- optional `ADEU_ALIGNMENT_MAX_SUGGESTIONS_DEFAULT` (default: `100`, bounded by API lock `1..500`)
- optional `ADEU_EXPLAIN_ANALYSIS_BUDGET_DEFAULT` (default: `40`, bounded `0..200`)
- optional `ADEU_QUESTION_FORCED_BUDGET_MAX` (default: `10`)
- optional `ADEU_QUESTION_FORCED_BUDGET_DIVISOR` (default: `3`)
- optional `ADEU_QUESTION_MIC_SHRINK_ITERS_MAX` (default: `20`)
- optional `ADEU_MAX_TOURNAMENT_DRY_RUN_EVALS_TOTAL` (default: question dry-run cap)
- optional `ADEU_MAX_TOURNAMENT_SOLVER_CALLS_TOTAL` (default: question solver-call cap)
- optional `ADEU_MAX_TOURNAMENT_REPLAY_CANDIDATES` (default: `20`)
- optional `ADEU_MAX_TOURNAMENT_PATCH_OPS_PER_CANDIDATE` (default: `50`)
- optional `ADEU_MAX_TOURNAMENT_TOTAL_PATCH_OPS` (default: `200`)
- optional `ADEU_MAX_TOURNAMENT_REPLAY_PAYLOAD_BYTES` (default: `500000`)
- optional `ADEU_MAX_TOURNAMENT_TOP_K` (default: `10`)

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
  For the current v3.0 conflict witness encoding: `UNSAT` means at least one kernel-derived
  conflict candidate exists (unsat core returns a witness subset of named atoms); `SAT` means none.
- SMT output is treated as **solver evidence** (model / unsat core / stats), not as proof
  certificates. Certificates are reserved for future proof-checked backends.
- `UNKNOWN` and `TIMEOUT` map to `REFUSE` in `STRICT` mode, `WARN` in `LAX`. `INVALID_REQUEST`
  remains `ERROR` severity in both modes.
- Accepted artifacts now persist one `ProofArtifact` (`proof_id`, `backend`, `theorem_id`, status,
  `proof_hash`, inputs) per theorem obligation via a v3.1 proof-check pipeline:
  `pred_closed_world`, `exception_gating`, and `conflict_soundness`.
  The proof details include deterministic metadata (`semantics_version`, `inputs_hash`,
  `theorem_src_hash`) and `lean_version` when available.

Proof retrieval endpoint:

- `GET /artifacts/{artifact_id}/proofs`
- `GET /artifacts/{artifact_id}/validator-runs`
- `POST /artifacts`, `GET /artifacts/{artifact_id}`, and `GET /artifacts` include
  trust-lane fields: `solver_trust` and `proof_trust`.

## Run Web

```bash
cd apps/web
npm install
NEXT_PUBLIC_ADEU_API_URL=http://localhost:8000 npm run dev
```

Web routes:

- `/` ADEU Studio
- `/concepts` Concepts Studio (propose/check/analyze/compare, question loop, and tournament ranking)
- `/puzzles` Puzzle Studio (propose/check/solve/compare for knights/knaves)
- `/papers` Paper Abstract Studio (documents-first concepts workflow + cross-doc alignment)
- `/artifacts` Artifact browser

Compare panel notes:

- The shared compare panel now calls `POST /explain_flip` (single request) instead of calling
  `/diff` directly.
- It remains non-blocking: explain failures fall back to structural + available solver deltas and
  never alter checker outcomes.
