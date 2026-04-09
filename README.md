# ADEU Studio

> A governed machine for producing, validating, executing, and packaging high-trust artifacts.

ADEU Studio is a docs-governed monorepo for turning source text into typed artifacts, validating them deterministically, executing bounded workflows, and keeping evidence attached to every meaningful step.

This front page stays intentionally compact. Deeper runtime and operator detail lives in the operator reference.

It is built around the ADEU frame:

| Axis | What It Governs |
|------|------------------|
| **Ontology** | Typed entities, package boundaries, artifact families |
| **Epistemics** | Deterministic validation, solver evidence, proof lanes, provenance |
| **Deontics** | Capability policy, locked scope, approval gates, fail-closed behavior |
| **Utility** | Arc-scoped delivery, dashboards, stop-gates, governed improvement |

## At A Glance

| Surface | Purpose |
|---------|---------|
| `packages/adeu_ir` + validation packages | Typed IR, deterministic kernel checks, solver and proof lanes |
| `packages/adeu_core_ir`, `adeu_concepts`, `adeu_puzzles`, `adeu_explain` | Higher-level artifact families and analysis workflows |
| `packages/urm_runtime` + `urm_domain_*` | Policy-governed orchestration, workers, events, runtime tools |
| `packages/adeu_agent_harness` | Taskpack pipeline: compile -> sign -> run -> verify -> package |
| `packages/adeu_semantic_*` + `adeu_commitments_ir` | Docs-to-contract semantic compiler lane |
| `apps/api` | FastAPI integration surface |
| `apps/web` | Next.js operator-facing UI |
| `docs/` + `artifacts/` | Locked arcs, stop-gates, assessments, dashboards, closeout evidence |

## Why It Is Different

- Artifacts are typed first, not inferred ad hoc at the edge.
- Validation is deterministic and fail-closed.
- Governance is part of the runtime, not an after-the-fact process layer.
- The repo is built to improve under explicit constraints instead of informal drift.

## Start Here

Bootstrap and run the default local gate:

```bash
make bootstrap
make check
```

`make bootstrap` also installs the repo-managed Git hooks path. After any local
`git merge`, the `post-merge` hook runs `make merge-post-check` so merge-result
lint regressions are caught before the next push.

Run the API:

```bash
.venv/bin/pip install -e apps/api
.venv/bin/python -m uvicorn adeu_api.main:app --reload --port 8000
```

Run the web UI:

```bash
cd apps/web
npm install
NEXT_PUBLIC_ADEU_API_URL=http://localhost:8000 npm run dev
```

The API supports `fixture`, `openai`, and `codex` provider modes.

## Useful Local Commands

Build the same quality dashboard artifact used by CI:

```bash
.venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard.json
```

Run determinism oracles and emit a machine-readable report:

```bash
.venv/bin/python apps/api/scripts/run_determinism_oracles.py --out artifacts/determinism_oracles.json
```

Validate a sample URM event stream:

```bash
.venv/bin/events validate --in apps/api/tests/fixtures/urm_events/sample_valid.ndjson --strict
```

Need more operational depth, provider settings, or runtime notes:

- [OPERATOR_REFERENCE_v0.md](docs/OPERATOR_REFERENCE_v0.md)

## Human-Facing Surfaces

Selected web routes:

- `/` for the main ADEU Studio flow
- `/concepts` for concept composition and coherence workflows
- `/puzzles` for puzzle propose and solve flows
- `/papers` for paper and document-first workflows
- `/artifacts` for stored artifact browsing
- `/copilot` for the URM copilot console

Selected API families:

- ADEU propose, check, and artifact storage
- concepts propose, check, analyze, patch, questions, tournament, align, and diff
- puzzles propose and solve
- explain flip narratives
- URM copilot, worker, and tool routes

## Current Shape

- 17 Python packages
- 54 JSON schemas under `spec/`
- 6 runtime policy files under `policy/`
- 71 locked continuation docs through `v71`

Stop-gate, assessment, and closeout coverage exists across many arcs and should be checked per arc rather than assumed to be uniform.

## License

This repository is licensed under the Apache License 2.0. See [LICENSE](LICENSE).

## Read Next

- [ARCHITECTURE_ADEU_STUDIO_v0.md](docs/ARCHITECTURE_ADEU_STUDIO_v0.md) for the working system architecture draft
- [OPERATOR_REFERENCE_v0.md](docs/OPERATOR_REFERENCE_v0.md) for local runtime, provider, and operator detail
- [REPO_ATLAS.md](REPO_ATLAS.md) for repo navigation
- [ADEU Recursive Self-Improvement Policy.md](ADEU%20Recursive%20Self-Improvement%20Policy.md) for the constitutional governance model
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS*.md` for per-arc scope commitments
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS*.md` for per-arc go or no-go decisions
