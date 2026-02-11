# Locked Cross-Repo Imports (v0)

This document freezes a focused import slice from two earlier LexLattice repos:

- `tf-lang`
- `true-modules`

Goal: adopt proven determinism/evidence/orchestration patterns in ODEU without changing solver semantics.

Status: additive-only spec.

## Global Locks

- No solver semantic changes (ADEU/Concepts/Puzzles).
- No trust-lane taxonomy changes (`mapping_trust`, `solver_trust`, `proof_trust` remain source of truth).
- New telemetry/evidence APIs are additive-only.
- Determinism is mandatory for all generated lists, event sequences, and summaries.
- All new file outputs must be reproducible from the same inputs.
- Codex protocol drift must be tolerated: URM never assumes provider event shapes are stable.

## Source Patterns Imported (Reference)

- From `tf-lang`:
  - canonicalization/oracle discipline (`crates/oracles/core`, `docs/oracles/*.md`)
  - capability/effect lattice thinking (`docs/l0-effects-lattice.md`, `policy/*.json`)
  - proof artifact posture (`docs/l0-proofs.md`, `packages/prover/z3.mjs`)
- From `true-modules`:
  - strict event envelope and replay model (`docs/events.md`, `spec/events.schema.json`)
  - evidence bindings (`docs/evidence-bindings.md`)
  - headless orchestration runbook (`docs/headless-cloud.md`)
  - timeline/replay/export UX (`apps/workflow-console`)

## X1) URM Event Envelope v1 (Imported from true-modules)

### Goal

Make URM streams first-class, replayable, and machine-verifiable.

### Lock

Define and enforce a stable event envelope for URM events:

- `schema: "urm-events@1"`
- `event: str`
- `ts: ISO8601`
- `seq: int` (strictly monotonic per stream)
- `stream_id: str` (for example `copilot:<session_id>` or `worker:<run_id>`)
- `source: { component: str, version: str, provider: "codex"|str }`
- `context: { session_id|run_id, role, endpoint, ir_hash? }`
- `detail: object` (event-specific payload)

Two-stream persistence lock:

- Persist raw provider output separately as `codex_raw.ndjson` (raw-first policy still applies).
- Persist normalized envelope stream as `urm_events.ndjson` (`urm-events@1`).
- Replay/SSE/timeline tooling uses `urm_events.ndjson` as canonical.
- Raw stream remains available for forensic/audit inspection.

Timestamp lock:

- `ts` is server receive time at ingestion.
- Replay emits stored `ts` verbatim (never rewritten at replay time).
- Test fixtures use fixed timestamps.

Event naming lock:

- Session lifecycle: `SESSION_START|SESSION_READY|SESSION_STOP|SESSION_FAIL`
- Worker lifecycle: `WORKER_START|WORKER_PASS|WORKER_FAIL|WORKER_CANCEL`
- Policy/approval: `MODE_CHANGED|APPROVAL_ISSUED|APPROVAL_CONSUMED|APPROVAL_REVOKED|POLICY_DENIED`
- Tool/evidence: `TOOL_CALL_START|TOOL_CALL_PASS|TOOL_CALL_FAIL|EVIDENCE_WRITTEN`

Core `detail` minima lock (allow additional properties):

- `SESSION_*`: at least `{ status }`
- `WORKER_*`: at least `{ worker_id, status }`
- `MODE_CHANGED`: at least `{ writes_allowed }`
- `APPROVAL_*`: at least `{ approval_id, action_kind }`
- `TOOL_CALL_*`: at least `{ tool_name }`
- `EVIDENCE_WRITTEN`: at least `{ evidence_id, path }`

### Acceptance

- Validation command passes on all generated URM NDJSON streams.
- `seq` monotonicity violations fail validation deterministically.
- Same run replay produces identical timeline ordering.

## X2) Evidence Binding for Decisions (Imported from true-modules)

### Goal

Bind user-facing outcomes (questions, answers, patch applies) to concrete evidence artifacts.

### Lock

For each persisted decision object (or decision-like response payload), add additive bindings:

- `evidence_refs: list[EvidenceRef]`
- `EvidenceRef = { kind: "event"|"run"|"validator"|"proof"|"artifact", ref: str, note?: str }`

Canonical `ref` format lock:

- `event:<stream_id>#<seq>`
- `run:<worker_run_id>`
- `validator:<validator_run_id>`
- `proof:<proof_id>`
- `artifact:<artifact_id>`

Binding minimums:

- Applying a patch must bind at least one `event` and one `validator`/`artifact` ref.
- A resolved question must bind at least one upstream analysis/question event ref.

### Acceptance

- API tests confirm required refs are present for patch-apply success paths.
- Missing required refs on persistence paths fail closed with deterministic error code.

## X3) URM Capability Lattice v1 (Imported from tf-lang)

### Goal

Replace ad-hoc permission checks with a versioned, explicit capability lattice.

### Lock

Introduce a static policy document (JSON) for URM tools:

- `policy/urm.capability.lattice.v1.json`
- `policy/urm.allow.v1.json`

Capabilities must be explicit for:

- read state
- run analysis/check
- spawn worker
- mutate/apply patch
- approve write
- manage session lifecycle

Decision lock:

- Tool execution checks must consult lattice + allow policy + runtime mode + approval.
- Denials must return stable URM policy codes.
- Deny-first evaluation order is frozen:
  1. capability exists in lattice
  2. allow policy grants capability
  3. runtime mode permits action
  4. approval exists and is valid/consumed atomically (when required)
  5. execute action

### Acceptance

- Policy test matrix covers allow/deny outcomes for all role x action pairs.
- No write-capable action succeeds when policy denies, even if client requests it.

## X4) URM Replay/Summary Commands (Imported from true-modules)

### Goal

Provide deterministic diagnostics for long Copilot/worker sessions.

### Lock

Add CLI/script utilities:

- `events validate --in <ndjson> [--strict]`
- `events replay --in <ndjson> [--out <file>]`
- `events summary --in <ndjson> [--out-json <file>] [--out-md <file>]`

Summary metrics (minimum):

- event counts by type
- first failure by category
- session/run duration
- tool call counts and error counts

### Acceptance

- Replay output is stable for identical NDJSON input.
- Summary JSON fields are stable and schema-validated.
- CI uploads replay/summary artifacts when URM tests run.

## X5) Determinism Oracles for ODEU Core Paths (Imported from tf-lang)

### Goal

Codify deterministic behavior as explicit oracles (not only endpoint tests).

### Lock

Create deterministic oracle fixtures for:

- bridge loss report generation
- questions generation/ranking
- patch apply core (success/failure ordering)

Oracle families:

- `idempotence`: same input twice -> same canonical output
- `conservation`: expected invariant fields unchanged across allowed transforms
- `ordering`: sorted tie-break outputs remain stable under permutation

### Acceptance

- Oracle test suite runs in CI and produces machine-readable reports.
- Any nondeterministic drift fails with precise diff output.

## Implementation Sequence (Frozen)

1. X1 URM Event Envelope v1
2. X4 Replay/Summary commands
3. X3 Capability lattice v1
4. X2 Evidence binding for decisions
5. X5 Determinism oracles

## Commit Plan (Small Green Commits)

1. `urm-events: add urm-events@1 schema and strict emitter fields`
2. `urm-events: add validate/replay/summary tooling and tests`
3. `policy: add capability lattice/allow docs and enforcement tests`
4. `evidence: add decision evidence_refs and persistence checks`
5. `oracles: add determinism oracle fixtures for bridge/questions/patch`

## Trust-Policy Note

- `kernel_only|solver_backed|proof_checked` semantics are unchanged.
- `mapping_trust` semantics are unchanged.
- This slice improves evidence traceability and runtime policy clarity only.
