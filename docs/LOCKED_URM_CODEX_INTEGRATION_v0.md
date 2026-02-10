# Locked URM + Codex Integration (Local/Self-Hosted Solo)

Status: implemented on `main` (February 10, 2026). This doc is now a baseline contract reference.

Initial implementation sequence completed:

- Step 1: `packages/urm_runtime` skeleton + models + role registry
- Step 2: storage/evidence tables + raw JSONL file writer (disk-first)
- Step 3: worker runner (`codex exec --json ...`) + fixtures + tests
- Step 4: app-server host + event bus + SSE + replay
- Step 5: `packages/urm_domain_adeu` tool adapters
- Step 6: `/copilot` route + evidence viewer
- Step 7: hardening (limits, approvals, drift handling, security)

New behavior beyond these locks should be introduced via a new locked roadmap doc.

---

## 0) Repo-grounded constraints (non-negotiable)

### C0.1 Package placement
- Keep runtime orchestration out of `apps/api/src/adeu_api/main.py`.
- Required package split:
  - `packages/urm_runtime/` (portable, domain-agnostic runtime)
  - `packages/urm_domain_adeu/` (ADEU-specific adapters/templates)

### C0.2 Trust taxonomy freeze
- Reuse existing trust lanes exactly; no near-duplicate enums:
  - `solver_trust`
  - `proof_trust`
  - `mapping_trust`
- New epistemic labels must be additive and not conflict with trust lanes.

### C0.3 Storage pattern freeze
- Reuse existing transactional discipline:
  - `PRAGMA foreign_keys=ON`
  - `BEGIN IMMEDIATE`
  - rollback-on-error
- Large JSONL evidence is file-based. DB stores metadata and pointers.

### C0.4 Streaming infra
- SSE is net-new and must be implemented explicitly when we reach streaming steps.

---

## 1) Integration model (two runtimes)

### R1.1 Copilot runtime (interactive)
- Transport: `codex app-server` subprocess
- Protocol: JSONL over stdio (request/response/notifications)
- Lifecycle: long-lived, keyed by `copilot_session_id`

### R1.2 Worker runtime (pipeline)
- Transport: `codex exec` subprocess (short-lived)
- Default safety flags:
  - `--json`
  - `--sandbox read-only`
  - `--ask-for-approval never`
- Raw JSONL always persisted. Normalization is tolerant.

---

## 2) Capability probe (startup lock)

### P2.1 Probe required
Probe and persist Codex capabilities at startup:
- `codex --version`
- `codex exec --help` (flags like `--json`, `--output-schema`)
- `codex app-server --help`
- optional: `codex app-server generate-json-schema`

Persist:
- DB row: `urm_codex_capability_probe`
- file: `apps/api/var/urm/codex_probe/<timestamp>.json`

Failure policy:
- Codex missing: disable URM-Codex features cleanly.
- `exec` available, `app-server` unavailable: worker-only mode.
- Missing optional flags: degrade gracefully; no server crash.

### P2.2 Smoke probe depth
Probe includes short smoke checks (timeout ~3-5s):
- `codex exec --json` trivial invocation
- `codex app-server` spawn/readiness check then terminate

Persist smoke outcomes with:
- `ok` flag
- duration
- exit/timeout status
- redacted stderr snippet

---

## 3) Session model (copilot)

### S3.1 Session entity
Minimum fields:
- `copilot_session_id` (UUID)
- `role` = `copilot`
- `status` = `starting|running|stopped|failed`
- `started_at`, `ended_at`
- `codex_version`, `capability_probe_id`
- `pid`, `bin_path`
- `raw_jsonl_path` (relative path under evidence root)
- `last_seq` (server-assigned monotonic sequence)
- `writes_allowed` (server-authoritative mode bit)

### S3.2 Session policy
- Default: single active copilot session.
- Starting a new session gracefully stops previous one.
- Multi-session is out of scope until explicitly re-locked.

### S3.3 App-server viability gate
- On start, wait up to `APP_SERVER_READY_SECS = 5` for readiness.
- If process exits early or readiness times out:
  - session `failed`
  - code `URM_CODEX_APP_SERVER_UNAVAILABLE`
  - capability flag `app_server_unavailable=true`
  - system enters worker-only mode
- Readiness (v0): first stdout line OR explicit ready event.

---

## 4) Evidence persistence (raw-first, disk)

### E4.1 Raw-first invariant
- Persist raw JSONL first.
- DB stores metadata/pointers/normalized summaries.

### E4.2 File layout
- Root: `apps/api/var/evidence/codex/`
- Copilot: `apps/api/var/evidence/codex/copilot/<copilot_session_id>.jsonl`
- Worker: `apps/api/var/evidence/codex/worker/<worker_run_id>.jsonl`
- Probe snapshots: `apps/api/var/urm/codex_probe/<timestamp>.json`

### E4.3 DB entities (minimum semantics)
- `urm_codex_capability_probe`
- `urm_copilot_session`
- `urm_worker_run`
- `urm_evidence_record` (or equivalent embedded metadata)
- `urm_approval`
- `urm_schema_ledger` (schema versioning)

### E4.4 Raw-line truncation lock
- If raw line exceeds `MAX_LINE_BYTES`:
  - persist truncated prefix (`MAX_LINE_BYTES`)
  - persist marker metadata with:
    - `original_bytes`
    - `bytes_dropped`
    - `sha256_full_line`
    - `truncated=true`
- Never silently drop lines.

### E4.5 Path safety lock
- Store relative evidence paths only.
- Resolve against configured evidence root and enforce containment.
- Evidence APIs accept `evidence_id`, never arbitrary file path.

---

## 5) Event normalization (tolerant, non-failing)

### N5.1 Parser behavior
- Parser never crashes a run/session due to unknown shape.
- Unknown events -> `unknown_event`.
- Parse failures -> `parse_error` with raw line preserved.

### N5.2 Normalized event shape
- `seq` (server-assigned, monotonic per session/run)
- `ts` (server receive time)
- `source` = `copilot_app_server|worker_exec`
- `event_kind` = known kind or `unknown_event|parse_error`
- `payload` (best effort)
- `raw_line` (always)

---

## 6) Warrant vs trust (strict separation)

### W6.1 Warrant labels
Claim-level warrant is additive:
- `observed|derived|checked|hypothesis|unknown`

### W6.2 Non-conflation rule
- Warrant is not trust.
- `checked` requires attached evidence refs.
- Trust lanes stay unchanged and are not inferred automatically from warrant.

---

## 7) Approval model (write-gated actions)

### A7.1 Approval object
Fields:
- `approval_id` (UUID)
- `action_kind`
- `action_hash`
- `created_at`, `expires_at`
- `granted_by_user` (bool)
- `revoked_at` (nullable)
- `consumed_at` (nullable)
- `consumed_by_evidence_id` (nullable)
- `session_id`

### A7.2 Approval policy
- Default single-use.
- Valid iff not expired/revoked/consumed and `action_hash` matches.
- Consumption is atomic (`BEGIN IMMEDIATE`).
- Reuse attempt returns `URM_APPROVAL_INVALID`.

---

## 8) Read-only enforcement and mode control

### D8.1 Worker safety defaults
- Worker launches with read-only sandbox + no approvals.

### D8.2 Tool surface enforcement
- Copilot acts only via URM tools.
- Enforcement checks:
  - role allowlist
  - server-side `writes_allowed`
  - approval requirement/presence

### D8.3 Mode authority lock
- `writes_allowed` is server-side state (not UI-only).
- Endpoint: `POST /urm/copilot/mode`.

---

## 9) SSE contract (replayable, auditable)

Endpoint:
- `GET /urm/copilot/events?session_id=<id>&after_seq=<n>&provider=codex`

Rules:
- Server-owned monotonic `seq`.
- Replay from `after_seq`.
- Heartbeat every 10s.
- Ring-buffer replay first, then persisted source fallback.
- Canonical audit record remains raw JSONL.

Frame types:
- `codex_event`
- `heartbeat`
- `session_status`

---

## 10) Resource limits and retention (defaults frozen)

- `MAX_LINE_BYTES = 1_000_000`
- `MAX_EVIDENCE_FILE_BYTES = 200_000_000`
- `MAX_SESSION_DURATION_SECS = 21600`
- `MAX_CONCURRENT_WORKERS = 2`
- `MAX_REPLAY_EVENTS = 10000`
- `APPROVAL_TTL_SECS = 120`
- `RETENTION_DAYS = 14`
- `MAX_TOTAL_EVIDENCE_BYTES = 2_000_000_000`

On limit breach:
- emit error event
- terminate affected process safely
- set terminal status with explicit code
- write terminal marker if possible

GC policy:
- purge oldest files to budget
- keep DB row tombstone fields:
  - `purged_at`
  - `purge_reason`
  - `raw_jsonl_path` cleared or tombstoned

---

## 11) Error model and HTTP semantics

### L1 HTTP validation freeze
- Request schema errors use FastAPI default `422`.
- Business/policy errors use URM envelope + `400/404/409/...` as applicable.

### L2 Error envelope freeze
URM business/policy errors:

```json
{
  "detail": {
    "code": "URM_...",
    "message": "human safe string",
    "context": {}
  }
}
```

### L3 Frozen error codes
Copilot/session:
- `URM_CODEX_BIN_NOT_FOUND`
- `URM_CODEX_START_FAILED`
- `URM_CODEX_APP_SERVER_UNAVAILABLE`
- `URM_CODEX_PROTOCOL_PARSE_ERROR`
- `URM_CODEX_SESSION_LIMIT_EXCEEDED`
- `URM_CODEX_SESSION_TERMINATED`
- `URM_CODEX_SSE_REPLAY_FAILED`
- `URM_SESSION_STOPPED`

Worker:
- `URM_WORKER_START_FAILED`
- `URM_WORKER_TIMEOUT`
- `URM_WORKER_OUTPUT_LIMIT_EXCEEDED`
- `URM_WORKER_JSON_PARSE_DEGRADED`
- `URM_WORKER_EXIT_NONZERO`
- `URM_WORKER_CANCELLED`

Policy/approval:
- `URM_POLICY_DENIED`
- `URM_APPROVAL_REQUIRED`
- `URM_APPROVAL_INVALID`
- `URM_APPROVAL_EXPIRED`

Storage/idempotency:
- `URM_EVIDENCE_WRITE_FAILED`
- `URM_DB_TX_FAILED`
- `URM_IDEMPOTENCY_KEY_CONFLICT`
- `URM_EVIDENCE_PURGED`
- `URM_NOT_FOUND`

---

## 12) Endpoint namespace and idempotency

### M2 Vendor-neutral URM namespace
All v0 endpoints are URM-first with provider metadata:
- `POST /urm/copilot/start`
- `POST /urm/copilot/send`
- `POST /urm/copilot/stop`
- `POST /urm/copilot/mode`
- `GET /urm/copilot/events`
- `POST /urm/worker/run`
- `POST /urm/worker/{id}/cancel`

`provider="codex"` is required in request/query metadata.

### M4 Stop/cancel idempotency
- Stop/cancel retry on terminal resource returns 200 with `idempotent_replay=true`.
- Unknown resource -> 404 `URM_NOT_FOUND`.

### M6 Client idempotency keys
For start/send/run:
- request includes `client_request_id` (UUID)
- same endpoint + same request id + same payload hash -> replay 200 with original identifiers and `idempotent_replay=true`
- same request id + different payload hash -> 409 `URM_IDEMPOTENCY_KEY_CONFLICT`

---

## 13) Process lifecycle and restart semantics

### L5 Termination policy
- Terminate gracefully, wait `GRACE_SECS=5`, then force kill if needed.
- Cross-platform abstraction required (POSIX/Windows).
- Persist termination marker with method/grace/exit details.

### L7 Restart recovery
- After API restart, previously `running` sessions are marked terminal (`stopped` or `failed`) with `URM_CODEX_SESSION_TERMINATED`.
- No subprocess reattach in v0.
- Replay remains possible from persisted evidence.

### L8 Single-process server lock
- v0 is single API process owner.
- Multi-worker process ownership is out of scope.

---

## 14) Security locks

- Never spawn with `shell=True`.
- Codex bin configurable via `ADEU_CODEX_BIN` (default `codex`).
- No credential storage in ADEU DB.
- Minimal worker environment; avoid leaking host secrets.
- Redact sensitive env values from persisted metadata.

---

## 15) Template/version metadata lock

Task/artifact metadata must include:
- `template_id`
- `template_version`
- `schema_version`
- `domain_pack_id`
- `domain_pack_version`

If `--output-schema` is unavailable:
- run without it
- validate extracted artifact server-side
- mark schema-invalid candidates explicitly; never treat as valid artifact silently.

---

## 16) Testability and CI locks

- CI must run without real Codex auth/network.
- Use fake subprocess/golden JSONL fixtures:
  - `tests/fixtures/codex_exec/*.jsonl`
  - `tests/fixtures/codex_app_server/*.jsonl`
- Required tests:
  - raw evidence file persisted
  - tolerant normalization survives unknown events
  - SSE replay is monotonic with heartbeats
  - policy gating error codes are correct
  - approval lifecycle (required/issued/consumed/expired)
  - idempotency behavior
  - restart/session recovery behavior

---

## 17) UI scope lock (v0)

- Add dedicated route: `/copilot`.
- No global omnipresent panel in v0.
- Show:
  - session status
  - streaming timeline
  - evidence link/viewer
  - mode state (read-only vs writes-enabled)

If app-server is unavailable, UI explicitly shows worker-only mode.

---

## 18) Runtime artifacts in git

- Add `apps/api/var/` to `.gitignore`.
- Runtime artifacts are not source-controlled.

---

## 19) Implementation sequencing (frozen)

1. `packages/urm_runtime` skeleton + models + role registry
2. storage/evidence schema + disk-first raw JSONL writer
3. worker runner (`codex exec --json ...`) + tests/fixtures
4. app-server host + event bus + SSE + replay
5. `packages/urm_domain_adeu` tool adapters
6. `/copilot` route + evidence viewer
7. hardening (limits, approvals, drift handling, security)

Completion note:
- All steps above are implemented on `main`.
- This section remains as sequence history, not as a pending go-ahead gate.

---

## 20) Acceptance criteria (v0)

1. Backend startup records Codex capability probe.
2. Copilot session start can stream events when app-server is viable.
3. Copilot can call safe read-only tools.
4. Worker run persists raw JSONL evidence and artifact candidate outputs.
5. No writes happen without server-side writes mode + approval object.
6. Raw JSONL evidence remains available (or clearly tombstoned if purged).
