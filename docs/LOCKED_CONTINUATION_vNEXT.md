# Locked Continuation vNext (Candidate Freeze)

This document freezes the next continuation arc after:

- `LOCKED_INSTRUCTION_KERNEL_v0.md`
- `LOCKED_CROSS_REPO_IMPORTS_v0.md`
- `LOCKED_ROADMAP_vNEXT_PLUS2.md`

Status: candidate freeze for review iteration.

## Global Locks

- No solver semantic changes in this arc.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- New behavior is additive-only unless explicitly marked breaking (none in this arc).
- Determinism and replayability are mandatory for all new outputs.
- All policy/runtime decisions must emit auditable evidence artifacts.
- New `/urm/...` endpoints in this arc must be idempotent with `client_request_id`.
- New lifecycle stop/cancel operations must be idempotent on retry and keep existing termination policy semantics (grace then force kill).
- Evidence stream targeting must be explicit:
  - policy-eval events append to the same stream as the governed action
  - steering and parent lifecycle events append to parent copilot stream
  - child lifecycle/run events append to child stream with parent linkage
- If a parent stream is unavailable/closed while a child is active:
  - append lifecycle policy/runtime events to a deterministic fallback stream `urm_audit:<parent_session_id>`.
- Any wall-clock/random/external nondeterministic mode must be explicit and excluded from replay-mode acceptance tests.
- New N2 endpoint namespace is frozen:
  - `POST /urm/copilot/steer`
  - `POST /urm/agent/spawn`
  - `POST /urm/agent/{child_id}/cancel`

## Chosen Arc (Frozen)

Implementation order is frozen to:

1. `N1` Instruction Kernel tooling thin slice
2. `N2` Codex dynamics thin slice
3. `N3` Portability proof thin slice
4. `N4` Semantic depth follow-on

Rationale:

- `N1` provides safe policy iteration controls (`eval` + semantic `diff`).
- `N2` adds the highest product/runtime signal (steering + delegation).
- `N3` pressure-tests URM portability before deeper domain optimization.
- `N4` then improves question/repair quality on top of proven runtime foundations.

## N1) Instruction Kernel Tooling (Thin)

### Goal

Make policy changes operable and auditable, not just load-time validated.

### Scope

- Add `policy eval` command:
  - deterministic decision report for supplied policy + context.
- Add `policy diff` command:
  - semantic diff over canonical policy form (ignores non-semantic fields like `message`).
- Add as subcommands under the existing `policy` CLI entrypoint.
- CLI input/output surface:
  - `policy eval --policy <path> --context <path> [--evaluation-ts <UTC_Z>] [--use-now] [--out <file>]`
  - `policy diff --old <path> --new <path> [--out <file>]`

### Locks

- Commands are read-only and never mutate runtime state.
- `policy diff` must compare semantic canonical form, not raw JSON text.
- Output schemas are versioned and deterministic.
- `policy eval` timestamp behavior is frozen:
  - deterministic mode requires explicit `--evaluation-ts` OR uses fixed default `1970-01-01T00:00:00Z`
  - wall-clock mode is explicit opt-in (`--use-now`) and is non-deterministic by contract
- `policy eval` report schema is frozen as `instruction-policy-eval@1` and includes at minimum:
  - `policy_hash`, `input_context_hash`, `decision`, `decision_code`, `matched_rule_ids`, `required_approval`, `evaluator_version`
- `policy diff` output must be structured:
  - `added_rules`, `removed_rules`, `modified_rules`
  - `modified_rules` lists semantic field deltas only (`priority`, `when`, `then`, `code`, `kind`, `rule_version`)
  - `message` must never be treated as semantic delta
- `policy explain` remains explicit non-goal for this arc.

### Acceptance

- Same policy/context input yields byte-identical `policy eval` output.
- Rule-order permutations and `message`-only edits produce no semantic delta in `policy diff`.
- Failures use existing URM error envelope conventions.
- Golden fixtures are required for deterministic tooling:
  - `examples/eval/policy_eval/**`
  - `examples/eval/policy_diff/**`

## N2) Codex Dynamics (Thin)

### Goal

Expose core dynamic interaction surfaces with strict policy/evidence controls.

### Scope

- Add policy-gated `turn/steer` support.
- Add one parent->child sub-agent lifecycle:
  - spawn -> send input -> wait -> close.
- Add child cancel endpoint:
  - `POST /urm/agent/{child_id}/cancel`.
- Record parent-child linkage in URM events/evidence.

### Locks

- Steering is advisory/input-shaping only unless separately authorized.
- Delegation depth cap: `1`.
- Max children per parent session: `1`.
- Child runs inherit parent deontic constraints and budgets.
- Missing capability degrades to deterministic deny/disable.
- Stable N2 error code set is frozen:
  - `URM_STEER_DENIED`
  - `URM_CHILD_DEPTH_EXCEEDED`
  - `URM_CHILD_LIMIT_EXCEEDED`
  - `URM_CHILD_SPAWN_FAILED`
  - `URM_CHILD_CANCEL_ALREADY_TERMINAL`
- Steer requests must target stable identity:
  - `target_turn_id` (preferred) or server-resolved `last_turn`
  - steer events include `target_turn_id`, `steer_intent_class`, `steer_payload_hash`
  - if `last_turn` cannot be resolved deterministically, deny with stable code (do not infer).
- Child spawn snapshots parent governance state:
  - inherited `policy_hash`, mode, capability facts, and budget snapshot at spawn time
  - budget snapshot shape includes:
    - `max_solver_calls`, `max_duration_secs`, `max_token_budget`, `remaining_parent_duration_secs`
- `experimentalApi`-gated methods are hard-denied with stable code when gate is off (no best-effort emulation).
- `experimentalApi` method mapping for this thin slice is frozen:
  - `turn/steer`, `spawn_agent`, `send_input`, `wait`, `close_agent`
- Capability lattice additions are required:
  - `urm.turn.steer`
  - `urm.agent.spawn`
  - `urm.agent.cancel`
- Steer rate limiting lock:
  - `max_steer_per_turn = 5` default, deterministic deny beyond cap.

### Acceptance

- Parent-child lifecycle replays deterministically from evidence.
- Steering events are visible, ordered, and tied to affected turns.
- Denials for unsupported/blocked dynamics emit stable policy/error codes.
- Child cancel is idempotent and emits deterministic terminal lifecycle events.

## N3) Portability Proof (Thin)

### Goal

Validate that URM runtime and instruction kernel are not ADEU-coupled.

### Scope

- Add minimal second domain pack:
  - frozen pilot: `paper.abstract`.
- Implement minimal tool adapters + template pack.
- Run one end-to-end flow using existing URM primitives and policies.
- Package layout is frozen:
  - `packages/urm_domain_paper/`

### Locks

- No fork of event taxonomy or error envelope for the second domain.
- Domain-specific semantics remain in domain pack boundary.
- New generic runtime primitives require cross-domain justification.
- `paper.abstract` thin slice is closed-world in this phase:
  - operates on provided local text only
  - no web retrieval, no citation-oracle retrieval
- Minimal typed tool surface for portability proof:
  - `paper.ingest_text`
  - `paper.extract_abstract_candidate`
  - `paper.check_constraints`
  - `paper.emit_artifact`
- Domain adapter registration mechanism is frozen:
  - use a runtime domain tool registry/protocol in `urm_runtime`
  - avoid hardcoded ADEU-only dispatch expansion.
- Capability lattice actions for paper domain are required:
  - `paper.ingest_text`
  - `paper.extract_abstract_candidate`
  - `paper.check_constraints`
  - `paper.emit_artifact`

### Acceptance

- Second domain run emits valid `urm-events@1` with replay/summaries.
- Instruction policy applies unchanged to baseline controls.
- Transfer report documents:
  - reused components
  - coupling points removed
  - intentionally domain-specific code retained
- Transfer report is evidence-backed and includes:
  - touched runtime primitives
  - ADEU couplings removed with file references
  - domain-only additions constrained to domain pack boundary
- Domain isolation test is required:
  - import-audit proving `urm_runtime` has no new `adeu_*` runtime coupling from this slice.

## N4) Semantic Depth (Follow-on)

### Goal

Improve question/tournament signal quality without changing solver semantics.

### Scope

- Bridge-loss-aware question/tournament metadata.
- Deterministic tournament score v2 objective vector.
- Cross-artifact coherence diagnostics expansion:
  - vocabulary drift detection
  - suggestion stability across refreshes
  - term-use consistency checks

### Locks

- Bridge loss stays informational (no solver-semantic effect).
- Replay mode remains deterministic and versioned.
- LLM-only scoring cannot override checker/solver evidence.
- Tournament score version is frozen to:
  - `concepts.tscore.v2`
- Score v2 tie-break order is frozen:
  - rank by objective vector (lexicographic, descending) then `stable_id` (ascending)
- Score/weight/version metadata must be emitted with each ranking artifact.
- Bridge-loss additive field shape is frozen:
  - `bridge_loss_signals: list[{signal_kind, affected_anchors, severity}]`
- If LLM-derived scoring conflicts with deterministic checker/solver evidence:
  - LLM score is recorded as evidence only
  - it cannot alter deterministic precedence dimensions used for final ordering

### Acceptance

- Eval fixtures show reduced redundancy and stable ranking in replay mode.
- Bridge-loss fields appear only when applicable and remain deterministic.
- Cross-document outputs preserve permutation invariance.
- Ranking artifacts include explicit score-version metadata and deterministic tie-break provenance.
- Quality delta measurement uses prior locked baseline fixtures in:
  - `examples/eval/questions/**`
  - `examples/eval/tournament/**`

## Commit Plan (Small Green Commits)

1. `policy: add eval command and deterministic report schema`
2. `policy: add semantic diff command and tests`
3. `urm-codex: add turn steer support with policy gates`
4. `urm-codex: add minimal parent-child lifecycle with depth/child caps`
5. `urm-codex: add idempotent child cancel and lifecycle terminal events`
6. `runtime: add domain tool registry/protocol and import-audit test`
7. `domain: scaffold minimal second domain pack and adapters`
8. `docs: add evidence-backed portability transfer report`
9. `semantic: add bridge-loss-aware question/tournament metadata`
10. `semantic: add deterministic tournament score v2 and eval updates`

## Test/CI Strategy Locks

- Each N1-N4 slice must include deterministic fixture coverage and CI invocation docs.
- Replay-mode acceptance tests must not use wall-clock dependent modes.
- Feature-flag rollout lock for N2 dynamics:
  - `URM_ENABLE_STEER_V1` and `URM_ENABLE_SUBAGENT_V1`
  - default off until both route and replay tests are green.

## Exit Criteria (Arc Complete)

- `N1` through `N3` pass and are merged with green CI.
- `N4` has at least one deterministic quality improvement slice merged.
- No trust-lane regression and no solver-semantics delta introduced.
