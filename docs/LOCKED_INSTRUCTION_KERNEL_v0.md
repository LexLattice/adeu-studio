# Locked Instruction Kernel v0 (Frozen)

This document freezes a focused slice to move agent instructions from prose-first guidance
to policy-first, machine-checkable ODEU lemmas.

Goal: keep instructions executable, auditable, replayable, and eventually proof-attachable.

Status: additive-only spec, no solver semantics changes.

## Global Locks

- No solver semantic changes (ADEU/Concepts/Puzzles).
- No trust-lane taxonomy changes (`mapping_trust`, `solver_trust`, `proof_trust`).
- Existing URM error envelope and idempotency behavior remain unchanged.
- Policy decisions must be deterministic for identical `(policy_hash, input_context)`.
- Human-readable instruction docs become generated views, not authoritative sources.

## Codex 0.99 Capability Matrix (Frozen Assumptions)

This section freezes the Codex runtime surfaces this spec relies on.
If a capability is unavailable at runtime, URM must degrade safely (deny or disable), never infer behavior.

| Capability | 0.99 Surface | Use in ODEU |
| --- | --- | --- |
| In-flight steering | `turn/steer` | Mid-turn user guidance without starting a new turn |
| Sub-agents | `spawn_agent`, `send_input`, `resume_agent`, `wait`, `close_agent` | Structured delegation and resumable collaboration |
| App connectors | `app/list`, `app/list/updated` | App discovery for tool/domain expansion |
| Worker event stream | `codex exec --json` | Raw event ingestion and deterministic normalization |
| Worker schema constraint | `codex exec --output-schema <file>` | Typed artifact contracts for pipeline-worker role |
| Worker safety controls | `--sandbox`, approval policy controls | Default read-only and explicit write gates |
| Requirements feed | `configRequirements/read` | Runtime policy bounds (sandbox/approval/network) |
| Notification control | `initialize.capabilities.optOutNotificationMethods` | Stream shaping for clients without changing semantics |
| Experimental gate | `initialize.capabilities.experimentalApi` | Explicit opt-in for unstable protocol surfaces |
| Schema generation | `codex app-server generate-json-schema`, `generate-ts` | Version-pinned client/protocol typing |

### Capability Degrade Lock

- If `app-server` capability is missing/unavailable: force worker-only mode.
- If a listed method is unavailable: return deterministic policy/code denial, do not emulate.
- If experimental capability is disabled: reject experimental methods with explicit policy code.
- Runtime capability facts must be probe-backed:
  - startup emits `CAPABILITIES_SNAPSHOT` with discovered methods/flags/version
  - `capability_present(...)` inputs are derived only from probe output (never from static docs)

### Capability Source Grounding

Frozen against Codex `rust-v0.99.0` in:
- `/home/rose/work/codex/fork/codex-rs/app-server/README.md`
- `/home/rose/work/codex/fork/codex-rs/app-server-protocol/src/protocol/common.rs`
- `/home/rose/work/codex/fork/codex-rs/app-server-protocol/src/protocol/v2.rs`
- `/home/rose/work/codex/fork/codex-rs/exec/src/cli.rs`
- `/home/rose/work/codex/fork/codex-rs/exec/src/lib.rs`

## K0) Design Boundary (Frozen)

### K0.1 Policy source of truth
- Authoritative source is a versioned policy IR file:
  - `policy/odeu.instructions.v1.json`
- Prose docs are derived renderings:
  - `docs/generated/AGENTS_POLICY_VIEW.md`
  - `docs/generated/SKILLS_POLICY_VIEW.md`
- Derived docs are CI-guarded and non-authoritative.

### K0.2 Non-goals (v0)
- No natural-language policy parsing.
- No full theorem prover in the runtime path.
- No policy hot-reload from remote sources.
- No multi-tenant policy model.

## K1) Instruction IR v1 (Lemma Set)

### K1.1 Decidable fragment lock
Use a restricted rule fragment only:
- finite typed facts + stratified rules
- no recursion through negation
- no unbounded quantification
- no side effects during evaluation

This keeps evaluation terminating and deterministic.

Resource caps are frozen in v1:
- `max_rules = 500`
- `max_expr_depth = 16`
- `max_expr_nodes = 2_000`
- cap violations fail closed with deterministic code `URM_POLICY_CAP_EXCEEDED`.
- cap-exceeded responses use standard URM error envelope with business-rule HTTP `400`.

### K1.2 Rule model lock
Each rule record must include:
- `rule_id: str` (stable, unique)
- `rule_version: int`
- `priority: int` (lower value = higher priority)
- `kind: "deny" | "allow" | "require" | "derive"`
- `when: PredicateExpr` (pure boolean expression over typed context)
- `then: RuleEffect`
- `message: str`
- `code: str` (stable machine code)

Field semantics lock:
- `message` is human-facing only and non-semantic.
- `message` is excluded from decision equality checks and semantic hash inputs.
- `code` is machine-facing and semantic.
- `rule_version` is semantic and participates in semantic canonicalization and hash derivation.

`derive` restriction lock (v1):
- `derive` may only emit `emit_advisory` or `set_warrant_invalid`.
- derived outputs cannot be referenced by `when` predicates in v1.
- evaluator must enforce a derive-firewall check at policy-load time:
  - if any `when` references derive-only outputs/facts, policy load fails closed.

Effect cardinality lock (v1):
- each rule has a single `then: RuleEffect` only.
- multi-effect rules are out of scope for v1 and require schema/version update.

### K1.3 PredicateExpr AST lock
`PredicateExpr` must be JSON AST only (no string expressions).

Allowed nodes:
- boolean operators:
  - `{ "op": "and", "args": [PredicateExpr, ...] }`
  - `{ "op": "or", "args": [PredicateExpr, ...] }`
  - `{ "op": "not", "arg": PredicateExpr }`
- atom call:
  - `{ "atom": "<name>", "args": [...] }`

Additional AST constraints:
- no implicit precedence; grouping only through explicit AST nesting.
- unknown operators/atoms are forbidden by schema validation.

### K1.4 Predicate and effect lock
Predicate atoms are typed and closed over a frozen vocabulary in v1:
- role/session: `role_is`, `mode_is`, `session_active`
- capability/policy: `capability_present`, `capability_allowed`
- action metadata: `action_kind_is`, `action_hash_matches`
- approval: `approval_present`, `approval_valid`, `approval_unexpired`, `approval_unused`
- evidence/warrant: `has_evidence_kind`, `warrant_is`

Effect vocabulary:
- `deny_action`
- `allow_action`
- `require_approval`
- `set_warrant_invalid`
- `emit_advisory`

Capability fact source lock:
- `capability_present` and `capability_allowed` facts in `PolicyContext` must be derived from
  the same probe-backed lattice/allow evaluation used by hard-gate steps 1-2.
- no secondary capability evaluator is allowed.

Action hash recipe lock:
- `action_hash_matches` must use the shared canonical action hash recipe:
  - `action_hash = sha256(canonical_json({action_kind, action_payload}))`.
- this recipe must be shared with approval hashing logic (no alternate implementations).

Approval atom semantics lock:
- `approval_valid` means: action hash matches recipe and approval shape/signature checks pass.
- `approval_unexpired` means: `evaluation_ts <= expires_at`.
- `approval_unused` means: `consumed_at IS NULL AND revoked_at IS NULL`.
- "valid approval available" means conjunction of:
  - `approval_present AND approval_valid AND approval_unexpired AND approval_unused`.

### K1.5 Conflict resolution lock
Decision semantics are frozen:
1. evaluate all matching rules
2. sort matches by `(priority ASC, rule_id ASC)`
3. apply `deny_overrides` globally
4. if no deny, apply explicit requires, then allow
5. if no allow, default deny with `URM_POLICY_DENIED`

Matching semantics lock:
- a rule is `matching` iff its `when` evaluates to `true` under `PolicyContext`.
- only matching rules contribute effects.
- `matched_rule_ids` includes all matching rules regardless of `kind`
  (`deny|allow|require|derive`) in sorted match order.
- final decision semantics still consider deny/require/allow as defined in conflict resolution;
  `derive` remains non-decisioning in v1.

`require_approval` aggregation lock:
- if any matched rule emits `require_approval`, then `required_approval = true`.

Decision code lock:
- fallback deny must emit `decision_code = "URM_POLICY_DENIED"`.
- rule-driven deny must emit that matched deny rule's `code` as `decision_code`.

### K1.6 Policy hash lock
- `policy_hash = sha256(canonical_json(policy_semantic_form))`
- `policy_semantic_form` is canonicalized before hashing:
  - rules sorted by `(priority ASC, rule_id ASC, rule_version ASC)`
  - map keys sorted; no whitespace; UTF-8
  - stable list ordering for all semantic lists
- non-semantic fields (for example `message`) are excluded from semantic form.
- Every decision output and policy event includes `policy_hash`.

Canonicalizer implementation lock:
- policy and context canonicalization must use the same shared canonicalizer implementation.
- no endpoint-local canonicalization variants are allowed.
- runtime should use the existing shared canonicalizer (`urm_runtime.hashing.canonical_json`)
  for both policy and context semantic forms.

### K1.7 Policy context lock
Evaluation input must use a typed context object:
- `PolicyContext` with:
  - role, mode, action_kind, action_hash
  - capability facts
  - approval state facts
  - evidence/warrant facts
  - evaluation timestamp

PolicyContext builder lock:
- runtime evaluation must obtain context from a single builder path in `urm_runtime`
  (no endpoint-specific context assemblers).
- the builder is responsible for injecting probe-backed capability facts and approval facts.

PolicyContext capability facts shape lock:
- `capabilities_present` must be a sorted string list in context semantic form.
- `capabilities_allowed` must be a sorted string list in context semantic form.
- map/set representations for these facts are forbidden in semantic form.

Timestamp representation lock:
- `evaluation timestamp` must be RFC3339/ISO8601 in UTC with `Z` suffix
  (example: `2026-02-12T09:10:00Z`).
- naive timestamps are invalid.

Hashing:
- `input_context_hash = sha256(canonical_json(policy_context_semantic_form))`
- time-dependent checks (for example expiry) use `evaluation timestamp` from context, not ambient wall clock.

Timestamp authority lock:
- `evaluation timestamp` is server-assigned.
- clients cannot provide or override `evaluation timestamp` in runtime policy evaluation paths.

## K2) Evaluator Integration in URM

### K2.1 Evaluation order lock (deny-first kernel)
For action execution, this order is frozen:
1. capability exists in lattice
2. allow policy grants capability
3. runtime mode permits action
4. approval precheck: if approval is provided, validate shape/state/hash (no consumption)
5. instruction-kernel rule evaluation
6. if `required_approval = true` and no valid approval is available, deny with `URM_APPROVAL_REQUIRED`
7. execute or deny; if execution proceeds and approval is required, consume approval atomically with execution

Hard-gate monotonicity lock:
- Steps 1-4 are hard gates.
- The instruction kernel can only further restrict outcomes (deny/require).
- The instruction kernel cannot convert an upstream deny into allow.

### K2.2 Decision trace lock
Each evaluated action returns/stores:
- `decision: "allow" | "deny"`
- `decision_code: str`
- `policy_hash: str`
- `input_context_hash: str`
- `matched_rule_ids: list[str]` (sorted by evaluation order)
- `required_approval: bool`
- `trace_version: "odeu.instruction-trace.v1"`
- `policy_schema_version: "odeu.instructions.schema.v1"`
- `policy_ir_version: "odeu.instructions.v1"`
- `evaluator_version: str`

`matched_rule_ids` lock:
- `matched_rule_ids` must equal the `rule_id` values from the sorted matching-rule list
  (the same list used by conflict resolution ordering), not insertion order.

### K2.3 Event emission lock
Emit deterministic URM events for policy evaluation:
- `POLICY_EVAL_START`
- `POLICY_EVAL_PASS`
- `POLICY_DENIED`

`detail` minimum:
- `policy_hash`
- `decision_code`
- `matched_rule_ids`

Compatibility lock:
- `POLICY_DENIED` is the canonical deny event name for summaries and validators.
- `POLICY_EVAL_PASS` is emitted only when final decision is `allow`.
- all policy-evaluation events must be emitted as `urm-events@1` envelopes
  (no parallel event schema for instruction-kernel events).

Event stream target lock:
- policy-evaluation events must be appended to the same stream as the governed action:
  - session stream for copilot actions
  - worker stream for worker actions
- if no session/run stream exists, append to dedicated `urm_audit` stream keyed by `session_id`.

Advisory emission lock:
- `emit_advisory` effects are retained even on final deny.
- advisory payloads must include final decision context (`decision`, `decision_code`).

## K3) Generated Instruction Views

### K3.1 Generated docs lock
Add a renderer that produces:
- `docs/generated/AGENTS_POLICY_VIEW.md`
- `docs/generated/SKILLS_POLICY_VIEW.md`

These files are informative views only.

### K3.2 Drift guard lock
CI must fail if generated view files drift from source policy IR:
- deterministic render command
- no manual edits accepted in generated files
- renderer must enforce stable ordering and normalized newlines.
- renderer must emit LF (`\n`) newlines on all platforms.

## K4) Proof-Attachable Pilot (Narrow)

### K4.1 Pilot obligations lock
Attach proof artifacts for two invariants first:
1. `no_write_without_mode_and_approval`
2. `approval_single_use_atomicity`

Proof artifact compatibility lock:
- instruction-kernel proof attachments must reuse existing `adeu_ir.ProofArtifact` shape:
  - `proof_id`
  - `backend`
  - `theorem_id`
  - `status`
  - `proof_hash`
  - `inputs[]`
  - `details`
- no parallel proof artifact schema is introduced in this slice.

### K4.2 Trust boundary lock
- Proof pilot does not change runtime decision semantics.
- No `proof_checked` promotion changes in this slice.
- Proof artifacts are evidence attachments only.
- when a proof is present, decision evidence must include:
  - `evidence_refs += { kind: "proof", ref: "proof:<proof_id>" }`
- `evidence_refs` must reuse the existing cross-repo EvidenceRef shape:
  - `{ kind, ref, note? }`

## K5) Schema + Storage Locks

### K5.1 Policy schema
Add JSON schema:
- `spec/instruction_policy.schema.json`

Validation rules:
- duplicate `rule_id` forbidden
- unknown predicate/effect atoms forbidden
- missing `code` forbidden
- invalid PredicateExpr AST shape forbidden
- resource-cap exceedance forbidden (`max_rules`, `max_expr_depth`, `max_expr_nodes`)

Policy-load failure code lock (business-rule HTTP 400 + standard URM error envelope):
- `URM_POLICY_INVALID_SCHEMA` for schema/AST violations
- `URM_POLICY_DERIVE_FIREWALL_VIOLATION` for derive-firewall violations
- `URM_POLICY_CAP_EXCEEDED` for resource-cap violations

### K5.2 Policy validation tooling lock
Add deterministic validation command:
- `policy validate --in policy/odeu.instructions.v1.json [--strict]`

Validation output requirements:
- machine-readable JSON report with stable field ordering
- deterministic issue ordering
- strict mode must include derive-firewall checks
- zero side effects

### K5.3 Storage fields (additive)
For policy decisions/evidence metadata, add:
- `policy_version`
- `policy_hash`
- `trace_version`

No existing fields removed or repurposed.

## K6) Acceptance Tests (Frozen)

### K6.1 Determinism tests
- same input + same policy hash -> identical decision + matched rule IDs.
- permutation of independent rule declaration order -> identical results.
- semantic no-op text changes (`message`) do not change `policy_hash`.
- deterministic replay path uses fixed server-test `evaluation timestamp` fixture input.

### K6.2 Deny precedence tests
- conflicting allow/deny matches must produce deny.
- fallback deny occurs when no allow is matched.

### K6.3 Approval gating tests
- write action denied when mode disallows.
- write action denied when approval invalid/expired/consumed.
- valid approval enables action only once.
- approval is consumed only when execution proceeds (never consumed on denied actions).

### K6.4 Generated-doc drift tests
- renderer output must be stable and CI-verified.

### K6.5 Policy validation tests
- derive-firewall violations are rejected by `policy validate --strict`.
- action hash recipe parity matches approval hashing path.

## Implementation Sequence (Frozen)

1. K1 Instruction IR schema + evaluator core
2. K2 pre-step: `PolicyContext` builder and hard-gate integration seam in URM
3. K2 URM integration + decision traces/events
4. K3 generated AGENTS/SKILLS policy views + CI drift check
5. K4 proof-attachment pilot for two invariants

## Commit Plan (Small Green Commits)

1. `policy: add odeu.instructions.v1 schema and deterministic evaluator core`
2. `policy: add deterministic policy validate command with strict derive-firewall checks`
3. `urm: add PolicyContext builder and wire instruction-kernel decision traces/events`
4. `docs: generate AGENTS/SKILLS policy views and add drift guard`
5. `proof: attach pilot artifacts for approval/mode invariants (no trust promotion changes)`

## Trust-Policy Note

- `kernel_only|solver_backed|proof_checked` semantics remain unchanged.
- `mapping_trust` semantics remain unchanged.
- This slice upgrades instruction governance and auditability only.
