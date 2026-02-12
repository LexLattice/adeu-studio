# Draft Continuation Paths (Post K-v0)

This document captures continuation options after the currently locked/implemented baseline:

- `LOCKED_ROADMAP_vNEXT.md`
- `LOCKED_ROADMAP_vNEXT_PLUS1.md`
- `LOCKED_ROADMAP_vNEXT_PLUS2.md`
- `LOCKED_URM_CODEX_INTEGRATION_v0.md`
- `LOCKED_CROSS_REPO_IMPORTS_v0.md`
- `LOCKED_INSTRUCTION_KERNEL_v0.md`

Status: draft planning only (not frozen).  
Goal: detail practical next-path options before choosing a single implementation sequence.

## Baseline Snapshot

Current baseline appears to include:

- Tri-lane legal/concepts/puzzles trust and determinism contracts.
- Questions + patch/apply + tournament + bridge + document workflows.
- URM + Codex local runtime with event envelope/replay/summaries/capability lattice.
- Instruction Kernel v0 (policy IR, evaluator, traces/events, generated views, proof attachments).

Net effect: architecture is now strongly governance-capable. Next work should choose one primary product vector.

## Repo-Grounded Edges (From Latest Review Pass)

1. Instruction policy is currently intentionally minimal:
   - `policy/odeu.instructions.v1.json` mostly demonstrates baseline allow-after-hard-gates.
   - Real governance still primarily sits in capability lattice + approval gates.
   - Implication: next policy increment should include at least one deny lemma and one require lemma.

2. Repo-root discovery assumptions can be brittle:
   - Some test/tool paths rely on `.git` discovery.
   - This can break in zip exports or non-standard checkout layouts.
   - Implication: prefer multi-anchor repo discovery (`.git` OR `pyproject.toml` OR `policy/` marker).

3. Policy hash/load lifecycle should be explicit as policy size grows:
   - Current flow recomputes hash in evaluator paths.
   - Implication: formalize load/cache/reload semantics before policy complexity increases.

4. Provider normalization still leaves high-level dynamics under-modeled:
   - Envelopes and replay are strong, but many provider events remain low-semantic.
   - Implication: Path 2 should promote structured runtime semantics (steer/sub-agent lifecycle) early.

## Shared Cross-Path Locks

- No solver semantic changes unless explicitly versioned and locked.
- Trust lanes remain explicit and non-collapsed.
- Additive API-first evolution by default.
- Determinism and replayability remain first-class.
- Any new policy/runtime behavior must emit evidence artifacts.

## Path 1: Instruction Kernel v1 (Governance/Productization)

### Goal

Move from "policy evaluator exists" to "policy operations are production-grade and auditable".

### Why This Path

- Highest leverage for operational reliability.
- Protects system behavior as complexity and contributors grow.
- Improves safe velocity for all other paths.

### Scope

1. Policy operations CLI extensions:
   - `policy eval`
   - `policy diff`
   - optional `policy explain`
2. Versioned policy profiles/scopes:
   - `safe_mode`, `default`, `experimental`
3. Decision forensics:
   - deterministic incident packet from event stream + policy trace
4. Rollout controls:
   - canary policy hash selection
   - explicit rollback to prior policy hash

### Locks

- Policy ops never mutate runtime state unless command explicitly says so.
- `policy diff` must be semantic diff, not raw text diff.
- Incident packets are reproducible from recorded evidence only.
- No policy hot-reload from remote sources in this phase.

### Acceptance

- Same `(policy_hash, input_context_hash)` gives same decision and trace.
- `policy diff` ignores non-semantic text fields (for example `message`).
- Incident reconstruction from saved evidence reproduces decision code and matched rules.
- Rollback to previous policy hash is deterministic and observable in events.

### Risks

- Overbuilding policy tooling before user-facing value moves.
- Scope creep into full policy management platform.

### Suggested PR Slices

1. `policy: add eval command and deterministic report schema`
2. `policy: add semantic diff command and tests`
3. `urm: add policy hash rollout/canary wiring`
4. `forensics: add deterministic incident packet generation`

## Path 2: Codex Dynamics v1 (Agentic Runtime Expansion)

### Goal

Use Codex advanced runtime surfaces (in-flight steering, sub-agents, app discovery) under existing deontic/evidence controls.

### Why This Path

- Directly advances URM as an orchestration runtime, not only a static wrapper.
- High product signal for "interactive + delegated + auditable" AI workflows.

### Scope

1. In-flight steering:
   - route support for `turn/steer`
   - policy-gated steering intent classes
2. Sub-agent lifecycle:
   - spawn, message, resume, wait, close
   - parent-child evidence binding and budgets
3. App connector discovery:
   - discover installed app surfaces
   - capability-filtered exposure to roles
4. Runtime governance:
   - delegation depth limits
   - cost/time/token budgets per session and per child agent

### Locks

- Parent agent remains accountable; child actions inherit deontic constraints.
- Sub-agent actions must produce stream-bound evidence refs.
- Steering is advisory/input-shaping only unless an action path is explicitly authorized.
- Missing runtime capabilities degrade to deterministic deny/disable, never emulate.

### Acceptance

- Sub-agent lifecycle events replay deterministically with parent linkage intact.
- Mid-turn steering updates are logged and reflected in subsequent trace events.
- App connectors are discoverable but filtered by capability lattice + instruction policy.
- Budget breaches terminate/deny deterministically with stable codes.

### Risks

- Complexity jump in session management and UI state.
- Protocol drift in app-server and experimental methods.

### Suggested PR Slices

1. `urm-codex: add turn steer support with policy gates`
2. `urm-codex: add sub-agent lifecycle endpoints/events`
3. `urm-codex: add app discovery and capability-filtered exposure`
4. `urm-codex: add delegation and budget guardrails`

## Path 3: Semantic Depth v1 (Words -> Concepts -> Repair Quality)

### Goal

Increase semantic quality of questioning/repair flows without changing solver semantics.

### Why This Path

- Closest to core product thesis: reverse-engineering concepts from language.
- Converts strong infrastructure into higher-signal user outcomes.

### Scope

1. Bridge-loss-aware analysis:
   - carry bridge loss signals into question/tournament evidence
2. Question quality v3:
   - rationale enrichment with bridge/dependency context
   - stricter dedupe and impact scoring
3. Tournament scoring v2:
   - objective vector includes coherence gain and evidence quality
4. Cross-artifact coherence checks:
   - stable alignment diagnostics across document/version sets

### Locks

- Bridge loss remains informational, not solver-semantic.
- No LLM-only scoring gate can override deterministic checker/solver evidence.
- Ranking/scoring remains versioned and deterministic for replay mode.
- Trust lanes must not be collapsed into a single aggregate score.

### Acceptance

- Question/tournament fixtures show measurable redundancy reduction.
- Replay mode yields stable ranking and rationale order.
- Bridge-loss references are present when applicable and absent otherwise.
- Cross-document alignment outputs remain permutation-invariant.

### Risks

- Quality work can look subjective without strong eval harness.
- UI complexity can outpace evidence clarity.

### Suggested PR Slices

1. `questions: add bridge-loss-aware rationale metadata`
2. `tournament: add deterministic score v2 objective vector`
3. `eval: add quality fixtures and dashboard deltas`
4. `alignment: add cross-artifact coherence diagnostics`

## Path 4: Portability Proof v1 (Second Domain Pack)

### Goal

Prove URM + instruction kernel portability by standing up a second domain pack with minimal core changes.

### Why This Path

- Validates architecture thesis beyond ADEU domain.
- Exposes hidden ADEU-coupling early.

### Scope

1. Select second domain:
   - recommended pilot: `paper.abstract` workflow extension
   - alternative: compact domain from prior repos
2. Implement `packages/urm_domain_<newdomain>`:
   - templates
   - tool adapters
   - evidence bindings
3. Reuse existing runtime surfaces:
   - event envelope, policy evaluator, capability lattice, instruction kernel
4. Produce transfer report:
   - what was reused unchanged
   - what required extension/versioning

### Locks

- No ADEU-specific assumptions in `urm_runtime`.
- Domain-specific semantics stay in domain pack boundary.
- Trust taxonomy labels remain shared/common.
- Any new generic runtime primitive must be justified by at least two domains.

### Acceptance

- Second domain completes a full run with evidence + replay + policy enforcement.
- No forked event or error taxonomy for the new domain.
- Instruction policy works unchanged for baseline controls.
- Transfer report is reproducible and tied to evidence artifacts.

### Risks

- Domain selection can stall progress if too broad.
- Temptation to over-generalize before second real use-case pressure.

### Suggested PR Slices

1. `domain: scaffold urm_domain_<newdomain> with templates and tool adapters`
2. `runtime: remove discovered ADEU coupling points`
3. `api/web: add minimal route/panel for second domain workflow`
4. `docs: add portability transfer report with evidence refs`

## Sequencing Options (Decision Aid)

### Option A (Governance-first)

1. Path 1
2. Path 2
3. Path 3
4. Path 4

Use when reliability and operating discipline are top priority.

### Option B (Agentic-first)

1. Path 2
2. Path 1
3. Path 3
4. Path 4

Use when Codex runtime dynamics are the primary differentiator now.

### Option C (Product-value-first)

1. Path 3
2. Path 2
3. Path 1
4. Path 4

Use when question/repair quality is the immediate north star.

### Option D (Portability-first)

1. Path 4
2. Path 1
3. Path 2
4. Path 3

Use when proving URM as reusable substrate is the immediate strategic goal.

## Recommendation For Discussion (Not a Freeze)

Use a hybrid kickoff with a portability bias:

1. Path 1 (thin slice only: policy eval/diff)
2. Path 2 (thin slice only: steering + one sub-agent cycle)
3. Path 4 (small second-domain portability proof)
4. Path 3 (semantic depth after dynamics + portability proof)

Why this order:

- Path 1 thin slice gives safe policy iteration and semantic change visibility.
- Path 2 thin slice gives the biggest immediate runtime/product signal.
- Path 4 validates URM portability before deeper ADEU-specific optimization.
- Path 3 then compounds quality on top of proven governance + dynamics + portability.

## Smallest Real Next Slice (Proposed)

If you want one compact kickoff milestone before freezing a new locked roadmap:

1. Policy tooling thin slice:
   - add `policy eval` deterministic report
   - add `policy diff` semantic diff (ignore non-semantic fields)
2. Codex dynamics thin slice:
   - add `turn/steer` policy-gated endpoint + events
   - add one parent->child sub-agent cycle with:
     - depth cap = 1
     - max children = 1
     - inherited deontics + evidence linkage
3. Portability pressure test:
   - scaffold one minimal second domain pack (`paper.abstract`-style workflow)
   - verify no runtime taxonomy fork and no ADEU assumptions leak
