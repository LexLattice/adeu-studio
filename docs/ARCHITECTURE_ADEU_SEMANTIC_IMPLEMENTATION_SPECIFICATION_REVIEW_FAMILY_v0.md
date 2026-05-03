# Architecture ADEU Semantic Implementation Specification Review Family v0

Status: architecture / decomposition note for planned `V83`.

Authority layer: architecture / decomposition.

This architecture note does not authorize implementation by itself. It defines
the intended family boundary for `V83` so starter locks can select bounded
implementation slices without turning semantic intent review into code edits,
runtime execution, worker dispatch, product authorization, release, or general
artifact truth.

## Family Thesis

`V83` should institutionalize the upstream reasoning step that transforms
intent into implementation specifications. The family should make the semantic
contract, edge decomposition, artifact obligations, drift risks, and handoff
surface explicit before any later family or slice writes code.

The practical goal is not to improve syntax generation. Syntactically valid
code is no longer the primary bottleneck. The bottleneck is whether the code
that gets written is a sound projection of the intended semantic structure.

`V83` may say:

- a source-bound semantic intent contract exists;
- an intent has explicit scope, success horizon, non-goals, authority posture,
  and source refs;
- an implementation target would need specific semantic edges preserved;
- a concrete artifact obligation exists for code, schema, fixture, test,
  documentation, UX, workflow, provider profile, or other bounded repo
  artifact;
- an ambiguity, missing source, contradictory edge, authority gap, or semantic
  drift risk blocks implementation-spec readiness;
- a projection packet can hand off to a later implementation or work-packet
  surface as review-only pressure.
- a model, agent, reviewer, or tool-assisted run produced an
  implementation-spec candidate with bounded prompt / profile / source
  provenance and candidate-only authority posture.

`V83` must not say:

- code was implemented;
- files may be edited outside a later active lock;
- a work packet has been executed;
- an implementation is correct because an intent spec exists;
- a generated implementation-spec candidate is semantic truth,
  implementation correctness, or work-packet authority;
- passing tests prove semantic intent preservation by themselves;
- a Morphic UX example is a universal implementation contract;
- an external direct-harness profile grants repo runtime authority;
- product, release, runtime, dispatch, connector, endpoint, corpus-ingestion,
  graph-memory, benchmark-truth, or recursive-policy authority exists;
- `V84` or any later family is selected.

## General Frame

`V83` is a standalone bridge family. It is intentionally narrower than the
larger theory of digital artifact projection.

The general theory is:

```text
domain intent
  -> semantic closure
  -> typed artifact obligations
  -> concrete artifact projection
```

The concrete artifact may be code, UI, a paper, a legal clause, a theorem, a
research question, a benchmark design, a product spec, a governance rule, a
dataset boundary, or an adjudication report. `V83` does not select all of that
territory. It selects the repo-practical bridge from intent to implementation
specification.

Morphic UX v2 is one downstream instantiation:

```text
semantic intent contract
  -> semantic supply / entity / interaction / geometry / style obligations
  -> UI implementation spec
```

The direct OAI harness docs are another downstream instantiation:

```text
semantic intent contract
  -> provider capability / event / evidence / authority obligations
  -> direct runtime harness spec
```

Those examples inform `V83`; they are not the umbrella and do not authorize
runtime changes.

## Source Stack Consumed

`V83` consumes:

- `V68` source / authority / namespace cartography;
- `V69` source-bound candidate identity;
- `V70` review classification and gap posture;
- `V71` ratification-review and authority-profile posture;
- `V72` containment, effect, rollback, and commit/release boundary posture;
- `V73` outcome and recommendation posture;
- `V74` operator projection and visibility posture;
- `V75` dispatch-review and worker-planning posture;
- `V76` reconciliation / arbiter and dissent posture;
- `V77` runtime-permission review, command preflight, telemetry, rollback, and
  authority posture;
- `V78` runtime execution authority review, tool-use permission envelope,
  command-scope boundary, exception, readiness, and handoff posture;
- `V79` controlled execution review, run-plan review, tool-invocation-plan
  review, effect-monitoring, exception, summary, and handoff posture;
- `V80` external branch activation review, data/tool/submission/result
  boundary posture, exceptions, summary, and handoff posture;
- `V81` cross-corpus governance request, source, boundary, provenance,
  authority-gap, exception, summary, and handoff posture;
- `V82` corpus-ingestion authority-review request, source, preflight,
  connector-boundary, authority-review, exception, summary, and handoff
  posture.

No upstream stage becomes implementation authority by being consumed.

## External Support Substrate

Two local direct-harness docs are relevant support substrate:

- `/home/rose/work/LexLattice/codex-review-shell-direct/docs/META_ORCHESTRATOR_LOOP_ODEU_SPEC.md`
- `/home/rose/work/LexLattice/codex-review-shell-direct/docs/OAI_CODEX_UPSTREAM_ODEU_PROFILE.md`

The first doc contributes the workflow distinction:

```text
routable evidence != valid evidence
object-level validity != workflow-transition authority
worker prose != transition event
```

The second doc contributes the capability-evidence distinction:

```text
codex_source_inferred != provider_served authority
tool call proposal != tool execution permission
raw provider event != local UX reduction
```

`V83` should absorb these as support doctrine for intent-to-spec projection.
It should not implement the direct harness, provider profile, meta-orchestrator
runtime, controller, work packet executor, or tool broker.

These support sources must be concrete before lock-level use. A future starter
should either cite repo-owned support artifacts, represent the local docs as
external support rows with import posture, or record explicit absence markers.
It should not reconstruct them from memory.

## Family Slices

### `V83-A`: Semantic Intent Contract Intake

Starter surfaces:

- `repo_semantic_intent_contract@1`
- `repo_intent_source_index@1`
- `repo_intent_non_implementation_guardrail@1`

Purpose:

- record source-bound intent contracts with scope, success horizon, non-goals,
  constraints, authority posture, and artifact-family target;
- index repo, operator, support, external, dogfood, and absence sources with
  authority-layer and currentness posture;
- index model/agent-generated spec candidates, prompt context, profile refs,
  reviewer amendments, and operator revisions as candidate-only sources;
- split intent recordability from semantic-spec eligibility so absence,
  support context, or generated candidate rows do not become semantic closure;
- preserve non-implementation guardrails before edge decomposition,
  obligation maps, projection packets, or handoffs exist.

Forbidden:

- edge decomposition rows;
- artifact obligation maps;
- drift / ambiguity registers;
- implementation-spec projection packets;
- work-packet handoffs;
- implementation, code edits, command execution, worker dispatch, PR creation,
  commit, merge, release, product authorization, runtime authority, or graph
  authority.

### `V83-B`: Edge Decomposition And Artifact Obligations

Later surfaces:

- `repo_intent_edge_decomposition@1`
- `repo_artifact_obligation_map@1`
- `repo_semantic_drift_ambiguity_register@1`

Purpose:

- decompose intent into semantic objects, relations, constraints, non-goals,
  authority edges, and validation needs;
- map each edge into concrete artifact obligations for code, schema, fixture,
  test, documentation, UX, provider profile, workflow, or support artifact
  work;
- bind acceptance evidence to semantic edges and validation needs rather than
  treating passing tests as general semantic preservation;
- preserve ambiguity, conflict, missing source, and semantic drift risks.

Forbidden:

- projection packets;
- work-packet handoffs;
- declaring an implementation target ready despite unresolved blockers;
- treating an obligation map as code correctness;
- implementing code or modifying runtime surfaces.

### `V83-C`: Implementation-Spec Projection And Handoff

Later surfaces:

- `repo_implementation_spec_projection_packet@1`
- `repo_intent_to_work_packet_handoff@1`
- `repo_semantic_implementation_spec_family_closeout_alignment@1`

Purpose:

- project released `V83-A` and `V83-B` substrate into bounded
  implementation-spec packets;
- record projection provenance, review checklist posture, and quality gates
  for human/model/agent/tool-assisted spec candidates;
- hand off later work-packet pressure without executing it;
- close `V83` as semantic implementation specification review only.

Forbidden:

- worker assignment or dispatch execution;
- meta-orchestrator runtime mutation;
- implementation work;
- PR creation, commit, merge, or release;
- product, runtime, external, connector, corpus-ingestion, benchmark,
  graph-memory, or recursive-policy authority;
- selecting `V84`.

## Required Boundary Distinctions

`V83` must keep these distinctions machine-checkable:

- intent contract is not implementation authority;
- source-bound intent is not semantic closure by itself;
- support context is not lock authority;
- external local docs are support sources unless imported into repo source rows;
- operator preference is not scoped intent without non-goal and constraint
  posture;
- model proposal is not intent truth;
- model/agent generated spec candidate is not implementation truth;
- prompt context is not semantic closure;
- edge decomposition is not artifact obligation by itself;
- artifact obligation is not implementation;
- implementation-spec projection is not code correctness;
- a work-packet handoff is not work-packet execution;
- routable evidence is not valid evidence;
- audit recommendation is not transition authority;
- provider/source-inferred capability is not runtime authority;
- Morphic UX doctrine is not UI runtime behavior;
- tests passing is not semantic intent preservation unless mapped to the
  relevant edges;
- handoff is not target-family completion.
- quality gate readiness is not permission to implement without a later lock.

## Negative Laws

- "Looks right" is not intent preservation.
- "Compiles" is not semantic alignment.
- "Tests pass" is not semantic closure unless the tests bind to intended
  edges.
- "The model said done" is not implementation evidence.
- "The model generated a spec" is not semantic closure.
- "The agent generated a work packet" is not work-packet authority.
- "The auditor can route it" is not object-level validity.
- "The meta-orchestrator advanced it" is not technical correctness.
- "Codex source inferred it" is not provider capability authority.
- "Morphic UX example shows it" is not a universal UI law.
- "The spec exists" is not permission to edit files.
- "The handoff exists" is not worker dispatch.

## Package Boundary

Primary implementation should remain in `packages/adeu_repo_description`
because `V83` is still repo-grounded review metadata about intent,
implementation-spec posture, and handoff readiness. It is not a live
meta-orchestrator, a work-packet executor, a code generator, a product UI, a
provider runtime, or a graph-query runtime.

If later work becomes a general digital artifact projection engine, live
workflow controller, meta-orchestrator runtime, direct OAI harness, product UI,
or graph memory system, it should split away rather than expanding
repo-description by implication.
