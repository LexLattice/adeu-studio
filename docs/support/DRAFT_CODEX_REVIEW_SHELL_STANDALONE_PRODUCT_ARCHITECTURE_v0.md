# Draft Codex Review Shell Standalone Product Architecture v0

Status: support note.

Authority layer: support only.

This note does not authorize implementation by itself. It records the intended product
architecture for the standalone review shell under the current two-track doctrine.

## 1. Product Thesis

The standalone review shell is not a mini ADEU Studio.

It is a workflow shell for coordinated use of:

- Codex as implementation partner
- ChatGPT as deliberation/review partner

with:

- explicit project binding
- explicit thread binding
- explicit control-plane mediation

The purpose is to improve real cognitive flow and implementation productivity by
preserving and coordinating distinct partner surfaces rather than flattening them into
one generic chat.

## 2. Key Product Claim

The product claim is not:

- “everything should become one unified super-chat”

The product claim is:

- “two distinct synthetic partners produce more value when their differences are
  preserved and coordinated through an explicit control plane”

The control plane should therefore do real work:

- bind the right project to the right threads
- preserve context locality
- reduce manual scavenging
- reduce transfer mistakes
- make handoff and synthesis explicit

## 3. Surface Doctrine

### 3.1 Left surface: Codex

The left surface should remain mostly Codex-like:

- implementation-focused
- repo-coupled
- tight loop friendly
- familiar to users already accustomed to Codex work

It may support:

- vanilla Codex-compatible runtime
- custom Codex fork runtime

If a custom fork is used, fork-native settings may be exposed in the app settings or
provider controls. Those extras are secondary, not the product thesis.

### 3.2 Right surface: ChatGPT

The right surface should remain a real ChatGPT web thread surface:

- brainstorming
- review
- critique
- architectural thinking
- world-modeling

It should not be replaced by a fake API-backed surrogate unless a later product move
selects that intentionally.

### 3.3 Middle surface: Control plane

The middle surface is the product heart.

It should own:

- project identity
- project-to-thread binding
- project-to-Codex binding
- relay state
- transfer affordances
- work tree and relevant evidence surfaces where needed
- status and history of handoffs

The control plane exists to coordinate difference, not erase it.

## 4. Workspace Model

The standalone shell should support a pluggable workspace/provider model.

Near-term provider examples:

- local workspace
- WSL workspace

Near-term Codex runtime examples:

- vanilla-compatible runtime
- custom fork runtime

The shell should own the workflow.
Providers should supply execution or transport capability.

## 5. Current Priority Surfaces

The highest-value standalone features right now are:

1. project-bound ChatGPT thread linkage
2. support for multiple relevant ChatGPT threads inside a project context
3. clear distinction between:
   - implementation thread(s)
   - review thread(s)
   - brainstorming thread(s)
   - architecture/research thread(s)
4. reduced scavenging through unrelated ChatGPT history
5. low-friction transfer between Codex and ChatGPT
6. reduced copy/paste routing mistakes

These are more important right now than exposing every ADEU-native control.

## 6. Provider Model

The standalone shell should support:

- a default Codex-compatible posture
- an optional advanced custom-fork posture

The correct mental model is similar to:

- default provider works without advanced extras
- if the selected runtime is a custom fork, the shell may surface advanced settings
  specific to that provider

This keeps the shell open to future widening without changing the main product thesis.

## 7. What The Standalone Shell Is Not

It is not currently the right place to optimize for:

- maximum ADEU control exposure
- every harness-native knob
- immediate meta-orchestrator posture
- deep bounded-Codex experimental semantics as the day-to-day default

Those belong primarily in the `odeu` experimental track until they are mature enough to
improve the standalone workflow.

## 8. Promotion Rule For ADEU Features

An ADEU-native feature should move from the `odeu` track into the standalone shell only
when it is:

- semantically stable
- understandable to the user
- worth surfacing
- clearly workflow-improving
- not merely interesting in a harness-laboratory sense

Examples of later candidate promoted modes:

- article/research mode
- legal-analysis mode
- domain-specialized relay modes

But these should land only after their semantics and UX burden are clear.

## 9. Product Roadmap Shape

### Phase 1: workflow shell

Focus:

- project binding
- thread binding
- transfer reduction
- low-friction dual-partner loop

### Phase 2: project-local thread topology

Focus:

- multiple ChatGPT thread roles per project
- better relay history
- explicit return-to-Codex conventions
- staging and review packet helpers

### Phase 3: mature ADEU feature adoption

Focus:

- selectively promote ADEU-native capabilities that improve the workflow shell without
  overloading it

## 10. Architecture Summary

The standalone shell should be understood as:

- an ADEU-derived workflow product
- not a full ADEU Studio replacement
- not a mini unified super-chat

Its native philosophy is still ADEU-like because it insists that:

- boundaries matter
- surface-conditioned roles matter
- offices should be explicit
- coordination should be explicit

But it expresses that philosophy through:

- a narrower product boundary
- a more familiar UX contract
- a cleaner distinction between mature product value and immature harness experiment
