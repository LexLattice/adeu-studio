# Draft Codex Review Shell Two-Track Doctrine v0

Status: support note.

Authority layer: support only.

This note does not authorize implementation by itself. It records the current working
separation between:

- the `odeu` / ADEU-native experimental track
- the standalone review-shell product track

## 1. Direct Answer

The review-shell effort should proceed on two distinct tracks that share some substrate
but do not share the same UX contract.

Shared substrate:

- custom Codex fork may be used in both tracks
- ChatGPT remains a real browser-embedded ChatGPT surface
- both tracks remain ADEU-derived in the broad sense that they make cognitive
  boundaries and office boundaries explicit

Distinct UX contracts:

- `odeu` track:
  - harness-first
  - ADEU-native
  - experiment-facing
  - deep knobs and unstable orchestration controls may be exposed directly
- standalone track:
  - product-first even if still internal-only and experimental
  - workflow-first
  - mostly familiar Codex-style and ChatGPT-style surfaces
  - deep ADEU controls remain secondary unless mature enough to improve the product

## 2. Why The Split Matters

Trying to do both jobs in one shell creates the wrong pressure:

- daily implementation work gets taxed by immature ADEU control complexity
- ADEU control experiments lose isolation
- it becomes harder to tell whether a failure is:
  - orchestration immaturity
  - product UX failure
  - context-management immaturity
  - pairing/handoff failure

The split keeps each track honest.

## 3. `odeu` Track

Purpose:

- experiment with Codex bound to ADEU harness
- evolve bounded Codex toward a meta-orchestrator posture
- expose deep control-plane semantics directly
- validate observability, context management, bounded sub-agent control, and similar
  ADEU-native capabilities before they are productized

Current examples of fork-native value that belong here first:

- deeper observability from main agent to sub-agents
- deeper context-management controls
- other custom fork-specific control surfaces

The `odeu` track is optimized for:

- semantic discovery
- control-law testing
- harness-native workflow iteration

It is not optimized primarily for:

- immediate familiarity
- minimal UI complexity
- lowest-friction day-to-day implementation work

## 4. Standalone Track

Purpose:

- demonstrate the cognitive value of using Codex and ChatGPT together as distinct
  partners
- reduce project/thread scavenging, copy/paste friction, and handoff mistakes
- improve actual productivity and cognitive flow in agentic development work

Core thesis:

- Codex and ChatGPT are not merely interchangeable role labels
- they are distinct cognitive partners
- the human interacts with each surface differently
- the surface therefore conditions the role

In practical terms:

- ChatGPT surface natively supports:
  - loose brainstorming
  - critique
  - reframing
  - world-modeling
- Codex surface natively supports:
  - tight implementation loops
  - patch-oriented execution
  - repo-coupled constraint tracking

Therefore:

- `reviewer` is not just a role assignment
- it is a role plus surface plus human-posture coupling

The standalone shell should preserve that difference rather than flatten it into one
unified generic chat.

## 5. Standalone UX Contract

The standalone shell should stay mostly familiar:

- Codex pane should remain mostly Codex-like
- ChatGPT pane should remain ChatGPT-like
- the control plane should mediate between them, not erase the distinction

Its current highest-value features are:

- explicit project-to-ChatGPT-thread binding
- ability to keep multiple ChatGPT threads relevant to the same implementation project
  visible and retrievable without scavenging through unrelated chats
- low-friction manual transfer between implementation and review surfaces
- reduced misrouting and copy/paste error

The main standalone focus right now is not “expose all ADEU controls.”
It is:

- help actual productivity
- help actual cognitive flow
- make the dual-partner workflow cleaner than the default consumer tooling path

## 6. Custom Codex Fork In The Standalone Track

The standalone shell may still use the custom Codex fork.

But that fork should be treated as:

- a provider/runtime choice
- an optional advanced path
- not the primary product thesis

Analogy:

- vanilla Codex-compatible UX remains the default mental model
- if the chosen Codex runtime is a custom fork, the shell may expose fork-native
  settings the way a controlled global UX can
- the fork-native extras are an advanced provider surface, not the core reason the
  product exists

This keeps the standalone shell coherent even if later it supports:

- vanilla Codex
- custom Codex fork
- other coding-agent providers

## 7. Promotion Rule

Feature movement should follow this rule:

1. deep ADEU capabilities mature first in the `odeu` track
2. only the subset that is:
   - stable
   - comprehensible
   - worth exposing
   - workflow-improving
   should graduate into the standalone shell

This prevents the standalone shell from becoming a dumping ground for immature harness
features.

## 8. Practical Boundary Summary

`odeu` track:

- experiment with ADEU-native controls
- custom fork internals first-class
- bounded Codex evolution toward meta-orchestrator

Standalone track:

- experiment with the dual-partner human workflow itself
- Codex and ChatGPT kept distinct
- control plane manages project binding and handoff
- custom fork extras exposed only as advanced provider settings

## 9. Non-Goals

This doctrine should not be read as authorization to:

1. collapse the two tracks back into one app contract
2. make the standalone shell the primary ADEU control-surface laboratory
3. flatten Codex and ChatGPT into one generic tabbed chat by default
4. treat every custom fork knob as product-worthy now
5. imply that ADEU Studio and the standalone shell should share the same maturity
   cadence
