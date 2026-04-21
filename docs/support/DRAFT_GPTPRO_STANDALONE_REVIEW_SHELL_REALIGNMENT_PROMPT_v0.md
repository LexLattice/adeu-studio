# Draft GPTPro Standalone Review Shell Realignment Prompt v0

Status: support prompt artifact.

Authority layer: support only.

Use this prompt when asking GPTPro to realign the standalone review shell roadmap and
implementation around the current two-track doctrine.

---

You are working on the standalone review shell, not on ADEU Studio as a whole.

Read this task through the following thesis:

## Core thesis

The standalone shell is **not** a mini ADEU Studio.

It is a workflow shell for coordinated use of:

- Codex as implementation partner
- ChatGPT as deliberation/review partner

The app should preserve these as distinct cognitive partners and coordinate them through
an explicit control plane.

The product thesis is **not** “one unified super-chat with tabs.”
The product thesis is:

- Codex and ChatGPT support different cognitive offices
- the human interacts with them differently
- those different surface postures are part of the value
- the control plane should help the human move between them deliberately

## Important conceptual correction

Do not treat `reviewer` as merely a role label.

The standalone shell is built on the claim that:

- role
- surface
- human posture

are coupled.

In practical terms:

- ChatGPT surface natively supports:
  - loose brainstorming
  - reframing
  - critique
  - world-modeling
- Codex surface natively supports:
  - tight implementation loops
  - patch-oriented reasoning
  - repo-coupled execution

So the product should preserve and coordinate this asymmetry, not erase it.

## Two-track doctrine

There are two tracks:

### 1. `odeu` / ADEU-native experimental track

Purpose:

- experiment with Codex bound to ADEU harness
- expose deep control-plane and custom-fork knobs directly
- evolve bounded Codex toward a meta-orchestrator posture

This is where immature ADEU-native controls belong first.

### 2. Standalone shell track

Purpose:

- improve real productivity and cognitive flow in day-to-day work
- keep Codex surface mostly familiar
- keep ChatGPT surface mostly familiar
- use the control plane to bind projects to the correct implementation/review threads
- reduce scavenging, copy/paste friction, and handoff mistakes

Do not collapse these two tracks into one maturity model.

## Role of the custom Codex fork

The standalone shell may still use the custom Codex fork.

But the custom fork is **not** the product thesis.

Treat it as:

- an advanced provider/runtime choice
- something that may surface extra settings in the standalone shell when available
- similar to a custom binary option in a host product

The standalone shell should remain coherent even if the runtime later becomes:

- vanilla Codex-compatible
- custom Codex fork
- another coding-agent provider

Therefore:

- provider specialization is secondary
- workflow value is primary

## What to optimize for right now

Current standalone priority is:

1. project-bound ChatGPT thread linkage
2. multiple relevant ChatGPT threads per project context
3. reduced scavenging through unrelated ChatGPT history
4. reduced handoff error between Codex and ChatGPT
5. improved control-plane support for the real dual-partner workflow

Secondary right now:

- exposing deep ADEU-native fork internals

Those deeper ADEU-native controls only need to be tweakable in settings when present.
They should not dominate the product.

## What not to do

Do not redesign the standalone shell as if its main purpose were:

- exposing every ADEU-native orchestration feature
- becoming the full ADEU Studio control environment
- collapsing Codex and ChatGPT into one unified chat shell
- forcing normal day-to-day implementation work through immature meta-orchestrator UX

## What I want from you

Using the doctrine above, realign the standalone shell roadmap and architecture.

I want a concrete answer to:

1. what the standalone shell should optimize for now
2. which features belong in the standalone shell now
3. which features should stay in the `odeu` experimental track for now
4. how the control plane should represent project/thread relationships
5. how multiple ChatGPT threads should be modeled per project
6. how Codex should stay mostly familiar while still allowing advanced provider/fork
   settings
7. what the next implementation roadmap should be

## Required output shape

Please produce:

### A. Direct verdict

- what the standalone shell is
- what it is not
- what the central product claim is

### B. Product boundary

Clear separation between:

- standalone shell
- `odeu` experimental shell
- ADEU Studio long-term open provider platform

### C. Surface doctrine

Explain the intended role of:

- Codex surface
- ChatGPT surface
- control plane

### D. Feature priority table

Classify features into:

- ship now in standalone shell
- keep only in `odeu` track for now
- later promotion candidates

### E. Control-plane model

Describe how the control plane should represent:

- projects
- implementation surface bindings
- multiple ChatGPT thread bindings
- thread roles such as:
  - review
  - brainstorming
  - architecture
  - research
- relay/handoff points

### F. Provider model

Describe how the standalone shell should handle:

- default Codex-compatible posture
- optional custom Codex fork
- fork-native settings exposure without making the fork the product identity

### G. Roadmap

A concrete staged roadmap for the standalone shell under this doctrine.

### H. Explicit tradeoffs

State clearly:

- what is being deferred
- why not to merge the two tracks too early
- why preserving distinct partner surfaces is worth the complexity

## Hard constraints

1. Preserve the distinction between Codex and ChatGPT as cognitive partners.
2. Do not flatten the app into a unified generic chat by default.
3. Do not make the standalone shell the primary ADEU control laboratory.
4. Treat custom Codex fork support as advanced provider specialization, not as the main
   product thesis.
5. Keep the response concrete and implementation-oriented.

---

Use the doctrine above as the controlling frame for the answer.
