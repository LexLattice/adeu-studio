# ADEU ARC-AGI Participation Architecture v0

**Status:** working draft snapshot - 2026-03-28
**Scope:** use ADEU Studio as a governed reasoning and orchestration substrate for
participation in the ARC-AGI-3 challenge
**Method:** repo-native extension of the released `V41` practical-analysis baseline over
the official ARC toolkit and agent interface

---

## 1. Direct Answer to the Problem

ADEU Studio should not approach ARC-AGI-3 as "just another puzzle solver."

It should approach ARC-AGI-3 as an external interactive benchmark where:

1. the official ARC toolkit owns environment truth;
2. ADEU owns the internal reasoning control plane;
3. the solver remains bounded by explicit task/session state, explicit hypotheses, and
   replayable action lineage;
4. online competition behavior is a later deployment mode over a stronger local-first
   baseline.

The right use of ADEU is therefore:

- not a standalone replacement for the official ARC environment;
- not a prompt-only agent with opaque branching;
- not a generic "let the model think harder" wrapper;
- but a typed, replayable reasoning harness around ARC task state, observation,
  hypothesis selection, action choice, and scorecard lineage.

In compiler terms:

```text
official ARC game/task state
    -> frozen ADEU task packet
    -> explicit observation frame
    -> explicit hypothesis / action proposal
    -> action execution through official ARC adapter
    -> observed outcome + replay trace
    -> scorecard / benchmark lineage
```

---

## 2. External Challenge Constraints

The external challenge imposes architectural constraints that should be treated as
first-class design inputs rather than as implementation details.

### 2.1 Interactive benchmark constraint

ARC-AGI-3 is an interactive benchmark over turn-based 2D grid environments rather than a
static batch of one-shot puzzle files.

That means ADEU must support:

- repeated observation/action turns;
- session state that changes after actions;
- legal action envelopes that come from the official environment;
- per-game and per-scorecard lineage.

### 2.2 Agent interface constraint

The official ARC agent path expects an agent to expose bounded lifecycle methods such as:

- environment/game/session setup;
- `is_done(...)`;
- `choose_action(...)`.

ADEU should wrap those methods, not bypass them.

### 2.3 Local-first constraint

The official ARC docs recommend local/offline development first because it is faster and
not rate-limited.

Therefore the first ADEU family should prefer:

- local benchmarking;
- deterministic replay;
- evidence-rich offline experimentation;
- bounded adapter work over online deployment.

### 2.4 Competition-mode constraint

Competition mode is stricter than ordinary online use.

Important deontic constraints include:

- API-only interaction;
- one `make` per environment;
- one scorecard per environment;
- no inflight scorecard peeking;
- stricter replay/score submission posture.

The first ADEU family should therefore treat competition mode as a later widening seam,
not as the first slice.

### 2.5 Deontic boundary constraint

ARC mode restrictions, legal external interactions, and scorecard/session restrictions
should be treated as binary admissibility surfaces rather than as descriptive metadata.

That means the ADEU ARC family should make first-class room for:

- mode-policy posture;
- legal action envelope;
- adapter-envelope restrictions;
- scorecard/session lifecycle restrictions when that seam is later selected.

If those boundaries remain prose-only, weaker models will tend to read them as soft
context rather than as operative `D` surfaces.

### 2.6 Action-counting constraint

The ARC methodology counts environment-altering actions, not the agent's internal
reasoning/tool calls.

That makes ADEU a good fit, because the repo's strength is explicit internal reasoning
discipline:

- frozen world;
- settlement and entitlement;
- observed facts;
- candidate interpretation or action intent;
- alignment or pressure against outcomes;
- run summary.

The cost surface still matters in practice, but the action-counting rule means richer
internal ADEU control does not automatically violate ARC's scoring model.

---

## 3. Repo-Native Design Thesis

ADEU Studio already has the right internal posture for this challenge.

The released `V41` family on `main` established a practical six-lane reasoning baseline:

```text
frozen world
    -> settlement / entitlement
    -> observed facts
    -> intended interpretation
    -> alignment findings
    -> habitual run summary
```

For ARC participation, those lanes should be reinterpreted over game/session state rather
than over repo state:

| ADEU lane | ARC reinterpretation |
|---|---|
| frozen world | one exact game/task/session state plus mode and action budget |
| settlement / entitlement | live hypothesis set, ambiguity register, and claim posture over possible rules/transforms |
| observed facts | direct and derived frame/object/grid observations |
| intended interpretation | currently selected transformation or action policy hypothesis |
| alignment findings | mismatch between expected and observed outcomes under a candidate hypothesis |
| run summary | replayable benchmark/scorecard/session manifest |

This is an inference from the released ADEU practical-analysis baseline and the official
ARC docs. It is not yet a released runtime contract.

Crucial carry-through rule for later slices:

- the settlement / entitlement discipline from `V41` should not disappear once ARC
  moves past task/session freeze;
- any hypothesis or action-proposal surface should carry claim posture and unresolved
  ambiguity state rather than only content.

---

## 4. Why A New Package Family Is Justified

Existing `adeu_puzzles` ownership is too narrow for ARC-AGI-3.

`adeu_puzzles` is centered on static puzzle IR plus deterministic solving over a bounded
problem class.

ARC-AGI-3 introduces additional first-class concerns that deserve their own ownership
surface:

- interactive session state;
- official toolkit adapter semantics;
- per-step observation/action lineage;
- scorecard and replay lineage;
- local-vs-online mode policy;
- competition-mode deontic constraints;
- search or hypothesis management over repeated actions.

That is enough new surface area to justify a dedicated ARC participation package family.

---

## 5. Proposed Package Boundaries

| Package | Responsibility |
|---|---|
| `packages/adeu_arc_agi` | typed ARC task/session artifacts, canonicalization, schema export, reason codes |
| `packages/adeu_arc_solver` | observation extraction, hypothesis ranking, action proposal, official toolkit adapter, local benchmark helpers |
| `apps/api` integration | later review/inspect/run endpoints over typed ARC artifacts |
| `apps/web` integration | later replay, frame, hypothesis, and scorecard inspection surfaces |

Design note:

- the first family should prefer introducing the typed ARC family and bounded solver
  adapter before any API or web widening;
- `adeu_agent_harness` and `urm_runtime` remain useful substrate and may be consumed
  later, but they should not force the first ARC participation slice to widen into
  generalized remote orchestration.
- the package table describes the family-scale architecture target, not the selected
  scope of `V42-A`; the first slice should remain narrowly adapter/task-packet focused
  until a dedicated decomposition explicitly widens it.

---

## 6. Proposed Artifact Family

### 6.1 Canonical artifacts

| Artifact | Purpose |
|---|---|
| `adeu_arc_task_packet@1` | one frozen ARC task/game/session input packet with mode, constraints, metadata, and initial state lineage |
| `adeu_arc_observation_frame@1` | direct and derived observations over one or more frames in a frozen task/session state |
| `adeu_arc_hypothesis_frame@1` | explicit candidate rules, action hypotheses, ambiguity register, claim posture, and selection posture |
| `adeu_arc_action_proposal@1` | one bounded proposed action plus expected effect, supporting refs, and explicit admissibility posture |
| `adeu_arc_rollout_trace@1` | canonical record of actions taken, observed outcomes, and stepwise lineage |
| `adeu_arc_scorecard_manifest@1` | scorecard/replay lineage and ADEU-side metadata over one bounded run |

### 6.2 Internal ladder

Recommended internal order:

```text
adeu_arc_task_packet@1
    -> adeu_arc_observation_frame@1
    -> adeu_arc_hypothesis_frame@1
    -> adeu_arc_action_proposal@1
    -> adeu_arc_rollout_trace@1
    -> adeu_arc_scorecard_manifest@1
```

This order keeps:

- external environment truth before internal interpretation;
- observation before action proposal;
- hypothesis pressure before commitment to a move;
- rollout trace before scorecard summary.

---

## 7. Control Plane And Pipeline

### 7.1 Local-first loop

The first complete practical loop should be:

1. load one ARC game through the official local toolkit;
2. freeze one canonical `adeu_arc_task_packet@1`;
3. derive one `adeu_arc_observation_frame@1`;
4. derive one `adeu_arc_hypothesis_frame@1`;
5. derive one `adeu_arc_action_proposal@1`;
6. execute the action through the official ARC adapter;
7. record the result in `adeu_arc_rollout_trace@1`;
8. iterate until the bounded stop condition is reached;
9. emit one `adeu_arc_scorecard_manifest@1` or local benchmark summary derivative.

This ladder is a family-scale target, not the implied selected scope of `V42-A`.

The first concrete slice should stop much earlier:

```text
official ARC toolkit adapter
    -> one frozen adeu_arc_task_packet@1
    -> validated local adapter/task-session boundary
```

### 7.2 Competition-mode loop

Competition mode should remain a later widening over the same local-first artifact ladder.

Its added responsibilities are:

- API-backed session/scorecard lifecycle;
- replay/share link lineage;
- stricter mode policy enforcement;
- no reliance on inflight scorecard inspection;
- no widening of internal reasoning authority.

### 7.3 Internal reasoning rule

ADEU's internal reasoning may be richer than the ARC environment's external action
surface, but it must remain:

- bounded;
- replayable;
- evidence-carrying;
- explicit about ambiguity and negative-claim posture.

The first ARC family should not confuse:

- "internal reasoning is not action-counted"

with:

- "arbitrary hidden branching is good enough."

The value proposition is explicit reasoning, not merely larger hidden chain-of-thought.

### 7.4 Model-sensitivity rule

ARC should be treated as a substrate-sensitivity test for ADEU, not as proof that the
harness lifts all model classes equally.

Therefore later local benchmark work should evaluate at least:

- task success;
- action efficiency;
- explicit control-plane usage;
- whether the model keeps ambiguity and claim posture explicit rather than silently
  collapsing into hidden branch selection.

---

## 8. First Family Thesis

The first ARC participation family should be narrow.

It should prove that ADEU can:

- wrap the official ARC toolkit without bypassing it;
- freeze task/session state into typed ADEU artifacts;
- make ARC-side legal and mode boundaries explicit as first-class admissibility
  surfaces;
- keep observation, hypothesis, action proposal, and rollout lineage explicit;
- benchmark locally before online deployment;
- carry replay/scorecard lineage honestly when later widened.

It should not initially try to solve:

- generic multi-benchmark orchestration;
- Studio web workbench release;
- fleet-scale swarm management inside ADEU;
- generalized multimodal reasoning infrastructure;
- claims of leaderboard readiness from local-only baseline work.

---

## 9. Authority And Non-Goals

This architecture note is:

- a high-level architecture / decomposition surface;
- not a lock doc;
- not a promise of challenge competitiveness by itself.

The first family should treat the following as deferred seams:

- direct online competition submission;
- API or web operator surfaces;
- generalized benchmark-agnostic runtime;
- large-scale multi-agent swarms inside ADEU;
- formal proof sidecar integration.

Useful seam classifications for those widenings are:

- `deferred_to_later_family`
- `not_selected_yet`

rather than:

- "already solved"; or
- "forbidden forever".

---

## 10. Bottom Line

The right ADEU strategy for ARC-AGI-3 is:

- use the official ARC toolkit as the environment authority;
- use ADEU as the explicit reasoning, evidence, and replay control plane;
- start with a local-first typed adapter family;
- widen to online competition mode only after the local artifact ladder is strong.

That is the narrowest plausible path from the released `V41` practical-analysis
baseline to external benchmark participation without collapsing back into opaque
prompt-only solving.
