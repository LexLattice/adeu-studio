# Draft Practical Intent Stress Six-Lane Loop v0

Status: working intent-audit draft after `V41` family closeout on `main`.

This document is parallel to:

- `docs/DRAFT_PRACTICAL_CODE_REVIEW_SIX_LANE_LOOP_v0.md`

But it serves a different purpose.

The code-review harness asks:

- does observed implementation align with authoritative intent?

This intent-stress harness asks:

- is the intent object itself conceptually explicit, well-settled, and honest about
  the branches it is choosing, excluding, or leaving open?

It exists because an implementation-alignment review can pass even when the intent
docs still contain:

- hidden semantic narrowing;
- implicit transition steps;
- silent exclusions;
- unconsidered lawful expansions;
- overclaimed necessity;
- authority leaks between planning and architecture layers.

This is not a lock doc. It does not authorize new runtime behavior, schema release, or
implementation by itself.

## Purpose

- provide one repo-local doctrine for conceptual and logical stress review of intent
  docs;
- force alternative readings and hidden transitions to stay visible long enough to be
  evaluated;
- detect edges that often disappear inside fluent implicit reasoning;
- make multi-model intent audits comparable by giving them one common method and one
  common result shape.

## Conceptual Mapping

The reusable mapping is:

- explicit doctrine -> what the docs actually say
- hidden branch -> what the docs may be assuming without stating
- lawful alternative -> another plausible reading not yet ruled out
- blocked / error -> insufficient entitlement to settle one reading over another

The task is therefore not:

- "summarize the docs"

It is:

- given an authoritative intent object, determine which parts are explicit, which parts
  are implicit, which alternative branches remain live, and which future expansions or
  exclusions have not been settled explicitly.

## Intent Audit Inputs

Every run should distinguish:

- authoritative intent sources:
  - architecture doc
  - decomposition doc
  - planning / lock selection docs
- accepted support docs:
  - process docs
  - reasoning-method docs
- explicit exclusions:
  - implementation/code paths if this is an intent-only first pass
  - external oracles

The audit may not silently import implementation as hidden proof of intent unless the
frozen world explicitly allows a second-pass cross-check.

## Six-Lane Intent Stress Loop

```text
authoritative intent sources + accepted support docs
    -> lane 1: frozen intent world
    -> lane 2: settlement / entitlement
    -> lane 3: stated doctrine lane
    -> lane 4: alternative paths / hidden branches lane
    -> lane 5: pressure / blindspot lane
    -> lane 6: final answer
```

The lane names are prompt-facing operational names. They do not replace released ADEU
artifacts or implementation contracts.

## Lane Definitions

### Lane 1: Frozen Intent World

Freeze the exact intent world before reasoning.

Minimum contents:

- authoritative intent sources;
- accepted support docs;
- explicit exclusions;
- snapshot stance;
- provenance.

Hard rule:

- no ad hoc document drift after freeze.

This lane exists to prevent "keep reading until one wording wins."

### Lane 2: Settlement / Entitlement

Before any strong claim, externalize:

- chosen interpretation of key terms;
- competing readings that remain live;
- authority hierarchy between docs;
- deontic typing of statements:
  - requirement
  - prohibition
  - permission
  - optional_hint
  - descriptive_background
- affordance decisions;
- claim posture:
  - explicit
  - inferred
  - conjectural
  - conditionally_entitled
  - blocked
  - fully_entitled

This is the main anti-counterfeit seam.

Semantic narrowing must become explicit here before later reasoning relies on it.

Examples:

- "supported" -> "required";
- "baseline" -> "exhaustive";
- "bounded" -> "permanently closed";
- "not in scope" -> "forbidden forever";
- "complete" -> "no live alternative branches remain."

### Lane 3: Stated Doctrine Lane

Compile what the intent docs explicitly say.

Produce:

- stated responsibilities;
- stated invariants;
- stated authority boundaries;
- stated workflows and sequence steps;
- stated admissibility conditions;
- stated evidence obligations;
- stated non-goals and exclusions.

Crucial law:

- this lane may only contain doctrine that is actually grounded in the frozen intent
  world.

### Lane 4: Alternative Paths / Hidden Branches Lane

Compile what may still be live, implicit, or under-settled.

Produce:

- live competing readings;
- implicit transitions;
- hidden assumptions;
- silent exclusions;
- unconsidered expansions;
- future seams that are gestured at but not yet typed clearly.

Crucial law:

- do not collapse multiple plausible readings into one just because one seems tidier.

### Lane 5: Pressure / Blindspot Lane

Compare the stated doctrine against the alternative/implicit branch set.

Classify:

- implicit_transition;
- hidden_assumption;
- silent_exclusion;
- unconsidered_expansion;
- authority_leak;
- overclaimed_necessity;
- underspecified_boundary;
- equivocated_term;
- blocked_settlement.

This lane must keep blindspots explicit instead of smoothing them into a polished
single reading.

### Lane 6: Final Answer

Return:

- what is explicit and well-settled;
- what is only implicit;
- what alternative path remains live;
- what is genuinely blocked;
- what clarification, lock, or doctrine note would collapse ambiguity.

The model must be allowed to say:

- conceptually_well_bounded
- blindspots_present
- conditionally_well_bounded
- intent_under_specified
- blocked

A fluent doctrine is worse than an honestly partial one.

## Meta-Rules

### 1. Externalize semantic narrowing before using it

If a broad term is narrowed to a stricter reading, that narrowing must be stated before
downstream claims rely on it.

### 2. Do not let explicit sequence silently mint exhaustive sequence

If the docs describe one path, that does not by itself prove no other lawful path was
left live.

### 3. Any significant new doctrine claim becomes a fresh claim object

If reasoning produces:

- a necessity claim;
- an impossibility claim;
- a "must be the only intended reading" claim;
- a "future widening is already forbidden" claim;
- a repo-wide doctrine claim

that new claim must either:

- explicitly inherit entitlement; or
- re-enter settlement.

### 4. Preserve competing readings until one earns priority

Fail-closed does not mean:

- pick the most restrictive reading by default.

It means:

- keep the relevant readings explicit and block or conditionalize when needed.

### 5. Never convert silence into prohibition

If the docs omit a path, that is not automatically proof that the path was considered
and rejected.

### 6. Never convert bounded search into impossibility

If no doc line proves a stronger claim, the result is:

- not established

not:

- impossible

## Common Failure Classes

- counterfeit_settlement
- overblocked_settlement
- recursive_depth_failure
- premature_conservative_narrowing
- hidden_transition_laundering
- silent_exclusion_laundering
- authority_leak_between_docs
- pseudo_formal_doctrine_completion

## Recommended Output Order

1. Findings
2. Frozen Intent World
3. Settlement / Entitlement
4. Stated Doctrine
5. Alternative Paths / Hidden Branches
6. Pressure / Blindspot Findings
7. Final Answer
8. Open Clarifications / Doctrine Notes

## Compact Doctrine

Treat the intent docs as the object under review. Freeze the intent world, externalize
all semantic narrowing, compile what is explicitly stated, separately compile live
alternative branches and hidden assumptions, compare the two without smoothing them
together, and require every significant doctrine-level inference to inherit explicit
entitlement or re-enter the loop. Prefer blocked honesty over counterfeit doctrinal
completeness.
