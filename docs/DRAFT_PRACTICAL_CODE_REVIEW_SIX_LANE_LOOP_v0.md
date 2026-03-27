# Draft Practical Code Review Six-Lane Loop v0

Status: working review-method draft after `vNext+88` closeout and the released `V41`
practical-analysis baseline on `main`.

This document specializes the released practical reasoning loop for code review.

It exists because generic code review prompts often collapse:

- architecture / intent;
- implementation reality;
- tests;
- and reviewer inference

into one fluent narrative.

This doc makes the review task explicit instead:

- freeze the review world;
- externalize semantic narrowing and entitlement;
- compile intended and observed lanes separately;
- compare them without blending;
- preserve blocked or conditional posture when the evidence does not support a strong
  claim.

This is not a lock doc. It does not authorize new runtime behavior, schema release, or
implementation by itself.

## Purpose

- provide one repo-local review doctrine for resident agents using the released ADEU
  practical-analysis method;
- map the six-lane reasoning loop onto software module / architecture review work;
- prevent hidden assumption laundering during code review;
- make multi-model review runs comparable by giving them one common method and one
  common result shape.

## Conceptual Mapping

The reusable mapping is:

- puzzle statement -> authoritative architecture / intent object
- candidate solution -> code implementation + lower planning docs + tests
- good door -> intended compliant implementation state
- bad door -> code that works locally but violates architecture, intent, or boundaries
- guardian question -> the six-lane review procedure
- blocked / error -> insufficient entitlement to settle, unresolved ambiguity, or
  underspecified intent

The review task is therefore not:

- "read code and summarize"

It is:

- given an authoritative intent object and an observed implementation object, determine
  whether the implementation is aligned with intended architecture under an explicitly
  settled interpretation.

## Review Inputs

Every run should distinguish:

- intended object:
  - architecture doc
  - spec
  - maintainer brief
  - authoritative invariants / boundaries
- observed object:
  - code
  - config
  - tests
  - lower planning docs
  - telemetry / evidence if accepted into the frozen world

The review method may not silently blend the two.

## Six-Lane Review Loop

```text
authoritative intent sources + authoritative observed sources + accepted support docs
    -> lane 1: frozen repo world
    -> lane 2: settlement / entitlement
    -> lane 3: intended lane
    -> lane 4: observed lane
    -> lane 5: alignment lane
    -> lane 6: final answer
```

This is the code-review specialization of the released practical-analysis sequence:

```text
analysis_request + source_set
    -> settlement frame
analysis_request + source_set + settlement frame
    -> observation frame
analysis_request + source_set + settlement frame + observation frame
    -> intended semantic IR
intended semantic IR + observed frame
    -> alignment report
analysis_request + settlement frame + observation frame + intended semantic IR + alignment report
    -> analysis run manifest
```

The review-facing lane names do not replace the released artifact family names. They are
the prompt-facing operational view over the same bounded method.

## Lane Definitions

### Lane 1: Frozen Repo World

Freeze the exact review world before reasoning.

Minimum contents:

- authoritative intent sources;
- authoritative observed sources;
- accepted support docs;
- explicit exclusions;
- snapshot stance;
- provenance.

Hard rule:

- no ad hoc file drift after freeze.

This lane exists to prevent "grep until a story appears."

### Lane 2: Settlement / Entitlement

Before any strong claim, externalize:

- chosen interpretation of intent terms;
- competing readings that remain live;
- authority hierarchy between docs and code surfaces;
- deontic typing of statements:
  - requirement
  - prohibition
  - permission
  - optional_hint
  - descriptive_background
- affordance decisions;
- claim posture:
  - observed
  - inferred
  - conjectural
  - conditionally_entitled
  - blocked
  - fully_entitled

This is the main anti-counterfeit seam.

Semantic narrowing must become explicit here before later reasoning relies on it.

Examples:

- "should" -> "must";
- "module boundary" -> one specific enforcement mechanism;
- "supported" -> "required";
- "missing evidence" -> "impossible";
- "large test suite" -> "proof of intent."

### Lane 3: Intended Lane

Compile the intended architecture from authoritative intent sources only.

Produce:

- intended responsibilities;
- intended invariants;
- intended authority boundaries;
- intended workflows;
- intended admissibility conditions;
- intended evidence obligations;
- intended non-goals / exclusions.

Crucial law:

- observed code may constrain overreach, but may not become the hidden source of
  intended truth.

### Lane 4: Observed Lane

Compile only what the implementation actually does.

Produce:

- direct observations from code/config/tests;
- derived observed behaviors;
- unresolved unknowns;
- implemented boundaries;
- missing guards;
- actual evidence surfaces.

Crucial law:

- do not infer intent here.

Tests should be treated as witness surfaces, not proof of global architecture
compliance unless the frozen world explicitly elevates them.

### Lane 5: Alignment Lane

Compare intended and observed deterministically.

Classify:

- implemented_as_intended;
- intended_but_unimplemented;
- implemented_but_undeclared;
- authority_boundary_drift;
- workflow_drift;
- evidence_or_observability_gap;
- ambiguity_in_intent;
- ambiguity_in_implementation;
- blocked_comparison_due_to_underspecified_intent.

This lane must keep mismatches explicit instead of smoothing them into one blended
story.

### Lane 6: Final Answer

Return:

- what is aligned;
- what is misaligned;
- what is ambiguous;
- what is blocked;
- what clarification or artifact would unlock stronger settlement.

The model must be allowed to say:

- blocked
- conditionally_aligned
- intent_under_specified
- implementation_evidence_under_specified

A fluent verdict is worse than a blocked honest one.

## Meta-Rules

### 1. Externalize semantic narrowing before using it

If a broad term is narrowed to a stricter reading, that narrowing must be stated before
downstream claims rely on it.

### 2. Do not let first-order success mint second-order necessity

One bug, one fix, one solution branch, or one working pattern may not be generalized
into architecture doctrine without a fresh entitlement check.

### 3. Any significant new inference becomes a fresh claim object

If reasoning produces:

- an impossibility claim;
- a necessity claim;
- a repo-wide doctrine claim;
- a family-of-solutions claim;
- a global architecture implication

that claim must either:

- explicitly inherit entitlement; or
- re-enter settlement.

### 4. Prefer distance from prohibition surfaces

If two branches are equally workable, prefer the one farthest from the explicit blocked
or forbidden seam.

### 5. Never convert bounded search into impossibility

For code review this means:

- missing evidence is not proof of absence;
- absent explicit doc support is not proof of impossibility;
- local code pattern is not proof of architectural necessity.

### 6. Preserve live competing readings until one earns priority

Fail-closed does not mean "pick the strictest reading immediately."

It means:

- keep relevant readings explicit;
- block or conditionalize when needed.

### 7. Preserve lane types

Common review failure:

- requirements read as suggestions;
- procedure read as explanatory prose;
- architecture law read as design flavor;
- tests read as proof of full intent;
- implementation accident read as intended doctrine.

The review method should actively detect this.

## Common Failure Classes

Useful review diagnostics:

- counterfeit_settlement
- overblocked_settlement
- scoped_conditional_entitlement
- recursive_depth_failure
- harness_cosplay
- legalist_deontic_overplay
- meta_typing_breach
- premature_conservative_narrowing
- pseudo_formal_combinatorics

These labels help compare multiple model runs over the same review world.

## Recommended Review Output

The review should be returned in this order:

1. Findings
2. Frozen Repo World
3. Settlement / Entitlement
4. Intended Interpretation
5. Observed Facts
6. Alignment Findings
7. Final Answer
8. Open Clarifications / Unblocking Artifacts

Each finding should include:

- mismatch class;
- entitlement level;
- typed support refs;
- file/line refs when applicable;
- concise statement of the issue.

No finding may be supported only by prose.

## Companion Template

When running several models against the same review world, use the structured template:

- `docs/templates/PRACTICAL_CODE_REVIEW_SIX_LANE_RESULT_TEMPLATE_v0.json`

That template is intentionally comparison-friendly:

- stable top-level sections;
- explicit lane outputs;
- explicit finding shape;
- explicit verdict/entitlement fields;
- explicit blocked/unknown handling.

## Bottom Line

For code review, the right ADEU task is not "read code and tell me if it looks good."

It is:

- freeze the review world;
- externalize semantic narrowing;
- compile intended and observed separately;
- compare without blending;
- require every significant second-order inference to inherit entitlement or re-enter
  the loop;
- prefer blocked honesty over counterfeit alignment.
