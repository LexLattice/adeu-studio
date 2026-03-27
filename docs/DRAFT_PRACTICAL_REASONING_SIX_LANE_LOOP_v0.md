# Draft Practical Reasoning Six-Lane Loop v0

Status: planning draft after `vNext+88` closeout and the released `V41` practical-analysis baseline on `main`.

This document names the practical reasoning loop that is already distributed across the
released `V41-A` through `V41-F` materials and makes its inference discipline explicit
enough to reference from prompts.

This is not a lock doc. It does not authorize new runtime behavior, schema release, or
implementation by itself.

## Purpose

- provide one explicit reference for the bounded practical reasoning loop over one frozen
  repo world;
- name the six lanes that are otherwise spread across the request, settlement,
  observation, intended, alignment, and runner materials;
- make settlement-stage interpretation discipline explicit, especially for semantic
  narrowing steps that are often smuggled in as ambient intuition;
- give prompts one repo-local reference instead of requiring ad hoc reconstruction from
  multiple docs.

## Existing Lineage

The loop already exists in released and planning materials, but not as one dedicated
reasoning-contract doc:

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS84.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS85.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS86.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS87.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS88.md`

## Six-Lane Loop

The bounded practical reasoning loop is:

```text
repo scope + maintainer brief + accepted docs
    -> lane 1: frozen repo world
    -> lane 2: settlement / entitlement
    -> lane 3: observed facts
    -> lane 4: intended interpretation
    -> lane 5: alignment findings
    -> lane 6: final run summary
```

This naming is a prompt-facing restatement of the released practical-analysis sequence:

```text
repo scope + maintainer brief + accepted docs
    -> canonical analysis request and source_set
    -> analysis settlement / entitlement frame
    -> observed implementation frame
    -> intended architecture semantic IR
    -> deterministic alignment / drift report
    -> habitual CLI-first run manifest
```

The prompt-facing lane names do not replace the released artifact family names. They are
the human-operational view over the same bounded sequence.

## Lane Definitions

### Lane 1: Frozen Repo World

Compile one bounded analysis world before reasoning downstream.

Minimum contents:

- exact repo scope;
- exact source set;
- snapshot stance such as `committed_tree` or explicit materialized snapshot;
- per-item provenance;
- explicit refusal to reason from ad hoc file selection after freeze.

This lane corresponds to the released analysis-request and source-set discipline.

### Lane 2: Settlement / Entitlement

Externalize interpretation before claims are allowed downstream.

Minimum contents:

- chosen interpretation;
- competing readings when still live;
- deontic typing;
- affordance decisions;
- claim posture;
- escalation triggers;
- compile-entitlement posture.

This lane is where semantic narrowing must be made explicit.

A move from a broad term, permission, failure mode, or semantic category to a stricter
special case may not be treated as ambiently obvious unless the frozen world actually
entitles that exhaustiveness.

Examples of narrowing moves that must stay explicit in this lane:

- broad term -> one favored subtype;
- open semantic space -> one exhaustive mechanism;
- local convenience reading -> global impossibility claim;
- missing proof surface -> silently assumed exclusion.

If a downstream conclusion depends on such a narrowing step, that dependence must remain
visible in the settlement record rather than being hidden in prose.

### Lane 3: Observed Facts

Extract observed implementation facts only from the frozen source set.

Minimum contents:

- direct observations;
- derived observations;
- unresolved observations;
- no intent laundering from observation.

Observed facts may constrain later lanes, but they may not become the hidden source of
intended truth.

### Lane 4: Intended Interpretation

Compile intended truth from the request-bound brief plus the settled interpretation.

Minimum contents:

- intended claims grounded in accepted docs and the settled frame;
- explicit carry-through of ambiguity, advisory posture, or refusal where entitlement is
  still blocked;
- no use of observation as the hidden mint of intended truth.

### Lane 5: Alignment Findings

Compare intended and observed lanes deterministically without collapsing them.

Minimum contents:

- explicit mismatch classes;
- unresolved unknowns;
- blocked posture where required;
- no merged-truth artifact that erases the lane separation.

### Lane 6: Final Run Summary

Emit the final answer as an explicit report over the prior five lanes.

Minimum contents:

- frozen repo world;
- settlement / entitlement;
- observed facts;
- intended interpretation;
- alignment findings;
- final answer.

This lane is a reporting lane. It does not retroactively repair missing settlement,
observation, intended, or alignment work.

## Negative-Claim Discipline

The six-lane loop is fail-closed on high-impact ambiguity.

Therefore:

- absence of a favored reading is not proof that no other reading exists;
- bounded search is not proof of impossibility;
- a negative answer that depends on an unsettled narrowing step remains unentitled;
- if the reasoning cannot lawfully choose among live interpretations, the run should stay
  blocked rather than manufacture certainty.

## Prompt Use

When this doc is referenced from a prompt, the intended effect is:

- the model should treat the six lanes as explicit work products;
- the model should surface semantic narrowing steps during settlement rather than hiding
  them inside later reasoning;
- the model should preserve competing readings until they are settled or explicitly
  blocked;
- the model should not claim impossibility unless the frozen world and settled frame
  actually entitle that claim.

## Bottom Line

The released repo already contains the bounded practical-analysis loop.

What this doc adds is one explicit prompt-facing contract for using that loop as a
disciplined reasoning method, with semantic narrowing forced into the settlement lane
instead of being left to ambient intuition.
