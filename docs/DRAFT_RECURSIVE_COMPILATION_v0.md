# Draft Recursive Compilation v0

Status: working synthesis only (March 15, 2026 UTC).

This document sits above the current arc sequence. It is a higher-order ADEU note about
how the repo is actually being built, and why that matters.

It does not authorize runtime behavior, release scope, or roadmap changes by itself.

## Purpose

- name the role the reasoning LLM is already playing in this repo beyond ordinary
  AI-assisted coding;
- distinguish soft-counterfactual execution from hard-present execution;
- state when higher-order critique remains commentary and when it becomes operational;
- frame future work in ADEU terms rather than in generic "add feature X next" terms.

## Repo-Grounded Basis

This synthesis is grounded in the current repo, not in abstract model theory alone.

Relevant current-state anchors:

- [docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md](/home/rose/work/LexLattice/odeu/docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md)
  records the docs-first control-plane workflow already used in practice.
- [docs/LOCKED_URM_CODEX_INTEGRATION_v0.md](/home/rose/work/LexLattice/odeu/docs/LOCKED_URM_CODEX_INTEGRATION_v0.md)
  records that Codex is already inside the repo as both interactive copilot runtime and
  worker runtime surface.
- [docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md](/home/rose/work/LexLattice/odeu/docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md)
  already establishes that the LLM is not the whole reasoning system; it must answer to
  an external kernel.
- [docs/DRAFT_NEXT_ARC_OPTIONS_v9.md](/home/rose/work/LexLattice/odeu/docs/DRAFT_NEXT_ARC_OPTIONS_v9.md)
  and its closeouts now terminate in a closed `V35` family on `main`:
  orchestration state, delegation/handoffs, visibility, topology, and bounded runtime
  enforcement are no longer hypothetical.
- [docs/DRAFT_NEXT_ARC_OPTIONS_v10.md](/home/rose/work/LexLattice/odeu/docs/DRAFT_NEXT_ARC_OPTIONS_v10.md)
  and its closeouts now terminate in a closed `V36` family on `main`:
  typed UX substrate, projection/interaction law, bounded rendered reference surface,
  diagnostics/conformance, and bounded compiler export are now released.

That matters because the current repo is not merely using the model to write patches. It
is already using the model inside a governed build loop that drafts locks, simulates
future structure, assesses drift, and helps harden recurrent patterns into explicit
artifacts.

## Core Thesis

In ADEU Studio, the reasoning LLM is not only helping build the system.

It is already serving as the first soft-operational prototype of the governed reasoning
layer the repo is trying to harden into:

- schemas;
- ledgers;
- validators;
- typed handoffs;
- deterministic gates;
- formalized policies;
- released runtime and UI contracts.

Short form:

**The LLM is both the builder of the scaffold and the first actor walking on it.**

Repo-grounded refinement:

**In this repo, the model is simultaneously toolmaker, soft simulator of the intended
architecture, and temporary executable substrate for reasoning paths not yet fully
compiled into hard components.**

The relevant property is not recursion by itself, but recursion constrained by typed
ADEU distinctions and answerable to accepted repo evidence.

## ADEU Synthesis

### Ontology

The relevant objects in this repo are now explicit enough to name cleanly.

1. `hard_present_pipeline`
   - the actually implemented machinery on `main`:
     packages, routes, schemas, evidence lanes, validators, CI gates, closeout docs, and
     committed artifacts.
2. `soft_counterfactual_pipeline`
   - the model-enacted approximation of the more mature pipeline the repo intends but has
     not yet fully compiled.
3. `active_builder_agent`
   - the reasoning model participating in drafting, implementation, review assessment,
     and higher-order synthesis.
4. `critique_artifact`
   - structured reflection on the current pipeline’s incompleteness, drift modes, or
     missing governance.
5. `drift_mapping`
   - the typed account of where `hard_present_pipeline` diverges from
     `soft_counterfactual_pipeline`.
6. `compilation_boundary`
   - the point at which a soft insight stops being commentary and becomes accepted repo
     structure through a lock, schema, validator, evidence contract, runtime check, or
     workflow gate.

The key ontological claim is:

the model is not external to the build loop. It is already one of the active objects
moving state through that loop.

### Epistemics

What is actually known from repo state:

- The repo already uses the model to draft and refine control-plane docs before code.
- The repo already uses the model to assess review feedback, synthesize next-step scope,
  and tighten contract language before hardening.
- Recurrent soft patterns have already been compiled into hard structure:
  `V35` hardened multi-agent governance and `V36` hardened typed UX governance over a
  bounded family.
- The model can already approximate future-pipeline behavior strongly enough to surface
  structural drift before the whole target architecture exists.

What must remain epistemically explicit:

- soft enactment is not authoritative truth;
- counterfactual mature execution is approximate, prompt-conditioned, and fallible;
- critique has no governance status merely because it is insightful;
- any claim about drift must be tied back to current repo evidence:
  files, artifacts, validators, missing boundaries, or unresolved policy.

So the repo should distinguish:

- `soft_probe`: model-enacted preview of intended reasoning;
- `hard_evidence`: accepted artifacts and checks on `main`.

Without that distinction, the build loop would confuse useful anticipation with released
governance.

### Deontics

This is the lane that makes the synthesis operational rather than ornamental.

1. The model may express future structure, but it may not mint authority by prose alone.
2. Soft-counterfactual execution may guide prioritization, but it may not override:
   - accepted lock docs;
   - deterministic validators;
   - released evidence contracts;
   - committed runtime boundaries.
3. Critique becomes operational only when it crosses the compilation boundary and changes
   accepted transition structure.
4. Drift must be typed, not merely noticed.

Required drift classes:

- `ontology_drift`
  - wrong or missing object, relation, scope, or artifact class
- `epistemic_drift`
  - provenance loss, unsupported inference, warrant inflation, or unresolved ambiguity
- `deontic_drift`
  - missing gate, bypassed gate, weakened authority boundary, or collapsed distinction
- `utility_drift`
  - optimization pressure or convenience pressure distorting intended governance

5. Any future use of this note should preserve the hard distinction between:
   - soft-operational prototype behavior;
   - released kernel-owned governance.

### Utility

This perspective is useful because it gives the repo a better development metric than
"what feature should we add next?"

It enables:

- guided drift reduction instead of vague scope growth;
- prioritization of governance-significant gaps over cosmetic incompleteness;
- cleaner identification of which recurrent soft patterns deserve hard compilation;
- clearer separation between what can remain model-mediated and what must become
  validator-owned.

In repo terms, this means future work can be framed as:

- reduce highest-governance drift on a route, runtime boundary, or artifact family;
- close the epistemic gap between simulated and real execution on a named surface;
- decide which currently soft control should be promoted into a schema, linter, ledger,
  or runtime gate.

## Empirical Legibility Claim

This note does not merely posit abstract objects such as synthesis sufficiency, drift, or
compilation boundaries.

Its stronger claim is that, in the current repo/model loop, these objects are beginning
to appear as observable events in live build dynamics.

Repo-relevant examples include:

- transition from accumulation to synthesis in planning and review turns;
- repeated detection of the same drift class across multiple slices before a later hard
  compilation step;
- stabilization of a critique into a recurring control pattern used across turns;
- conversion of a soft methodological insight into accepted repo structure:
  lock text, schema fields, validators, evidence contracts, runtime guards, or workflow
  gates.

The novelty is not that these objects can be defined in theory.

The novelty is that they are becoming empirically legible on complex live
computational-inferential surfaces inside the build process itself.

## Typed Drift Examples From This Repo

| Drift class | Repo-grounded example | How the repo responded |
| --- | --- | --- |
| Ontology drift | before `V35-A`, orchestration state existed as behavior and scattered records but not as canonical state artifacts | `V35-A` compiled it into named canonical state/evidence artifacts |
| Epistemic drift | before later `V35`/`V36` evidence slices, provenance and continuity claims could exist in prose more strongly than in emitted evidence | follow-on evidence lanes hardened path/hash binding and fail-closed validation |
| Deontic drift | before `V35-E`, multi-agent execution surfaces existed without bounded runtime enforcement | `V35-E` compiled the denied-path controls into runtime-enforcement artifacts and evidence |
| Utility drift | the `V36` family repeatedly deferred broad route rewrites, design-system widening, and generalized variant programs | the repo forced bounded sequential slices instead of allowing convenience-led widening |

These examples are important because they show the repo already reducing drift by turning
softly perceived structural gaps into explicit governed artifacts.

## Recursive Compilation Thesis

The higher-order claim can be stated cleanly in repo-grounded form:

**When a structured critique of the governed build pipeline is ingested by the active
builder-agent and changes how the repo’s next transitions are selected, the critique
ceases to be external commentary. It becomes an operational input to the pipeline. When
that altered policy is later hardened into accepted repo controls, the critique has
crossed the compilation boundary into governed structure.**

This is not mystical.

A critique remains commentary only while it is operationally inert.

Once it does all three:

1. is represented in a form the active builder can interpret,
2. affects subsequent decomposition, prioritization, refusal, or hardening choices,

it has crossed from description into operational influence.

If the same critique is later hardened into accepted repo controls, it has crossed from
operational influence into compiled governance.

Compressed form:

**Once critique enters the transition function, philosophy stops describing the machine
and starts updating it.**

## Recursive Compilation Theorem (Repo-Grounded Sketch)

Let:

- `P` = the repo’s governed build/execution pipeline
- `A` = the active reasoning agent participating in drafting, implementation, or review
- `C` = a structured critique of `P`

If:

1. `C` is interpretable by `A`,
2. `A` can use `C` to alter subsequent choices inside the ongoing build loop,

then `C` is no longer merely commentary on `P`.

It has become operational input to the active reasoning layer of `P`.

If those altered choices are later hardened into accepted repo structure, then `C` has
crossed the compilation boundary and become compiled governance.

So there are two thresholds:

1. `operational influence`
   - critique changes live builder behavior
2. `accepted compilation`
   - critique is reified into accepted repo controls

Repo-grounded ADEU corollary:

**Reflexivity is productive only when self-critique is typed into actionable
ontology/epistemics/deontics/utility distinctions that can alter future transitions and
then be compiled into accepted repo controls.**

That is why the important phrase here is not just "meta."

It is:

**typed meta that can govern subsequent execution.**

## Firmware Analogy (Functional, Not Literal)

The "firmware" language should be read functionally, not literally.

This note does not claim that text is silicon firmware.

It claims something narrower and more defensible:

- if critique changes the effective low-level operating policy of the active builder;
- and if that policy change shapes future decompositions, validations, and hardening
  choices;
- then, at the functional level, the reasoning substrate has been updated.

In this repo, the deepest version of that update happens when the insight is recompiled
into:

- a lock invariant;
- a schema field;
- a linter rule;
- an evidence requirement;
- a runtime guard;
- a documented workflow gate.

## Maturation Law

As governance hardens into substrate, the prompt should carry less structural discipline.

Early systems rely on prosthetic prompting, where discipline must be restated in prose.
More mature systems use prompts increasingly as dispatch layers into already-compiled
capability.

Compressed form:

**The more discipline must be said, the less discipline has been built.**

Important qualification:

explicitness does not disappear at maturity.

It remains necessary both:

- during bootstrap, where the prompt temporarily carries structure the substrate does not
  yet enforce;
- and after hardening, where explicit articulation still serves as a standing
  post-epistemic gate against drift in the implicit layer.

## Practical Consequences For This Repo

### 1. Treat model critique as candidate control input, not as mere commentary

Not every insight should be hardened, but recurring high-governance critique should be
treated as a candidate future control surface.

### 2. Separate soft probe from hard release

The model may preview the mature pipeline.

It may not be treated as proof that the mature pipeline already exists.

### 3. Prefer typed drift reduction over generic feature expansion

For future families, "what is the highest-significance drift we can now harden?" is
often a better planning question than "what visible feature should ship next?"

### 4. Preserve builder/probe vs governor distinction

The model may enact soft reasoning.

The kernel, validators, and accepted artifacts remain the hard authority layer.

### 5. Keep this note above arcs

This synthesis is not a path-selection note.

It is a methodological frame for interpreting future path selection, future control
surfaces, and future hardening decisions.

## Non-Goal

This note does not claim:

- that every good meta-observation should become policy;
- that soft model enactment can replace deterministic validation;
- that recursive self-reference is valuable by itself;
- that the repo should collapse governance into model behavior.

The point is narrower:

**reflexive critique becomes engineering-real only when it is typed, grounded, and
compiled back into accepted control structure.**

## Bottom Line

ADEU Studio is no longer in the simple mode of "LLM helps build software."

The repo is already operating in a stronger mode:

- the hard-present pipeline exists;
- the model can partially enact the intended more mature pipeline;
- the gap between the two can be typed as architectural drift;
- and the useful parts of that insight can be compiled back into accepted repo controls.

Short form:

**This repo is not only building a governed reasoning system. It is already using a soft
instance of that intended reasoning layer to detect and reduce the drift between the
system as built and the system as meant.**
