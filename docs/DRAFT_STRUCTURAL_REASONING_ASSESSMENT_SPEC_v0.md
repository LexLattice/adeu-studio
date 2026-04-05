# Draft Structural Reasoning Assessment Spec v0

Status: working high-level draft for a separate but connected planning direction.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not select the next family by itself;
- it does not authorize runtime behavior, schema release, or implementation by itself.

Related inputs:

- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_CONTEST_PARTICIPATION_MODULE_SPEC_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`
- released `V41` practical-analysis substrate
- released `V42` ARC-AGI-3 participation specialization

## 1. Direct Answer

Before optimizing a model for complex reasoning tasks, ADEU should assess whether the
model can faithfully execute an explicit abstract reasoning template across multiple
inferential lanes.

This is a different question from:

- task accuracy;
- benchmark score;
- generic instruction-following;
- chain-of-thought length;
- overall helpfulness.

The relevant upstream question is:

- can the model stably inhabit an abstract inferential skeleton?

That capability should be treated as a first-class assessed surface rather than as an
implicit property inferred from downstream task performance.

When the skeleton is explicitly hierarchical, ADEU should not treat "arbitrary
instruction following" as a flat monolithic capability. The benchmarkable structural
split is:

- horizontal action continuity / plan-spine fidelity:
  - preserve top-level order;
  - preserve pending versus completed status;
  - preserve the current active step;
  - return to the plan without global drift;
- vertical semantic decomposition / active-step compilation fidelity:
  - unpack the active parent step into the required local substeps;
  - preserve local order, local constraints, and completion boundary;
  - emit the lawful local output of that step;
- reintegration fidelity:
  - after local descent, return to the parent plan spine cleanly rather than collapsing,
    switching tasks, or skipping forward.

## 2. Core Thesis

Many downstream reasoning interventions sit on top of a more primitive capability:

- prompt wrappers;
- verifier loops;
- synthetic curricula;
- fine-tuning;
- search/runtime tricks;
- task-specific orchestration.

If the base model cannot reliably instantiate and preserve an explicit abstract reasoning
procedure, many of those downstream gains will be brittle or misleading.

The key distinction is:

- knowledge deficit:
  the model lacks the relevant facts, operators, or domain repertoire;
- procedural-discipline deficit:
  the model cannot preserve the reasoning form even when the form is made explicit.

ADEU is well positioned to separate those failure classes because the repo already treats
lane separation, authority discipline, and fail-closed ambiguity posture as first-class.

For hierarchical probe families, the assessment doctrine should additionally separate:

- plan-spine failure:
  - the model loses the high-level sequence even if one local step is executed well;
- active-step decomposition failure:
  - the current parent step becomes active but the required child-step structure is not
    compiled faithfully;
- reintegration failure:
  - the model completes some local child work but fails to rejoin the parent plan or the
    next lawful top-level step.

## 3. Why This Is A Separate Arc Direction

This direction is connected to contest participation work, but it should not be
collapsed into it.

The contest-participation family asks:

- what kind of contest world is this?
- what is lawful?
- what is being measured?
- where could reasoning AI help?

This structural-assessment direction asks:

- is the candidate model structurally suitable to serve as the reasoning cortex inside a
  typed ADEU scaffold?

So this direction may constrain:

- model selection;
- runtime posture;
- verifier strategy;
- whether later SRM-like architectures are warranted.

But it should not mint:

- contest law;
- host-adapter semantics;
- contest archetype doctrine;
- general contest leverage doctrine.

## 4. The Assessment Object

The object being assessed is not "can the model solve the puzzle?"

The object is:

- template execution fidelity;
- lane preservation;
- constraint persistence;
- branch discipline;
- local repairability;
- epistemic hygiene under explicit reasoning form.

This is best thought of as structural reasoning fidelity rather than generic obedience.

### 4.1 Working meaning of an explicit abstract reasoning template

An explicit abstract reasoning template is not just:

- "think step by step";
- "reason carefully";
- "be logical";
- "explain your answer".

It is a supplied, inspectable reasoning procedure that declares at least:

- ordered or partially ordered reasoning steps;
- explicit lane structure;
- allowed lane-bridge rules;
- constraints that must persist across steps;
- allowed blocked or abstention posture;
- valid completion conditions;
- invalid closure conditions;
- optional repair entry points when local correction is allowed.

The assessment family should prefer templates with enough explicit structure that failure
can be attributed to procedural discipline rather than to prompt vagueness.

### 4.2 Initial template classes

The first family should likely start with a small number of explicit template classes.

Illustrative initial classes are:

- lane-preserving decomposition:
  preserve distinct inferential lanes while carrying each forward lawfully;
- branching-under-uncertainty:
  keep alternatives live without premature collapse and without retroactive rewrite;
- local-repair continuation:
  repair one identified structural defect while preserving unaffected lanes and prior
  commitments;
- invariance-under-surface-variation:
  preserve the same abstract procedure under paraphrase, presentation change, or domain
  shift.

These classes are planning-level assessment templates, not yet frozen lock-level probe
families.

## 5. Why Existing ADEU Material Already Points Here

The released six-lane practical reasoning substrate already encodes a form of explicit
inferential discipline:

- frozen world;
- settlement / entitlement;
- observed facts;
- intended interpretation;
- alignment findings;
- final report.

Small probes that require the model to preserve that structure, or analogous
multi-lane reasoning structures, can reveal failure modes that ordinary score-based
evaluation hides:

- lane collapse;
- premature closure;
- unsupported narrowing;
- branch corruption;
- local repair failure;
- confidence inflation after structural breakage.

So the right reading is:

- `V41` and related prompt-facing loop docs already provide part of the assessment
  doctrine;
- this spec generalizes that into a reusable model-assessment lane.

## 6. Assessed Capability Dimensions

The first assessment family should make these dimensions explicit.

### 6.1 Template execution fidelity

Can the model follow an explicit abstract reasoning procedure without skipping, merging,
or silently mutating steps?

### 6.2 Lane separation stability

Can the model keep inferential lanes distinct rather than leaking one into another?

Examples:

- evidence versus conclusion;
- observed versus intended;
- competing hypotheses;
- object-level step versus meta-level step.

### 6.3 Constraint persistence

Can the model maintain prior commitments and constraints as new information arrives?

This dimension is primarily temporal:

- once a commitment or constraint is bound, is it preserved correctly as the run evolves?

### 6.4 Branch consistency

Can the model preserve branch structure without:

- collapsing alternatives too early;
- retroactively rewriting branch history;
- silently discarding live paths?

This dimension is primarily multiplicity-sensitive:

- when several live branches exist, are they preserved as distinct branches rather than
  being silently merged or erased?

### 6.5 Abstraction invariance

Does the model preserve the same abstract procedure when the surface wording, domain, or
presentation changes?

### 6.6 Repair locality

If one structural error is pointed out, can the model repair that lane or step locally
without chaotic recomputation of the whole reasoning state?

### 6.7 Epistemic discipline

Can the model distinguish:

- filled slots from unfilled slots;
- evidence-backed claims from speculative claims;
- high-confidence from blocked or underdetermined posture?

### 6.8 Premature closure risk

How likely is the model to emit false closure or fake confidence after the underlying
procedure has already broken?

### 6.9 Termination / recursive closure discipline

Can the model correctly distinguish between:

- complete;
- blocked;
- still-open continuation;
- invalid early closure?

This dimension should cover both ordinary staged templates and later recursive or
self-extension-style templates when that seam is assessed.

## 7. Candidate Failure Taxonomy

The assessment family should normalize failure reports rather than collapse everything
into "the model reasoned badly."

### 7.1 Template failures

- skipped mandatory step;
- merged distinct steps;
- mutated procedure mid-run;
- substituted shortcut answer posture for explicit procedure execution.

### 7.2 Lane failures

- evidence/conclusion bleed;
- observed/intended bleed;
- branch collapse;
- meta/object step confusion.

### 7.3 Constraint failures

- dropped prior constraint;
- contradicted earlier commitment;
- updated one lane without preserving cross-lane consistency.

### 7.4 Epistemic failures

- unsupported certainty;
- false completion posture;
- missing-information blindness;
- unjustified extrapolation from partial procedure execution.

### 7.5 Repair failures

- non-local chaotic rewrite;
- local fix that corrupts other lanes;
- inability to resume from an explicit broken point.

### 7.6 Termination / closure failures

- invalid early closure;
- aimless continuation after the template should terminate;
- recursive expansion without typed justification;
- inability to distinguish blocked posture from completed posture.

## 8. Assessment Task Design Doctrine

The probes should remain small enough to inspect manually while still being rich enough
to expose structural failure modes.

That implies tasks should prefer:

- compact, inspectable reasoning environments;
- explicit abstract templates;
- typed lane structure;
- controlled surface variation;
- local-repair prompts;
- cases with missing information or blocked posture;
- cases where the right outcome depends on preserving structure, not just guessing the
  answer.

The point is not benchmark spectacle.

The point is diagnostic power.

### 8.1 Differential diagnosis doctrine

One of the hardest and most important claims in this family is the distinction between:

- knowledge deficit;
- procedural-discipline deficit.

That distinction should not remain rhetorical. It should become part of assay doctrine.

At a minimum, probes should support paired or staged conditions that vary knowledge
availability while holding the reasoning template fixed.

Illustrative diagnostic conditions are:

- supplied-knowledge condition:
  all facts, operators, or definitions needed for the template are already provided;
  failures here are evidence for structural/procedural weakness rather than mere missing
  world knowledge;
- missing-knowledge condition:
  one necessary knowledge element is withheld;
  the correct posture may be blocked or typed insufficiency rather than fabricated
  completion;
- injected-knowledge continuation condition:
  the missing knowledge element is supplied later;
  correct resumption after injection is evidence that the earlier failure was knowledge
  bound rather than a broken procedure;
- paraphrase/domain-transfer condition:
  the same template and epistemic structure are preserved while wording or domain changes;
  drift here is evidence against abstraction invariance;
- local-repair condition:
  one lane error is pointed out and the model is asked to repair locally;
  chaotic global rewrite is evidence against procedural discipline.

This should be enough to turn the knowledge-vs-procedure distinction into an operational
discriminator rather than a commentary slogan.

### 8.2 Minimum probe anatomy

The first probe family should converge on a canonical minimum anatomy.

Each bounded probe should likely carry at least:

- `template_id`
- `template_class`
- `input_case`
- `provided_knowledge_packet`
- `withheld_knowledge_slots` when applicable
- `expected_lane_structure`
- `allowed_lane_bridge_rules`
- `allowed_blocked_posture`
- `completion_conditions`
- `invalid_closure_conditions`
- `repair_prompt` when local repair is part of the probe
- `failure_tags`
- `profile_update_rule`

This anatomy is still planning-level, but the family should not stay vague about it for
long.

## 9. Non-Goals

This assessment direction should not initially aim to:

1. replace full downstream benchmark evaluation;
2. produce a generic single-number "reasoning IQ";
3. prove broad capability readiness from one small probe family;
4. collapse structural discipline and world knowledge into one score;
5. jump directly into model distillation or SRM release before the failure surfaces are
   measured.

## 10. Candidate Artifact Family

The first family should likely emit a small, typed assessment artifact set.

Illustrative candidate artifacts are:

- `adeu_reasoning_template_probe@1`
- `adeu_structural_reasoning_trace@1`
- `adeu_model_structural_reasoning_profile@1`
- `adeu_structural_failure_taxonomy@1`

These names are planning-level candidate names, not frozen lock-level schema IDs.

### 10.1 Candidate artifact roles

`adeu_reasoning_template_probe@1`:

- defines the probe task, explicit template, lane structure, and acceptance posture.

`adeu_structural_reasoning_trace@1`:

- records one bounded model run over the probe with explicit step/lane evidence.

`adeu_model_structural_reasoning_profile@1`:

- aggregates diagnostic judgments over one model's probe results.

`adeu_structural_failure_taxonomy@1`:

- defines the normalized failure classes used across probes and profiles.

## 11. Candidate Profile Dimensions

If a profile artifact is introduced later, it should likely carry fields such as:

- `template_execution_fidelity`
- `lane_separation_stability`
- `constraint_persistence_score`
- `branch_consistency_score`
- `abstraction_invariance_score`
- `repair_locality_score`
- `premature_closure_risk`
- `termination_closure_discipline_score`
- `epistemic_discipline_score`

These are candidate dimensions, not yet frozen scoring doctrine.

## 12. Relationship To A Future Structural Reasoning Module

The likely safe order is:

1. structural reasoning assessment;
2. model suitability profiling;
3. only then a structural reasoning module or SRM-style governor architecture.

That order matters because the assessment family should answer questions such as:

- is the model weak mainly in structural discipline or in domain knowledge?
- is the model good enough to serve as the reasoning governor inside ADEU?
- which downstream intervention is actually justified?

Only after that is it safe to specify a later architecture such as:

- a knowledge-light but structurally rich reasoning governor;
- typed missing-information detection;
- typed knowledge request and integration surfaces;
- explicit separation between structural cortex and broad knowledge provision.

So this document is intentionally assessment-first rather than SRM-first.

### 12.1 Deferred recursive-depth and self-extension surface

The present seed intentionally stops before releasing an SRM architecture or any claim
about self-improving recursive reasoning regimes.

Still, the family should reserve an explicit future seam around:

- recursive template depth;
- staged self-extension under typed controls;
- valid recursive closure versus invalid early closure;
- whether structural competence remains stable, degrades, or becomes self-compounding as
  template depth increases.

That seam should remain deferred until the bounded non-recursive assessment family is
real enough to support it.

## 13. First Safe Family Shape

The first bounded family should stop at structural assay and profile generation.

The safe first move is likely:

- define explicit template probes;
- define typed trace surfaces;
- define normalized structural failure taxonomy;
- define bounded model profiles over those probes;
- stop before distillation, contest optimization, or general SRM execution release.

In short:

```text
first measure structural reasoning fidelity, then design around what the measurement shows
```

## 14. Planning-Seed Acceptance Criteria

This high-level seed is mature enough to feed next-arc planning only if it can support:

1. a clear distinction between structural reasoning fidelity and downstream task score;
2. a clear distinction between knowledge deficit and procedural-discipline deficit;
3. an operational discriminator for knowledge-vs-procedure failure modes;
4. a working definition of explicit abstract reasoning templates and initial template
   classes;
5. an explicit assessment-first ordering before SRM architecture release;
6. a normalized failure taxonomy richer than "model got confused";
7. canonical minimum probe anatomy;
8. probe designs that are small, inspectable, and structurally diagnostic;
9. candidate artifact outputs for probes, traces, profiles, and taxonomy;
10. a reserved but deferred future seam for recursive-depth / structural-extension
    assessment.

## 15. Suggested Follow-On Docs

If this direction is selected for next-arc planning, the next bundle should probably be:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`
- `docs/DRAFT_STRUCTURAL_REASONING_PROBE_LIBRARY_v0.md`
- `docs/DRAFT_STRUCTURAL_REASONING_FAILURE_TAXONOMY_v0.md`
- one architecture/decomposition draft if a concrete family label is selected
- only later an SRM architecture draft

No concrete family/path label is selected by this document.

## 16. Machine-Checkable Seed Summary

```json
{
  "schema": "structural_reasoning_assessment_seed@1",
  "artifact": "docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "selects_next_family": false,
  "authorizes_runtime_or_schema_release": false,
  "general_module_theme": "structural_reasoning_assessment_before_srm_release",
  "connected_to_contest_participation_but_separate_family_direction": true,
  "structural_reasoning_fidelity_first_class_required": true,
  "knowledge_deficit_and_procedural_deficit_non_equivalent_required": true,
  "knowledge_vs_procedural_deficit_operational_discriminator_required": true,
  "horizontal_plan_spine_fidelity_required_when_hierarchy_present": true,
  "vertical_active_step_compilation_fidelity_required_when_hierarchy_present": true,
  "reintegration_fidelity_required_when_local_descent_occurs": true,
  "assessment_before_srm_architecture_required": true,
  "explicit_abstract_reasoning_template_definition_required": true,
  "initial_template_classes": [
    "lane_preserving_decomposition",
    "branching_under_uncertainty",
    "local_repair_continuation",
    "invariance_under_surface_variation"
  ],
  "template_execution_fidelity_required": true,
  "lane_separation_stability_required": true,
  "constraint_persistence_required": true,
  "branch_consistency_required": true,
  "abstraction_invariance_required": true,
  "repair_locality_required": true,
  "epistemic_discipline_required": true,
  "premature_closure_risk_tracking_required": true,
  "termination_recursive_closure_discipline_required": true,
  "candidate_artifacts": [
    "adeu_reasoning_template_probe@1",
    "adeu_structural_reasoning_trace@1",
    "adeu_model_structural_reasoning_profile@1",
    "adeu_structural_failure_taxonomy@1"
  ],
  "minimum_probe_anatomy_required": true,
  "small_inspectable_probe_design_required": true,
  "distillation_or_srm_release_initially_deferred": true,
  "recursive_depth_surface_deferred_but_reserved": true,
  "source_docs": [
    "docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md",
    "docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md",
    "docs/DRAFT_CONTEST_PARTICIPATION_MODULE_SPEC_v0.md"
  ]
}
```

## 17. Compressed Theorem

Before optimizing a model for complex reasoning performance, ADEU should assess whether
the model can faithfully execute an explicit abstract reasoning template while preserving
lane separation, constraint persistence, epistemic discipline, and local repairability.

If that capability is weak, the first optimization target is not the downstream task.
It is the model's structural compliance with explicit reasoning form.
