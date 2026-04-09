# Draft Morphic UX Governed Enactment Protocol v0

Status: working draft support protocol (April 8, 2026 UTC).

Authority layer: support.

This document makes explicit one support-layer method for discovering missing frontend
support surfaces by repeatedly enacting the current Morphic UX skill over bounded real
tasks and logging where the agent is still simulating infrastructure in thought.

It does not authorize runtime behavior, new tool surfaces, schema release, or prompt
policy by itself.

## Purpose

- turn the current Morphic UX skill into an operational test surface rather than a
  declarative posture only;
- distinguish recurring tool gaps from skill-spec gaps;
- force repeated simulation burdens into explicit evidence instead of hiding them inside
  fluent reasoning;
- provide one bounded protocol for generating a minimal frontend support-layer roadmap.

## Controlling Sources By Authority Layer

### Architecture / decomposition

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/ARCHITECTURE_ADEU_STUDIO_v0.md`

These are authoritative for the repo's broader doctrine: typed intermediate artifacts,
authority/evidence separation, and the rule that open-ended work should be made legible
before implementation.

### Planning

- `docs/seed arc v10.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`

These are authoritative for the `ux_morph` family-selection posture and for the idea
that morph selection should happen before raw code generation.

### Lock / released bounded family

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS65.md`

These are authoritative for the released `V36-A` through `V36-E` bounded UX family.
They define what is frozen about the current `artifact_inspector_advisory_workbench`
reference family and what the support-layer protocol must not silently redefine.

### Support

- `.agents/skills/morphic-ux-frontend/SKILL.md`
- `.agents/skills/morphic-ux-frontend/references/source-grounding.md`
- `.agents/skills/morphic-ux-frontend/references/frontend-delivery-checklist.md`
- `docs/support/DRAFT_UX_MORPH_CHANGE_SCOPING_WALKTHROUGH_v0.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_TASK_CORPUS_v0.md`
- `docs/templates/MORPHIC_UX_GOVERNED_ENACTMENT_BURDEN_LOG_TEMPLATE_v0.md`

These support surfaces define how the protocol should be run, but they do not mint new
runtime authority, tool authority, or lock scope.

## The Method In One Sentence

Freeze the current Morphic UX skill, enact multiple bounded frontend tasks under it,
refuse silent compensation, log recurring reasoning substitutes as burden entries, and
promote only the repeated minimal operations that the skill cannot keep simulating
cheaply or lawfully.

## ADEU Framing

The protocol is ADEU-native because it keeps four questions separate:

- `O`: What objects must exist for the skill to be real?
  - enacted task
  - burden entry
  - recurring operation family
  - candidate tool surface
- `E`: What evidence entitles promotion from burden to tool candidate?
  - repeated recurrence
  - explicit source refs
  - stable input/output shape
  - retest delta after promotion
- `D`: What may and may not happen during the runs?
  - no silent compensation
  - no ad hoc widening of skill scope
  - no tool authority minted from support docs alone
- `U`: What makes execution robust rather than merely possible?
  - promote only recurring stable operations
  - reject bloated helper bundles
  - keep the candidate surface minimal

## Definitions

### Enacted task

One bounded frontend task run under the current Morphic UX skill and a frozen source
world.

### Reasoning substitute

A stable operation the agent is repeatedly performing in its head because no explicit
support surface exists yet.

Examples:

- repeatedly reconstructing the region/lane topology from several files;
- repeatedly tracing whether evidence is same-context reachable;
- repeatedly inferring whether an action is advisory, authoritative, gated, or reversible;
- repeatedly comparing a realized surface against morph axes with no structured helper.

### Candidate tool surface

One proposed externalized operation with a stable contract, explicit inputs, explicit
outputs, and a bounded non-goal statement.

### Classification

- `lawful_required`
  - without this support surface, the skill cannot execute honestly without counterfeit
    certainty, hidden rule laundering, or repeated unauthorized inference;
- `reliable_required`
  - lawful execution is still possible, but the repeated reconstruction burden threatens
    consistency and reviewability;
- `performance_only`
  - the support surface would make execution faster or cheaper, but not more lawful or
    more reliable;
- `skill_gap`
  - the burden disappears if the skill or source-grounding is clarified instead of adding
    a tool;
- `unresolved`
  - insufficient recurrence or insufficient evidence to classify yet.

## Non-Compensation Rule

The run may not hide missing infrastructure behind extra private reasoning.

If the agent has to repeatedly:

- reconstruct stable state from multiple files;
- infer a recurring topology indirectly;
- re-derive the same classification rubric from prose;
- simulate a stable inspection operation more than once;

then that burden should be logged explicitly instead of silently absorbed.

The point is not to ban reasoning. The point is to stop laundering stable missing
operations into invisible reasoning cost.

## What Counts As A Real Burden

A burden entry is appropriate when all three are true:

1. the operation is stable enough to name;
2. the operation recurs within or across tasks;
3. the operation is not merely ordinary code reading.

Examples that usually count:

- "I keep rebuilding the binding/provenance map by hand to know whether a control is
  authority-bearing."
- "I keep manually checking same-context evidence reachability by reading layout and
  interaction files together."
- "I keep reconstructing the realized morph profile from CSS/JSX because no comparison
  surface exists."

Examples that usually do not count:

- one-off unfamiliarity with a file;
- normal local reading to understand a new component;
- a problem caused entirely by ambiguous or missing skill instructions rather than a
  stable missing operation.

## Protocol Steps

### 1. Freeze the baseline

Before any enactment run:

- freeze the governing skill path and current contents;
- freeze the accepted source set for the task;
- freeze the accepted support docs and explicit exclusions;
- choose one bounded task from the task corpus;
- declare `task_mode`:
  - `design`
  - `implementation`
  - `review`
- declare `execution_mode`:
  - `governed_enactment`
- declare `grounding_status`:
  - `repo_grounded`
  - `artifact_grounded_repo_incomplete`
  - `inference_only`
- declare `implementation_inspection_status`:
  - `implementation_inspected`
  - `implementation_not_inspected`

If required implementation facts remain uninspected, later judgments should stay
explicitly inferred rather than being written in repo-grounded certainty.

If a comparison across models is desired, keep the frozen world unchanged and vary only
the model identity.

### 2. Enact the task under the skill

Run the task as though the skill were already operationally real.

Required discipline:

- obey the skill's doctrine as written;
- do not widen the doctrine ad hoc;
- do not silently substitute hidden reasoning for missing stable support surfaces;
- preserve the repo's support-vs-lock authority distinction throughout the run.

### 3. Log burdens during the run

Whenever a recurring reasoning substitute appears, log it immediately in the burden log.

Each entry should record:

- the recurring operation family;
- where in the run it appeared;
- the current manual workaround;
- the source refs involved;
- why this feels like infrastructure rather than ordinary reasoning.

Use:

- `docs/templates/MORPHIC_UX_GOVERNED_ENACTMENT_BURDEN_LOG_TEMPLATE_v0.md`

### 4. Adjudicate each burden after the run

Each burden must be sorted into one of two top-level bins:

- likely `tool_candidate`
- likely `skill_gap`

Then classify it with one of:

- `lawful_required`
- `reliable_required`
- `performance_only`
- `unresolved`

The crucial separation is:

- if the agent already has the governing doctrine but keeps reconstructing the same
  operation anyway, it is probably a tool candidate;
- if the burden vanishes after clarifying doctrine or narrowing the task contract, it is
  probably a skill gap.

### 5. Aggregate across the corpus

Do not promote tool surfaces from one dramatic run alone.

Default promotion rule:

- the same operation family should recur in at least two corpus tasks;
- or recur in one task so heavily that later runs should deliberately try to falsify it.

At aggregation time, merge entries by operation family rather than by local wording.

Examples:

- "manual authority posture trace"
- "same-context evidence reachability trace"
- "morph-profile realization comparison"
- "binding/provenance coverage inspection"

### 6. Propose the minimal support surface

For each recurring burden that survives aggregation:

- define the smallest useful operation;
- define explicit inputs;
- define explicit outputs;
- define clear non-goals;
- state whether the support surface is inspect-only, diagnostic-only, or transform-bearing.

The proposal should be minimal.

Bad proposal:

- "frontend super-inspector that knows layout, authority, evidence, profile drift, and
  runtime intent"

Better proposal:

- "given route files and reference artifacts, classify each control as advisory /
  authoritative / gated / evidence-bearing and emit provenance refs"

### 7. Retest under the same skill

After any accepted support-layer addition, rerun the same or closely comparable task.

The important question is not whether the task still succeeds.
The important questions are:

- did the burden count drop;
- did the run become more explicit and consistent;
- did a purported tool surface actually remove a recurring simulation burden;
- did any burden remain because the real problem was skill ambiguity instead.

## Output Bundle Per Enactment Cycle

One enactment cycle should produce:

- one filled burden log;
- one short run summary;
- one aggregated candidate-surface table after enough runs exist;
- one explicit "tool gap vs skill gap" adjudication note.

## Exit Condition

The current support-layer loop is in a healthy state when:

- no `lawful_required` burden remains unowned;
- repeated `reliable_required` burdens are either promoted or explicitly deferred;
- candidate surfaces have minimal contracts rather than vague wishlists;
- the skill still does real governing work instead of collapsing into tool-specific
  procedural text.

## Bottom Line

This protocol treats missing frontend tools as evidence discovered under governed
enactment, not as brainstorming output.

That is the important move.

It turns the Morphic UX skill into both:

- a frontend operating doctrine; and
- a support-layer adequacy test.
