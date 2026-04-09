# Draft Morphic UX Governed Enactment Task Corpus v0

Status: working draft support corpus (April 8, 2026 UTC).

Authority layer: support.

This document defines a bounded task corpus for running the Morphic UX governed-enactment
protocol against the current released `artifact_inspector_advisory_workbench` family.

It does not authorize code changes, tool releases, or schema changes by itself.

## Purpose

- provide a stable comparison corpus for multi-run or multi-model enactment;
- make recurring burdens comparable instead of anecdotal;
- keep tool discovery tied to real frontend work instead of generic wishlists.

## Corpus Discipline

Keep these fixed unless the run explicitly says otherwise:

- governing skill:
  - `.agents/skills/morphic-ux-frontend/SKILL.md`
- reference grounding:
  - `.agents/skills/morphic-ux-frontend/references/source-grounding.md`
- primary released surface:
  - `apps/web/src/app/artifact-inspector/page.tsx`
  - `apps/web/src/app/artifact-inspector/reference-surface.ts`
  - `apps/web/src/app/artifact-inspector/page.module.css`
- released reference artifacts:
  - `apps/api/fixtures/ux_governance/vnext_plus61/`
  - `apps/api/fixtures/ux_governance/vnext_plus62/`
- relevant contract and walkthrough support:
  - `docs/support/DRAFT_UX_MORPH_CHANGE_SCOPING_WALKTHROUGH_v0.md`
  - `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`

Suggested exclusions:

- `.git/`
- `.venv/`
- `node_modules/`
- `.next/`
- unrelated app routes
- web lookups and non-repo oracles

## Recommended Run Order

Run the corpus in this order so the earlier tasks establish baseline burdens before
implementation-bearing tasks start:

1. `MUX-GE-01`
2. `MUX-GE-02`
3. `MUX-GE-03`
4. `MUX-GE-04`
5. `MUX-GE-05`
6. `MUX-GE-06`

## Task Definitions

### `MUX-GE-01` — Reference Surface Conformance Review

Type: review-only.

Goal:

- review the current artifact inspector reference surface under the Morphic UX skill and
  report whether the realized surface preserves the released family doctrine.

Expected outputs:

- concise conformance review;
- filled burden log.

Burdens to watch for:

- manual reconstruction of action posture across `page.tsx` and `reference-surface.ts`;
- manual same-context evidence reachability proof;
- manual state-surface truth classification;
- manual inference of why a given region or lane counts as evidence-bearing.

Why this task is in the corpus:

- it establishes the baseline reading burden before any design or implementation change
  is attempted.

### `MUX-GE-02` — Alternate Profile Morph Plan

Type: design-only.

Goal:

- derive a lawful morph plan from the current reference profile to the released alternate
  profile without breaking frozen invariants or widening authority.

Expected outputs:

- explicit invariant list;
- explicit morphable list;
- before/after region and lane comparison;
- filled burden log.

Burdens to watch for:

- manual comparison of chosen profile versus realized layout;
- manual determination of which topology changes are lawful versus family-breaking;
- repeated cross-reference between profile axes and current CSS/JSX.

Why this task is in the corpus:

- it stresses morph-axis reasoning directly, which should reveal whether a comparison or
  projection helper is missing.

### `MUX-GE-03` — Add One New Gated Authoritative Interaction

Type: implementation-bearing.

Goal:

- add one bounded authoritative or commit-adjacent interaction to the current family
  without minting authority locally and while preserving explicit gating posture.

Expected outputs:

- implementation diff;
- explanation of gate source, preconditions, and visible consequences;
- filled burden log.

Burdens to watch for:

- manual reconstruction of interaction-contract fields from existing patterns;
- repeated uncertainty about disabled-state visibility and gate-source placement;
- repeated manual checks that the action stays in the correct cluster and lane.

Why this task is in the corpus:

- it tests whether the skill can move from doctrine to interaction-bearing execution
  without needing hidden infrastructure.

### `MUX-GE-04` — Preserve Same-Context Evidence Reachability On Narrow Width

Type: implementation-bearing.

Goal:

- adapt the surface for a narrower viewport while preserving the same-context evidence
  rule and without laundering a route transition into a lawful morph.

Expected outputs:

- responsive diff or plan;
- explicit statement of what changed spatially versus semantically;
- filled burden log.

Burdens to watch for:

- repeated manual reasoning about whether a disclosure move remains same-context;
- repeated uncertainty about whether a drawer, panel, or section reveal is lawful;
- manual proof that evidence and status stay reachable before commit.

Why this task is in the corpus:

- it should reveal whether the support layer is missing a direct reachability or
  responsive-semantic inspection surface.

### `MUX-GE-05` — Add One New State-Distinction Surface With Stable Hooks

Type: implementation-bearing.

Goal:

- add one new status, warning, diagnostic, or provisional surface and wire it with stable
  provenance or binding exposure compatible with the family's truth posture.

Expected outputs:

- implementation diff;
- explicit state classification and styling rationale;
- filled burden log.

Burdens to watch for:

- manual determination of which surfaces count as state-distinction surfaces;
- repeated uncertainty about hook shape or coverage;
- manual tracing of where provenance and binding expectations come from.

Why this task is in the corpus:

- it probes whether the missing support is really about provenance coverage inspection.

### `MUX-GE-06` — Diagnose A Deliberately Bad Surface Proposal

Type: review-only or design-only.

Goal:

- evaluate a deliberately unlawful proposal such as:
  - collapsing advisory and commit actions into one toolbar;
  - hiding required evidence behind a route transition;
  - styling provisional data as authoritative;
  - presenting two competing primary actions in one region.

Expected outputs:

- explicit violation analysis;
- severity classification;
- filled burden log.

Burdens to watch for:

- manual recollection of violation families and thresholds;
- repeated need to justify a finding from several support and released sources at once;
- manual crosswalk from proposal shape to conformance severity.

Why this task is in the corpus:

- it tests whether the skill already has enough explicit diagnostic structure or whether a
  conformance helper is missing.

## Comparison Rule

If multiple models or multiple tool surfaces are being compared:

- do not change the frozen world;
- do not change the task text materially;
- do not change the accepted support docs;
- change only the model, tool surface, or skill revision being tested.

That is what makes burden recurrence meaningful instead of anecdotal.

## Promotion Signal

One burden family becomes a serious support-layer promotion candidate when:

- it appears in at least two tasks in this corpus;
- it survives after one honest attempt to clarify the skill instead;
- it has a stable enough input/output shape to specify minimally.

## Bottom Line

This corpus is not a generic UX benchmark.

It is a bounded pressure rig for the current Morphic UX skill and the released
`artifact_inspector_advisory_workbench` family.
