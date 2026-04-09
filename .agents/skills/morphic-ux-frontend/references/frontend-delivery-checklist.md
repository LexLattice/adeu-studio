# Morphic UX Delivery Checklist

Use this when implementing, reviewing, or refining a surface under the skill.

## Before design

- Declare `task_mode`, `execution_mode`, `grounding_status`, and `implementation_inspection_status`.
- Identify the user archetype, risk level, trust sensitivity, and interaction mode.
- List required evidence visibility rules.
- Rank utility goals in order.
- Declare invariants and morphable choices separately.
- Choose a lawful morph profile or state that a new profile is being proposed.
- Name the required surface artifacts and support artifacts before discussing implementation details.
- For each required artifact, state whether the plan is to import, align, compose, or build it.
- For each artifact, name the host-owned meta-properties that cannot be delegated away.

## Before coding

- Inspect the current route entrypoint, component tree or region composition, state-bearing surfaces, and interaction boundaries for the target surface.
- Name the workbench root.
- Define regions.
- Define lanes inside regions.
- Place action clusters in lanes.
- Place state surfaces in lanes.
- Mark evidence-bearing regions.
- Mark trust-boundary surfaces.
- Mark explicit commit or handoff boundaries.
- Note which responsive changes are allowed and which would count as a context break.
- Decide which required artifacts can be adopted from OSS or existing local implementations rather than rebuilt.
- For every imported artifact, state what the host workbench still owns semantically.
- If no single import fits, decide whether several lower-level pieces should be composed into one bounded local artifact.
- For every recurring layout or geometry problem, decide whether a reusable support artifact should own it instead of ad hoc reasoning.

## During implementation

- Keep advisory, commit, and authoritative actions visually distinct.
- Keep gate states visible.
- Put prerequisite explanations close to gated controls.
- Render provisional, ambiguous, stale, conflicted, and authoritative states with distinct treatment.
- Keep evidence lanes persistent or same-context reachable.
- Avoid moving required evidence behind navigation, route changes, or detached overlays unless the contract says so.
- Use motion to reveal state or focus changes, not to simulate authority.
- Prefer data attributes or stable ids when provenance and testability matter.
- Wrap adopted artifacts so the host can normalize posture, truth state, and bindings instead of inheriting their semantics wholesale.
- Feed support artifacts high-level relations or constraints rather than repeatedly hand-tuning raw numbers when possible.
- When repeated numeric tuning appears, push it into a reusable support artifact instead of continuing manual trial-and-error.
- If implementation facts remain uninspected or uncertain, keep the output labeled as inferred rather than repo-grounded.

## Review questions

- Can a user understand what is authoritative without reading surrounding prose?
- Can a user understand what is missing before a gated action becomes available?
- Is the primary action obvious?
- Is any destructive or committing action reachable before evidence review?
- Does any visual styling overstate certainty or permission?
- Does mobile or narrow layout preserve the same-context rule?
- Did the implementation keep the chosen morph profile coherent, or drift into mixed signals?
- Were missing implementation facts called out explicitly, or did the review speak with counterfeit certainty?
- Was there a real import, compose, or build decision for each recurring capability, or did the team default blindly?
- Did any imported artifact leak a foreign command grammar, status language, or authority posture into the governed host surface?
- Did the team keep manually re-solving a recurring abstract schema that should have been externalized as a support artifact?

## Common failure patterns

- Evidence-first brief, task-first implementation.
- Full-explicit state exposure in the plan, collapsed hidden statuses in the UI.
- Dual-lane command posture in the IR, merged control bar in the layout.
- Advisory surface with authoritative color and emphasis.
- Ambiguous or loading state rendered with success affordances.
- Commit boundary represented as a normal primary button with no surrounding gate explanation.
- Responsive simplification that removes status or evidence lanes entirely.
- Treating widgets or inline math as the design unit when a bounded artifact should exist.
- Repeated hand-tuning of ratios, adjacency, or non-overlap rules with no reusable artifact boundary.

## Closeout expectation

A good closeout summary for Morphic UX work should say:

- which profile was used
- which invariants were preserved
- which artifacts were imported, aligned, composed, or built
- where evidence-before-commit is rendered
- how authority boundaries are expressed
- how responsive states preserve same-context reachability
