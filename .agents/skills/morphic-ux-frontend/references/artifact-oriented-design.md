# Artifact-Oriented Design

This skill uses `artifact` rather than `artefact` to match the repo's existing
vocabulary, but the concept is the same.

## Core rule

Treat the artifact as the minimal operative unit of meaning.

An artifact is the smallest bounded thing the surface can reason with coherently.

That means the design loop should not reason directly in terms of raw pixels, widget
names, or repeated manual calculations when a stable artifact boundary can exist one
level up.

If a needed capability already exists as a trustworthy artifact, import and align it.
If it does not, build it once as a reusable artifact instead of repeatedly
reconstructing it in human reasoning or ad hoc code.

## Artifact classes

### Surface artifacts

These are bounded user-facing capability surfaces.

Examples:

- terminal
- editor
- diff viewer
- tree view
- log viewer
- file picker

### Support artifacts

These are bounded engines or helpers that carry recurring lower-level mechanics so the
host surface can operate at a higher-level formula.

Examples:

- layout solver
- pane ratio engine
- split-view or docking engine
- geometric neighboring or packing helper
- text measurement helper
- diff computation engine

## Decision ladder

For every required capability:

1. Name the artifact and the meta-properties it must satisfy.
2. Check whether a mature existing artifact can be imported.
3. If yes, import and align it into the host workbench.
4. If no, check whether several lower-level artifacts can be composed into one bounded
   local artifact.
5. If not, build one reusable artifact.
6. Do not repeatedly solve the same abstract schema inline in every design pass.

## Meta-properties to name explicitly

Before import or build, state:

- workbench role
- lane or region placement
- authority posture
- evidence posture
- state truth posture
- interaction grammar
- required bindings or provenance hooks
- responsive expectations

For support artifacts, also state:

- input formula or constraint language
- output shape
- non-overlap or adjacency rules
- ratio or geometry rules
- failure or fallback posture

The point is to state the higher-level relation once and let the artifact own the
repeatable lower-level mechanics.

## Import rule

Importing an artifact is not outsourcing design judgment.

The imported artifact may own:

- local rendering mechanics
- local event capture
- local low-level math
- local internal data structures

The host workbench still owns:

- why the artifact exists
- where it sits
- what posture it expresses
- how its states are interpreted
- how its actions interact with gates and evidence
- whether its status language is trustworthy in the host context

## Terminal example

If a terminal is needed:

- prefer adopting a mature OSS terminal implementation;
- treat it as a bounded execution or diagnostic substrate;
- decide at the host layer whether the lane is advisory, operational, diagnostic, or
  commit-adjacent;
- normalize its surrounding state, warnings, bindings, and commit semantics in the host.

Do not let the terminal implementation become the semantic center of the workbench by
default.

## Layout-solver example

If a surface repeatedly needs:

- non-overlapping artifacts
- stable proportions
- geometric neighboring rules
- pane ratios
- bounded split behavior

then do not keep solving those numbers manually in the main design loop.

Prefer one support artifact that accepts the higher-level relation and emits the lower
level math.

Good:

- "left evidence lane stays between 0.28 and 0.36 width while preserving a visible
  trust-boundary lane"

Bad:

- repeated hand-tuning of pixel or flex ratios every iteration with no reusable artifact
  boundary
- re-deriving the same abstract layout schema through trial and error each time a new
  surface or breakpoint is touched

## Common failure patterns

- importing a surface artifact and inheriting its command grammar wholesale
- letting imported status colors define truth posture
- embedding evidence semantics inside a black-box module with no host normalization
- repeatedly re-deriving the same geometry logic in ad hoc code
- solving a recurring low-level problem in human reasoning every time instead of making
  it an artifact
- importing a helper that is mathematically convenient but semantically misaligned with
  the host workbench

## Review questions

- Was the needed capability named as an artifact before implementation?
- Was there a real import, compose, or build decision, or was the team defaulting blindly?
- If imported, did the host retain semantic ownership?
- If composed or built, was it turned into one bounded artifact instead of repeatedly inlined?
- Did a support artifact remove recurring manual math from the design loop?
