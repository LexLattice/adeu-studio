# Draft Future Seam Promotion Rules v0

Status: working doctrine note after `V41` family closeout on `main`.

This note records how a future seam should move from "explicitly deferred" to
"selectable for a new family."

It does not authorize runtime behavior, schema release, or implementation by itself.

## Purpose

- make future-family promotion more explicit;
- reduce silent widening from closed-family planning docs into new work;
- clarify how prior-family artifacts should be treated by successor families.

## Promotion Rules

### 1. A deferred seam remains live until explicitly forbidden

If a seam is:

- deferred;
- not solved;
- not attempted; or
- reserved for later family-selection work

then the default reading is:

- still live for later explicit selection.

Silence is not prohibition.

### 2. A future seam should not be promoted without an explicit authority surface

A seam promotion should identify:

- the governing authority source;
- the target family label;
- the claimed scope;
- the accepted shipped scope;
- the non-goals that remain deferred.

### 3. Entry criteria should be typed

Before a future seam is promoted, the successor doctrine should state at least:

- why the seam is being selected now;
- which unresolved pressure or user need motivates it;
- what prior-family assumptions it inherits;
- what disqualifies promotion at the current time.

### 4. Prior-family artifact consumption default

Default rule:

- released prior-family artifacts should be consumed as the stable substrate for
  successor work unless a later lock explicitly says otherwise.

If a successor family wants to supersede or version-bump a prior-family artifact, the
successor authority surface should state:

- which artifact is being superseded;
- whether the old artifact remains valid for historical replay;
- whether migration, coexistence, or replacement is intended;
- why stable consumption is insufficient.

### 5. Broad architecture family to narrow family mapping should be explicit

When a broad architecture spec names more artifacts or seams than a later family
instantiates, the narrowing should classify each broader item as one of:

- instantiated_here
- deferred_to_later_family
- superseded_by_alternate_surface
- not_selected_yet

This avoids an implicit jump from:

- "the architecture family can support X"

to:

- "the current family silently replaced or exhausted X"

### 6. Future-family notes should state successor posture plainly

A future-family selection note should say whether prior closed-family artifacts are
being treated as:

- stable substrate
- bounded baseline likely to be extended
- bounded baseline likely to be superseded

That posture should not be left implicit.
