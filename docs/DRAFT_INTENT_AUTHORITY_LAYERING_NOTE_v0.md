# Draft Intent Authority Layering Note v0

Status: working doctrine note after `V41` family closeout on `main`.

This note clarifies how committed intent docs should be read when they carry draft or
planning status labels but still function as active doctrine surfaces in the repo.

It does not authorize runtime behavior, schema release, or implementation by itself.

## Purpose

- separate interpretive authority from implementation authority;
- make planning-boundary language easier to read without over-promoting it into
  lock-level prohibition;
- clarify what "working draft" means when a doc is committed on `main`.

## Layers

### 1. Lock docs

Lock docs are the only intent surfaces that directly authorize:

- runtime behavior;
- schema release;
- implementation scope;
- new emitted artifact families;
- hard prohibitions that bind a concrete slice.

If a rule needs implementation-authoritative force, it should be stated in a lock doc
or bound by an explicit released contract that points back to one.

### 2. Architecture and decomposition docs

Architecture and decomposition docs are authoritative for:

- conceptual structure;
- family decomposition;
- design intent;
- interpretive boundaries;
- explicit future seams.

They are not, by themselves, implementation-authoritative lock surfaces.

### 3. Planning docs

Planning docs are authoritative for:

- current family-selection posture;
- current planning boundary;
- whether a family/path is considered closed, active, or awaiting successor
  selection;
- what this planning surface does not authorize.

Planning-boundary lines such as:

- "no widening is authorized by this planning draft"
- "no reopening is authorized by this planning draft"

should be read as:

- scope guards for the planning surface; and
- explicit absence-of-authorization statements

not as lock-equivalent permanent prohibitions unless a lock later binds the same rule.

### 4. Support docs

Support docs are authoritative for:

- process discipline;
- review method;
- result-shape expectations;
- claim-posture hygiene.

They are not replacement doctrine for architecture, planning, or locks.

## Working-Draft Status On `main`

When a doctrine doc is committed on `main`, a "working draft" status label should be
read as:

- living doctrine surface;
- open to later refinement;
- still usable for interpretation inside the current repo state.

It should not be read as:

- non-authoritative noise; or
- automatically equivalent to a lock.

So the repo can legitimately use committed draft docs as active intent surfaces while
still reserving implementation authority to locks.

## Transfer Rule

Text from a planning or decomposition doc becomes implementation-authoritative only
when one of the following happens:

1. a lock doc binds it explicitly;
2. a released artifact contract restates it as machine-checkable law;
3. a later authoritative doctrine note promotes it explicitly.

Absent one of those transfers, the text remains:

- interpretive doctrine;
- planning posture; or
- support-method discipline

rather than a lock-level rule.

## Practical Reading Rule For `v23`

For the released `V41` baseline on `main`:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md` may record that no widening or reopening is
  authorized by that planning surface;
- that wording should not be over-read as proof that no later family may lawfully
  revisit adjacent seams;
- later family selection still requires an explicit successor authority surface.
