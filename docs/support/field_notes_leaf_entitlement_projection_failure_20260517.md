# Field Notes: Leaf Entitlement and Projection Failure

Authority layer: support / field notes.

Date: 2026-05-17.

ProgramBench task:

```text
boyter__scc.515f91c
```

## Observation

The Phase31 repair fixed a real class of errors. The candidate moved from the
Phase22 official score of `29` to the Phase32 official score of `40`, and raw
official eval rows improved from `134 passed / 341 failed` to
`188 passed / 287 failed`.

The local gate before Phase32 was fully green:

```text
phase25_promoted_rows = 106 / 106
phase28_repaired_rows = 36 / 36
legacy_local_gate = 142 / 142
```

So the remaining official failures should not be read as evidence that Phase31
was ineffective. Phase31 correctly repaired a narrower transition failure:

```text
observed local leaf
  -> overpromoted to implementation-ready behavior
  -> missing proof that the same discriminator owns sibling projections
```

The repaired class was not a new top-level ontology. It was a bad promotion
boundary. We had leaves that were locally witnessed, but we let them cross into
implementation truth before proving their projection rights over sibling
surfaces.

## Failure Class

Name:

```text
leaf_entitlement_projection_failure
```

Shape:

```text
high-level phenomenon exists in the tree
  -> one or more leaves are observed
  -> local probes pass for those leaves
  -> leaf is treated as implementation-ready
  -> sibling projection surfaces remain unproven
  -> official eval exposes the missing projection entitlement
```

This differs from a missing ontology failure. The parent concept can be present
and still fail if the transition from concept to executable obligation does not
prove enough siblings.

## Meta-Program Patch

Insert a required pass between scoped observation and implementation handoff:

```text
Leaf Entitlement / Projection Rights Audit
```

For every candidate implementation leaf, require:

```text
leaf_id
owning_parent_discriminator
observed_fixture_refs
public_projection_surfaces
sibling_projection_matrix
negative_control_refs
regression_retention_refs
cross_axis_composition_refs
status
```

Allowed statuses:

```text
observed_leaf_only
projection_entitled
scoped_ready
gold_ready
projection_gap
explicitly_deferred_with_expected_risk
```

Hard rule:

```text
observed_leaf_only cannot become implementation-ready.
```

Promotion requires at least one of:

```text
projection_entitled:
  the leaf's owning discriminator has been tested across the relevant sibling
  projection surfaces and negative controls.

explicitly_deferred_with_expected_risk:
  the missing siblings are named, the score risk is carried forward, and the
  run is not called a gold implementation handoff.
```

## Required Sibling Matrix

For SCC-like counting programs, a leaf is not entitled merely because it works
in one default table row. The audit must ask whether the discriminator still
holds across relevant public surfaces such as:

```text
aggregate vs by-file
default table vs wide vs csv/json/sql/html/openmetrics
stdout vs output file
normal vs debug/trace/verbose
single root vs multi-root
included vs ignored vs count-ignore
generated/minified included vs excluded vs labeled
remapped language vs native language vs shared extension
cost disabled vs cocomo vs locomo
sort disabled vs sort by each derived metric
flag enabled vs disabled vs invalid value
```

The exact list is task-specific. The generic requirement is not.

## Regression Rule

If fixing one leaf breaks another leaf that was already green, do not keep
patching the two leaves independently. Ascend to the smallest shared parent
discriminator and repair that parent rule.

Expected artifact:

```text
upstream_discriminator_row
  broken_branch_refs
  retained_green_branch_refs
  candidate_parent_rule
  counterfactual_probe_refs
  regression_retention_probe_refs
```

## Practical Lesson

The meta-program must separate these statements:

```text
We observed this behavior once.
We know the discriminator that generated it.
We know which sibling projections it owns.
We know which projections remain unproven.
We are ready to implement it as gold behavior.
```

Only the fourth and fifth statements can support a full gold handoff.

