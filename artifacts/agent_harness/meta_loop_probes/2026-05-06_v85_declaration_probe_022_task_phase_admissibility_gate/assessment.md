# V85 Declaration Probe 022 Assessment

Probe 022 isolated task-phase admissibility as its own gate after component admission and operator-object compatibility.

Result:

```text
shape pass:                   8 / 8
branch pass:                  8 / 8
policy pass:                  8 / 8
overall pass:                 8 / 8
component preservation pass:  8 / 8
repair status pass:           8 / 8
full pointer non-admission:   4 / 4 applicable
task phase block:             2 / 2 applicable
```

Model split:

```text
gpt-5.4-mini medium:  4 / 4
gpt-5.4 medium:       4 / 4
```

The key case was:

```text
ARCHIVE ui.menu@v1
active phase = semantic_declaration_review
```

The operator, object class, version ref, and operator-object pair were all admitted:

```text
ARCHIVE is registered
ui.menu is registered
ui.menu@v1 is registered
ARCHIVE/ui.menu is admitted
```

But `ARCHIVE` was not phase-admissible in `semantic_declaration_review`. Both models selected:

```text
phase blocked
full pointer not admitted
non-admission reason = task_phase_blocked
repair status = no_repair
component preservation = admitted_components_preserved
```

The controls also passed:

```text
ARCHIVE ui.menu@v1 in archive_review
  full pointer admitted
  non-admission reason = not_applicable

CREATE ui.menu@v1 in semantic_declaration_review
  full pointer admitted
  non-admission reason = not_applicable

ARCHIVE ui.menu@v2 in archive_review
  phase admitted
  version ref gap
  full pointer not admitted
  non-admission reason = version_ref_gap
```

Architecture read:

```text
component admission
+ operator-object compatibility
+ task-phase admissibility
+ full pointer admission
+ non-admission reason
+ repair status
+ component preservation
```

The phase gate is now cleanly separated from registry and compatibility gates. A phase block does not erase admitted components, and it does not authorize repair to a nearby phase-admissible operator.

Evidence boundary:

```text
proven:
  given harness-parsed candidates, explicit registry evidence, explicit phase rows,
  and closed branches, both residents select the lawful task-phase gate

not proven:
  natural task -> semantic pointer binding
  large-registry generalization
  selection under noisy or contradictory phase evidence
  fully opaque branch meanings
```

Recommended next probe:

```text
Probe 023 should keep the split-branch basis but make phase evidence less direct:
move phase admissibility into separate evidence rows, include irrelevant phase rows
and task-intent bait, and test that the resident follows the active phase row rather
than the nearest task-shaped operator.
```
