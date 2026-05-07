# V85 Declaration Probe 024 Assessment

Probe 024 tested the next phase authority law:

```text
phase authority requires a unique current, non-stale phase witness
```

Result:

```text
shape pass:                         8 / 8
branch pass:                        8 / 8
policy pass:                        8 / 8
overall pass:                       8 / 8
component preservation pass:        8 / 8
repair status pass:                 8 / 8
full pointer non-admission pass:    8 / 8
current over stale pass:            2 / 2 applicable
phase authority uncertainty pass:   6 / 6 applicable
```

Model split:

```text
gpt-5.4-mini medium:  4 / 4
gpt-5.4 medium:       4 / 4
```

The current-over-stale case passed:

```text
stale archive row admits ARCHIVE
current semantic row admits CREATE only
ARCHIVE ui.menu@v1
```

Both models followed the unique current non-stale witness:

```text
operator admitted
object admitted
version admitted
pair admitted
phase blocked by current witness
full pointer not admitted
reason = task_phase_blocked
repair = no_repair
components preserved
```

The uncertainty cases also passed:

```text
two current rows conflict
  -> phase_authority_conflict
  -> full pointer not admitted

current row missing
  -> missing_current_phase
  -> full pointer not admitted

currentness marker = current-ish
  -> malformed_currentness
  -> full pointer not admitted
```

All three preserved component admissions and rejected repair or normalization.

Architecture read:

```text
unique current non-stale witness:
  may provide phase authority

stale witness:
  context only

conflicting current witnesses:
  phase_authority_conflict

missing current witness:
  missing_current_phase

malformed currentness:
  malformed_currentness
```

The important result is that phase uncertainty did not collapse into either admission or component erasure. It became a precise non-admission reason that can be routed later by the harness.

Evidence boundary:

```text
proven:
  residents can select closed phase-authority uncertainty branches
  residents do not infer current phase from stale/context rows or task-shaped pointers
  residents preserve admitted components under phase-authority uncertainty

not proven:
  natural task -> semantic pointer binding
  large-registry generalization
  fully opaque branch meanings
  harness-generated remand/correction loop for phase-authority defects
```

Recommended next probe:

```text
Probe 025 should test harness-computed remand after phase-authority uncertainty:
  resident selects conflict/missing/malformed branch
  harness emits targeted remand reasons
  resident corrects only the phase witness defect
  resident preserves component admissions and no-repair posture
```
