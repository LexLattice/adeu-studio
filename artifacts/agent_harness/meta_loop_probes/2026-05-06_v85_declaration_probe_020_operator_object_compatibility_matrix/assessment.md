# V85 Declaration Probe 020 Assessment

Probe 020 moved beyond component admission into operator-object compatibility and task-phase admissibility.

The new D-law was:

```text
Full pointer admission requires:
  component admission
  operator-object compatibility
  task-phase admissibility
```

Result:

```text
shape pass:    14 / 14
branch pass:   13 / 14
policy pass:   13 / 14
overall pass:  13 / 14
```

Model split:

```text
gpt-5.4-mini medium:  7 / 7
gpt-5.4 medium:       6 / 7
```

The good result is that the compatibility gate held where it mattered:

```text
PROJECT ui.menu@v1
  operator admitted
  object admitted
  version admitted
  phase admitted
  pair compatibility blocked
  full pointer null
```

Both models handled that correctly. Component existence was not treated as full pointer authority, and neither model repaired `PROJECT/ui.menu` to `CREATE/ui.menu` or `MODIFY/ui.menu`.

The version-gap cases also held:

```text
CREATE ui.modal@v2
CREATE ui.menu@v2
```

Both models kept operator/object/pair/phase admissions where appropriate, blocked the missing version refs, and did not repair to `ui.modal@v1` or `ui.menu@v1`.

The useful failure:

```text
case:
  DELETE ui.menu@v1

expected:
  full_pointer_admission_branch = S9
  full pointer null

observed in one gpt-5.4 specimen:
  full_pointer_admission_branch = S2
  repaired_or_unknown pointer
```

The failure is precise. The resident correctly selected:

```text
operator_admission_branch = P2
object_admission_branch = L8
version_ref_admission_branch = N5
operator_object_compatibility_branch = U3
task_phase_admissibility_branch = X4
```

So it preserved the raw operator gap and did not null object/version components. But it interpreted the explicit full-pointer null branch as if that would erase admitted object/version components:

```text
S9 would wrongly null an otherwise admitted object/version
```

That is the shape leak:

```text
full pointer null
  got confused with
component nulling
```

The correct doctrine is:

```text
full_pointer_admission = null
  means no canonical full pointer admitted

It does not mean:
  admitted component branches are nulled
```

Architecture read:

```text
proven:
  operator-object compatibility belongs in the admission gate
  component admissions can be preserved while full pointer is blocked
  gpt-5.4-mini is still stable as a bounded branch selector in this matrix

not proven:
  full-pointer null wording is unambiguous under operator-gap cases
  residents reliably separate full-pointer non-admission from component nulling
```

Recommended next probe:

```text
Probe 021 should isolate the DELETE/operator-gap case with split branches:

full_pointer_admission:
  admitted
  not_admitted

full_pointer_non_admission_reason:
  operator_registry_gap
  version_ref_gap
  compatibility_gap

component_preservation:
  admitted_components_preserved
  admitted_components_nulled

repaired_pointer_status:
  no_repair
  repaired_or_unknown
```

That should remove the ambiguity exposed here: a null full pointer is not a nulling of its admitted components.
