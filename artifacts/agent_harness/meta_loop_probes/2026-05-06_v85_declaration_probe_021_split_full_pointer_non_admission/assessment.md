# V85 Declaration Probe 021 Assessment

Probe 021 isolated the Probe 020 failure by splitting four concepts that had been compressed into one branch:

```text
full_pointer_admission
full_pointer_non_admission_reason
repair_status
component_preservation
```

Result:

```text
shape pass:                   8 / 8
branch pass:                  8 / 8
policy pass:                  8 / 8
overall pass:                 8 / 8
component preservation pass:  8 / 8
repair status pass:           8 / 8
```

Model split:

```text
gpt-5.4-mini medium:  4 / 4
gpt-5.4 medium:       4 / 4
```

The key case was the prior failure:

```text
DELETE ui.menu@v1
```

Probe 020 failure:

```text
full pointer null
  was confused with
component nulling
```

Probe 021 expected and observed:

```text
operator_admission = operator_registry_gap
object_admission = admitted
version_ref_admission = admitted
compatibility = blocked_by_operator_registry_gap
task_phase = blocked_by_operator_registry_gap
full_pointer_admission = not_admitted
full_pointer_non_admission_reason = operator_registry_gap
repair_status = no_repair
component_preservation = admitted_components_preserved
```

Both models selected that correctly.

The pair-gap and version-gap cases also passed:

```text
PROJECT ui.menu@v1
  non-admission reason = operator_object_pair_gap
  component preservation = admitted_components_preserved
  repair status = no_repair

CREATE ui.menu@v2
  non-admission reason = version_ref_gap
  component preservation = admitted_components_preserved
  repair status = no_repair
```

The full-admission control also passed:

```text
CREATE ui.menu@v1
  full pointer admitted
  non-admission reason = not_applicable
  repair status = no_repair
  component preservation = admitted_components_preserved
```

Architecture read:

```text
full pointer non-admission:
  is a canonical full-pointer status

component preservation:
  is a separate partial-knowledge status

repair status:
  is a separate anti-silent-repair status
```

This confirms that the Probe 020 failure was representational, not a failure of the resident to follow the D-law. Once the branch basis was decomposed, both `gpt-5.4-mini` and `gpt-5.4` followed it cleanly.

Evidence boundary:

```text
proven:
  split branches remove the full-pointer-null/component-nulling ambiguity
  residents can preserve partial component knowledge while blocking canonical full pointer admission
  no-repair status is stable when made first-class

not proven:
  large-registry generalization
  hidden-route semantic binding
  stable selection when branch meanings are fully opaque
```

Recommended next probe:

```text
Probe 022 should keep the split-branch shape, then increase difficulty by using
either a larger mixed registry or less self-descriptive branch labels.
```
