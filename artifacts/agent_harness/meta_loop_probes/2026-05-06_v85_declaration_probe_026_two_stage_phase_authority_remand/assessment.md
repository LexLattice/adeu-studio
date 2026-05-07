# V85 Declaration Probe 026 Assessment

Probe 026 tested the full local two-stage phase-authority remand loop:

```text
stage 1:
  resident selects the initial phase-authority defect branch

stage 2:
  harness sends a sparse remand packet
  resident applies only a harness-supplied correction candidate
  or preserves non-admission when no correction is supplied
```

Result:

```text
shape pass:                              8 / 8
branch pass:                             8 / 8
policy pass:                             8 / 8
overall pass:                            8 / 8
two-stage defect detection pass:         8 / 8
component preservation pass:             8 / 8
resident no-repair pass:                 8 / 8
harness correction split pass:           8 / 8
remand correction admission pass:        6 / 6 applicable
unresolved non-admission preserved pass: 2 / 2 applicable
```

Model split:

```text
gpt-5.4-mini medium:  4 / 4
gpt-5.4 medium:       4 / 4
```

The corrected cases passed:

```text
conflicting current rows
  stage 1 -> phase_authority_conflict
  stage 2 -> harness delta makes semantic witness context_only
  -> full pointer admitted

missing current row
  stage 1 -> missing_current_phase
  stage 2 -> harness adds current archive witness
  -> full pointer admitted

malformed currentness
  stage 1 -> malformed_currentness
  stage 2 -> harness changes current-ish to current
  -> full pointer admitted
```

The unresolved case passed:

```text
conflicting current rows
  stage 1 -> phase_authority_conflict
  stage 2 -> no correction supplied
  -> phase_authority_conflict preserved
  -> full pointer not admitted
```

Architecture read:

```text
harness_correction_status:
  corrected_witness_supplied
  no_correction_supplied

resident_repair_status:
  no_resident_repair
```

This split worked. The resident applied harness-supplied correction candidates, but did not treat remand as permission to invent a correction, select the task-shaped row, mutate pointer components, or infer execution or obligation authority.

Scorer note:

```text
An initial policy false positive required widening the no-invented-authority
visibility check to accept equivalent no-extra/no-mutation language.
Branches, shape, and specimen bodies were unchanged.
```

Evidence boundary:

```text
proven:
  residents can detect the initial phase-authority defect
  residents can apply harness-supplied candidate corrections
  residents can preserve unresolved non-admission when no correction is supplied
  residents preserve components and no-resident-repair status across both stages

not proven:
  runtime harness generation of remand packets
  resident artifact editing rather than branch selection
  natural task -> semantic pointer binding
  large-registry generalization
  fully opaque branch meanings
```

Recommended next probe:

```text
Probe 027 should test remand candidate validity:
  valid harness correction
  invalid correction source
  invalid correction field
  conflicting correction candidates

Expected:
  apply only valid harness correction;
  preserve non-admission for invalid or conflicting candidates.
```
