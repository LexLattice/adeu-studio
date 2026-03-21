# Assessment vNext+73 Edges

Status: planning-edge assessment for `V39-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS73_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Authorship Regression

- Risk:
  the slice could slide back into "AI accent" policing instead of governing
  pressure-mismatch drift.
- Response:
  keep authorship, origin, and model identity out of the registry schema and tests.

### Edge 2: Detector Smuggling

- Risk:
  the first slice could quietly ship observation packets, detectors, or scoring
  behavior under the registry label.
- Response:
  keep `V39-B` limited to taxonomy, schema law, canonical fixture, and validators
  only; defer detectors to `V39-C`.

### Edge 3: Scoring Creep

- Risk:
  the registry could introduce a hidden scalar posture or merge-worthiness summary
  that later becomes policy by inertia.
- Response:
  keep the registry anti-score by construction and reserve any convenience posture
  summaries for later report artifacts only.

### Edge 4: Weak-Signal Overreach

- Risk:
  weakly evidential families such as shape regularity could be over-enforced as if
  they were deterministic correctness failures.
- Response:
  block `safe_autofix` for those classes in the first slice and preserve explicit
  evidence-regime distinctions.

### Edge 5: Glossary Boundary Blur

- Risk:
  the new vocabulary could silently overload the existing `V36-A` same-context
  glossary or create a second glossary without explicit lock text.
- Response:
  keep the vocabulary registry-local in `V39-B` and freeze any glossary export
  decision to a later lock if still needed.

### Edge 6: Package Fragmentation

- Risk:
  the slice could split across new packages too early, creating schema drift before
  the conformance family has proven its stable shape.
- Response:
  keep first implementation placement in `adeu_core_ir` and revisit a dedicated
  conformance package only after multiple released slices justify it.

### Edge 7: Oracle-Lane Leakage

- Risk:
  adding `resolution_route` could be misread as proof that oracle-assisted execution
  already exists in the repo.
- Response:
  keep the route vocabulary as routing metadata only in `V39-B` and reserve actual
  checkpoint execution to `V39-E`.

### Edge 8: Utility Vocabulary Mush

- Risk:
  `expected_utility_gain` could stay too open-ended and erode the otherwise precise
  registry law.
- Response:
  freeze `expected_utility_gain` to a bounded vocabulary in the first schema release.

### Edge 9: Registry/Instance Collapse

- Risk:
  registry entries could be misread as concrete findings rather than law about where a
  rule may apply and how it may resolve.
- Response:
  make registry-only applicability explicit and use bounded
  `applicable_subject_kinds` arrays instead of instance-like subject references.

### Edge 10: Safe-Autofix Drift

- Risk:
  `safe_autofix` could drift into contextual or oracle-assisted rules over time.
- Response:
  require every `safe_autofix` rule to pair with
  `evidence_regime = deterministic_local` and
  `resolution_route = deterministic_only`.

### Edge 11: Counterexample Mush

- Risk:
  `counterexample_policy` could be present in name only while remaining too vague to
  constrain false positives.
- Response:
  require it to state non-application conditions, defeating evidence, and exemption
  review posture.

### Edge 12: Registry Integrity Drift

- Risk:
  the first canonical fixture could still admit duplicate ids, empty registries, or
  rules with no admissible subject surface.
- Response:
  reject those shapes deterministically in the first validator release.

## Current Judgment

- `V39-B` is worth implementing now because the repo has already released a bounded
  conformance substrate in `V39-A` and now needs a typed registry law before it can
  safely widen into detectors, fix plans, or hybrid adjudication.
