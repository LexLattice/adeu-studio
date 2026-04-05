# Assessment vNext+137 Edges

Status: pre-lock edge assessment for `V46-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS137_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Concrete Projection Reopens Substrate Doctrine

- Risk:
  the first concrete procedural-depth slice could quietly redefine the released
  `V46-A` benchmark substrate instead of consuming it.
- Response:
  require exact binding to the released family spec, projection spec, and execution
  context, and forbid a second benchmark-substrate fork in `V46-B`.

### Edge 2: Declared Contract Ids Drift From Released Artifacts

- Risk:
  the released `V46-A` projection spec already declares downstream procedural-depth
  contract ids, and `V46-B` could ship mismatched live ids.
- Response:
  require exact id parity between the `declared_*_contract_id` fields in the released
  projection spec and the actual released procedural-depth schema ids.

### Edge 3: Tiny Reference Chain Widens Into Benchmark-Library Sprawl

- Risk:
  the first concrete benchmark projection could widen from one tiny deterministic
  hierarchical reference chain into a broader library before the family has released
  perturbation or non-regression doctrine.
- Response:
  freeze `V46-B` to one tiny hierarchical `3x3` reference chain only and defer wider
  perturbation/non-regression families to `V46-C`.

### Edge 4: Imported Materialization Bug Reappears In Repo-Owned Instance Law

- Risk:
  the imported prototype computes procedural-depth instance ids before canonical step
  ordering is validated, which can make lawful payloads fail id checks.
- Response:
  require canonical structural validation before instance-id materialization and treat
  that imported bug as explicitly non-importable.

### Edge 5: Gold Trace And Run Trace Drift Apart Semantically

- Risk:
  `V46-B` could release a gold trace and run trace that appear compatible while lacking
  deterministic shared binding to one released instance and repo snapshot.
- Response:
  require exact instance binding, deterministic gold-trace derivation from the
  instance, and deterministic run-trace scoring against that bound gold trace only.

### Edge 6: Metrics Collapse Into One-Number Benchmark Promotion

- Risk:
  the first metrics surface could over-collapse the structural split into a single
  promotion-ready number.
- Response:
  keep component fidelity surfaces explicit:
  - `plan_spine_fidelity`
  - `active_step_compilation_fidelity`
  - `reintegration_fidelity`
  - `dominant_failure_family`
  and forbid ranking/promotion semantics in the starter slice.

### Edge 7: Diagnostic Reports Overclaim Operational Authority

- Risk:
  the first diagnostic-report surface could be overread as routing, ranking, or
  training authority rather than bounded benchmark diagnosis.
- Response:
  keep `V46-B` diagnostic reports explicitly non-promotional and defer downstream
  consumer seams to `V46-E`.

### Edge 8: Event Vocabulary Widens Before Perturbation Doctrine Exists

- Risk:
  the starter projection could start carrying branch/repair/recursive event kinds that
  belong to later perturbation or wider projection lanes.
- Response:
  freeze the starter event vocabulary to:
  - `activate`
  - `complete`
  - `return`
  and defer wider event families to later `V46` paths.

## Current Judgment

- `V46-B` is the right next slice because `V46-A` has already released the benchmark
  substrate and the family now needs one concrete procedural-depth projection stack.
- the safest starter move is one tiny deterministic hierarchical `3x3` reference chain
  over a bounded repo snapshot, not perturbation widening and not benchmark-library
  sprawl.
- the most important implementation edge is canonical instance materialization:
  the known imported id-ordering bug must not survive into the live repo-owned package.
