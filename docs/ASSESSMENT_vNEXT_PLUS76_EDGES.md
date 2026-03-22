# Assessment vNext+76 Edges

Status: planning-edge assessment for `V39-E`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS76_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Deterministic / Oracle Authority Collapse

- Risk:
  the first hybrid lane could let oracle output become the de facto authority instead
  of a typed advisory input to deterministic adjudication.
- Response:
  keep deterministic adjudication as the only authority over final checkpoint
  disposition and trace materialization, and freeze exact
  `checkpoint_class -> final_adjudication` transition law.

### Edge 2: Released Coverage Overclaim

- Risk:
  because released `V39-C` / `V39-D` fixtures are intentionally deterministic-local,
  the first hybrid baseline could fake oracle-assisted coverage by pretending local
  hybrid fixtures are already released conformance findings.
- Response:
  require explicit `source_kind` separation between released findings / fix-plan items
  and local hybrid fixtures, and forbid laundering the latter into released
  observation coverage.

### Edge 3: Registry / Report / Plan Bypass

- Risk:
  the hybrid lane could skip released upstream artifacts and synthesize checkpoints
  directly from raw repo scans or free-form prompts.
- Response:
  require exact binding to released registry, conformance, and fix-plan artifacts
  whenever those bindings exist, fail closed on mismatches, and keep it explicit that
  checkpoints may bind either to released conformance findings or released fix-plan
  projections depending on source surface.

### Edge 4: Cache / Replay Drift

- Risk:
  oracle request reuse could occur across different source, policy, or model
  identities and silently distort adjudication.
- Response:
  pin replay identity across source hashes, policy hashes, model id, model version,
  reasoning effort, and evaluator/template version, and reject non-exact cache reuse.

### Edge 5: Unbounded Oracle Recursion

- Risk:
  once the lane can call an oracle, it could quietly expand into repeated oracle
  retries or open-ended agent loops.
- Response:
  freeze one oracle request / resolution cycle maximum per checkpoint in `V39-E`.

### Edge 6: Human-Only Route Leakage

- Risk:
  `human_only` rules could still emit oracle requests through convenience logic and
  undermine the route boundary.
- Response:
  require direct `human_needed` disposition for `human_only` checkpoints with no
  oracle request emission, and forbid request emission outside
  `checkpoint_class = oracle_needed`.

### Edge 7: Oracle-Output Mutation Overclaim

- Risk:
  oracle response text could be treated as if it were already an authorized edit,
  patch payload, or repo-mutation instruction.
- Response:
  keep oracle output advisory-only and forbid any direct mutation authority in the
  released artifacts, including minting new rule metadata or new subject provenance.

### Edge 8: Source-Identity Ambiguity

- Risk:
  duplicate or stale checkpoints could survive validation if checkpoint identity is
  left implicit rather than frozen to an exact source-binding tuple.
- Response:
  define checkpoint identity explicitly from `source_kind`, exact source binding,
  `rule_id`, `subject_ref`, and local anchor, and reject exact duplicates.

### Edge 9: Contradictory-Output Laundering

- Risk:
  contradictory or unstable oracle outputs could be normalized into apparent success
  instead of surfacing as unresolved.
- Response:
  require fail-closed conversion of contradictory, unstable, or replay-inconsistent
  resolutions into `human_needed`.

### Edge 10: Live-Network Evidence Leakage

- Risk:
  the hybrid lane could start treating live GitHub state or live network responses as
  canonical evaluation evidence rather than reproducible local inputs.
- Response:
  keep canonical evidence local and committed; allow only deterministic local
  provenance in the released baseline.

### Edge 11: Detector-Widening Leakage

- Risk:
  `V39-E` could quietly smuggle broader detector rollout or semantic-ambiguous
  observation coverage into the family under the label of hybrid execution.
- Response:
  keep released detector coverage unchanged in this slice and route oracle/human cases
  through explicit local hybrid fixtures only.

### Edge 12: Authorship Regression

- Risk:
  once hybrid adjudication exists, the lane could slide back into governing against
  “AI-looking code” rather than pressure-mismatch drift.
- Response:
  keep authorship/origin absent from the hybrid schemas, builders, fixtures, and
  tests.

## Current Judgment

- `V39-E` is worth implementing now because `V39-A` through `V39-D` are released on
  `main`, and the family now needs an explicit typed checkpoint and oracle lane before
  any later widening into mutation or broader execution surfaces can be discussed
  honestly.
