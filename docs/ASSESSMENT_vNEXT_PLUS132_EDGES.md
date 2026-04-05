# Assessment vNext+132 Edges

Status: post-closeout edge assessment for `V44-B` (April 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS132_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Taxonomy Overclaims As Score

- Risk:
  the first taxonomy slice could collapse structural reasoning fidelity into a single
  promotional number or ranking surrogate.
- Response:
  keep `V44-B` taxonomy-first only and explicitly forbid one-number
  structural-fidelity summaries, rankings, or benchmark scoring.
- Closeout Evidence:
  the shipped schema/package surface carries normalized taxonomy only, with no score,
  ranking, profile, or benchmark projection fields.

### Edge 2: Blocked Posture Is Misread As Failure

- Risk:
  lawful insufficiency could be normalized into failure-family outputs, erasing the
  distinction already released in `V44-A`.
- Response:
  freeze a separate blocked taxonomy status and require reject fixtures for blocked
  traces coerced into failure-family output.
- Closeout Evidence:
  the released taxonomy vocabulary keeps `blocked_lawful_insufficiency` distinct, the
  blocked reference fixture validates cleanly, and the reject fixture for
  blocked-with-failure-family posture fails closed.

### Edge 3: Mapping Law Becomes Implementation Taste

- Risk:
  the taxonomy helper could silently map break tags or event combinations using
  unstated heuristics rather than released `V44-A` structure.
- Response:
  bind the starter mapping law to released probe/trace surfaces and the released
  `V44-A` fixture expectation matrix, failing closed on unmapped cases.
- Closeout Evidence:
  `taxonomy.py` consumes only released `V44-A` structures, the mapping-matrix fixture
  is committed, and unsupported break tags fail closed through the shipped reject
  trace.

### Edge 4: Hierarchy-Aware Families Stay Vocabulary-Only

- Risk:
  `plan_spine_drift`, `active_step_decomposition_failure`, and
  `reintegration_failure` could remain frozen in vocabulary while never being
  positively exercised in fixtures.
- Response:
  require direct positive reference fixtures for all three hierarchy-aware starter
  families before accepting the slice.
- Closeout Evidence:
  the shipped `v44b` fixture pack contains explicit reference taxonomy and supporting
  trace fixtures for all three hierarchy-aware starter families.

### Edge 5: `V44-C` Differential Doctrine Arrives Prematurely

- Risk:
  paired-condition knowledge-versus-procedure diagnosis could enter the taxonomy slice
  before the differential lane is explicitly selected.
- Response:
  keep `V44-B` blind to paired supplied/withheld conditions and reserve that doctrine
  explicitly for `V44-C`.
- Closeout Evidence:
  no paired-condition, knowledge-supplied, knowledge-withheld, or provisional profile
  fields were shipped in the released taxonomy contract or helper.

### Edge 6: `V46` Benchmark Projection Bleeds Upstream

- Risk:
  the taxonomy slice could start carrying benchmark-family or scoring assumptions just
  because the imported benchmarking package expects a downstream projection surface.
- Response:
  keep `V44-B` as a released substrate consumer of `V44-A` only, with `V46`
  remaining a later consumer of the taxonomy surface.
- Closeout Evidence:
  the shipped package surface contains no benchmark-instance, benchmark-score, or
  benchmarking-family projections; `V46` remains planning/support context only.

### Edge 7: External Bundle Becomes Silent Mapping Authority

- Risk:
  the imported reasoning-benchmark package could quietly set the normalized failure
  vocabulary or mapping law even though its primary target is later `V46`.
- Response:
  use the external bundle only as support evidence, and re-author mapping law from the
  released `V44-A` contracts and committed fixtures.
- Closeout Evidence:
  live implementation ownership is entirely under
  `packages/adeu_reasoning_assessment`, while the benchmarking bundle remains
  normalized under `examples/external_prototypes/...` and non-precedent.

## Current Judgment

- `V44-B` was the right next move because it normalized starter structural failure
  families only after the probe/trace object was already released on `main`.
- the shipped result remains properly bounded:
  - one repo-owned package
  - one taxonomy schema
  - one deterministic taxonomy helper
  - clean and blocked non-failure posture
  - hierarchy-aware normalized failure fixtures
  - no paired-condition/profile/benchmark metrics
- `V44-C` is now the right next path because the taxonomy substrate exists without
  overclaiming as diagnosis, profile, or scoring.
