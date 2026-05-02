# Assessment vNext+230 Edges

Status: pre-lock assessment for `V82-A`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS230_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Corpus-Ingestion Review Could Become Ingestion

- Required containment:
  `V82-A` may create request, source-index, and non-transfer guardrail rows
  only. Reference rows must carry no-corpus-ingestion, no-data-transfer,
  no-customer-data-handling, no-connector-activation, no-endpoint-access, and
  no-cross-corpus-adjudication-execution posture.
- Planned result:
  must pass in implementation.

### Edge 2: Descriptor Or URL Could Become Import Permission

- Required containment:
  source rows distinguish corpus content, corpus descriptors, benchmark
  descriptors, connector identifiers, endpoint identifiers, authority sources,
  and absence markers. Descriptor, connector, endpoint, and absence rows
  cannot satisfy eligibility by themselves.
- Planned result:
  must pass in implementation.

### Edge 3: Absence Could Become Eligibility

- Required containment:
  explicit absence rows support request recordability or missing-source
  blockers only. Eligible rows require current concrete corpus or customer
  corpus source posture and source-permission posture.
- Planned result:
  must pass in implementation.

### Edge 4: Support Context Could Become Eligibility

- Required containment:
  dogfood, roadmap, and support-process rows remain context only. Eligible
  corpus-ingestion review requests require released `V81-C` source roles,
  current concrete corpus/customer source posture, and non-transfer guardrails.
- Planned result:
  must pass in implementation.

### Edge 5: Customer Corpus Could Bypass Privacy Or License Authority

- Required containment:
  customer corpus rows require explicit privacy, license/consent, and
  customer-data authority posture. Missing posture blocks validation.
- Planned result:
  must pass in implementation.

### Edge 6: Connector Or Endpoint Refs Could Become Access Permission

- Required containment:
  connector identifiers and endpoint refs remain non-authorizing source
  metadata in `V82-A`; connector activation and endpoint access posture must
  remain negative.
- Planned result:
  must pass in implementation.

### Edge 7: Future V82-B Surfaces Could Appear In V82-A

- Required containment:
  future preflight, connector boundary, data-handling authority, and exception
  pressure is represented by horizons and postures. Refs to unshipped `V82-B`
  surfaces reject.
- Planned result:
  must pass in implementation.

### Edge 8: Product, Benchmark, Or Graph Pressure Could Launder Readiness

- Required containment:
  product, benchmark, and graph-memory pressure remains blocked,
  future-family-only, or out of scope for corpus-ingestion review. Benchmark
  descriptors cannot become benchmark truth; graph-memory pressure cannot
  become living-memory authority.
- Planned result:
  must pass in implementation.

### Edge 9: Guardrail Rows Could Be Empty Or Non-Source-Bound

- Required containment:
  non-transfer guardrails must have non-empty forbidden ingestion, transfer,
  connector, endpoint, and downstream authority lists. Required later authority
  refs must resolve to current source rows or embedded authority requirement
  rows, not future `V82-B` rows.
- Planned result:
  must pass in implementation.

### Edge 10: V82-A Could Select V83

- Required containment:
  `V82-A` may carry future pressure but cannot select `V83` or any later
  family. Later selection remains deferred to future family-level selection
  after `V82` closeout.
- Planned result:
  must pass in implementation.

## Current Judgment

- `vNext+230` is safe to use as a bounded starter only if it remains scoped to
  `V82-A`.
- The first implementation should prove that `V82-A` can record
  corpus-ingestion review pressure over released `V81-C` substrate without
  ingesting corpora, transferring data, handling customer data, activating
  connectors, accessing endpoints, executing cross-corpus adjudication,
  productizing, releasing, creating graph memory, or selecting `V83`.
