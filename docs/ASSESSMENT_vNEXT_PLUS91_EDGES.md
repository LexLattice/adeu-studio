# Assessment vNext+91 Edges

Status: post-closeout edge assessment for `V42-C`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS91_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v91_closeout_edge_assessment",
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Upstream Lineage Drift

- Risk:
  action/rollout artifacts could be authored against ambient state while claiming
  released task/observation/hypothesis lineage.
- Response:
  require explicit upstream lineage refs and fail closed on any mismatch.

### Edge 2: Deontic Admissibility Drift

- Risk:
  proposed actions could be accepted without strict carry-through from released legal
  action envelope constraints.
- Response:
  require explicit proposal deontic posture and reject proposals outside released legal
  envelope.

### Edge 3: Expectation-Lineage Omission

- Risk:
  rollout outputs could report outcomes without explicit pre-action expectation anchor,
  making comparison non-auditable.
- Response:
  require structured expected-outcome surfaces in proposals plus expectation-vs-outcome
  comparison in rollout traces.

### Edge 4: Settlement Carry Loss

- Risk:
  ambiguity/claim posture from `V42-B` could disappear once action commitment is emitted.
- Response:
  require explicit settlement posture carry fields in rollout trace and reject posture
  erasure.

### Edge 5: Decision-Basis Compression

- Risk:
  a legal action could be emitted with a thin expected-outcome summary while actual
  tactical choice logic stays hidden.
- Response:
  require explicit machine-checkable decision-basis fields across hypothesis selection,
  utility pressure, and ambiguity handling.

### Edge 6: Hidden Utility Laundering

- Risk:
  utility-driven tactical preference could be smuggled as prose without explicit utility
  posture surfaces.
- Response:
  require explicit utility posture plus alternative-action register carry-through under
  ambiguity.

### Edge 7: Post-Hoc Expectation Rewrite

- Risk:
  expected-outcome surfaces could be rewritten after observing rollout results to fake
  alignment.
- Response:
  require proposal-bound expectation identity (`expectation_surface_hash`) and reject
  rollout traces that do not preserve byte-identical expectation lineage.

### Edge 8: Forced Commitment Under Honest Block/Defer Posture

- Risk:
  the system could force committed-action output even when posture should remain blocked
  or deferred.
- Response:
  require explicit `proposal_status` enum and reject committed action payloads when status
  is `blocked` or `deferred_pending_resolution`.

### Edge 9: Retroactive Necessity Laundering

- Risk:
  one successful rollout could be laundered into universal task-rule necessity.
- Response:
  reject post-hoc necessity claims without explicit entitlement evidence.

### Edge 10: Hidden Scorecard/Competition Leakage

- Risk:
  `V42-C` artifacts could smuggle scorecard/replay/competition semantics under rollout
  naming.
- Response:
  keep `V42-C` bounded to action+rollout only and reject scorecard/replay authority
  leakage.

## Current Judgment

- `V42-C` is the correct next slice because it introduces tactical commitment while
  preserving released decomposition and settlement posture.
- `V42-C` closed safely on `main` because decision basis, utility posture, proposal
  status, structured expectation lineage, settlement carry-through, and anti-laundering
  constraints shipped as machine-checkable fail-closed surfaces.
