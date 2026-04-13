# Assessment vNext+152 Edges

Status: planning-edge assessment for `V56-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS152_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: The Family Could Drift Back Into Hidden-Cognition Governance

- Risk:
  the slice could overclaim by trying to govern the resident model's hidden latent
  reasoning instead of its externally effective action loop.
- Response:
  keep the family law fixed on packet, contract, proposal, checkpoint, and post-action
  trace only.

### Edge 2: The `agentic_de_*` Lineage Could Be Misread As Mere UX Restatement

- Risk:
  the implementation could treat the family as only a UX-schema reuse exercise instead
  of a runtime-governance family with retained lineage carriers.
- Response:
  keep the lineage/family split explicit:
  - `agentic_de_*` is the lineage carrier
  - `V56` is the runtime-governance family role

### Edge 3: The Membrane Checkpoint Could Become Implicit Again

- Risk:
  a dry-run membrane gate could be implemented as internal logic with no first-class
  checkpoint artifact, weakening the proposal-before-effect law.
- Response:
  require `agentic_de_membrane_checkpoint@1` as a starter artifact in `V56-A`.

### Edge 4: Checkpoint Results Could Collapse Status And Reason

- Risk:
  the starter checkpoint could return one flat outcome string, making later action
  ticket issuance and diagnostics semantically weak.
- Response:
  require explicit status / reason separation from the first slice onward.

### Edge 5: Conformance Could Degenerate Into Narrative

- Risk:
  the family could claim conformance early but ship only a prose after-action summary.
- Response:
  keep `agentic_de_conformance_report@1` as a typed delta surface over packed state,
  proposal, checkpoint entitlement, and observed dry-run effect with
  `executed_or_observed_effect = no_live_effect`.

### Edge 5A: Hidden-Cognition Governance Could Reappear Indirectly Through Proxy Metrics

- Risk:
  the slice could avoid explicit hidden-cognition governance claims while still
  importing speculative internal certainty or latent-state proxy metrics as if they
  were authoritative governance inputs.
- Response:
  keep governance inputs externalized and boundary-artifact-based only, and forbid
  speculative internal-state proxies in `V56-A`.

### Edge 6: The Runtime Boundary Could Widen Prematurely Into Live Interception

- Risk:
  once packet/contract/proposal artifacts exist, implementation pressure could jump
  directly into live write / execute / dispatch interception.
- Response:
  keep `V56-A` dry-run only and defer runtime state, action ticket, and live effect to
  `V56-B`.

### Edge 7: Family Boundaries Could Blur With `V48`, `V51`, Or `V55`

- Risk:
  resident-agent governance could silently absorb delegated worker execution,
  simulation ownership, or constitutional coherence checking into one mixed family.
- Response:
  keep the ordering explicit:
  - `V55` checks constitutional coherence of surfaces
  - `V56` governs resident-agent runtime boundary crossing
  - `V48` governs delegated worker execution after lawful dispatch
  - `V51` may shape semantics but does not own runtime authority here

### Edge 8: Action-Class Semantics Could Stay Too Intuitive For Later Live Gating

- Risk:
  the family could carry `write` / `execute` / `dispatch` labels forward without
  typing what those classes actually mean.
- Response:
  treat exact action-class taxonomy as a mandatory precondition for `V56-B`, not as an
  ambient intuition.

## Current Judgment

- `V56-A` is worth implementing now because it closes a real missing runtime-governance
  layer between:
  - constitutional/schema law,
  - constitutional coherence checking,
  - and live resident-agent action
- the slice is properly bounded if it stays:
  - package-first
  - dry-run only
  - checkpoint-explicit
  - typed-delta-conformance-first
  - non-product
  - non-multi-agent
  - non-hidden-cognition-governing
