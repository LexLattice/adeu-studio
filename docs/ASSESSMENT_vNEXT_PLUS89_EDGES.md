# Assessment vNext+89 Edges

Status: planning-edge assessment for `V42-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS89_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Environment-Authority Drift

- Risk:
  the slice could silently replace the official ARC toolkit with repo-local or prompt-only
  environment semantics while still describing itself as an adapter.
- Response:
  keep official local ARC toolkit authority explicit in the contract and reject
  non-authoritative adapter posture in fixtures and tests.

### Edge 2: Deontic Boundary Laundering

- Risk:
  mode restrictions and legal action limits could be carried only as descriptive
  metadata, which weaker models would then treat as soft context rather than operative
  admissibility boundaries.
- Response:
  require explicit machine-readable `mode_posture`, `legal_action_envelope`, and
  `adapter_boundary_policy` surfaces in the task packet.

### Edge 2A: Packet Identity Ambiguity

- Risk:
  `task_packet_id` could silently collapse into raw environment-state identity while the
  packet also carries governed adapter/mode/legal-envelope identity.
- Response:
  freeze `task_packet_id` as canonical full packet identity and keep any narrower
  environment-state identity explicit as a separate concept if needed later.

### Edge 2B: Legality Normalization Drift

- Risk:
  toolkit legality data could be normalized into ADEU legality data with silent loss or
  semantic mutation at the adapter seam.
- Response:
  require both toolkit and mirrored legality surfaces plus explicit
  `legal_action_envelope_provenance` so normalization remains inspectable and
  loss-auditable.

### Edge 2C: Boundary-Policy Semantic Smuggling

- Risk:
  `adapter_boundary_policy` could become a hidden carrier of proto-solver or
  interpretation semantics while presenting as deontic metadata.
- Response:
  constrain boundary policy to deontic admissibility and reject observation/hypothesis
  semantics in that surface.

### Edge 3: Premature Solver Widening

- Risk:
  the family start could drift into observation, hypothesis, or action logic and
  effectively select `adeu_arc_solver` before the decomposition and later locks do.
- Response:
  keep `packages/adeu_arc_solver` deferred in `vNext+89` and reject solver-surface
  widening in the lock and fixture ladder.

### Edge 4: Hidden Competition-Mode Leakage

- Risk:
  the first slice could smuggle in scorecard, replay, or competition-mode concepts under
  local adapter naming and create counterfeit readiness.
- Response:
  treat local adapter/task-packet work as a local-only baseline and reject scorecard,
  replay, and competition-mode authority in the first slice.

### Edge 4A: Synthetic Packet Authority Leakage

- Risk:
  canonical packets could be prompt-authored synthetic reconstructions presented as if
  they were sourced from the official local toolkit.
- Response:
  require toolkit-derived packet provenance and reject synthetic packet authority in
  fixtures and tests.

### Edge 5: Settlement Loss In Later ARC Reasoning

- Risk:
  once the family widens beyond task/session freeze, hypotheses or action proposals could
  silently lose claim posture and unresolved ambiguity state.
- Response:
  record now that later `V42-B` / `V42-C` locks must carry settlement-style posture rather
  than raw content-only artifacts.

### Edge 6: Model-Uplift Overclaim

- Risk:
  maintainers could overread a clean adapter baseline as proof that ADEU lifts all model
  classes equally well on ARC tasks.
- Response:
  keep model sensitivity explicit in the decomposition and treat later local benchmarking
  as an empirical control-plane adherence test, not just a task-success test.

## Current Judgment

- `V42-A` is worth implementing now because it closes the narrowest real gap between the
  released ADEU practical-analysis substrate and a truthful external benchmark adapter.
- The slice is only safe if it stays boring: official local toolkit wrapper, canonical
  task/session packet, explicit deontic boundary capture, and no solver theater.
