# Draft Stop-Gate Decision vNext+152

Status: proposed gate for `V56-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS152.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `adeu_agentic_de` package scaffold exists and is the only active
  implementation package for the slice;
- typed models or schemas exist for:
  - `agentic_de_domain_packet@1`
  - `agentic_de_morph_ir@1`
  - `agentic_de_interaction_contract@1`
  - `agentic_de_action_proposal@1`
  - `agentic_de_membrane_checkpoint@1`
  - `agentic_de_morph_diagnostics@1`
  - `agentic_de_conformance_report@1`
- the starter path emits one dry-run membrane checkpoint artifact rather than only
  evaluating membrane logic implicitly;
- `agentic_de_action_proposal@1` remains non-entitling in `V56-A` and carries only
  candidate action, claimed basis, and dry-run checkpointability;
- checkpoint status and reason code remain distinct in the typed surface;
- conformance is emitted as a typed delta surface over packed state, proposed action,
  checkpoint entitlement, and executed or observed effect, with
  `executed_or_observed_effect = no_live_effect` in `V56-A`;
- no live write / execute / dispatch effect is authorized in the starter slice;
- Python tests cover:
  - packet validation,
  - contract validation,
  - proposal validation,
  - dry-run checkpoint emission,
  - status / reason separation,
  - diagnostics emission,
  - typed delta conformance emission,
  - refusal of live action effect.

## Do Not Accept If

- the slice claims to govern hidden cognition directly;
- speculative internal-state proxies are presented as authoritative governance inputs;
- `membrane_checkpoint` is treated as implicit logic rather than a first-class
  artifact;
- checkpoint reasons and statuses collapse into one flat result field;
- conformance degrades into prose summary instead of typed delta;
- live action tickets, runtime state, or actual tool interception appear in `V56-A`;
- the package silently widens into product API/UI or multi-agent surfaces;
- support doctrine is treated as live runtime authority by citation alone.

## Local Gate

- run `make check`
