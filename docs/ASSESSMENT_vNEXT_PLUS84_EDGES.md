# Assessment vNext+84 Edges

Status: planning-edge assessment for `V41-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS84_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Silent Interpretation Branch Choice

- Risk:
  the practical loop could bind the right repo world in `V41-A` and then silently pick
  one semantic reading without externalizing that choice.
- Response:
  require `interpretation_register` plus `chosen_interpretation_id`, and fail closed
  when the chosen reading is missing or unresolved.

### Edge 2: Request / Source-Set Drift During Settlement

- Risk:
  settlement could claim to govern the released request while actually settling a
  different `source_set_hash`, brief universe, or authority policy.
- Response:
  bind `analysis_request_id`, `analysis_request_ref`, `source_set_hash`, and
  `authority_boundary_policy` exactly back to the released `V41-A` request boundary,
  and require all internal support refs and targets to resolve inside that released
  request world.

### Edge 3: Typed-Top / Mushy-Inside Register Drift

- Risk:
  the settlement artifact could look typed at the top level while the real semantic
  payload hides inside semi-structured blobs.
- Response:
  require every interpretation, deontic, affordance, claim-posture, escalation, and
  blocking entry to remain explicitly addressable and grounded.

### Edge 4: Permission-To-Obligation And Affordance Disappearance

- Risk:
  the system could notice a permitted affordance, quietly upgrade it into a required
  path, or silently omit the fact that it was seen and declined.
- Response:
  freeze deontic vocabulary, freeze `affordance_decisions`, require rationale for
  deferred / declined affordances, require decision coverage for request-bound
  affordances surfaced by deontic typing, and reject silent promotion of permitted or
  fallback surfaces into obligations.

### Edge 5: Negative-Claim Overreach

- Risk:
  "not found under the current search / proof bound" could be emitted as if it were
  proved impossibility and then used to justify compile.
- Response:
  keep `unentitled_negative_claim` explicit, keep
  `impossibility_claim_without_proof` as an escalation trigger, and block compile
  entitlement while such posture remains active; require explicit rationale and
  bounded-support markers on unentitled negative claims.

### Edge 6: Hidden Escalation Trigger Drift

- Risk:
  high-impact ambiguity or silent semantic assumptions could be known internally but
  not surfaced as explicit blockers.
- Response:
  freeze `escalation_trigger_policy`, require grounded `active_escalation_records`,
  and make `compile_entitlement = entitled` illegal while any active trigger remains.

### Edge 7: Entitlement Fail-Open

- Risk:
  the settlement artifact could look complete while downstream compile is still not
  actually entitled.
- Response:
  freeze `compile_entitlement` to `entitled` / `blocked` only and require
  `blocked` whenever unresolved high-impact ambiguity, active escalation, or
  unentitled negative claims remain; require explicit `blocking_lineage` when blocked.

### Edge 8: Prose Escape Hatch / Observation / Alignment Creep

- Risk:
  `V41-B` could start extracting observed facts or drafting drift diagnostics under the
  cover of "settlement context," or let advisory prose become the real home of the
  settlement semantics.
- Response:
  keep the slice bounded to settlement and entitlement only; observation, intended
  compile, and alignment remain later seams; and mark `advisory_notes` as
  non-authoritative so it cannot become a semantic backchannel.

## Current Judgment

- `V41-B` is worth implementing now because `V41-A` already froze the repo world and
  the next missing seam is exactly the explicit settlement / entitlement gate that
  earns the right for later compile lanes to make claims about that world.
