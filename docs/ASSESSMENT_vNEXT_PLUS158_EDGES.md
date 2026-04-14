# Assessment vNext+158 Edges

Status: starter edge assessment for `V58-A` (April 14, 2026 UTC).

Authority layer: starter planning + lock draft only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS158_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Outer Harness Capability Could Collapse Into Inner Action Entitlement

- Risk:
  the existing URM `writes_allowed` mode or approval posture could be mistaken for the
  thing that authorizes the write.
- Response:
  keep outer harness capability necessary at most, never sufficient.
  - require the exact current-turn `V56-B` ticket lineage for entitlement
  - reject `writes_allowed` and approval posture as ticket equivalents

### Edge 2: Current-Turn Bridge State Could Stay Ambient Instead Of Becoming Artifacts

- Risk:
  the harness could keep critical state implicit between session facts, ticket issuance,
  and observed effect, leaving the bridge sovereign in practice.
- Response:
  require explicit current-turn surfaces:
  - `agentic_de_live_turn_admission_record@1`
  - `agentic_de_live_turn_handoff_record@1`
  - `agentic_de_live_turn_reintegration_report@1`

### Edge 3: Transcript / Event Stream Could Be Mistaken For Native Witness

- Risk:
  `urm_events.ndjson` or conversational transcript could be treated as the authoritative
  proof that the effect occurred.
- Response:
  keep transcript and event stream as observability / coordination surfaces only.
  - current-turn native witness must remain the current-turn observation /
    conformance chain

### Edge 4: Prior Fixtures And Closeout Evidence Could Be Laundered Into Current-Turn Permission

- Risk:
  committed fixtures and closeout artifacts could get read as current-turn entitlement
  instead of baseline and drift-guard material.
- Response:
  keep prior committed artifacts higher-ranked than narrative docs for drift checks, but
  never as current-turn witness or entitlement.

### Edge 5: One Exact Create-New Exemplar Could Be Generalized Into Broader `local_write` Authority

- Risk:
  once the live harness carries the first path, the repo could over-read that as owning
  broader `local_write` semantics.
- Response:
  freeze the selected live path exactly:
  - `local_write`
  - `create_new`
  - designated root `artifacts/agentic_de/v57/local_effect/`
  - target centered on `runtime/reference_patch_candidate.diff`
  - no broader class or sandbox generalization by default

### Edge 6: Hidden Cleanup Could Reintroduce Sovereignty

- Risk:
  the starter slice could auto-run restoration or retry behavior that never appears in
  the governed artifacts.
- Response:
  keep restoration entirely out of `V58-A`.
  - no auto-restoration
  - no hidden compensators
  - no hidden retries

### Edge 7: Broad Repo Mutation Surfaces Could Be Reused Under Cover Of Harness Integration

- Risk:
  the family could quietly reuse broader repo-mutation surfaces such as generic patch
  application or broader write modes, jumping past the selected exemplar.
- Response:
  keep the starter slice bound to the exact shipped `V56-B -> V57-A` path only.
  - no broader repo-authority write surface
  - no `local_reversible_execute`
  - no dispatch

### Edge 8: Pairwise Coherence Could Be Mistaken For Adequate Reintegration Without Explicit Witness

- Risk:
  the repo could infer that because the inner family artifacts look coherent, the live
  turn is therefore lawfully reintegrated.
- Response:
  require explicit reintegration reporting over current-turn artifacts.
  - positive reintegration must be declared and evidenced
  - blocked or residualized posture must stay explicit

## Current Judgment

- `V58-A` is the right next slice because the strongest remaining practical gap is one
  lawful live harness bind over the already shipped `V56` / `V57` stack.
- the starter should remain properly bounded:
  - existing-session-path-first
  - existing-lineage-first
  - current-turn-artifact-first
  - exact-exemplar-first
  - non-restoration-first
  - non-dispatch
  - non-product
  - non-hidden-cognition-governing
- any next move after `V58-A` should depend on whether one real live turn can be bound
  and reintegrated without hidden sovereignty, not on appetite for broader classes.
