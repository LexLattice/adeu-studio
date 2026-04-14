# Assessment vNext+158 Edges

Status: post-closeout edge assessment for `V58-A` (April 15, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS158_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Outer Harness Capability Could Collapse Into Inner Action Entitlement

- Risk:
  the existing URM `writes_allowed` mode or approval posture could be mistaken for
  what authorizes a live write in the governed lane.
- Response:
  keep outer harness capability necessary at most, never sufficient.
  - require the exact current-turn `V56-B` ticket lineage for entitlement
  - reject `writes_allowed` and approval posture as ticket equivalents
- Closeout Evidence:
  shipped `V58-A` admission/handoff/reintegration surfaces preserve explicit
  non-equivalence and tests assert fail-closed behavior.

### Edge 2: Current-Turn Bridge State Could Stay Ambient Instead Of Becoming Artifacts

- Risk:
  the harness could keep critical state implicit between session facts, ticket issuance,
  and observed effect, leaving the bridge sovereign in practice.
- Response:
  require explicit current-turn surfaces:
  - `agentic_de_live_turn_admission_record@1`
  - `agentic_de_live_turn_handoff_record@1`
  - `agentic_de_live_turn_reintegration_report@1`
- Closeout Evidence:
  merged `V58-A` introduces exactly those three surfaces with deterministic fixtures
  and schema export parity.

### Edge 3: Transcript / Event Stream Could Be Mistaken For Native Witness

- Risk:
  `urm_events.ndjson` or conversational transcript could be treated as the authoritative
  proof that the effect occurred.
- Response:
  keep transcript and event stream as observability / coordination surfaces only.
  - current-turn native witness must remain the current-turn observation /
    conformance chain
- Closeout Evidence:
  shipped reintegration logic and fixtures keep transcript/event stream
  observability-only; runtime event stream is committed for traceability but not as
  entitlement witness.

### Edge 4: Prior Fixtures And Closeout Evidence Could Be Laundered Into Current-Turn Permission

- Risk:
  committed fixtures and closeout artifacts could get read as current-turn entitlement
  instead of baseline and drift-guard material.
- Response:
  keep prior committed artifacts higher-ranked than narrative docs for drift checks, but
  never as current-turn witness or entitlement.
- Closeout Evidence:
  merged slice keeps prior fixtures/evidence as required drift guards only and does
  not treat them as current-turn witness basis.

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
- Closeout Evidence:
  shipped `V58-A` runner and fixtures preserve exact `local_write/create_new` over the
  designated sandbox root and target path only.

### Edge 6: Hidden Cleanup Could Reintroduce Sovereignty

- Risk:
  the starter slice could auto-run restoration or retry behavior that never appears in
  the governed artifacts.
- Response:
  keep restoration entirely out of `V58-A`.
  - no auto-restoration
  - no hidden compensators
  - no hidden retries
- Closeout Evidence:
  merged implementation performs no restoration integration and no hidden compensating
  behavior in the `V58-A` path.

### Edge 7: Broad Repo Mutation Surfaces Could Be Reused Under Cover Of Harness Integration

- Risk:
  the family could quietly reuse broader repo-mutation surfaces such as generic patch
  application or broader write modes, jumping past the selected exemplar.
- Response:
  keep the starter slice bound to the exact shipped `V56-B -> V57-A` path only.
  - no broader repo-authority write surface
  - no `local_reversible_execute`
  - no dispatch
- Closeout Evidence:
  merged diff adds no broader write class, no execute widening, and no dispatch path.

### Edge 8: Pairwise Coherence Could Be Mistaken For Adequate Reintegration Without Explicit Witness

- Risk:
  the repo could infer that because the inner family artifacts look coherent, the live
  turn is therefore lawfully reintegrated.
- Response:
  require explicit reintegration reporting over current-turn artifacts.
  - positive reintegration must be declared and evidenced
  - blocked or residualized posture must stay explicit
- Closeout Evidence:
  shipped reintegration report requires explicit status/reason posture and declared
  witness basis or certificate reference for positive reintegration.

### Edge 9: Review Hardening Could Drift From Fail-Closed Correctness Into Scope Widening

- Risk:
  late review fixes could accidentally widen `V58-A` beyond its bounded admission /
  handoff / reintegration role.
- Response:
  keep review hardening limited to fail-closed correctness for the selected path.
  - reject explicit target turn ids that are not visible in current session turn state
  - compare snapshot cwd directly against admitted repo root
- Closeout Evidence:
  `5022d48fc25dd3fae635f23f08529b7436f3c617` lands exactly those fail-closed checks
  and accompanying regressions without widening class, restoration, execute, dispatch,
  or product authority.

## Current Judgment

- `V58-A` was the right slice because the strongest remaining practical gap after
  closed `V55`/`V56`/`V57` was one lawful live harness bind over already shipped inner
  ticket/effect lineage.
- the shipped result remained properly bounded:
  - existing-session-path-first
  - existing-lineage-first
  - current-turn-artifact-first
  - exact-exemplar-first
  - non-restoration-first
  - non-dispatch
  - non-product
  - non-hidden-cognition-governing
- `V58-A` is now closed on `main` in the branch-local sense:
  - `adeu_agentic_de`
  - `urm_runtime`
- any next move should be a new arc selection rather than widening `V58-A` in place.
