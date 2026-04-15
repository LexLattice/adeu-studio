# Architecture: ADEU Resident-Agent Live Harness Integration Family v0

Status: architecture / decomposition draft for `V58`.

Authority layer: architecture_decomposition.

This note does not authorize implementation by itself. It defines the bounded family
role that should compose the already shipped live URM copilot harness with the already
shipped `V56` / `V57` resident-action stack without collapsing them into one coarse
authority surface.

## 1. Family Role

`V58` is not another checkpoint family and not another local-effect family.

It is the family that owns:

- live-turn admission into explicit current-turn artifacts;
- explicit ticket-to-effect handoff inside the live harness;
- reintegration of observed effect back into the resident turn report;
- and the anti-sovereignty law that keeps outer harness capability from masquerading as
  inner action entitlement.

The family therefore sits downstream of `V56` and `V57`.

- `V56` owns packet / proposal / checkpoint / ticket law.
- `V57` owns observed / restored local-effect evidence and path-level hardening advice.
- `V58` owns how one real live turn carries those surfaces as its governing path.

## 2. Lineage And Naming

`agentic_de_*` remains the lineage carrier for the typed runtime-governance objects.

That naming choice should not be over-read.

- lineage carrier:
  - `agentic_de_*`
- family role:
  - resident-agent live harness integration and reintegration

So this family is not “just more `V56`” and not “just more `V57`,” even though it
reuses those shipped lineage objects nearly as-is.

## 3. Runtime Boundary Thesis

The central law is:

- outer live harness capability is necessary at most;
- inner artifact entitlement remains necessary;
- neither side may silently absorb the other.

In the current repo that means:

- URM session mode, approval posture, and event streaming are real outer harness facts;
- packet / proposal / checkpoint / ticket / observation are real inner governed facts;
- the live path is lawful only when both sides are externalized and the bridge between
  them is itself explicit.

So:

- `writes_allowed` is not a `V56` ticket;
- approval posture is not a ticket equivalent;
- transcript and event stream are not native effect witness;
- prior fixtures and closeout evidence are not current-turn witness;
- and no hidden bridge state may decide eligibility.

## 4. Starter Artifact Ladder

The starter family ladder should add these new shapes over the shipped `V56` / `V57`
surfaces:

1. `agentic_de_live_turn_admission_record@1`
   - current live-turn snapshot of the relevant harness facts
   - typed admission verdict, not boolean presence
2. `agentic_de_live_turn_handoff_record@1`
   - explicit bridge from current-turn ticket lineage to the selected observed effect
3. `agentic_de_live_turn_reintegration_report@1`
   - typed closeout over observed effect and six-lane reintegration posture
   - explicit reintegration witness basis or certificate reference

Those shapes should reuse, not reopen, the shipped:

- `agentic_de_domain_packet@1`
- `agentic_de_action_proposal@1`
- `agentic_de_membrane_checkpoint@1`
- `agentic_de_action_ticket@1`
- `agentic_de_local_effect_observation_record@1`
- `agentic_de_local_effect_conformance_report@1`

## 5. Starter Runtime Boundary Model

The starter live path should be:

```text
URM session facts
  -> live_turn_admission_record
  -> V56 packet / proposal / checkpoint / ticket
  -> live_turn_handoff_record
  -> V57-A observed effect + local-effect conformance
  -> live_turn_reintegration_report
  -> six-lane run summary
```

What changes here is not the inner law.

What changes is that the bridge stops being ambient.

## 6. Starter Freeze

`V58-A` should stay frozen to one exact path:

- live session path:
  - existing URM copilot session path
- action class:
  - `local_write`
- write kind:
  - `create_new`
- designated sandbox root:
  - `artifacts/agentic_de/v57/local_effect/`
- exact starter target centered on:
  - `runtime/reference_patch_candidate.diff`
- duration posture:
  - single-step local only

The family should preserve the shipped `V57-A` fresh-sandbox semantics in the first
live slice. Persistent workspace continuity is not selected yet.

## 7. Reintegration Law

Reintegration is required for operational sufficiency.

But positive reintegration status must be witness-bearing, not oracle-like.

So the family should require:

- explicit current-turn admission facts;
- explicit typed admission verdicts and reason codes rather than simple present/missing
  posture;
- explicit current-turn packet / proposal / checkpoint / ticket lineage;
- explicit current-turn observed pre/post state;
- explicit current-turn reintegration verdict;
- explicit reintegration witness basis or certificate reference for any positive
  reintegration claim;
- and explicit reason codes when reintegration stays blocked, residualized, or
  under-witnessed.

The starter family should therefore keep three distinctions explicit:

- observed effect;
- intended interpretation of what that effect means;
- and final reintegration / alignment judgment.

No scalar confidence score or intuitive closure impression should replace that typed
reporting chain.

The starter family should also require field-origin / dependence tagging over handoff and
reintegration surfaces so that:

- current-turn native witness remains distinguishable from derived current-turn content;
- transcript and event stream remain observability only;
- prior fixtures, prior closeout artifacts, and shaping inputs remain non-native support;
- and echoed lineage cannot return as apparently fresh independent current-turn witness.

For later advisory hardening slices in this family, the same discipline should remain
extensional and replayable:

- the same selected evidence chain plus the same frozen policy must yield the same
  recommendation outcome;
- and multiple artifacts rooted in the same observed/restored lineage must not count
  as independent escalation support merely because they appear in different report
  positions.

## 8. Pairwise Default

The starter family may remain pairwise by default.

That is defensible because the first live path is still:

- one session;
- one ticketed local action;
- one exact target path;
- one exact designated sandbox root;
- one exact observed effect lineage.

Higher-arity reserve should remain deferred until identical pairwise profiles can still
yield different operational outcomes for the selected act. Dispatch and richer execute
paths will likely push there later. The starter create-new path does not require it.

## 9. Relationship To Other Families

- `V55`
  - checks constitutional coherence of released family surfaces
  - does not own live-turn enactment
- `V56`
  - remains sole owner of packet / proposal / checkpoint / ticket semantics
- `V57`
  - remains sole owner of observed / restored / hardening evidence over the selected
    local-effect path
- `V48`
  - remains sole owner of delegated worker execution after lawful dispatch
- `V51`
  - may shape membrane and reintegration reading
  - does not own runtime authority here

## 10. Deferred Seams

Deferred seams should be classified explicitly:

- `instantiated_here`
  - live-turn admission
  - ticket-to-effect handoff
  - reintegration report
- `deferred_to_later_slice`
  - explicit restoration-state harness integration
  - harness replay / drift hardening
  - persistent workspace continuity
- `deferred_to_later_family`
  - delegated or external dispatch integration
  - worker reconciliation after dispatch
- `not_selected_yet`
  - second `local_write` exemplar
  - `local_reversible_execute`
  - stronger execute
- `superseded_by_alternate_surface`
  - any attempt to govern hidden cognition directly
  - any attempt to treat outer harness write mode as inner action entitlement

## 11. Machine-Checkable Summary

```json
{
  "schema": "adeu_resident_agent_live_harness_integration_family@1",
  "artifact": "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_FAMILY_v0.md",
  "status": "draft",
  "authority_layer": "architecture_decomposition",
  "lineage_carrier": "agentic_de_*",
  "family_role": "resident_agent_live_harness_admission_handoff_and_reintegration",
  "governs_hidden_cognition": false,
  "outer_harness_capability_is_necessary_at_most": true,
  "outer_harness_capability_is_not_inner_entitlement": true,
  "starter_artifact_ladder": [
    "agentic_de_live_turn_admission_record@1",
    "agentic_de_live_turn_handoff_record@1",
    "agentic_de_live_turn_reintegration_report@1"
  ],
  "admission_verdict_must_be_typed_not_boolean": true,
  "positive_reintegration_requires_explicit_witness_basis_or_certificate_ref": true,
  "handoff_and_reintegration_origin_tags_required": true,
  "root_origin_dedup_required_for_current_turn_support": true,
  "reused_shipped_surfaces": [
    "agentic_de_domain_packet@1",
    "agentic_de_action_proposal@1",
    "agentic_de_membrane_checkpoint@1",
    "agentic_de_action_ticket@1",
    "agentic_de_local_effect_observation_record@1",
    "agentic_de_local_effect_conformance_report@1"
  ],
  "selected_starter_path": {
    "live_session_path": "urm_copilot_session_path",
    "action_class": "local_write",
    "write_kind": "create_new",
    "designated_sandbox_root": "artifacts/agentic_de/v57/local_effect/",
    "target_relative_path": "runtime/reference_patch_candidate.diff",
    "auto_restoration": false
  },
  "pairwise_default_retained": true,
  "higher_arity_reserved": true
}
```
