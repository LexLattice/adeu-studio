# Architecture ADEU Resident-Agent Interaction Governance Family v0

Status: architecture / decomposition draft for `V56`.

Authority layer: architecture / decomposition.

This document defines the bounded family shape for resident-agent runtime governance. It
is not a lock doc and does not authorize runtime behavior, schema release, or CI gating
by itself.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`
- `docs/support/ADEU_SCHEMA_META_GRAMMAR.md`
- `docs/support/AGENTIC_DE_TYPE_GRAMMAR.md`
- `docs/support/ODEU_MEMBRANE_ARCHITECTURE.md`
- `docs/support/ODEU AS A COUPLED SEMANTIC HYPERSPACE WITH LAWFUL MORPHISMS_v2.md`

## 1. Direct Answer

The resident agent should not be governed by attempting to formalize or constrain its
hidden cognition directly.

It should be governed by owning one bounded family that externalizes the effective loop
around the agent into typed artifacts:

- packet before action;
- contract before transition;
- proposal before effect;
- membrane gate before write / execute / dispatch;
- diagnostics and conformance after action.

That is the minimum ADEU-native closed-loop runtime governance shape.

## 2. Family Role

This family owns:

- per-turn or per-run packet loading;
- resident-agent interaction contract definition;
- action-proposal typing;
- bounded membrane gate evaluation;
- diagnostics and conformance emission; and
- later harvest / calibration / migration decision surfaces.

This family does not own:

- hidden latent inference;
- generic prose interpretation;
- broad product routing;
- delegated worker topology already owned by `V48`; or
- constitutional artifact coherence already owned by `V55`.

## 3. Core Family Law

The family should make these laws explicit:

1. inferential search may remain free, but externally effective action may not;
2. resident-agent outputs are advisory until a governed gate entitles stronger effect;
3. no hidden write / execute / dispatch boundary is allowed;
4. unresolved, insufficient-evidence, authority-missing, and not-evaluable states may
   not be laundered into action;
5. projections may express but may not mint authority;
6. post-action traces are part of governance, not optional commentary.

This family should also forbid surrogate hidden-cognition laundering:

- speculative internal-state proxies such as reasoning-quality scores, latent certainty
  estimates, or plan-stability guesses may not be presented as authoritative
  governance inputs unless they are separately externalized into lawful boundary
  artifacts.

## 4. Artifact Ladder

The bounded family ladder is:

1. `agentic_de_domain_packet@1`
   - task, scope, authority frame, capability posture, risk posture, environment
2. `agentic_de_morph_ir@1`
   - canonical semantic / O-E-D-U interaction model for the current governed context
3. `agentic_de_interaction_contract@1`
   - action semantics, authoritative/advisory distinction, handoff boundary, gate law
4. `agentic_de_action_proposal@1`
   - resident-agent proposed action with evidence, authority basis, and consequence
5. `agentic_de_membrane_checkpoint@1`
   - checkpoint result over proposal under current packet + contract + state
6. `agentic_de_action_ticket@1`
   - bounded entitlement token for selected live actions when later slices select it
7. `agentic_de_morph_diagnostics@1`
   - typed findings over packet / contract / proposal / checkpoint coherence
8. `agentic_de_conformance_report@1`
   - post-action report over what was proposed, allowed, executed, and observed
9. `agentic_de_runtime_harvest_record@1`
   - harvested prior patterns that may shape later governance without minting it

The first slice should instantiate only the first five plus diagnostics and conformance.

## 5. Relationship To Existing Repo-Native Surfaces

This family should not start from zero.

The released `ux_*` schema surfaces in `packages/adeu_core_ir` already express three
important constitutional slots:

- domain packet;
- morph IR;
- interaction contract.

`V56` should treat those as released shaping lineage and particularize them for the
resident-agent runtime family rather than pretending the family is unrelated to them.

But `V56` is not merely a UX restatement. It adds:

- action proposal;
- membrane checkpoint;
- later action ticket;
- conformance and harvest over actual resident-agent action.

So the correct reading is:

- `agentic_de_*` is the retained lineage carrier for the family slots; and
- `V56` is the runtime-governance family role particularized through those lineage
  slots.

This family is therefore not "just another UX bundle". It is a runtime-governance
family that descends through existing agentic-DE/UX constitutional slots.

## 5.1 Relationship To `V48`, `V51`, And `V55`

The ordering between nearby families should remain explicit:

- `V55` checks constitutional coherence of family surfaces before or alongside release;
- `V56` governs the resident runtime boundary crossing and post-action trace;
- `V48` governs delegated worker execution after a `dispatch` action is lawfully
  issued by `V56`;
- `V51` may shape the runtime reading of packet, checkpoint, and membrane law, but does
  not own runtime authority in this family by itself.

## 6. Runtime Boundary Model

The runtime boundary should be:

```text
packet -> morph_ir -> interaction_contract
       -> action_proposal
       -> membrane_checkpoint
       -> [optional later action_ticket]
       -> action execution
       -> diagnostics + conformance
       -> harvest
```

The family therefore governs:

- what the agent may ask to do;
- what must be visible before the system lets it do it;
- what happens when the proposal is under-evidenced or under-authorized; and
- what record remains after execution.

## 6.1 Action-Class Exactness

The bounded starter action classes are:

- `write`
- `execute`
- `dispatch`

But those classes are not yet sufficiently exact by label alone.

Before any `V56-B` lock, the family should type at least:

- what counts as pure read / inspect;
- what counts as capability-sensitive or effect-bearing inspect;
- what counts as local reversible execute;
- what counts as stronger execute;
- what counts as local write; and
- what crosses into delegated or external dispatch.

That taxonomy belongs to this family because the live gate cannot remain coherent if
these classes remain purely intuitive.

## 7. Bounded O-E-D-U Runtime Reading

The family should use O-E-D-U at runtime like this:

- `O`: current task/object/scope situation and target identity
- `E`: evidence refs, provenance, admissibility, uncertainty, contradiction
- `D`: authority frame, capability posture, gate status, escalation / residual law
- `U`: proposed utility, preferred path, optimization posture

The governing rule is:

- `U` may help choose within an already lawful region;
- `U` may not authorize a transition that `D` blocks or that `E` cannot support.

## 7.1 Checkpoint Status Algebra

`agentic_de_membrane_checkpoint@1` should separate:

- checkpoint status; from
- checkpoint reason code.

Starter status vocabulary should be at least:

- `accepted`
- `residualized`
- `blocked`
- `escalated`
- `rejected_by_form`

Starter reason-code vocabulary may include:

- `authority_missing`
- `insufficient_evidence`
- `proposal_malformed`
- `out_of_scope`
- `noncomparable`
- `unresolved_dependency`
- `not_evaluable_yet`

The family should not collapse reasons into statuses or statuses into reasons.

Checkpoint acceptance should remain necessary but not sufficient for later action
ticket issuance.

Later live slices should also require:

- selected live action-class membership;
- runtime-state compatibility;
- authority/capability posture validity at issuance time; and
- bounded ticket scope/time.

## 8. Starter Package Shape

The likely starter implementation home is:

- `packages/adeu_agentic_de/src/adeu_agentic_de/`
- `packages/adeu_agentic_de/tests/`

Likely starter module split:

- `domain_packet.py`
- `morph_ir.py`
- `interaction_contract.py`
- `action_proposal.py`
- `membrane.py`
- `diagnostics.py`
- `conformance.py`

One thin script seam may live under:

- `apps/api/scripts/`

## 9. Deferred Seams

Deferred seams should be classified explicitly:

- `instantiated_here`
  - packet, contract, proposal, starter checkpoint, diagnostics, conformance
- `deferred_to_later_family`
  - broader multi-agent orchestration or social protocol families
- `deferred_to_later_slice`
  - live action ticket issuance
  - harvest and governance calibration
  - broader profile / variant management
- `superseded_by_alternate_surface`
  - any attempt to govern hidden cognition directly rather than governing the external
    action loop

## 9.1 Conformance Delta Law

`agentic_de_conformance_report@1` should be treated as a typed delta surface, not a
prose after-action summary.

At minimum it should compare:

- what was packed;
- what was proposed;
- what the checkpoint entitled; and
- what was actually executed or observed.

For ticketed live slices such as `V56-B`, the delta chain should also make ticket
issuance explicit through either:

- one typed ticket-issued-or-not axis; or
- one explicit linked ticket reference/summary surface carried alongside conformance.

For dry-run slices such as `V56-A`, the effect axis should remain explicit as one
non-live posture such as `no_live_effect` rather than pretending an execution effect
occurred.

That delta law is the reason conformance belongs in the family ladder early rather than
as a later reporting convenience.

## 10. Machine-Checkable Summary

```json
{
  "schema": "adeu_resident_agent_interaction_governance_family@1",
  "artifact": "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_FAMILY_v0.md",
  "status": "draft",
  "authority_layer": "architecture_decomposition",
  "governs_hidden_cognition": false,
  "governs_external_action_loop": true,
  "starter_artifact_ladder": [
    "agentic_de_domain_packet@1",
    "agentic_de_morph_ir@1",
    "agentic_de_interaction_contract@1",
    "agentic_de_action_proposal@1",
    "agentic_de_membrane_checkpoint@1",
    "agentic_de_morph_diagnostics@1",
    "agentic_de_conformance_report@1"
  ],
  "package_home": "packages/adeu_agentic_de"
}
```
