# Architecture: ADEU Remote Operator UX And Phone Control Plane Family v0

Status: architecture / decomposition draft for `V63`.

Authority layer: architecture_decomposition.

This note does not authorize implementation by itself. It defines the bounded family
role that should expose one remote operator surface over the already shipped `V60`
continuation kernel and `V61` governed communication membrane, without letting
phone transport, remote presence, acknowledgements, or UI reachability become a
hidden sovereign.

## 1. Family Role

`V63` is not another continuation family, not another governed communication
family, not the connector family, and not yet the repo-widening family.

It is the family that owns:

- one bounded remote operator session posture over the shipped loop;
- one explicit remote-operator principal and admitted remote-session identity;
- one phone-safe task / ask / evidence view model over shipped `V60` / `V61`
  lineage in the starter slice;
- one bounded remote acknowledgement / response surface over that same session in
  the starter slice;
- later one governed remote command/control bridge over that same admitted session;
- and later one advisory remote-operator hardening surface over that same selected
  remote lineage.

The family therefore sits downstream of `V60` / `V61`, sibling to `V62`, and
upstream of any repo-bound writable authority or delegated execution widening.

- `V60` owns continuation / residual-intent identity.
- `V61` owns governed communication ingress / egress, interpretation, bridge-office
  binding, rewitness, and communication hardening over resident seams.
- `V62` owns connector admission and external assistant bridge posture over those
  already shipped `V61` packets.
- `V63` owns remote operator session, read-mostly remote view, and later governed
  command/control posture over the already shipped `V60` / `V61` outputs.
- `V64` should later own repo-bound writable-surface authority.

## 2. Remote Boundary Thesis

The central law is:

- remote phone/control transport is transport only;
- remote presence is context, not permission;
- remote-operator principal identity is explicit and selected, not ambient;
- remote acknowledgement is response material, not witness by itself;
- remote visibility is not bridge office by itself;
- remote visibility is not connector law;
- selected bounded remote responses consume shipped `V60` / `V61` semantics rather
  than inventing a new independent command ontology;
- and remote UX must consume shipped continuation and communication law rather than
  inventing remote-native governance semantics.

So:

- remote notification is not witness;
- remote acknowledgement is not bridge-office promotion;
- remote response is not charter compilation;
- remote response is not repo authority;
- free-form phone command semantics are not selected in the starter slice;
- and UI reachability is not standing authority.

## 3. Starter Artifact Ladder

The family ladder should add these new shapes over the shipped `V60` / `V61`
surfaces:

1. `agentic_de_remote_operator_session_record@1`
   - typed admitted-remote-session artifact
   - explicit remote-operator principal
   - explicit remote session / surface identity
   - explicit session basis summary
   - explicit frozen-policy anchor
   - explicit admission verdict from one bounded verdict family:
     - `admitted`
     - `rejected_principal_not_selected`
     - `rejected_surface_not_admitted`
     - `rejected_missing_basis`
     - `rejected_inconsistent_basis`
2. `agentic_de_remote_operator_view_packet@1`
   - typed read-mostly remote dashboard/view artifact
   - explicit admitted remote-session ref
   - explicit consumed `V60` loop-state and `V61` communication basis
   - explicit task / ask / evidence view basis
3. `agentic_de_remote_operator_response_record@1`
   - typed bounded remote response artifact
   - explicit admitted remote-session ref
   - explicit selected response kind only from:
     - `acknowledge`
     - `approve`
     - `continue`
     - `pause`
     - `escalate`
   - explicit consumed control basis ref or equivalent matched to the selected
     response kind
   - explicit consumed shipped URM approval/session or shipped `V60` / `V61`
     posture basis summary
4. later `agentic_de_remote_operator_control_bridge_packet@1`
   - typed richer command/control bridge over the admitted remote operator session
   - structured answers, inspect-rich controls, and broader typed intervention
5. later `agentic_de_remote_operator_hardening_register@1`
   - advisory remote-operator hardening surface over the same admitted remote
     lineage

Those shapes should consume, not reopen, the shipped:

- `agentic_de_loop_state_ledger@1`
- `agentic_de_continuation_refresh_decision_record@1`
- `agentic_de_communication_ingress_packet@1`
- `agentic_de_surface_authority_descriptor@1`
- `agentic_de_ingress_interpretation_record@1`
- `agentic_de_communication_egress_packet@1`
- `agentic_de_bridge_office_binding_record@1`
- `agentic_de_message_rewitness_gate_record@1`
- `agentic_de_governed_communication_hardening_register@1`

The starter slice is instantiated here only because richer remote command/control is
later.

That should be read as:

- instantiated_here:
  - one admitted remote operator session only
  - one `remote_operator` principal only
  - one read-mostly phone-safe view packet only
  - one bounded remote response record only
- deferred_to_later_lane:
  - richer typed command/control bridge
  - structured answers or clarifications
  - inspect-rich controls
  - advisory remote-operator hardening
- deferred_to_later_family:
  - connector law
  - repo-bound writable authority
  - delegated export / worker widening

## 4. Starter Runtime Boundary Model

The starter remote operator path should be:

```text
shipped V60 loop state + shipped V61 communication posture + URM approval/session state
  -> remote operator session record
  -> remote operator view packet
  -> later if bounded remote response is emitted:
       consume shipped approval/session or shipped V60/V61 posture
       -> remote operator response record
  -> later if richer command/control is selected:
       typed governed remote control bridge
  -> later advisory remote-operator hardening
```

What changes here is not continuation law, not communication law, not connector law,
and not repo authority.

What changes is that one remote operator surface stops being ambient UI reachability
and becomes one admitted, provenance-bearing remote posture over shipped
continuation and communication law.

## 5. Starter Freeze

`V63-A` should stay frozen to one exact starter path:

- one admitted remote operator session only
- one selected principal only:
  - `remote_operator` selected
  - `external_assistant` not selected
  - `human_via_connector` not selected
- one remote operator session record only
- one remote operator view packet only
- one bounded remote response record only
- one selected response set only:
  - `acknowledge`
  - `approve`
  - `continue`
  - `pause`
  - `escalate`
- no richer control bridge yet
- no structured answers or clarifications yet
- no inspect-rich controls yet
- no connector admission or connector trust mutation
- no direct repo mutation UI
- no broad shell / terminal control
- no repo-bound writable authority
- no execute widening
- no dispatch widening

The family should not expand to connector law, repo-bound write authority,
free-form phone command execution, or delegated worker law in the first slice.

## 6. Session Law

Remote operator session posture should remain explicit and replayable.

At minimum the starter family should preserve these laws:

- session admission derives from:
  - explicit remote-operator principal
  - explicit session / surface identity facts
  - explicit shipped loop and communication basis
  - frozen policy basis
- remote presence is not session admission by itself;
- UI reachability is not session admission by itself;
- session admission is replayable:
  - same operator/session identity facts
  - same shipped basis
  - same frozen policy
  - same admission verdict

Only the remote operator session record may say that a remote operator surface is
selected here.

Presence alone may not self-promote into authority.
Missing or inconsistent session basis must fail closed.

## 7. View And Response Law

Remote operator view and response surfaces should remain explicit and bounded.

At minimum the starter family should preserve these laws:

- remote view derives from:
  - admitted remote session record
  - shipped `V60` loop-state basis
  - shipped `V61` communication basis
  - frozen policy basis
- bounded remote response derives from:
  - admitted remote session record
  - one explicit selected response kind
  - shipped URM approval/session basis where relevant
  - shipped `V60` continuation posture where relevant
  - shipped `V61` blocked/escalation communication posture where relevant
  - frozen policy basis
- remote responses are typed response artifacts only;
- `acknowledge` is notification/session posture only and may not mutate
  continuation, communication, or authority state by itself;
- remote responses are not witness;
- remote responses are not bridge office;
- remote responses are not connector law;
- remote responses are not repo authority;
- remote responses are replayable:
  - same admitted session basis
  - same consumed shipped basis
  - same frozen policy
  - same response record

Only the bounded response record may define starter-slice remote responses.

The starter slice does not yet solve:

- broader free-form message ingress
- structured answers or clarifications
- inspect-rich intervention
- richer command/control bridge semantics

Those belong to `V63-B`.

## 8. Non-Generalization Law

Remote evidence should remain path-level and non-generalizing by default.

At minimum the starter family should preserve these laws:

- one admitted remote operator surface does not generalize by default into:
  - connector law
  - broader remote-admin law
  - all-device or all-surface operator law
  - repo-authority law
  - execute-authority law
  - dispatch law
- one successful remote operator response does not prove repo control law;
- one admitted remote surface does not mint standing authority for later surfaces
  or devices.

## 9. Later Family Boundary

`V63` should stop before:

- connector admission or external assistant bridge law;
- repo-bound writable authority;
- execute widening;
- dispatch widening;
- delegated worker export;
- free-form shell / terminal control;
- direct file editing from phone.

Those are later branch or later family concerns.
