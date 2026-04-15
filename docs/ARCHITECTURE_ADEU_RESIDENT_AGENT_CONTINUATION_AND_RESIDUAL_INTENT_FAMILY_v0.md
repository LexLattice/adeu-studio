# Architecture: ADEU Resident-Agent Continuation And Residual-Intent Family v0

Status: architecture / decomposition draft for `V60`.

Authority layer: architecture_decomposition.

This note does not authorize implementation by itself. It defines the bounded family
role that should turn the already shipped `V55` / `V56` / `V57` / `V58` / `V59`
governed stack into one explicit continuation / residual-intent kernel without
widening `V56` tickets into standing authority, and without letting transcript,
continuity state, or communication surfaces become a hidden sovereign.

## 1. Family Role

`V60` is not another checkpoint family, not another effect family, not another live
harness family, not another continuity family, and not yet the governed communication
family.

It is the family that owns:

- one bounded task-law compilation surface over typed seed intent;
- one explicit derived residual-intent carrier after reintegration;
- one loop-state identity that binds charter, residual, session, continuity, and last
  reintegration lineage without collapsing into transcript memory;
- and one bounded continuation decision surface that selects the next lawful posture.

The family therefore sits downstream of `V59` and upstream of `V61`.

- `V56` owns packet / proposal / checkpoint / ticket law.
- `V57` owns bounded observed / restored local-effect evidence.
- `V58` owns live-turn admission / handoff / reintegration.
- `V59` owns persistent workspace continuity over the selected path.
- `V60` owns bounded task-law compilation and continuation identity over that already
  governed stack.
- `V61` should later own governed communication packets and office law that consume
  `V60` continuation outputs.

## 2. Lineage And Naming

`agentic_de_*` remains the lineage carrier for the typed runtime-governance objects.

That naming choice should not be over-read.

- lineage carrier:
  - `agentic_de_*`
- family role:
  - resident-agent continuation and residual-intent kernel

So this family is not “just more `V59`,” even though it reuses the shipped
continuity-bound path nearly as-is.

## 3. Continuation Boundary Thesis

The central law is:

- continuation must be first-class and externally structured;
- it must not collapse into transcript memory, continuity state, or prompt habit;
- and it must not widen ticket duration.

In the current repo that means:

- starter seed intent must enter through one typed, bounded starter artifact;
- task law must be compiled into explicit continuation artifacts rather than echoed
  from raw user text;
- residual state must be derived from reintegration and declared policy;
- and every externally effective act must still descend into a fresh single-step
  governed path.

So:

- raw transcript is not starter task law;
- generic chat memory is not continuation identity;
- connector traffic is not starter ingress law;
- prior continuity success is not standing authority;
- prior reintegration is not ambient permission;
- and hidden cognition is not the continuation kernel.

## 4. Starter Artifact Ladder

The starter family ladder should add these new shapes over the shipped `V56` / `V57` /
`V58` / `V59` surfaces:

1. `agentic_de_seed_intent_record@1`
   - typed non-chat-native starter ingress record
   - bounded seed intent only for the starter slice
2. `agentic_de_task_charter_packet@1`
   - bounded task-law compilation over the selected path
   - explicit completion tests, stop conditions, and downstream path identity
   - typed and replayable charter compilation over seed intent plus frozen policy
3. `agentic_de_task_residual_packet@1`
   - derived continuation artifact after reintegration and policy reading
   - not human-authored law and not standing authority
4. `agentic_de_loop_state_ledger@1`
   - canonical loop-state identity over charter, residual, resident session,
     continuity region, approvals, and latest reintegration lineage
5. `agentic_de_continuation_decision_record@1`
   - typed next-posture decision over the bounded loop state
   - replayable and policy-bound

Those shapes should reuse, not reopen, the shipped:

- `agentic_de_domain_packet@1`
- `agentic_de_action_proposal@1`
- `agentic_de_membrane_checkpoint@1`
- `agentic_de_action_ticket@1`
- `agentic_de_local_effect_observation_record@1`
- `agentic_de_local_effect_conformance_report@1`
- `agentic_de_live_turn_admission_record@1`
- `agentic_de_live_turn_handoff_record@1`
- `agentic_de_live_turn_reintegration_report@1`
- `agentic_de_workspace_continuity_region_declaration@1`
- `agentic_de_workspace_continuity_admission_record@1`
- `agentic_de_workspace_occupancy_report@1`
- `agentic_de_workspace_continuity_reintegration_report@1`

The starter ingress record is instantiated here only because `V61` is later.

That should be read as:

- instantiated_here:
  - one typed starter ingress record
- deferred_to_later_family:
  - governed communication packets
  - ingress interpretation over raw communication surfaces
  - office binding and rewitness gates under `V61`

## 5. Starter Runtime Boundary Model

The starter continuation path should be:

```text
typed starter seed-intent record
  -> task charter packet
  -> initial task residual packet
  -> loop-state ledger
  -> continuation decision record
  -> if continue_to_governed_act:
       shipped V58 live admission / handoff lineage
       -> shipped V56 proposal / checkpoint / ticket
       -> shipped V57 / V59 selected effect or continuity-bound restore lineage
       -> shipped V58 / V59 reintegration
  -> later V60 residual refresh / reproposal path
  -> six-lane run summary
```

What changes here is not the inner act law, not the effect law, and not the
continuity law.

What changes is that the loop stops relying on prose memory for what the task still is
and what it may do next.

The continuation decision is therefore an explicit kernel output over already shipped
runtime/governance surfaces.

It is never a substitute for shipped `V56` ticketing, and any
`continue_to_governed_act` posture still descends into the already ordered
`V58` / `V56` / `V57` / `V59` path rather than reordering it.

Charter compilation itself should remain extensional as well:

- same selected seed intent plus same frozen policy
- same task charter packet

## 6. Starter Freeze

`V60-A` should stay frozen to one exact starter path:

- starter ingress mode:
  - typed `agentic_de_seed_intent_record@1` only
  - not raw transcript semantics
  - not generic chat memory
  - not connector traffic
- live session path:
  - existing URM copilot session path already selected by `V58`
- selected downstream live action class:
  - `local_write`
- selected downstream write kind:
  - `create_new`
- declared continuity root:
  - `artifacts/agentic_de/v59/workspace_continuity/`
- exact starter target centered on:
  - `runtime/reference_patch_candidate.diff`
- duration posture:
  - single-step local only

The family should not expand to raw communication ingress, connector ingress,
repo-bound writable authority, or multi-step ticket duration in the first slice.

## 7. Residual Law

`TaskResidual` should remain explicitly derived.

At minimum the starter family should preserve these laws:

- residual derives from:
  - task charter
  - latest reintegration lineage
  - declared policy basis
  - bounded runtime fact posture such as approvals and blockers
- residual is not human-authored law;
- residual is not standing authority;
- residual is not a stretched ticket;
- and residual is replayable:
  - same selected derivation basis plus same frozen policy
  - same residual posture

At minimum the starter family should preserve these distinctions inside the residual:

- current frontier
- open obligations
- open blockers
- open approvals
- owed communication posture
- stop or escalation posture
- latest reintegration refs

Only the continuation decision may decide what the loop may do next.

Residual alone may not self-promote into permission.

## 8. Charter Compilation Law

Task charter compilation should remain explicit and replayable.

At minimum the starter family should preserve these laws:

- task charter is compiled bounded task law;
- task charter is not raw user request echo;
- task charter derives from:
  - typed seed-intent record
  - frozen policy basis
  - selected downstream path freeze
- and charter compilation is replayable:
  - same selected seed intent plus same frozen policy
  - same task charter packet

Only the task charter may define the bounded starter task law for the slice.

Starter seed intent alone may not self-promote into task law.

## 9. Starter Posture Law

The starter continuation decision should remain bounded to outcomes such as:

- `continue_to_governed_act`
- `await_authority`
- `emit_governed_communication`
- `pause_blocked`
- `stop_complete`
- `escalate_for_review`

Those outcomes should not be over-read.

In particular:

- `continue_to_governed_act`
  - descends into the already shipped act ladder
  - must select the exact already shipped downstream `V59` continuity-bound exemplar
    only in `V60-A`
  - does not widen ticket duration
- `emit_governed_communication`
  - is a posture outcome only in `V60`
  - actual communication packet law and office binding remain deferred to `V61`
- `await_authority`, `pause_blocked`, `stop_complete`, and `escalate_for_review`
  - are explicit continuation outcomes
  - not hidden model-side behavior

The same selected continuation evidence chain plus the same frozen policy must yield
the same continuation posture.

## 10. Pairwise Default

The starter family may remain pairwise by default.

That is defensible because the first continuation path is still:

- one typed seed-intent record;
- one resident session;
- one continuity-bound work surface;
- one loop-state ledger;
- one continuation decision over one exact downstream path.

Higher-arity reserve should remain deferred until identical pairwise profiles can still
yield different continuation outcomes for the selected path. Multi-party
communication, connector arbitration, or worker export may push there later. The
starter continuation slice does not require it.

## 11. Relationship To Other Families

- `V55`
  - checks constitutional coherence of released family surfaces
  - does not own continuation enactment
- `V56`
  - remains sole owner of packet / proposal / checkpoint / ticket semantics
  - may be descended into by `continue_to_governed_act`
  - does not own continuation selection
- `V57`
  - remains sole owner of observed / restored local-effect evidence
  - does not own seed-intent or residual law
- `V58`
  - remains sole owner of live-turn admission / handoff / reintegration
  - does not own task-law compilation or residual identity
- `V59`
  - remains sole owner of persistent workspace continuity over the selected path
  - does not own semantic continuation
- `V61`
  - should later own communication packets, ingress interpretation, office binding,
    and rewitness law
  - may consume `V60` continuation outcomes
  - does not own starter task-law compilation in `V60-A`
- `V48`
  - remains sole owner of delegated worker execution after lawful dispatch

## 12. Deferred Seams

The starter slice should keep these seams explicit:

- deferred_to_later_family:
  - governed communication packet law
  - communication ingress interpretation over raw surfaces
  - office binding and rewitness gate law
  - connector admission
  - remote operator control surfaces
  - repo-bound writable-surface authority
  - delegated worker export under `V48`
- deferred_to_later_slice:
  - residual refresh / reproposal / escalation over multiple reintegrations
  - advisory continuation hardening / migration
- not_selected_yet:
  - raw chat-native starter ingress
  - ticket duration widening
  - replay / resume authority
  - execute widening
  - dispatch widening

## 13. Machine-Checkable Summary

- family:
  - `V60`
- family role:
  - bounded task-law compilation and continuation identity
- starter ingress:
  - typed `agentic_de_seed_intent_record@1` only
  - non-chat-native
- starter outputs:
  - `agentic_de_task_charter_packet@1`
  - `agentic_de_task_residual_packet@1`
  - `agentic_de_loop_state_ledger@1`
  - `agentic_de_continuation_decision_record@1`
- task charter posture:
  - compiled bounded task law
  - not raw user request echo
  - typed and replayable
- `TaskResidual` posture:
  - derived only
  - not authored law
  - not standing authority
- selected downstream path:
  - shipped exact `V59` continuity-bound `local_write/create_new` exemplar
- continuation decision:
  - replayable and policy-bound
- `continue_to_governed_act`:
  - exact already shipped downstream path only in `V60-A`
- `emit_governed_communication`:
  - posture outcome only in `V60`
  - packet law deferred to `V61`
- forbidden by default:
  - ticket-duration widening
  - raw transcript ingress as task law
  - connector traffic as starter ingress law
  - repo-bound writable widening
  - delegated export widening
