# Architecture: ADEU Resident-Agent Persistent Workspace Continuity Family v0

Status: architecture / decomposition draft for `V59`.

Authority layer: architecture_decomposition.

This note does not authorize implementation by itself. It defines the bounded family
role that should turn the already shipped `V56` / `V57` / `V58` governed live path
into a declared persistent workspace-continuity path without allowing prior workspace
state to become ambient authority.

## 1. Family Role

`V59` is not another checkpoint family, not another local-effect family, and not
another live-harness admission family.

It is the family that owns:

- declared bounded continuity-region identity;
- current-turn continuity admission over carried-forward workspace state;
- explicit occupancy / prior-presence classification for the selected target;
- explicit drift classification over carried-forward governed state versus out-of-band
  state;
- and continuity reintegration of the governed act back into the resident turn report.

The family therefore sits downstream of `V58`.

- `V56` owns packet / proposal / checkpoint / ticket law.
- `V57` owns observed / restored local-effect evidence and path-level hardening advice.
- `V58` owns live-turn admission / handoff / reintegration over the selected live path.
- `V59` owns how that already integrated live path persists across turns inside one
  declared bounded work region.

## 2. Lineage And Naming

`agentic_de_*` remains the lineage carrier for the typed runtime-governance objects.

That naming choice should not be over-read.

- lineage carrier:
  - `agentic_de_*`
- family role:
  - resident-agent persistent workspace continuity and continuity reintegration

So this family is not “just more `V58`,” even though it reuses the shipped live-turn
lineage nearly as-is.

## 3. Continuity Boundary Thesis

The central law is:

- prior workspace continuity is necessary context at most;
- current-turn artifact entitlement remains necessary;
- neither side may silently absorb the other.

In the current repo that means:

- carried-forward files inside a declared continuity region are real state;
- prior governed lineage over those files is real context;
- out-of-band mutations are real drift context;
- but none of those surfaces is current-turn permission by itself.

So:

- stopping a reset is not continuity law;
- prior successful turn is not standing admissibility;
- prior ticket is not standing authority;
- prior reintegration is not ambient current-turn witness;
- and no hidden workspace state may decide eligibility.

## 4. Starter Artifact Ladder

The starter family ladder should add these new shapes over the shipped `V56` / `V57` /
`V58` surfaces:

1. `agentic_de_workspace_continuity_region_declaration@1`
   - declared bounded persistent region
   - explicit target set and occupancy policy
2. `agentic_de_workspace_continuity_admission_record@1`
   - current-turn continuity snapshot over carried-forward state
   - typed and replayable continuity verdict, not boolean continuity presence
3. `agentic_de_workspace_occupancy_report@1`
   - target-level prior-presence and drift classification before the act
   - explicit witness-bearing basis for the occupancy verdict
4. `agentic_de_workspace_continuity_reintegration_report@1`
   - typed closeout over the continuity-bound act and its carried-forward state
   - explicit continuity witness basis or certificate reference for any positive
     reintegration claim

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

## 5. Starter Runtime Boundary Model

The starter continuity path should be:

```text
shipped V58 live-turn admission / handoff lineage
  -> declared continuity region
  -> current-turn continuity admission record
  -> occupancy report
  -> shipped V56 ticketed act
  -> shipped V57 observed effect + conformance
  -> shipped V58 live-turn reintegration
  -> continuity reintegration report
  -> six-lane run summary
```

What changes here is not the inner law and not the live bridge.

What changes is that carried-forward workspace state stops being ambient.

Continuity admission is therefore an additional gate over carried-forward state.

It is never a substitute for shipped `V58` current-turn live admission, and continuity
reintegration wraps around the already ordered `V58` / `V56` / `V57` path rather than
reordering it.

## 6. Starter Freeze

`V59-A` should stay frozen to one exact path:

- live session path:
  - existing URM copilot session path already selected by `V58`
- action class:
  - `local_write`
- write kind:
  - `create_new`
- declared continuity root:
  - `artifacts/agentic_de/v59/workspace_continuity/`
- exact starter target centered on:
  - `runtime/reference_patch_candidate.diff`
- duration posture:
  - single-step local only

The family should not expand to general repo-source continuity in the first slice.

The declared continuity root remains bounded inside `artifacts/` until later selection.

## 7. Occupancy Law

Persistent continuity changes the semantics of `create_new`.

So the starter family should require one explicit occupancy verdict before the act.

At minimum the starter slice should distinguish:

- `unoccupied`
- `occupied_prior_governed_exact`
- `occupied_prior_governed_drifted`
- `occupied_out_of_band`
- `occupied_unknown`

The occupancy verdict itself must remain witness-bearing and replayable.

At minimum the starter family should require a declared basis drawn only from:

- declared region snapshot identity;
- target-level file presence or absence under the declared region;
- prior governed artifact refs when a prior governed match is asserted;
- root-origin linkage for any claimed prior governed lineage; and
- explicit out-of-band detection grounds when out-of-band occupancy is asserted.

So the same selected occupancy evidence chain plus the same frozen policy must yield
the same occupancy verdict.

The starter entitlement law should then remain exact:

- `create_new` is admissible only when the occupancy verdict is `unoccupied`;
- any occupied verdict is non-entitling in the starter slice;
- occupied or drifted state may inform diagnostics and reintegration;
- occupied or drifted state may not be silently normalized into admissibility.

The starter family should also keep one explicit region-scope law:

- non-target occupants already present inside the declared continuity root are
  contextual only in `V59-A`;
- they may be recorded as region-scope context or out-of-scope drift;
- they do not become target entitlement, ambient admissibility, or silent blocking
  unless a later lock explicitly selects broader region semantics.

## 8. Continuity Witness And Drift Law

Carried-forward state should remain explicitly typed.

At minimum the starter family should preserve these distinctions:

- carried-forward state
- lineage context
- drift context
- declared continuity witness
- current-turn native witness

Only the last category is native current-turn authority.

The others may inform continuity admission and reintegration, but may not self-promote
into current-turn ticket equivalence, current-turn occupancy entitlement, or current-turn
native witness.

The family should therefore require origin / dependence tagging over continuity
admission, occupancy, and reintegration surfaces so that:

- prior governed lineage remains distinguishable from current-turn native evidence;
- out-of-band drift remains distinguishable from governed carried-forward state;
- transcript and event stream remain observability only;
- and echoed lineage cannot return as apparently fresh independent current-turn support.

Continuity admission itself should also remain typed and replayable.

At minimum the starter family should distinguish verdicts such as:

- `admitted`
- `region_mismatch`
- `stale_continuity_basis`
- `unresolved_drift`
- `withheld_by_policy`
- `unknown`

The same selected continuity evidence chain plus the same frozen policy must yield the
same continuity admission verdict.

In the starter slice, only `admitted` is entitling.

Any other continuity admission verdict remains non-entitling and fail-closed until a
later lock explicitly selects broader continuity posture.

## 9. Pairwise Default

The starter family may remain pairwise by default.

That is defensible because the first continuity path is still:

- one session;
- one declared continuity region;
- one target path;
- one ticketed local action;
- one occupancy report;
- one exact observed effect lineage.

Higher-arity reserve should remain deferred until identical pairwise profiles can still
yield different operational outcomes for the selected continuity-bound act. Dispatch,
execute, or multi-target continuity will likely push there later. The starter
continuity-bound `create_new` path does not require it.

## 10. Relationship To Other Families

- `V55`
  - checks constitutional coherence of released family surfaces
  - does not own continuity enactment
- `V56`
  - remains sole owner of packet / proposal / checkpoint / ticket semantics
- `V57`
  - remains sole owner of observed / restored / hardening evidence over the selected
    local-effect path
- `V58`
  - remains sole owner of live-turn admission / handoff / reintegration over that path
- `V48`
  - remains sole owner of delegated worker execution after lawful dispatch
- `V51`
  - may shape membrane and reintegration reading
  - does not own runtime authority here

## 11. Deferred Seams

Deferred seams should be classified explicitly:

- `instantiated_here`
  - continuity-region declaration
  - continuity admission
  - occupancy report
  - continuity reintegration report
- `deferred_to_later_slice`
  - explicit continuity-safe restoration
  - continuity hardening / drift advisory surface
  - multi-target continuity
- `deferred_to_later_family`
  - delegated or external dispatch integration over persistent work surfaces
  - worker reconciliation over continuity regions
- `not_selected_yet`
  - append-only continuity
  - overwrite or destructive continuity semantics
  - `local_reversible_execute`
  - stronger execute
  - standing resume or replay authority
- `superseded_by_alternate_surface`
  - any attempt to treat prior workspace state as ambient entitlement
  - any attempt to govern hidden cognition directly

## 12. Machine-Checkable Summary

```json
{
  "schema": "adeu_resident_agent_persistent_workspace_continuity_family@1",
  "artifact": "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_FAMILY_v0.md",
  "status": "draft",
  "authority_layer": "architecture_decomposition",
  "lineage_carrier": "agentic_de_*",
  "family_role": "resident_agent_persistent_workspace_continuity_and_reintegration",
  "governs_hidden_cognition": false,
  "prior_workspace_state_is_context_at_most": true,
  "prior_workspace_state_is_not_standing_authority": true,
  "ceasing_runtime_reset_is_not_continuity_law": true,
  "starter_artifact_ladder": [
    "agentic_de_workspace_continuity_region_declaration@1",
    "agentic_de_workspace_continuity_admission_record@1",
    "agentic_de_workspace_occupancy_report@1",
    "agentic_de_workspace_continuity_reintegration_report@1"
  ],
  "continuity_admission_must_be_typed_and_replayable": true,
  "starter_continuity_admission_verdicts": [
    "admitted",
    "region_mismatch",
    "stale_continuity_basis",
    "unresolved_drift",
    "withheld_by_policy",
    "unknown"
  ],
  "occupancy_verdict_must_be_witness_bearing_and_replayable": true,
  "reused_shipped_surfaces": [
    "agentic_de_domain_packet@1",
    "agentic_de_action_proposal@1",
    "agentic_de_membrane_checkpoint@1",
    "agentic_de_action_ticket@1",
    "agentic_de_local_effect_observation_record@1",
    "agentic_de_local_effect_conformance_report@1",
    "agentic_de_live_turn_admission_record@1",
    "agentic_de_live_turn_handoff_record@1",
    "agentic_de_live_turn_reintegration_report@1"
  ],
  "selected_starter_path": {
    "live_session_path": "urm_copilot_session_path",
    "action_class": "local_write",
    "write_kind": "create_new",
    "declared_continuity_root": "artifacts/agentic_de/v59/workspace_continuity/",
    "target_relative_path": "runtime/reference_patch_candidate.diff"
  },
  "starter_occupancy_verdicts": [
    "unoccupied",
    "occupied_prior_governed_exact",
    "occupied_prior_governed_drifted",
    "occupied_out_of_band",
    "occupied_unknown"
  ],
  "non_target_occupants_are_contextual_only_in_starter": true,
  "starter_create_new_requires_unoccupied_target": true,
  "positive_continuity_reintegration_requires_explicit_witness_basis_or_certificate_ref": true,
  "pairwise_default_retained": true,
  "higher_arity_reserved": true,
  "continuity_safe_restoration_selected_in_starter": false,
  "replay_or_resume_widening_selected_in_starter": false
}
```
