# Draft ADEU ODEU Transition Broker OTB-0-C Implementation Mapping v0

Status: support / implementation mapping record for planned `OTB-0-C`.

Authority layer: support.

This note maps likely implementation for `OTB-0-C`. It does not authorize
implementation by itself and does not replace a future `vNext+<n>` lock,
stop-gate decision, or edge assessment. `OTB-0-C` should remain deferred until
`OTB-0-A` and `OTB-0-B` have been released and real A/B artifacts exist.

## Slice Intent

`OTB-0-C` should consume released A/B records plus run-delta inputs and produce
pressure-only transition attribution, stale phase-object invalidation, and
integration handoff records.

It should answer:

```text
Given this run delta and these transition records, which bridge field or phase
handoff is under pressure, which artifacts are stale, and what handoff is safe?
```

It must not answer:

```text
What is the clean product truth?
Should implementation proceed?
Should the official score be trusted as semantic evidence?
Which future family is selected?
```

## Selected Surfaces

Likely schema / model surfaces:

- `repo_phase_transition_delta_attribution_ledger@1`
- `repo_phase_stale_object_invalidation_report@1`
- `repo_transition_broker_integration_handoff@1`
- `repo_transition_broker_family_closeout_alignment@1`

Likely source files:

- `packages/adeu_transition_broker/src/adeu_transition_broker/attribution.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/invalidation.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/handoff.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/closeout.py`
- `packages/adeu_transition_broker/tests/test_otb_0c.py`

## Field-Level Expectations

`repo_phase_transition_delta_attribution_ledger@1` should include:

- `transition_delta_attribution_ledger_ref`
- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `input_closure_report_refs`
- `run_delta_ref`
- `attribution_rows`
- `evidence_boundary_posture`
- `canonical_output_hash`

Attribution rows should include:

- `attribution_ref`
- `transition_id`
- `bridge_field`
- `pressure_kind`
- `pressure_summary`
- `evidence_boundary_posture`
- `run_delta_refs`
- `confidence_posture`
- `recommended_route`

Every attribution row should explicitly state one of:

- `post_eval_pressure_only`
- `local_locked_probe_delta`
- `official_like_pressure`
- `source_postmortem_pressure`
- `clean_first_pass_disallowed`

`repo_phase_stale_object_invalidation_report@1` should include:

- `stale_object_invalidation_report_ref`
- `input_artifact_refs`
- `new_artifact_refs`
- `invalidated_artifact_rows`
- `invalidation_reason_rows`
- `required_revalidation_frontier`

Invalidation reason rows should include:

- `object_hash_changed`
- `catalog_hash_changed`
- `bridge_contract_hash_changed`
- `evidence_boundary_changed`
- `obligation_set_changed`
- `target_substrate_changed`
- `run_topology_changed`

`repo_transition_broker_integration_handoff@1` should include:

- `transition_broker_integration_handoff_ref`
- `source_family`
- `target_family_or_lane`
- `handoff_posture`
- `allowed_consumption`
- `forbidden_consumption`
- `pressure_rows`
- `required_revalidation_rows`

`repo_transition_broker_family_closeout_alignment@1` should include:

- `family_closeout_alignment_ref`
- `completed_slices`
- `unimplemented_slices`
- `accepted_surfaces`
- `deferred_surfaces`
- `non_authority_boundary_confirmation`
- `future_pressure_notes`

## Core API Expectations

The implementation should expose deterministic module APIs equivalent to:

```text
attribute_transition_delta(closure_reports, run_delta)
  -> PhaseTransitionDeltaAttributionLedger
invalidate_stale_phase_objects(old_artifacts, new_artifacts, bridge_contracts)
  -> PhaseStaleObjectInvalidationReport
build_integration_handoff(attribution, invalidation, target_lane)
  -> TransitionBrokerIntegrationHandoff
emit_family_closeout_alignment(accepted_surfaces, deferred_surfaces)
  -> TransitionBrokerFamilyCloseoutAlignment
canonical_hash(payload) -> sha256
```

Names may vary if repo conventions prefer different names.

## Validation Requirements

`OTB-0-C` should fail closed when:

- score movement is treated as bridge proof without transition evidence;
- official failure pressure is labeled clean first-pass evidence;
- attribution row lacks evidence boundary posture;
- pressure is attributed to product semantics while an earlier unproven
  transition can explain it;
- stale artifact reuse is detected without invalidation;
- integration handoff grants implementation, execution, product, or future
  family authority;
- closeout claims a slice complete without accepted surface rows;
- unknown vocabulary appears in any row.

## Dominance Rule

`OTB-0-C` should preserve this failure attribution law:

```text
A failure is evidence about the earliest unproven or broken transition bridge
that can explain it.
```

If artifact packaging, target substrate, object identity, or evidence boundary
fails, downstream product semantics are not yet the dominant explanation.

## Non-Authority Guardrails

`OTB-0-C` can attribute pressure and invalidate stale objects. It cannot:

- claim clean product truth;
- select future families;
- grant implementation authority;
- dispatch workers;
- execute gates;
- patch code;
- launder post-eval pressure as first-pass evidence.

## Family Closeout Posture

Family closeout should state:

- which A/B/C surfaces were implemented;
- which surfaces were deferred;
- which integration lanes are allowed to consume outputs;
- which integration lanes remain forbidden;
- which evidence boundary rules remain pressure-only;
- which future families are suggested but not selected.

