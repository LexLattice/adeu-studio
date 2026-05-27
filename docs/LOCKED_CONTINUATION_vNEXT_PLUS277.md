# LOCKED_CONTINUATION_vNEXT_PLUS277

## Status

Bounded starter lock draft for `OTB-0-C` (transition delta attribution, stale
phase-object invalidation, integration handoff, and family closeout alignment).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`OTB-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `OTB-0`
- slice: `OTB-0-C`
- branch-local execution target: `arc/otb-0-c`

## Purpose

Freeze the bounded `OTB-0-C` starter slice so the repo can consume released
`OTB-0-A` / `OTB-0-B` records plus run-delta inputs and emit pressure-only
transition attribution, stale-object invalidation, integration handoff, and
family closeout alignment records.

`vNext+277` authorizes docs plus the next implementation path over the existing
repo-owned `adeu_transition_broker` package. It does not authorize semantic
adjudication, clean product truth claims, implementation authority, gate
execution, probe generation, probe execution, worker dispatch, product behavior
claims, official-eval submission, ProgramBench integration, future-family
selection, release authority, or recursive policy amendment.

Controlling invariant:

```text
OTB-0-C may classify observed pressure against phase-transition bridges,
invalidate stale phase objects, and prepare constrained handoff records.

OTB-0-C may not launder post-eval pressure into clean first-pass evidence,
grant implementation authority, select a future family, or treat score movement
as proof that a bridge is correct.
```

## Instantiated Here

- `OTB-0-C` instantiates the third deterministic transition-broker seam:
  - existing repo-owned package:
    - `adeu_transition_broker`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`
    - `docs/ARCHITECTURE_ADEU_ODEU_TRANSITION_BROKER_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS275.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS276.md`
    - `docs/ASSESSMENT_vNEXT_PLUS275_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS276_EDGES.md`
    - `artifacts/agent_harness/v275/evidence_inputs/otb_0a_closeout_evidence_v275.json`
    - `artifacts/agent_harness/v276/evidence_inputs/otb_0b_closeout_evidence_v276.json`
  - consumed package surfaces:
    - `packages/adeu_transition_broker/src/adeu_transition_broker/otb_0a.py`
    - `packages/adeu_transition_broker/src/adeu_transition_broker/otb_0b.py`
    - `packages/adeu_transition_broker/tests/test_otb_0a.py`
    - `packages/adeu_transition_broker/tests/test_otb_0b.py`
    - `packages/adeu_transition_broker/schema/`
  - emitted starter record shapes:
    - `repo_phase_transition_delta_attribution_ledger@1`
    - `repo_phase_stale_object_invalidation_report@1`
    - `repo_transition_broker_integration_handoff@1`
    - `repo_transition_broker_family_closeout_alignment@1`

## Required Starter Vocabulary

`OTB-0-C` must reuse A/B vocabulary where possible and add only C-level
pressure, invalidation, and handoff vocabulary:

- `pressure_kind`
- `confidence_posture`
- `evidence_boundary_posture`
- `invalidation_reason`
- `handoff_posture`
- `allowed_consumption`
- `forbidden_consumption`
- `closeout_alignment_status`

Required evidence boundary postures:

```text
post_eval_pressure_only
local_locked_probe_delta
official_like_pressure
source_postmortem_pressure
clean_first_pass_disallowed
```

Required invalidation reasons:

```text
object_hash_changed
catalog_hash_changed
bridge_contract_hash_changed
evidence_boundary_changed
obligation_set_changed
target_substrate_changed
run_topology_changed
```

## Required Record Shapes

Minimum `repo_phase_transition_delta_attribution_ledger@1` fields:

- `transition_delta_attribution_ledger_ref`
- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `input_closure_report_refs`
- `run_delta_ref`
- `attribution_rows`
- `evidence_boundary_posture`
- `canonical_output_hash`

Attribution rows must include:

- `attribution_ref`
- `transition_id`
- `bridge_field`
- `pressure_kind`
- `pressure_summary`
- `evidence_boundary_posture`
- `run_delta_refs`
- `confidence_posture`
- `recommended_route`

Minimum `repo_phase_stale_object_invalidation_report@1` fields:

- `stale_object_invalidation_report_ref`
- `input_artifact_refs`
- `new_artifact_refs`
- `invalidated_artifact_rows`
- `invalidation_reason_rows`
- `required_revalidation_frontier`
- `canonical_output_hash`

Minimum `repo_transition_broker_integration_handoff@1` fields:

- `transition_broker_integration_handoff_ref`
- `source_family`
- `target_family_or_lane`
- `handoff_posture`
- `allowed_consumption`
- `forbidden_consumption`
- `pressure_rows`
- `required_revalidation_rows`
- `canonical_output_hash`

Minimum `repo_transition_broker_family_closeout_alignment@1` fields:

- `family_closeout_alignment_ref`
- `completed_slices`
- `unimplemented_slices`
- `accepted_surfaces`
- `deferred_surfaces`
- `non_authority_boundary_confirmation`
- `future_pressure_notes`
- `canonical_output_hash`

## Required APIs

`OTB-0-C` must provide deterministic functions or equivalent module APIs that:

- attribute a run delta to transition bridge fields without treating score
  movement as proof;
- invalidate stale phase objects when object identity, bridge contracts,
  evidence boundaries, obligation sets, substrates, or run topology change;
- build integration handoff records with allowed and forbidden consumption
  boundaries;
- emit family closeout alignment records over accepted and deferred surfaces;
- compute stable canonical hashes independent of input order.

## Required Validation

`OTB-0-C` must fail closed when:

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

`OTB-0-C` must preserve this attribution law:

```text
A failure is evidence about the earliest unproven or broken transition bridge
that can explain it.
```

## Required Starter Fixtures

`OTB-0-C` must include focused fixtures for:

1. post-eval pressure row remains `post_eval_pressure_only`;
2. score movement without bridge evidence fails closed;
3. clean-first-pass label on official/postmortem pressure fails closed;
4. missing evidence boundary posture fails closed;
5. earlier unproven bridge dominates downstream product attribution;
6. object hash change emits stale-object invalidation;
7. bridge/evidence/obligation/substrate/run-topology changes emit distinct
   invalidation reasons;
8. handoff cannot grant implementation, execution, product, or future-family
   authority;
9. closeout alignment cannot mark an unaccepted slice complete;
10. shuffled input order preserves output order and canonical hashes.

## Deferred

Deferred to later families:

- actually executing generated gates or probes;
- dispatching workers;
- patching product code;
- ProgramBench integration;
- official-result governance;
- future-family selection;
- semantic compiler integration;
- implementation authority.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+277",
  "target_path": "OTB-0-C",
  "authority_layer": "lock",
  "selected_family": "OTB-0",
  "selected_slice": "OTB-0-C",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS277.md",
  "allowed_package": "packages/adeu_transition_broker",
  "selected_record_shapes": [
    "repo_phase_transition_delta_attribution_ledger@1",
    "repo_phase_stale_object_invalidation_report@1",
    "repo_transition_broker_integration_handoff@1",
    "repo_transition_broker_family_closeout_alignment@1"
  ],
  "local_gate": "make arc-start-check ARC=277",
  "non_authority_summary": "No semantic adjudication, clean product truth, gate execution, probe execution, worker dispatch, implementation authority, official-eval authority, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=277
```

Before opening the implementation PR:

```text
make check
```
