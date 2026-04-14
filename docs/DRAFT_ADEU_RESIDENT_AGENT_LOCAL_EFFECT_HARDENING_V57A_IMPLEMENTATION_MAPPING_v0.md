# Draft ADEU Resident-Agent Local-Effect Hardening V57A Implementation Mapping v0

Status: support note for the `V57-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the first slice
should capture one actually observed bounded local effect without silently widening the
released `V56` live gate.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v40.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_V56C_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V56-A`, `V56-B`, and `V56-C` surfaces
- the exact `V56-B` interpretation of `local_write` as `bounded_local_artifact`
- the rule that actual effect remains downstream of lawful ticket lineage
- the rule that one observed effect does not by itself authorize hardening

## Re-Author With Repo Alignment

`V57-A` should add exactly:

- `agentic_de_local_effect_observation_record@1`
- `agentic_de_local_effect_conformance_report@1`

These should be evidence-bearing only in this slice.

`V57-A` should select exactly:

- one actual `local_write` effect path only
- one first safe `local_write` subset only:
  - `create_new`
  - `append_only`

It should not select:

- overwrite
- truncate
- rename or move
- delete
- metadata mutation
- `local_reversible_execute`
- `stronger_execute`
- `delegated_or_external_dispatch`

## `V57-A` Evidence Inputs

`V57-A` should consume shipped outputs from prior lanes, not narrative docs alone:

- one `V56-A` packet / proposal / checkpoint / conformance reference set
- one `V56-B` taxonomy / runtime-state / ticket / conformance reference set
- one `V56-C` harvest / calibration / migration reference set
- one `agentic_de_lane_drift_record@1`

Committed fixtures, tickets, conformance outputs, harvest outputs, lane-drift record,
and closeout evidence should outrank narrative interpretation when `V57-A` derives its
effect observation surfaces.

## Starter Observation Law

`V57-A` should require:

- one designated local-effect sandbox root only:
  - `artifacts/agentic_de/v57/local_effect/`
- one anti-escape sandbox law only:
  - no symlink escape
  - no parent traversal
  - no indirect alias or mount redirection
  - no write-through into authority-bearing surfaces through sandbox references
- one explicit binding law only:
  - every observed write must bind to one live ticket
  - one selected action proposal
  - one checkpoint-entitled bounded effect scope
- one explicit pre-state ref before effect
- one explicit observed write-set after effect
- one explicit post-state ref after effect
- one explicit boundedness verdict over the observed effect
- one explicit observation outcome vocabulary at least:
  - `bounded_effect_observed`
  - `no_effect_observed`
  - `out_of_scope_write_observed`
  - `mismatched_effect_observed`
  - `boundedness_verdict_failed`

The starter slice should keep actual effect out of:

- repo source paths
- lock/decision/assessment docs
- CI config
- secrets or credentials
- dispatch surfaces
- external/remote paths

## Defer To Later Slice

- restoration / compensating restore
- hardening register
- broader repo write authority
- product-wide rollout
- multi-agent coordination

## Do Not Import

- silent widening from designated sandbox to general repo write authority
- harvest/calibration or hardening recommendations inside the same slice
- claims of restoration without restoration evidence
- hardening claims from one observed effect alone
- hidden-cognition proxies as effect-governance inputs
