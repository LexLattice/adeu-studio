# Draft ADEU Resident-Agent Interaction Governance V56C Implementation Mapping v0

Status: support note for the `V56-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the third slice
should add post-action governance evidence, harvest, and local calibration without
silently changing live gate behavior globally.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_V56_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_V56B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the shipped `V56-A` and `V56-B` surfaces
- per-surface and per-action-class calibration posture by default
- the rule that live behavior does not strengthen globally just because evidence now
  exists
- the operative interpretation of the selected `V56-B` live classes stays frozen by
  default in this slice

## Re-Author With Repo Alignment

`V56-C` should add exactly:

- `agentic_de_runtime_harvest_record@1`
- `agentic_de_governance_calibration_register@1`
- `agentic_de_migration_decision_register@1`

These should be advisory-only in this slice.

`agentic_de_runtime_harvest_record@1` should record observed pattern, delta, and
bounded derived summaries only. It should not by itself classify governance defects or
candidate escalations.

They may decide:

- `keep_warning_only`
- `needs_more_evidence`
- `candidate_for_later_local_hardening`
- `not_selected_for_escalation`

They may not decide:

- `gate_now`
- `checker_global_gate_now`
- `ci_required_now`

`agentic_de_migration_decision_register@1` should nominate later candidate hardening
paths only. It may not alter current ticket issuance law, checkpoint law, or
action-class entitlement in this slice.

## `V56-C` Evidence Inputs

`V56-C` should consume shipped outputs from prior lanes, not narrative docs alone:

- one `V56-A` diagnostics surface
- one `V56-A` conformance reference
- one `V56-B` checkpoint / ticket / conformance reference set
- one `agentic_de_lane_drift_record@1`

Committed fixtures, tickets, conformance outputs, lane-drift record, and closeout
evidence should outrank narrative interpretation when calibration and migration
surfaces are derived.

The advisory outputs in `V56-C` should keep conformance as a typed delta surface over:

- packed state
- proposed action
- checkpoint entitlement
- ticket issued or not
- executed or observed effect

## Defer To Later Slice

- product-wide rollout
- multi-agent coordination
- checker-global enforcement
- direct governance over hidden reasoning

## Do Not Import

- silent live-behavior mutation from advisory registers alone
- narrative-only calibration with no shipped evidence surfaces
- semantic reinterpretation of the selected `V56-B` live classes that changes live
  boundary behavior by default
- runtime-harvest features, latent-score proxies, internal-quality heuristics, or
  post hoc inferred cognitive descriptors as authority-bearing calibration inputs
