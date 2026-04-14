# Draft ADEU Resident-Agent Local-Effect Hardening V57C Implementation Mapping v0

Status: support note for the `V57-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the third slice
should decide whether the observed and restored local-write path deserves stronger
local hardening later without silently mutating the shipped `V56` or `V57` live
behavior by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v40.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V57-A` observation/conformance surfaces
- shipped `V57-B` restoration surface
- the frozen `local_write` sandbox semantics

## Re-Author With Repo Alignment

`V57-C` should add exactly:

- `agentic_de_local_effect_hardening_register@1`

This should remain advisory-only in this slice.

It may decide:

- `keep_warning_only`
- `needs_more_evidence`
- `candidate_for_later_local_hardening`
- `not_selected_for_escalation`

It may not decide:

- `gate_now`
- `sandbox_widen_now`
- `broader_write_now`
- `dispatch_now`
- `ci_required_now`

## Defer To Later Slice

- actual checkpoint/ticket mutation
- broader repo-write authority
- `local_reversible_execute` effect hardening
- stronger execute rollout
- delegated/external dispatch rollout

## Do Not Import

- hardening by narrative symmetry alone
- advisory-to-live promotion by default
- hidden-cognition proxy inputs
