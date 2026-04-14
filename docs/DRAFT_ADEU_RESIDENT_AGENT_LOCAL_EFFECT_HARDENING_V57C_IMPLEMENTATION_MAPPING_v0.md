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
- the frozen shipped `V57-B` restoration exemplar semantics

## Re-Author With Repo Alignment

`V57-C` should add exactly:

- `agentic_de_local_effect_hardening_register@1`

This should remain advisory-only in this slice.

`V57-C` should consume:

- shipped observation / conformance / restoration fixtures
- one explicit `agentic_de_lane_drift_record@1`
- committed closeout evidence from shipped `V57-A` and `V57-B`

Those committed lane artifacts should outrank narrative interpretation by default.

The selected hardening target in this slice should remain exactly:

- the shipped observed and restored `create_new` exemplar only

`V57-C` should make the hardening-decision law explicit:

- the register is advisory-only in this slice
- the register is candidate-only for any later local hardening selection
- one observed/restored effect does not by itself mint checkpoint, ticket, class,
  sandbox, or entitlement change
- evidence from the selected observed/restored exemplar may not be generalized by
  default into class-level conclusions about `local_write`
- evidence from the selected observed/restored exemplar may not be generalized by
  default into restoration-family law
- observation evidence and restoration evidence remain separate from hardening
  suggestion
- hardening assessment should consume boundedness verdicts from both observation and
  restoration, not merely their refs
- the register should record target path, evidence basis, boundedness/conformance
  summary, and recommendation outcome without treating recommendation as an attribute
  of the evidence itself
- the register remains a path-level advisory surface, not a family-wide migration
  surface
- the register may assess the shipped path but may not mutate live checkpoint,
  ticket, observation, conformance, or restoration behavior by default

It may decide:

- `keep_warning_only`
- `needs_more_evidence`
- `candidate_for_later_local_hardening`
- `not_selected_for_escalation`

In this slice, `candidate_for_later_local_hardening` may nominate only one later
bounded evaluation target. It does not identify the scope of later hardening unless a
later lock types and selects that scope explicitly.

It may not decide:

- `gate_now`
- `sandbox_widen_now`
- `broader_write_now`
- `dispatch_now`
- `ci_required_now`

It should also forbid by default:

- semantic repartition of `local_write`
- semantic repartition of the shipped `V57-B` restoration exemplar
- restoration generalization from the shipped `create_new` exemplar
- hardening by narrative symmetry alone

## Defer To Later Slice

- actual checkpoint/ticket mutation
- broader repo-write authority
- broader restoration-law widening
- `local_reversible_execute` effect hardening
- stronger execute rollout
- delegated/external dispatch rollout

## Do Not Import

- advisory-to-live promotion by default
- hidden-cognition proxy inputs
