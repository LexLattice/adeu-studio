# Draft ADEU Resident-Agent Local-Effect Hardening V57B Implementation Mapping v0

Status: support note for the `V57-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the second slice
should add bounded restoration/replay evidence over the shipped `V57-A` observed local
effect without widening the selected live class or the sandbox boundary.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v40.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57A_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V57-A` sandbox, observation, and local-effect conformance surfaces
- the frozen `local_write` interpretation from `V56-B`
- the rule that one observed effect still does not mint hardening by itself

## Re-Author With Repo Alignment

`V57-B` should add exactly:

- `agentic_de_local_effect_restoration_record@1`

This should remain bounded to:

- the same designated sandbox root from shipped `V57-A`
- the same frozen `local_write` semantics
- one restoration / compensating-restore path only
- first over the shipped `create_new` exemplar from `V57-A`
- with append-only restoration still out of scope

Replay in this slice should mean only:

- bounded recomputation and re-evaluation of the restoration event against the prior
  observed-effect lineage
- not general re-execution of arbitrary prior live actions

`V57-B` should make the restoration entitlement law explicit:

- the original ticket is not ambient ongoing authority for later writes
- restoration is lawful only when one bounded compensating scope can be derived from
  the prior observed path and matched fail-closed against the shipped ticket /
  checkpoint lineage
- reuse of the `V57-A` observation subset does not imply restoration eligibility for
  every observed subset member
- restoration pre-state and post-state remain scoped only to the designated sandbox
  effect region, not to repo-global state
- the restoration record records bounded compensating behavior and outcomes only; it
  does not by itself nominate policy, class, or entitlement changes

## Defer To Later Slice

- hardening register
- any change to checkpoint/ticket law
- any class widening beyond `local_write`

## Do Not Import

- restoration claims with no explicit pre/post evidence
- silent widening from compensating restore of the shipped `create_new` exemplar into
  general delete or append-only restoration authority
- wider repo write authority
- `local_reversible_execute` effect widening
- stronger execute or dispatch rollout
