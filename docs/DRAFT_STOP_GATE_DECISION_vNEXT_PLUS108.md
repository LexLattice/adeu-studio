# Draft Stop-Gate Decision (Pre vNext+108)

This note records the pre-start stop-gate posture for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md`

Status: starter decision scaffold for `V47-C` (April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS108.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v108_start_stop_gate_scaffold",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Starter scaffold only. Closeout evidence, metric continuity, and final gate values are added after implementation merges."
}
```

## Stop-Gate Question

Should `vNext+108` release the bounded `V47-C` coexistence and companion-doc adoption
lane over the already released `V47-A` + `V47-B` stack without reopening ANM
architecture, hardening drift, ownership transition, or execution authority?

Current answer: not yet evaluated. This document is the pre-start scaffold only.

## Required Release Shape

To pass stop-gate at closeout, `V47-C` should show:

- one canonical `anm_markdown_coexistence_profile@1` with authoritative/mirrored schema
  parity;
- deterministic standalone-vs-companion classification over one declared snapshot and
  bounded source scope;
- explicit current-markdown non-override posture on all companion examples;
- exact consistency between `current_markdown_authority_relation` and
  `requires_later_lock_for_supersession`;
- explicit companion embedding posture plus valid host-or-companion linkage on all
  companion rows;
- explicit bounded migration doctrine that does not authorize repo-wide conversion;
- explicit adoption-boundary rows showing:
  - allowed constrain actions now;
  - actions requiring later lock-level adoption;
  - actions forbidden in `V47-C`;
- action vocabulary consistency between source rows and adoption-boundary rows;
- fail-closed rejection of implicit supersession, orphaned or contradictory linkage,
  migration overreach, ownership-transition creep, and authority laundering.

## Non-Goals

`V47-C` must not be treated as authority to ship:

- repo-wide markdown migration;
- imported O-owned selector handles;
- imported E-owned predicate registries;
- source-level `DEFERRED`;
- execution, approval, mutation, scheduling, waiver, or deferral authority;
- implicit current-markdown supersession by companion ANM existence alone.

## Expected Evidence At Closeout

Closeout should supply:

- merged PR and green CI evidence;
- one canonical `v47c_authoritative_normative_markdown_coexistence_evidence@1` input;
- authoritative/mirrored schema parity evidence;
- accepted standalone, companion, mixed-scope, and adoption-boundary fixtures;
- reject-fixture evidence for non-override, supersession inconsistency, orphaned or
  stale linkage, migration, compatibility, action-vocabulary drift, and
  anti-authority-laundering failures;
- stop-gate continuity artifacts and runtime observability comparison.

## Provisional Release Criteria

`V47-C` should be considered releasable only if:

1. coexistence/adoption doctrine is explicit rather than prose-inferred;
2. companion posture remains explicitly non-overriding relative to current markdown
   authority;
3. supersession fields remain exact and non-contradictory;
4. companion embedding and linkage semantics are explicit and valid;
5. same-snapshot identity and artifact-local source-scope compatibility are enforced;
6. bounded coexistence vocabularies remain exact;
7. the shipped slice remains non-executive and non-migratory.
