# Assessment vNext+156 Edges

Status: post-closeout edge assessment for `V57-B` (April 14, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS156_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Restoration Could Escape The Designated Sandbox

- Risk:
  once `V57-B` allows one compensating-restore path, implementation pressure could
  drift from one designated sandbox root into broader repo write authority.
- Response:
  require the same designated local-effect sandbox root from shipped `V57-A` and fail
  closed on restoration writes outside that root.
  - no symlink escape
  - no parent traversal
  - no indirect alias or mount redirection
  - no write-through into authority-bearing surfaces through sandbox references
- Closeout Evidence:
  merged `V57-B` keeps restoration under
  `artifacts/agentic_de/v57/local_effect/` and tests preserve fail-closed anti-escape
  checks.

### Edge 2: Restoration Could Be Claimed Without Prior Observation Evidence

- Risk:
  the slice could claim "restoration" while omitting one prior bounded observation or
  one prior conformance surface.
- Response:
  require one restoration record that binds exactly one prior
  `bounded_effect_observed` outcome and one prior conformance ref before restoration
  can be evaluated.
- Closeout Evidence:
  shipped checker path requires prior observation + conformance lineage and rejects
  malformed/missing prior evidence posture.

### Edge 3: Restoration Entitlement Could Be Misread As Ambient Ongoing Ticket Authority

- Risk:
  "same ticket lineage" could be read as if the original ticket authorizes a whole
  chain of later writes rather than one bounded compensating restore.
- Response:
  make the restoration entitlement law explicit.
  - the original ticket is not ambient ongoing authority
  - restoration is lawful only when one bounded compensating scope can be derived and
    matched fail-closed from prior observation and shipped ticket/checkpoint lineage
  - replay means bounded recomputation and re-evaluation of the restoration event, not
    general re-execution of arbitrary prior live actions
- Closeout Evidence:
  merged `V57-B` fixtures and tests preserve the lineage-bound entitlement posture and
  fail closed when ticket/conformance lineage mismatches appear.

### Edge 4: `V57-B` Could Smuggle In Broader Destructive Authority

- Risk:
  compensating restore of the shipped `create_new` exemplar could quietly widen into
  general delete, overwrite, truncate, rename, or append-only restoration authority.
- Response:
  keep the exact `V56-B` `bounded_local_artifact` interpretation frozen, reject any
  semantic repartition by default, and narrow the first restoration exemplar to:
  - compensating restore of the shipped `V57-A` `create_new` artifact only
  - reuse of the `V57-A` observation subset does not imply restoration eligibility for
    every observed subset member
- Closeout Evidence:
  shipped `V57-B` checker and tests enforce create-new restoration-only posture and
  reject append-only restoration in this slice.

### Edge 5: Restoration Could Drift Away From Ticket Lineage

- Risk:
  restoration writes could happen inside the sandbox but not remain attributable to
  one lawful ticket/proposal/checkpoint scope reused from the observed path.
- Response:
  require every restoration write to bind to one prior observation ref, one prior
  conformance ref, one live ticket, one selected action proposal, and one
  checkpoint-entitled bounded effect lineage.
  - restoration pre-state and post-state remain scoped only to the designated sandbox
    effect region, not to repo-global state
- Closeout Evidence:
  shipped restoration fixture includes explicit observation/conformance/ticket/
  proposal/checkpoint refs with sandbox-scoped pre/post state refs, and tests preserve
  fail-closed lineage checks.

### Edge 6: Restoration Could Quietly Mutate Ticket Or Checkpoint Law

- Risk:
  once compensating restore exists, the repo could start treating restoration success
  as if checkpoint or ticket semantics had strengthened automatically.
- Response:
  keep the new restoration output evidence-bearing only in this slice and forbid
  default mutation of checkpoint or ticket behavior.
- Closeout Evidence:
  shipped restoration fixture keeps `evidence_only = true` and
  `changes_live_behavior_by_default = false`.

### Edge 7: `V57-B` Could Overclaim Hardening

- Risk:
  one successful restoration could be mistaken for immediate local hardening.
- Response:
  keep hardening explicitly deferred to later `V57-C`.
  - `V57-B` may emit restoration evidence only
  - it may not classify that evidence into hardening recommendation inside the same
    slice
  - the restoration record does not by itself nominate policy, class, or entitlement
    changes
- Closeout Evidence:
  merged `V57-B` ships no hardening register and no advisory hardening output over the
  restoration record.

### Edge 8: `V57-B` Could Smuggle In Other Live Classes

- Risk:
  restoration support could be used to widen into `local_reversible_execute`,
  stronger execute, or delegated/external dispatch.
- Response:
  keep the live class exactly `local_write` only and keep all other live classes out
  of scope.
- Closeout Evidence:
  merged `V57-B` adds bounded `local_write` restoration only and introduces no new
  live class or dispatch/stronger-execute path.

### Edge 9: Hidden-Cognition Or Product/Worker Boundaries Could Reappear

- Risk:
  local restoration work could be used to reintroduce hidden-cognition proxies,
  product rollout, or delegated worker ownership under a different name.
- Response:
  keep `V57-B` grounded in externalized restoration evidence only, keep
  product/multi-agent widening out, and preserve `V48` ownership after any later
  lawful dispatch.
- Closeout Evidence:
  shipped `V57-B` is sandbox-local, lineage-bound, evidence-bearing only, and
  introduces no hidden-thought proxy input, product/API surface, or delegated worker
  ownership.

## Current Judgment

- `V57-B` was the right next slice because `V57-A` closed one bounded local-effect
  observation path on `main` and surfaced one exact later candidate:
  - `compensating_restore_of_observed_create_new_local_write_path`
- the shipped result remained properly bounded:
  - existing-package-first
  - shipped-`V56`-surface-reuse-first
  - shipped-`V57-A`-surface-reuse-first
  - designated-sandbox-first
  - `local_write`-only
  - create-new-restore-exemplar-only
  - explicit restoration-entitlement law
  - narrow replay meaning only
  - explicit prior observation/conformance lineage
  - sandbox-region-scoped pre/post state
  - explicit negative restoration outcomes
  - evidence-bearing rather than hardening-bearing
  - non-append-only-restoration
  - non-dispatch
  - non-product
  - non-hidden-cognition-governing
- `V57-B` is now closed on `main` in the branch-local sense:
  - `adeu_agentic_de`
- any later restoration widening, hardening-register addition, execute selection,
  dispatch widening, or repo-authority widening should proceed only through explicit
  next-lane lock and drift-check handoff.
