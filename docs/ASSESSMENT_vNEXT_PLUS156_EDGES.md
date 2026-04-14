# Assessment vNext+156 Edges

Status: planning-edge assessment for `V57-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS156_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
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

### Edge 2: Restoration Could Be Claimed Without Prior Observation Evidence

- Risk:
  the slice could claim "restoration" while omitting one prior bounded observation or
  one prior conformance surface.
- Response:
  require one restoration record that binds exactly one prior
  `bounded_effect_observed` outcome and one prior conformance ref before restoration
  can be evaluated.

### Edge 3: Restoration Entitlement Could Be Misread As Ambient Ongoing Ticket Authority

- Risk:
  "same ticket lineage" could be read as if the original ticket authorizes a whole
  chain of later writes rather than one bounded compensating restore.
- Response:
  make the restoration entitlement law explicit.
  - the original ticket is not ambient ongoing authority
  - restoration is lawful only when one bounded compensating scope can be derived and
    matched fail-closed from the prior observation and shipped ticket / checkpoint
    lineage
  - replay means bounded recomputation and re-evaluation of the restoration event, not
    general re-execution of arbitrary prior live actions

### Edge 4: `V57-B` Could Smuggle In Broader Destructive Authority

- Risk:
  compensating restore of the shipped `create_new` exemplar could quietly widen into
  general delete, overwrite, truncate, rename, or append-only restoration authority.
- Response:
  keep the exact `V56-B` `bounded_local_artifact` interpretation frozen, reject any
  semantic repartition by default, and narrow the first restoration exemplar to:
  - compensating restore of the shipped `create_new` artifact only
  - reuse of the `V57-A` observation subset does not imply restoration eligibility for
    every observed subset member

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

### Edge 6: Restoration Could Quietly Mutate Ticket Or Checkpoint Law

- Risk:
  once compensating restore exists, the repo could start treating restoration success
  as if checkpoint or ticket semantics had strengthened automatically.
- Response:
  keep the new restoration output evidence-bearing only in this slice and forbid
  default mutation of checkpoint or ticket behavior.

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

### Edge 8: `V57-B` Could Smuggle In Other Live Classes

- Risk:
  restoration support could be used to widen into `local_reversible_execute`,
  stronger execute, or delegated/external dispatch.
- Response:
  keep the live class exactly `local_write` only and keep all other live classes out
  of scope.

### Edge 9: Hidden-Cognition Or Product/Worker Boundaries Could Reappear

- Risk:
  local restoration work could be used to reintroduce hidden-cognition proxies,
  product rollout, or delegated worker ownership under a different name.
- Response:
  keep `V57-B` grounded in externalized restoration evidence only, keep
  product/multi-agent widening out, and preserve `V48` ownership after any later
  lawful dispatch.

## Current Judgment

- `V57-B` is worth implementing next because `V57-A` already shipped one bounded
  `create_new` observation on `main`, and the strongest remaining bounded gap is one
  compensating-restore path over that same sandbox-local exemplar.
- the slice remains properly bounded if it stays:
  - existing-package-first
  - shipped-`V56`-surface-reuse-first
  - shipped-`V57-A`-surface-reuse-first
  - designated-sandbox-first
  - `local_write`-only
  - `create_new`-restore-exemplar-only
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
