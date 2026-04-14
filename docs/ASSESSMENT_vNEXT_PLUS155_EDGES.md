# Assessment vNext+155 Edges

Status: planning-edge assessment for `V57-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS155_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Actual Local Effect Could Escape The Designated Sandbox

- Risk:
  once `V57-A` allows one actual effect, implementation pressure could drift from one
  designated sandbox root into broader repo write authority.
- Response:
  require one explicit designated local-effect sandbox root and fail closed on writes
  outside that root.
  - no symlink escape
  - no parent traversal
  - no indirect alias or mount redirection
  - no write-through into authority-bearing surfaces through sandbox references

### Edge 2: Observed Effect Could Be Claimed Without Explicit Pre/Post Evidence

- Risk:
  the slice could claim "observed local effect" while omitting explicit pre-state,
  observed write-set, or post-state evidence.
- Response:
  require one local-effect observation surface and one local-effect conformance surface
  with explicit pre/post and boundedness axes.
  - preserve explicit negative outcomes:
    - bounded effect observed
    - no effect observed
    - out-of-scope write observed
    - mismatched effect observed
    - boundedness verdict failed

### Edge 3: `local_write` Could Still Be Too Broad For The First Actual-Effect Slice

- Risk:
  even if the class label stays frozen, the first actual-effect slice could still allow
  destructive, overwrite, rename, delete, or metadata-mutating writes while
  restoration remains out of scope.
- Response:
  keep the exact `V56-B` `bounded_local_artifact` interpretation frozen, reject any
  semantic repartition by default, and narrow the first selected subset to:
  - `create_new`
  - `append_only`

### Edge 4: Observed Writes Could Drift Away From Ticket Lineage

- Risk:
  actual writes could be observed inside the sandbox but not remain attributable to one
  lawful ticket/proposal/checkpoint scope.
- Response:
  require every observed write to bind to one live ticket, one selected action
  proposal, and one checkpoint-entitled bounded effect scope.

### Edge 5: Actual Effect Could Quietly Mutate Ticket Or Checkpoint Law

- Risk:
  once actual local effect exists, the repo could start treating effect success as if
  checkpoint or ticket semantics had strengthened automatically.
- Response:
  keep the new observation/conformance outputs evidence-bearing only in this slice and
  forbid default mutation of checkpoint or ticket behavior.

### Edge 6: `V57-A` Could Overclaim Restoration Or Hardening

- Risk:
  one observed effect could be mistaken for restoration evidence or immediate local
  hardening.
- Response:
  keep restoration and hardening explicitly deferred to later `V57` lanes.
  - `V57-A` may emit observed-effect evidence only
  - it may not classify that evidence into governance hardening recommendations or
    restoration policy inside the same slice

### Edge 7: `V57-A` Could Smuggle In Other Live Classes

- Risk:
  actual effect support could be used to widen into `local_reversible_execute`,
  stronger execute, or delegated/external dispatch.
- Response:
  select exactly `local_write` only and keep all other live classes out of scope.

### Edge 8: Hidden-Cognition Or Product/Worker Boundaries Could Reappear

- Risk:
  actual local-effect work could be used to reintroduce hidden-cognition proxies,
  product rollout, or delegated worker ownership under a different name.
- Response:
  keep `V57-A` grounded in externalized effect evidence only, keep product/multi-agent
  widening out, and preserve `V48` ownership after any later lawful dispatch.

## Current Judgment

- `V57-A` is worth implementing next because `V56-C` closed the resident-agent
  governance family on `main` and identified one exact later candidate:
  - `local_write_post_effect_observation_path`
- the slice remains properly bounded if it stays:
  - existing-package-first
  - shipped-`V56`-surface-reuse-first
  - designated-sandbox-first
  - `local_write`-only
  - safe-subset-only:
    - `create_new`
    - `append_only`
  - explicit pre/post observation
  - explicit negative outcomes
  - lawful ticket/proposal/checkpoint binding
  - evidence-bearing rather than hardening-bearing
  - non-restoration
  - non-dispatch
  - non-product
  - non-hidden-cognition-governing
