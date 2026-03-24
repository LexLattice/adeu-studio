# Assessment vNext+79 Edges

Status: planning-edge assessment for `V40-C`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS79_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Hybrid Source-Bypass Drift

- Risk:
  the slice could synthesize checkpoints from ad hoc local ambiguity data instead of
  binding hybrid artifacts back to released `V40-A` semantic-root and `V40-B`
  conformance surfaces.
- Response:
  require every request, resolution, delta, and checkpoint trace to carry exact
  semantic-root and conformance lineage and reject free-floating checkpoint fixtures
  where released upstream artifacts already exist.

### Edge 2: Oracle Authority Drift

- Risk:
  oracle output could start acting like a mutation authority or a policy-authority
  surface instead of bounded advice.
- Response:
  keep oracle output advisory-only, forbid authority/capability/boundary/scope minting,
  and preserve deterministic adjudicator ownership over final checkpoint disposition.

### Edge 3: Replay Identity Under-Specification

- Risk:
  a too-small replay identity could let cache reuse or resolution replay occur across
  mismatched context, model versions, or policy-source sets.
- Response:
  pin exact request identity across semantic/conformance lineage, policy-source hashes,
  model/version, reasoning effort, template version, compiler version, and bounded
  context identity.

### Edge 4: Delta Surface Widening Into Patch Semantics

- Risk:
  `adeu_architecture_ir_delta@1` could silently become a patch-payload or repo-mutation
  vehicle before deterministic revalidation and downstream lowering boundaries exist.
- Response:
  treat `ir_delta` as the only legal repair-shaped output, but keep it proposal-only,
  bounded to existing or pre-authorized refs, and incapable of direct mutation in
  `vNext+79`.

### Edge 5: Conformance / Hybrid Collapse

- Risk:
  the new checkpoint trace could restate or overwrite deterministic readiness semantics
  that already belong to `adeu_architecture_conformance_report@1`.
- Response:
  preserve the architecture rule that final adjudication in checkpoint trace and compile
  readiness in conformance report remain distinct surfaces with distinct authority.

### Edge 6: Multi-Round Oracle Creep

- Risk:
  the first baseline could widen into repeated oracle back-and-forth and lose exact
  replayability.
- Response:
  freeze one oracle round trip per checkpoint in the first baseline and fail closed on
  contradictory or unstable resolution states.

### Edge 7: Premature Human-Review Surface Inflation

- Risk:
  `V40-C` could overreach into API or web human-review workbench territory before the
  checkpoint/oracle/trace contract itself is stable.
- Response:
  keep human review represented only as typed `human_needed` /
  `escalated_human` disposition in this slice and defer workbench surfaces.

### Edge 8: Formal-Sidecar Drift

- Risk:
  the Lean sidecar could be mistaken for the source of truth and silently redefine the
  mainline hybrid artifact boundary.
- Response:
  keep the formal lane parallel and optional, restrict it to proof-mirror work over
  already-frozen finite laws, and reconcile it before crossing into the `V40-D`
  boundary it mirrors.

## Current Judgment

- `V40-C` is worth implementing now because the repo has released architecture meaning
  and deterministic readiness, but still lacks a typed, replayable, bounded way to
  resolve or escalate architecture ambiguity before lowering begins.
