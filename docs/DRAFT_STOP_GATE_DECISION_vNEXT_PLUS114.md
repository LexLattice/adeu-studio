# Draft Stop-Gate Decision vNext+114

Status: proposed gate for `V48-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS114.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `task_run_boundary_instance@1`, `worker_execution_attestation@1`, and
  `worker_execution_provenance@1` validate and export cleanly;
- accepted fixtures show one released `V48-B` compiled binding consumed by one explicit
  task/run boundary instance and one explicit attestation / provenance chain;
- every accepted starter input binds exactly one compiled binding ref, one repo ref,
  one declared task instance identity, and one worker subject kind / ref;
- every accepted starter output carries one explicit provider / model / adapter tuple;
- worker provider/model identity remains explicit `V48-C` envelope fact and is not
  inferred from attestation-provider identity;
- runner-result and runner-provenance support refs remain explicit and hash-coherent;
- any selected verifier-result or attestation-validator support refs remain explicit
  and bound to the same run lineage rather than ambiently discovered;
- attestation artifacts carry explicit hash anchors for the support chain they bind;
- `repo_ref` remains one exact execution repository identity coherent with
  `snapshot_id` / `snapshot_sha256`;
- provenance `emitted_artifact_refs` remain support-artifact outputs only rather than
  widening into observed-action carriers;
- released signature / trust-anchor inputs remain transitive support behind released
  verifier / attestation carriers rather than new `V48-C` authority objects;
- prompt / chat / `AGENTS.md` posture remains projection-only and prompt-boundary
  conflict fails closed;
- stale, dangling, unresolved, or cross-repo compiled boundary reuse fails closed;
- no accepted entrypoint bypasses the released compiled binding through raw `V48-A`,
  raw `V45`, raw `V47`, raw taskpack components, or raw `D-IR` starters;
- the shipped slice remains pre-conformance and single-worker only;
- Python tests cover:
  - boundary-instance replay,
  - worker-execution attestation derivation,
  - worker-execution provenance derivation,
  - support-artifact hash / lineage validation,
  - schema export parity.

## Do Not Accept If

- the starter lane accepts more than one compiled binding source;
- task instance identity, repo ref, worker subject, or provider / model / adapter
  identity can be inferred from prose or omitted;
- worker provider/model identity is conflated with attestation-provider identity;
- released runner-result / runner-provenance support carriers are smuggled in by local
  repo search rather than explicit refs;
- runner-result / runner-provenance hash drift is tolerated;
- attestation support refs are accepted without corresponding hash anchors;
- `repo_ref` is treated as a floating branch or ref label rather than exact execution
  repository identity;
- raw `V48-A` / `V45` / `V47` bypass is accepted as an implementation convenience;
- prompt / chat / `AGENTS.md` conflict is tolerated as extra authority;
- provenance `emitted_artifact_refs` widen into arbitrary mutation inventory or action
  traces;
- released signature / trust-anchor inputs are re-surfaced as new `V48-C` authority
  objects;
- task/run boundary instance or attestation surfaces are overread as replayable
  post-run conformance;
- multi-worker topology or observed-action carrier release appears in the first
  worker-envelope release;
- the slice emits execution, approval, waiver, or deferral authority as if a later
  worker-governance lane had already shipped.

## Local Gate

- run `make arc-start-check ARC=114`
