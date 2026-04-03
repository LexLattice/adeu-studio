# Draft Stop-Gate Decision vNext+116

Status: proposed gate for `V48-E`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS116.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `worker_delegation_topology@1` validates and exports cleanly;
- accepted fixtures show one bounded `supervisor_to_worker` topology over one
  explicit released parent `V48-D` report and one explicit released child `V48-D`
  report;
- every accepted starter input binds exactly one parent conformance report, one child
  conformance report, one parent role `supervisor`, one child role `worker`, one
  `delegation_edge_id`, one explicit `parent_task_instance_identity`, one explicit
  `delegated_task_identity`, and one explicit `child_task_instance_identity`;
- parent and child remain coherent on:
  - one exact repo ref;
  - one exact `snapshot_id` / `snapshot_sha256`;
  - one exact released compiled-binding identity;
- parent and child worker subjects must remain distinct rather than re-labelling one
  single worker as both roles;
- accepted topology consumes already released `V48-D` conformance surfaces rather than
  raw `V48-C`, raw `V48-B`, or raw `V48-A` inputs;
- accepted topology requires both parent and child reports to be `conformant`;
- same compiled-boundary equality remains the deliberate starter restriction for this
  slice rather than a general delegation algebra;
- handoff result remains typed and bounded rather than prose-only, with accepted
  starter fixtures frozen to `completed` while `rejected` and `incomplete_lineage`
  remain typed emitted states for reject / fail-closed posture only;
- supporting diagnostic families remain explicit and bounded;
- prompt / chat / `AGENTS.md` posture remains projection-only and conflict fails
  closed;
- the shipped slice remains single-edge, supervisor-to-worker only, and
  non-recursive;
- Python tests cover:
  - accepted topology replay;
  - raw-input bypass rejection;
  - role and lineage validation;
  - boundary-equality fail-closed behavior;
  - schema export parity.

## Do Not Accept If

- the starter lane accepts raw `V48-D`, raw `V48-C`, or raw `V48-B` bypass;
- a topology can omit the released child or parent conformance report and still
  validate;
- parent/child compiled-boundary identity drift is tolerated;
- parent/child repo or snapshot identity drift is tolerated;
- non-conformant or incomplete-evidence child lineage can still be judged accepted;
- parent and child can resolve to the same worker subject and still validate;
- parent/child role ambiguity or swapped role posture is tolerated;
- supporting diagnostics widen beyond the frozen starter family set;
- worker/worker claims appear in the first topology release;
- recursive topology, multi-edge topology, or repo-wide orchestration appears in the
  first topology release;
- execution / approval authority expansion appears in the first topology release.

## Local Gate

- run `make arc-start-check ARC=116`
