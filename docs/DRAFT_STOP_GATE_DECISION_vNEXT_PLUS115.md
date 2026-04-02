# Draft Stop-Gate Decision vNext+115

Status: proposed gate for `V48-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS115.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `worker_boundary_conformance_report@1` validates and exports cleanly;
- accepted fixtures show one bounded conformant replay and one bounded
  non-conformant replay over one explicit released `V48-C` worker-envelope chain;
- every accepted starter input binds exactly one released boundary instance, one
  released worker execution attestation, one released worker execution provenance,
  and one explicit observed-action carrier set;
- the observed-action carrier set remains frozen to:
  - one filesystem mutation set;
  - one command invocation log;
  - one emitted artifact set;
  - one exact execution-repository identity / branch-ref carrier;
- each observed-action carrier kind has one explicit source-of-truth / acquisition
  rule rather than ambient reconstruction posture;
- support/provenance artifacts remain lineage support only and may not substitute for
  the filesystem mutation set, command invocation log, emitted artifact set, or exact
  execution-repository identity carrier;
- repo ref, task-instance identity, worker subject, and provider/model/adapter
  identity remain coherent across the consumed lineage and the observed-action set;
- mutation checks fail closed on off-boundary changes rather than treating them as
  advisory-only;
- command checks fail closed on unallowlisted invocation, forbidden-effect drift, or
  missing command lineage;
- emitted artifact set checks fail closed on contradiction with the bound compiled
  boundary or with support-only provenance posture;
- overall judgment precedence remains frozen exactly:
  - missing required carrier or unresolved lineage => `incomplete_evidence`;
  - any definite drift or contradiction => `non_conformant`;
  - only fully checked, fully coherent evidence => `conformant`;
- starter `check_family` and per-check `judgment` vocabularies remain explicit and
  bounded;
- prompt / chat / `AGENTS.md` posture remains projection-only and prompt-boundary
  conflict fails closed;
- overall judgment remains derived from frozen check results rather than prose
  assertion;
- the shipped slice remains single-worker only and pre-topological;
- Python tests cover:
  - conformant replay;
  - non-conformant replay;
  - mutation and command validation;
  - lineage fail-closed behavior;
  - schema export parity.

## Do Not Accept If

- the starter lane accepts raw `V48-B` or raw `V48-A` bypass;
- a conformance report can omit the released `V48-C` lineage and still validate;
- any observed-action carrier can be inferred from ambient repo search or omitted;
- any observed-action carrier can be reconstructed from provenance/support artifacts
  alone;
- repo/task/worker identity drift is tolerated across the consumed lineage;
- off-boundary mutation can still be judged `conformant`;
- unallowlisted command use can still be judged `conformant`;
- emitted-artifact contradiction is tolerated as advisory-only;
- the exact execution-repository / branch-ref carrier is underdefined or
  contradictory;
- prompt / chat / `AGENTS.md` conflict is tolerated as extra authority;
- multi-worker topology or execution / approval authority expansion appears in the
  first conformance release.

## Local Gate

- run `make arc-start-check ARC=115`
