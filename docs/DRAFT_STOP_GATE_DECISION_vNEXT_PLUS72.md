# Draft Stop-Gate Decision vNext+72

Status: proposed gate for `V39-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS72.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new ADEU core schemas validate and export cleanly;
- one imported reference contribution can be materialized into a valid
  `external_contribution_alignment_packet@1`;
- the same input packet deterministically produces the same
  `module_conformance_report@1` on repeated runs;
- canonical evidence records:
  - exact policy source paths,
  - exact policy content hashes,
  - evaluator or tool version;
- the report clearly separates:
  - code alignment,
  - meta-sequence alignment,
  - claimed scope,
  - observed reachable surfaces,
  - accepted shipped scope,
  - required follow-ups,
  - precedent status;
- the report defaults to `non_precedent` unless a maintainer explicitly grants
  precedent-bearing status with a reason;
- the accepted shipped scope for the reference contribution matches actual repo
  surfaces instead of PR-title rhetoric;
- the canonical subject is a committed local subject bundle rather than a live
  GitHub PR object;
- missing required alignment inputs fail closed rather than becoming hand-waved
  pass results;
- Python tests cover:
  - schema/model validation,
  - deterministic report derivation,
  - scope-truthfulness checks,
  - fail-closed handling of missing alignment inputs.

## Do Not Accept If

- the slice rewrites imported history as if the contribution was born inside the
  native ADEU arc sequence;
- code-quality judgment and process-alignment judgment collapse into a single
  opaque pass/fail label;
- live GitHub or network state is required for canonical report derivation;
- policy provenance remains unpinned, leaving deterministic replay dependent on
  a moving policy frame;
- `observed_reachable_surfaces` is collapsed into `accepted_shipped_scope`,
  hiding where maintainer judgment corrected the original claim;
- silence about precedent is treated as approval rather than as
  `non_precedent`;
- the reference contribution is described as shipped user-facing behavior when
  no reachable surface actually exists;
- the conformance layer claims to auto-resolve architectural semantics or merge
  worthiness without explicit maintainer judgment;
- the first slice widens into a broad all-module marketplace or generic scoring
  engine.

## Local Gate

- run `make check`
