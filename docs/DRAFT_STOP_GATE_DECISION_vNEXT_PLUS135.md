# Draft Stop-Gate Decision vNext+135

Status: proposed gate for `V44-E`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS135.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `packages/adeu_reasoning_assessment` surface remains the only active
  `V44-E` package;
- one released `adeu_recursive_reasoning_assessment@1` exports and mirrors
  deterministically;
- released `V44-A`, `V44-B`, and `V44-D` contracts are consumed as-is, with no
  semantic redefinition;
- released `V44-C` remains informative context only and is not promoted into a
  required upstream contract for the starter slice;
- recursive assessment remains bounded to exactly one recursive re-entry depth beyond
  the released non-recursive baseline;
- recursive status and closure judgment remain explicit and deterministic across:
  - lawful recursive closure;
  - degraded but lawful recursive closure;
  - insufficient recursive comparison;
  - invalid recursive early closure;
- invalid or under-evidenced baseline posture may normalize only to
  `recursive_extension_insufficient`;
- recursive evidence refs remain trace-qualified and deterministic across:
  - `baseline`
  - `recursive_extension`;
- explicit return-to-parent evidence is required for lawful recursive closure;
- at least one positive recursive reference pair is anchored to a hierarchical
  released suite member;
- reject fixtures fail closed for:
  - missing recursive return-to-parent evidence;
  - non-local recursive rewrite posture;
- no profile, benchmark, or SRM-governor execution surfaces appear in the `V44-E`
  package surface;
- targeted tests cover deterministic assessment ids, status/judgment coupling,
  recursive mapping replay, and reject posture.

## Do Not Accept If

- recursive continuation silently compares unrelated probe lineages;
- recursive extension widens into unbounded self-extension or nested recursive
  grandchildren;
- invalid recursive early closure is normalized into a lawful closure posture;
- non-local recursive rewrite is treated as lawful recursive repair;
- model-profile, ranking, benchmark, or SRM execution doctrine appears in the released
  contract;
- root `spec/` mirrors are claimed in docs but missing from the released package lane.

## Local Gate

- run `make arc-start-check ARC=135`
