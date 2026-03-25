# Draft Stop-Gate Decision vNext+83

Status: proposed gate for `V41-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS83.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- `adeu_architecture_analysis_request@1` validates and exports cleanly from
  `packages/adeu_architecture_ir` with byte-identical authoritative and mirrored
  schemas;
- one bounded repo-root-relative scope is captured deterministically through:
  - subtree anchor,
  - explicit file additions,
  - exclusion rules,
  - allowed artifact kinds;
- the request accepts only:
  - `committed_tree`
  - `materialized_snapshot`
  snapshot modes and rejects ambient working-tree capture by default;
- the request binds immutable snapshot identity appropriate to the chosen mode:
  - `commit_sha` or `tree_sha` for `committed_tree`
  - `snapshot_manifest_ref` or `snapshot_manifest_hash` for
    `materialized_snapshot`;
- every captured source item binds repo-root-relative path, artifact kind, and
  per-item `sha256`;
- canonical `source_set` ordering is normalized repo-root-relative path order;
- the aggregate `source_set_hash` replays deterministically for the accepted fixture;
- exact maintainer-brief refs, accepted-doc refs, and authority-boundary policy
  pinning are required;
- each brief/doc ref resolves either to frozen `source_set` content or to a separately
  materialized and hashed artifact captured by the request;
- the request lane rejects settlement, drift, and impossibility claims as out of
  scope for `V41-A`;
- Python tests cover:
  - schema/model validation,
  - schema export parity,
  - deterministic request / `source_set` replay,
  - snapshot-mode rejection,
  - path normalization and duplicate-path rejection,
  - unsupported artifact-kind rejection,
  - missing brief-ref or policy-pinning rejection.

## Do Not Accept If

- the slice captures "whatever is in the working tree" without an explicit frozen
  snapshot mode;
- the slice names a snapshot mode but not an immutable snapshot identity;
- `source_set` provenance is only globally hashed and not per-item addressable;
- canonical source ordering is left implicit and hash replay depends on enumerator
  accident;
- repo scope is represented as vague prose instead of deterministic subtree/addition/
  exclusion structure;
- free-form maintainer prose is treated as sufficient without exact refs and content
  closure;
- request capture smuggles in settlement, entitlement, drift, or impossibility
  authority;
- observed extraction, intended compile, alignment, or runner code lands in the same
  slice;
- path escape or duplicate-path drift is normalized silently instead of failing
  closed.

## Local Gate

- run `make check`
