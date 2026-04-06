# Draft Parallel Arc Branching Policy v0

Status: working policy draft only.

Authority layer: support only.

This note specializes the branch topology for the parallel-family pilot described in
`docs/DRAFT_PARALLEL_ARC_META_LOOP_PROTOCOL_v0.md`.

## Purpose

- keep `main` as governance trunk only;
- give each family a stable implementation trunk;
- make final `main` integration explicit and conflict-aware.

## Branch Classes

### `main`

Reserved for:

- meta-orchestrator-controlled governance changes
- family-level planning selection
- final family-to-`main` integration
- post-merge reconciliations if needed

Forbidden on `main` during the pilot:

- direct slice implementation commits
- slice review-fix commits
- feature experimentation for one family only

### Family Arc Branches

Canonical names:

- `arc/v53`
- `arc/v54`

Purpose:

- family-local control plane and implementation trunk
- starter bundle commits for that family
- merged slice PRs for that family
- family-local closeout commits

For repeated pilot runs:

- preserve prior family trunks with explicit run suffixes such as:
  - `arc/v53-r2`
  - `arc/v54-r2`
- create fresh family trunks for the new run with explicit run suffixes such as:
  - `arc/v53-r3`
  - `arc/v54-r3`

This keeps comparative run evidence inspectable instead of overwriting one family trunk
in place.

### Slice Branches

Canonical pattern:

- `slice/<family-lower>/<path-lower>-vnext-plus<arc-number>`

Examples:

- `slice/v53/v53-a-vnext-plus141`
- `slice/v54/v54-a-vnext-plus142`

Purpose:

- one bounded slice implementation or slice review-fix lane only

For repeated pilot runs, the slice branch may also carry the run marker if needed for
clarity.

## PR Base Rules

- slice PRs target the family arc branch
- family arc branches do not target each other
- family-to-`main` integration happens only through explicit maintainer-side merge work

## Sync Rules

- only the meta-orchestrator syncs `main` into family arc branches
- sync happens intentionally, not continuously
- sync should happen:
  - before starting a new family if the family branch is stale enough to matter
  - before final family-to-`main` integration
- workers should not rebase or merge `main` into family branches on their own

Sync method for the pilot:

- use explicit non-interactive merge or rebase chosen by the meta-orchestrator
- record the chosen method and resulting sha in the orchestrator log
- treat sync as a governance event, not as invisible branch housekeeping

## Closeout Rules

- slice closeout happens on the family arc branch
- family-completion closeout for `main` happens only after family-to-`main` merge is
  approved and conflict-reviewed

## Conflict Posture

This pilot intentionally delays family-to-`main` merge so maintainers can observe:

- doc drift
- schema collisions
- package-surface overlap
- generated artifact conflicts

The delay is a feature, not a workflow bug.

Preflight collision rule:

- if two families are about to touch the same authoritative package surface, schema
  family, or generated artifact namespace, the meta-orchestrator must declare one of:
  - proceed_in_parallel
  - serialize_temporarily
  - re-scope_one_family
before both lanes continue
