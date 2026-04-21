# Assessment vNext+182 Edges

Status: pre-lock edge assessment for `V66-A`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS182_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V66-A` Could Quietly Reopen `V47` Language And Compiler Ownership

- Risk:
  the new adoption family could start widening `D@1`, normalized `D-IR`,
  selector/predicate ownership, or policy-consumer doctrine instead of consuming
  the released `V47` stack.
- Response:
  keep `V47` authoritative.
  - released `V47-A` through `V47-F` remain the only consumed ANM substrate here
  - `V66-A` is source discovery / authority-profile / class-policy posture only

### Edge 2: Classification Could Collapse Multiple Axes Into One Flat Doc Type

- Risk:
  the starter slice could flatten `doc_class`, `authority_layer`,
  `source_posture`, `lifecycle_status`, and `classification_status` into one
  bucketed doc-type field, recreating the same flat authority model the family is
  meant to prevent.
- Response:
  keep the starter axes explicit and disjoint.
  - class and layer remain distinct
  - posture and lifecycle remain distinct
  - unknown classification remains explicit

### Edge 3: The Whole Repo Could Become Hard-Gated ANM Source By Accident

- Risk:
  repo crawling could be mistaken for repo-wide ANM governance, turning all
  historical or support markdown into starter ANM liabilities merely because the
  files exist.
- Response:
  keep the source-set boundary explicit and fail-closed.
  - `discovered_doc_inventory` remains broader than `governed_anm_source_set`
  - only explicitly entered docs become starter ANM-governed source

### Edge 4: Minimal Companion Registration Could Drift Into Silent Supersession

- Risk:
  even without the full migration-binding profile, minimal host / companion
  registration could be overread as if nearby `.adeu.md` presence already
  superseded the current markdown host.
- Response:
  keep supersession law explicit and deferred.
  - minimal registration only in `V66-A`
  - full migration binding later in `V66-B`
  - supersession without explicit transition law fails closed

### Edge 5: Generated Reader Views Or Semantic Diffs Could Land Early And Overpromote

- Risk:
  reader projection or semantic diff surfaces could sneak into the starter slice
  and start behaving like authority-bearing projections before the migration /
  projection lane is selected.
- Response:
  keep those surfaces deferred.
  - no generated reader projection in `V66-A`
  - no semantic diff report in `V66-A`
  - generated-reader authority remains explicitly absent here

### Edge 6: Starter Diagnostics Could Drift Into Stable Advisory Artifacts

- Risk:
  the need for repo-scale diagnostics could cause `V66-A` to mint a stable
  versioned compile-report artifact even though that lane is supposed to stay
  deferred until advisory hardening.
- Response:
  keep starter diagnostics ephemeral only.
  - CLI/test diagnostics are acceptable
  - stable `anm_compile_report@1` remains deferred to `V66-C`

### Edge 7: Support-Layer ANM Awareness Could Drift Into Lock Or Planning Promotion

- Risk:
  ANM-aware support docs or optional support companions could be overread as if
  they minted lock or planning authority merely because they became visible to the
  starter source set.
- Response:
  keep support posture explicit and bounded.
  - support remains support
  - support ANM awareness is not lock promotion by itself

## Current Judgment

- `V66-A` is the right next slice because the repo already closed the bounded ANM
  language/compiler stack in `V47`, while the repo still lacks a repo-native
  adoption layer for source discovery, doc authority profiles, and class policy.
- the starter should stay properly bounded:
  - one governed ANM source-set starter only
  - one explicit doc authority profile starter only
  - one explicit class-policy starter only
  - one minimal companion-registration posture only
  - no `V47` language widening
  - no `V66-B` reader / migration widening yet
  - no `V66-C` advisory hardening yet
- if `V66-A` lands cleanly, later work should move to `V66-B` migration / reader
  projection, not reopen the starter slice into a broad ANM rewrite doctrine.

