# Assessment vNext+121 Edges

Status: planning-edge assessment for `V50-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS121_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Silent Fork Of `repo_symbol_catalog@1`

- Risk:
  the family could claim simple overlap with released `repo_symbol_catalog@1` while
  actually redefining symbol identity or shared symbol-kind meaning.
- Response:
  keep the overlap law explicit, reuse the released textual symbol-id law for shared
  kinds, and freeze lawful divergence to narrower pilot scope, stricter closure
  ordering, and one explicit `local_function` extension only.

### Edge 2: Hidden `local_function` Laundering

- Risk:
  `local_function` could be introduced as if it were already part of the released
  descriptive baseline rather than one family-local extension.
- Response:
  make `local_function` explicit, non-superseding, and identity-law-compatible where
  declared.

### Edge 3: Pilot-Scope Drift

- Risk:
  the first slice could overreach into a looser “architecture_ir pilot” concept rather
  than one exact committed byte set.
- Response:
  freeze the first release to exactly three committed files, bind them in the scope
  manifest with explicit `sha256` values, and require deterministic replay over those
  bytes only.

### Edge 4: Coverage Drift Into Semantic Audit

- Risk:
  the first `coverage.py` implementation could quietly inherit the prototype’s
  audit-coupled coverage semantics and thereby smuggle `V50-B` concerns into `V50-A`.
- Response:
  freeze `V50-A` coverage as manifest-to-census closure only and defer semantic-audit
  coverage semantics entirely.

### Edge 5: Missing-Manifest Drift

- Risk:
  the coverage report could type unexpected-source drift but leave the inverse case
  implicit, letting manifest files disappear from the census without one explicit
  carrier.
- Response:
  freeze one typed `missing_source_files` carrier and fail closed when any manifest file
  is absent from the observed census source set.

### Edge 6: Identity Drift For Shared Kinds

- Risk:
  the first census release could choose a new symbol-id law and make later comparison
  with released `repo_symbol_catalog@1` fuzzy.
- Response:
  explicitly reuse the released textual `symbol:{module_path}:{qualname}:{symbol_kind}`
  law for shared kinds and permit no further delta in this slice; `local_function` may
  reuse that textual shape only as one family-local extension and not as a parity claim
  against the released `SymbolKind` universe.

### Edge 7: Non-Deterministic Census Ordering

- Risk:
  AST traversal or incidental iteration order could make repeated census emission
  unstable even over the same exact bytes.
- Response:
  require deterministic ordering, deterministic indices, and committed fixture replay.

### Edge 8: Semantic-Primitive Prematurity

- Risk:
  the first B-track slice could accidentally decide whether later semantic-audit
  vocabulary reuses `V49` primitives or remains independent.
- Response:
  keep `V50-A` artifacts semantically minimal enough that either later choice remains
  open and defer that decision explicitly to `V50-B`.

### Edge 9: Consumer Prematurity

- Risk:
  semantic audit, CLI, API, or web consumers could leak into the first read-only slice
  and blur family ownership.
- Response:
  keep `V50-A` bounded to package scaffold, manifest/census/coverage contracts,
  fixtures, and targeted tests only.

## Current Judgment

- `V50-A` is worth implementing now because it closes a real gap between the released
  descriptive symbol universe and a read-only closure-oriented audit family.
- the bounded starter shape is right: one repo-owned package, one exact three-file
  pilot scope, one deterministic census, one manifest-to-census coverage report, one
  explicit `local_function` family-local extension, and no semantic-audit ledger or
  consumer widening yet.
