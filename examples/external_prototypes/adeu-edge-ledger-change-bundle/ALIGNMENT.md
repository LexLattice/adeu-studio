# ADEU Edge Ledger Change Bundle Alignment

Authority layer: support / maintainer intake note only.

Source lane:

- imported external prototype bundle
- class: `X2`
- precedent status: `non_precedent`

## Artifact Relationship

- narrative ingress note:
  [CLAIMED_SCOPE.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md)
- unpacked source payload:
  [source_overlay](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay)

This pack is an overlay-oriented import. Its payload preserves repo-relative code
surfaces exactly as claimed by the external bundle rather than being installed into the
live repo package paths.

## Claimed Scope

The imported narrative claims:

- one new bounded adjacent package:
  `packages/adeu_edge_ledger`
- one bounded downstream consumer of released `V45` + `V50` artifacts rather than a
  reopening of `adeu_symbol_audit`
- five typed artifact families with package-local schemas plus root `spec/` mirrors
- one real 3-level starter taxonomy plus applicability/adjudication/revision flows
- targeted package tests and deterministic fixtures over the released `V50`
  architecture-ir pilot scope

## Observed Reachable Surfaces

The unpacked overlay actually contains:

- bootstrap wiring candidate at
  [source_overlay/Makefile](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay/Makefile)
- support docs at
  [source_overlay/docs/DRAFT_ADEU_EDGE_LEDGER_PROTO_v0.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay/docs/DRAFT_ADEU_EDGE_LEDGER_PROTO_v0.md)
  and
  [source_overlay/docs/DRAFT_ADEU_EDGE_LEDGER_IMPLEMENTATION_MAPPING_v0.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay/docs/DRAFT_ADEU_EDGE_LEDGER_IMPLEMENTATION_MAPPING_v0.md)
- package metadata at
  [source_overlay/packages/adeu_edge_ledger/pyproject.toml](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay/packages/adeu_edge_ledger/pyproject.toml)
- package source under
  [source_overlay/packages/adeu_edge_ledger/src/adeu_edge_ledger](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay/packages/adeu_edge_ledger/src/adeu_edge_ledger)
- package-local schemas under
  [source_overlay/packages/adeu_edge_ledger/schema](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay/packages/adeu_edge_ledger/schema)
- mirrored root schema candidates under
  [source_overlay/spec](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay/spec)
- tests and fixtures under
  [source_overlay/packages/adeu_edge_ledger/tests](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-edge-ledger-change-bundle/source_overlay/packages/adeu_edge_ledger/tests)

## Accepted Shipped Scope

Current accepted shipped scope is intentionally narrow:

- intake pack only
- unpacked overlay only
- no live package addition
- no accepted schema contract
- no accepted edge-ledger family selection
- no accepted `V45` / `V50` continuation by implication

## Maintainer Alignment Notes

- The selected home is plausible. This package reads as a downstream consumer of
  released `V45` repo-description discipline and released `V50` symbol-audit artifacts
  rather than as a silent reopening of either family.
- GPT’s review is directionally right:
  - constant taxonomy layer is materially stronger than the variable applicability /
    adjudication layer
  - `covered_by_existing_tests` and `bounded_safe_by_structure` currently sound stronger
    than the evidence they actually carry
  - the revision surface is real, but not yet a cumulative history/register layer

## Additional Maintainer Edge Cases

- The delivered test suite is not self-contained as a diff bundle:
  - `tests/conftest.py` resolves `repo_root` from the extracted temp path and then
    expects live `packages/adeu_architecture_ir/...` files that are not included in the
    zip
  - running the extracted bundle tests directly therefore fails before the claimed
    `27 passed` posture can be reproduced
- The schema-export tests are also path-coupled:
  - `test_edge_ledger_export_schema.py` calls `adeu_ir.repo.repo_root(anchor=Path(__file__))`
    from the extracted temp path, so the exported-schema checks fail outside a live
    repo-native install location
- Explicit overrides can bypass applicability posture entirely:
  - `derive_symbol_edge_adjudication_ledger(...)` evaluates `witness_summaries` and
    `checked_no_witness_edge_class_refs` before it respects source applicability
  - this means a caller can currently force `witness_found` or
    `checked_no_witness_found` even when the bound applicability row is
    `not_applicable`
- Explicit override evidence can silently conflict:
  - `derive_symbol_edge_adjudication_ledger(...)` allows the same edge class to appear
    in both `witness_summaries` and `checked_no_witness_edge_class_refs`
  - the current implementation silently gives `witness_found` precedence instead of
    failing closed on contradictory override input
- Unknown override refs are silently ignored:
  - the bundle does not validate that every explicit override ref is present in the
    bound applicability frame for the symbol
  - a caller can therefore submit unused override evidence without any fail-closed
    signal
- The package duplicates released symbol-id law locally:
  - `compute_symbol_id(...)` is redefined inside the package rather than imported from
    the released `V45` / `V50` authority surface
- The symbol-id duplication is a broader authority-drift cluster:
  - the applicability collector also constructs symbol ids inline rather than
    consuming one released identity authority surface
- The evidentiary statuses still overstate what is known:
  - `covered_by_existing_tests` is still fundamentally lexical test-token adjacency
  - `bounded_safe_by_structure` is still cue overlap plus non-low-confidence audit
    posture
  - this is not only a naming issue; it is a status/evidence mismatch that needs an
    explicit repo-native resolution

## Required Before Internal Integration

- select a concrete internal planning family and lock rather than importing the package
  as ambient `V50` continuation
- re-author the verification lane so tests run from a normalized intake/live repo path
  rather than assuming the zip has been copied into the repo tree
- tighten applicability discrimination so the taxonomy is exercised beyond one dominant
  archetype
- require explicit-adjudication fail-closed rules:
  - contradictory overrides rejected
  - out-of-frame overrides rejected
  - applicability-violating overrides rejected
- either weaken or strengthen the evidentiary meaning of:
  - `covered_by_existing_tests`
  - `bounded_safe_by_structure`
- import one canonical released symbol-id helper instead of duplicating it locally
- decide whether the starter internal family should:
  - release taxonomy + applicability first, with adjudication deferred; or
  - release adjudication in the first slice only if the override and evidence laws are
    made constitutional enough first
