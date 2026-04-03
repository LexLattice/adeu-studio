# ADEU Symbol Audit v0 Bundle Alignment

Authority layer: support / maintainer intake note only.

Source lane:

- imported external prototype bundle
- class: `X2`
- precedent status: `non_precedent`

## Artifact Relationship

- narrative ingress note:
  [CLAIMED_SCOPE.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/CLAIMED_SCOPE.md)
- unpacked source payload:
  [source_tree](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree)
- in-pack prototype readme:
  [source_tree/adeu_symbol_audit_v0/README.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/README.md)

## Claimed Scope

The combined narrative and bundle claim:

- a read-only parser-first closure engine for per-symbol auditing
- one deterministic symbol census artifact
- one semantic audit artifact over the frozen census
- one coverage/closure report artifact
- a bounded pilot scope over `packages/adeu_architecture_ir`

## Observed Reachable Surfaces

The unpacked source tree contains:

- package source under
  [source_tree/adeu_symbol_audit_v0/adeu_symbol_audit](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/adeu_symbol_audit)
- core package modules at
  [models.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/adeu_symbol_audit/models.py),
  [census.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/adeu_symbol_audit/census.py),
  [spu.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/adeu_symbol_audit/spu.py),
  [coverage.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/adeu_symbol_audit/coverage.py),
  and
  [cli.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/adeu_symbol_audit/cli.py)
- sample output artifacts at
  [sample_symbol_census.json](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/sample_symbol_census.json),
  [sample_symbol_semantic_audit.json](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/sample_symbol_semantic_audit.json),
  and
  [sample_symbol_audit_coverage_report.json](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree/adeu_symbol_audit_v0/sample_symbol_audit_coverage_report.json)

## Accepted Shipped Scope

Current accepted shipped scope is intentionally narrow:

- intake pack only
- unpacked source tree and sample artifacts only
- no accepted package addition
- no accepted audit gate
- no accepted CLI/build integration

## Maintainer Alignment Notes

- This bundle is also a strong fit for repo philosophy because it is read-only,
  parser-first, and closure-oriented.
- It is not internal ADEU work yet because it introduces a new artifact family and a
  new audit gate without repo-native planning, tests, or build integration.
- Compared with the earlier app-heavy prototypes, this one has low blast radius and is
  a plausible candidate for an early internalization path.

## Required Before Internal Integration

- choose the rightful family / package placement
- freeze the authoritative status of:
  - symbol census
  - semantic audit
  - coverage report
- define how it relates to, rather than silently overlaps with, `repo_symbol_catalog@1`
- re-author one bounded internal slice with repo-native tests and gate wiring
