# ADEU History Semantics Bundle Alignment

Authority layer: support / maintainer intake note only.

Source lane:

- imported external prototype bundle
- class: `X2`
- precedent status: `non_precedent`

## Artifact Relationship

- narrative ingress note:
  [CLAIMED_SCOPE.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-history-semantics-bundle/CLAIMED_SCOPE.md)
- unpacked source payload:
  [source_overlay](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-history-semantics-bundle/source_overlay)

This pack is an overlay-oriented import. Its payload preserves repo-relative code
surfaces exactly as claimed by the external bundle rather than being installed into the
live repo package paths.

## Claimed Scope

The imported narrative claims:

- one new bounded package-first semantic module:
  `packages/adeu_history_semantics`
- one deterministic source -> ledger -> slice -> theme -> O/E/D/U packet -> workspace
  pipeline
- one small bootstrap integration change in `Makefile`
- bounded synthetic fixtures and package tests only
- no API/UI/runtime widening

## Observed Reachable Surfaces

The unpacked overlay actually contains:

- bundle manifest at
  [source_overlay/MANIFEST.txt](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-history-semantics-bundle/source_overlay/MANIFEST.txt)
- bootstrap wiring candidate at
  [source_overlay/Makefile](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-history-semantics-bundle/source_overlay/Makefile)
- support doc at
  [source_overlay/docs/DRAFT_ADEU_HISTORY_SEMANTICS_IMPLEMENTATION_MAPPING_v0.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-history-semantics-bundle/source_overlay/docs/DRAFT_ADEU_HISTORY_SEMANTICS_IMPLEMENTATION_MAPPING_v0.md)
- package metadata at
  [source_overlay/packages/adeu_history_semantics/pyproject.toml](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-history-semantics-bundle/source_overlay/packages/adeu_history_semantics/pyproject.toml)
- package source under
  [source_overlay/packages/adeu_history_semantics/src/adeu_history_semantics](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-history-semantics-bundle/source_overlay/packages/adeu_history_semantics/src/adeu_history_semantics)
- tests and fixtures under
  [source_overlay/packages/adeu_history_semantics/tests](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-history-semantics-bundle/source_overlay/packages/adeu_history_semantics/tests)

The imported payload does not contain:

- package-local authoritative schema exports
- root `spec/` schema mirrors
- an `export_schema.py` helper
- any lock/planning selection that would authorize live integration by itself

## Accepted Shipped Scope

Current accepted shipped scope is intentionally narrow:

- intake pack only
- unpacked overlay only
- no live package addition
- no accepted history-semantics family selection
- no accepted schema contract release
- no accepted API/UI/runtime surface

## Maintainer Alignment Notes

- The selected home is plausible. This bundle reads as a package-first semantic artifact
  family adjacent to `adeu_semantic_forms`, `adeu_paper_semantics`, and other typed
  semantic lanes rather than as an app/runtime surface.
- GPT’s review is directionally right:
  - architecture and artifact-family choice are materially stronger than the heuristic
    parser/reconstruction layer
  - the current preclassification and lane-scoring heuristics are brittle enough to
    distort real corpora
  - the delivered tests mostly prove determinism and internal replay, not heuristic
    adequacy
- these docs are therefore intake docs, not implementation-arc docs:
  - they are strong enough to seed a later repo-owned family
  - they are intentionally not yet an internalization decision by themselves

## Maintainer Internalization Seed

The future repo-owned family should likely be framed as one bounded internalization /
reconstitution arc rather than a direct import.

Adopt nearly as-is:

- package-first home under `packages/adeu_history_semantics`
- bounded typed artifact-family posture
- explicit O/E/D/U packet posture
- workspace snapshot concept
- no API/UI/runtime widening in starter scope

Rework before release:

- source-authority semantics
- schema/export posture
- parser and grouping heuristics
- lane scoring and provenance strictness
- fixture and regression coverage

Reject as-is:

- any implication that the imported overlay is already a repo continuation
- any implication that the current tests justify real corpus ingestion
- any soft phrasing that hides the absence of released schema/export surfaces

## Authority Ladder Seed

If this family is later selected internally, the starter authority posture should likely
be:

- source artifact:
  authority root
- ledger and preclassification:
  deterministic derived overlay
- slices and theme anchors:
  bounded interpretive overlay
- O/E/D/U packets:
  advisory reconstruction artifacts
- workspace snapshot:
  advisory synthesized substrate, never the authority root

## Additional Maintainer Edge Cases

- The delivered bundle name and the narrative link do not match:
  - the note points to `adeu_history_semantics_diff.zip`
  - the delivered drop is `adeu_history_semantics_bundle.zip`
- The “raw source authoritative” posture is not byte-faithful:
  - `build_history_source_artifact(...)` normalizes `CRLF` / `CR` to `LF` before
    storing and hashing `source_text`
  - this means the preserved authoritative source text is already a normalized variant,
    not the literal raw input bytes
- The package claims typed artifact-family discipline but does not deliver schema export
  surfaces:
  - there are no package-local schema json files
  - there are no root `spec/` mirrors
  - there is no export helper to bind model contracts into the repo’s usual release
    posture
- The shorthand role parser is brittle:
  - `U:` / `A:` style logs can be misparsed into one unknown block rather than clean
    alternating turns
- Consecutive same-speaker grouping is brittle:
  - multiple user turns can be over-collapsed or over-split instead of preserving one
    bounded authored sequence
- Quote/paste heuristics can overfire:
  - quoted native user text can be reclassified as `external_paste_like`
- Substring lane scoring can produce false positives:
  - lexical substrings such as `mustard` and `shouldered` can spuriously trigger
    deontic-style cues
- Empty input currently compiles too far:
  - the bundle can produce a zero-entry semantic bundle instead of fail-closing on
    unusable source input
- The shipped tests are self-consistent and pass in an extracted environment, but they
  do not exercise:
  - schema/export discipline
  - raw-source preservation boundaries
  - broader repo gate compatibility

## Required Before Internal Integration

- choose a concrete internal planning family and lock rather than importing the package
  directly as ambient semantic-family continuation
- implement explicit schema export / mirror posture if this is meant to join the repo’s
  released typed-artifact pattern
- decide whether source authority means:
  - raw bytes authoritative, or
  - normalized text authoritative,
  and bind that choice explicitly in the models and docs
- freeze the later family’s authority ladder explicitly:
  - source authority root
  - deterministic derived overlays
  - advisory reconstruction layers
- tighten the heuristic/parser layer along the defects GPT already identified:
  - shorthand role parsing
  - consecutive user-message grouping
  - quote/paste overfiring
  - substring lane scoring
  - empty input acceptance
- add regression tests for both GPT-identified and maintainer-identified edge cases
