# Draft ADEU History Semantics V54 Implementation Mapping v0

Status: support-layer implementation mapping for `V54`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the imported
`adeu-history-semantics-bundle` prototype material to a repo-owned `V54` family so
implementation can stay grounded without importing heuristic reconstruction semantics as
live authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
- `examples/external_prototypes/adeu-history-semantics-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- one adjacent package home:
  - `packages/adeu_history_semantics`
- one bounded typed artifact-family posture rather than vague memory/runtime language:
  - history source artifact
  - text-shape signals
  - preclassification
  - ledger entry / ledger
  - slice
  - theme anchor
  - evidence ref
  - O/E/D/U lane reconstruction
  - O/E/D/U reconstruction packet
  - workspace question
  - workspace theme frame
  - workspace snapshot
- one deterministic compilation pipeline with bounded fixtures
- one package-first scope with no API/UI/runtime widening in starter posture

## Re-Author With Repo Alignment

- live owner:
  - `packages/adeu_history_semantics/src/adeu_history_semantics/`
- `V54-A` starter slice:
  - release source contract and starter schema/export posture first
  - choose explicitly:
    - raw bytes authoritative; or
    - normalized text authoritative; or
    - dual raw-plus-normalized surfaces with one named authority root
  - release only the authority root and deterministic derived preclassification
    surfaces needed to make that choice real
- `V54-B` later slice:
  - release ledger / slice / theme substrate
  - rebuild parser, grouping, and heuristic law under explicit regression corpus
  - require regressions for:
    - shorthand role parsing
    - consecutive same-speaker grouping
    - quote/paste overfiring
    - substring lane false positives
    - empty input fail-closed posture
- `V54-C` later slice:
  - release advisory O/E/D/U lane reconstruction and packet artifacts
  - explicitly mark these as advisory reconstruction artifacts, not authority roots
- `V54-D` later slice:
  - release workspace question / theme-frame / snapshot seam only
  - explicitly mark workspace synthesis as advisory, never the source authority root
- repo-native release posture:
  - add package-local schema exports
  - add root `spec/` mirrors
  - add export helper so the family participates in the repo’s released contract lane

## Authority Ladder Seed

- source artifact:
  - authority root
- ledger and preclassification:
  - deterministic derived overlay
- slices and theme anchors:
  - bounded interpretive overlay
- O/E/D/U packets:
  - advisory reconstruction artifacts
- workspace snapshot:
  - advisory synthesized substrate only

## Defer To Later Slice

- Wave 0 bootstrap corpus widening
- broad history ingestion beyond bounded starter source classes
- API/UI/runtime worker surfaces
- operational memory or retrieval claims
- cross-domain planner or digest integration beyond narrow released artifact exchange

## Do Not Import

- any implication that the imported overlay is already a repo continuation
- any claim that current tests justify real corpus ingestion by themselves
- absence of package-local schema exports as if it were already a released contract lane
- ambiguous source-authority semantics
- current heuristic parser/grouping behavior as if it were already adequate for live
  corpus use
