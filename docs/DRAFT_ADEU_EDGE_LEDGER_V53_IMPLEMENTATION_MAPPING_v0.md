# Draft ADEU Edge Ledger V53 Implementation Mapping v0

Status: support-layer implementation mapping for `V53`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the imported
`adeu-edge-ledger-change-bundle` prototype material to a repo-owned `V53` family so
implementation can stay grounded without importing prototype adjudication semantics as
live authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- one adjacent package home:
  - `packages/adeu_edge_ledger`
- one typed artifact-family split rather than prompt-soft reviewer logic:
  - edge class catalog
  - probe template catalog
  - symbol applicability frame
  - symbol adjudication ledger
  - taxonomy revision judgment
- one real 3-level starter taxonomy with families, subfamilies, and archetypes
- one downstream-consumer posture over the released `V45` + `V50` stack rather than a
  silent reopening of `adeu_symbol_audit`
- package-local schema and root `spec/` mirror posture as a likely release target

## Re-Author With Repo Alignment

- live owner:
  - `packages/adeu_edge_ledger/src/adeu_edge_ledger/`
- released symbol identity:
  - import one canonical released symbol-id helper from the `V45` / `V50` stack
  - remove local identity-law duplication and inline symbol-id authority drift
- `V53-A` starter slice:
  - release taxonomy and applicability only
  - release:
    - `adeu_edge_class_catalog@1`
    - `adeu_edge_probe_template_catalog@1`
    - `adeu_symbol_edge_applicability_frame@1`
  - bind to one bounded released `V50` pilot scope only
  - no explicit override channel yet
  - no strong adjudication status promotion yet
- `V53-B` later slice:
  - release:
    - `adeu_symbol_edge_adjudication_ledger@1`
  - explicit fail-closed override law:
    - contradictory overrides rejected
    - out-of-frame overrides rejected
    - applicability-violating overrides rejected
  - explicit evidence/status law:
    - lexical test adjacency is not proof by default
    - structural cue overlap is not proof by default
    - explicit witness / checked-no-witness evidence must be typed and auditable
- `V53-C` later slice:
  - evolve isolated revision judgment into a cumulative revision lineage/register
  - explicit split / merge / stabilize / deprecate history rather than one-off verdicts
- repo-native verification:
  - tests must pass from a live repo-native path, not only from an extracted bundle path
  - exported schema tests must resolve against the real repo root
  - bundle portability and repo verification should be separated explicitly in docs

## Defer To Later Slice

- broad probe execution framework
- repo-wide scope widening beyond the released `V50` architecture-ir pilot
- integration with released `V45-D` test-intent surfaces
- mutation, enforcement, or CI-governance semantics
- broader reviewer platform UX

## Do Not Import

- current contradictory override precedence behavior
- silent dropping of unknown override refs
- local duplication of released symbol-id authority
- current `covered_by_existing_tests` semantics as if they were already proof-grade
- current `bounded_safe_by_structure` semantics as if they were already proof-grade
- extracted-bundle path assumptions in the live repo test posture
