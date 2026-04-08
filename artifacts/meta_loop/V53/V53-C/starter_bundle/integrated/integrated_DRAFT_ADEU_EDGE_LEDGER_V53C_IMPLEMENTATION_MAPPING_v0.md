# Draft ADEU Edge Ledger V53C Implementation Mapping v0

Status: support-layer starter-slice mapping for `V53-C`.

Authority layer: support only.

This note does not authorize implementation by itself. It narrows the broader `V53`
family mapping into the cumulative revision/register slice so the `vNext+145` draft
bundle can stay explicit about what is instantiated here, what is deferred, and what
remains for later `V53` slices.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md`
- `docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS141.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS143.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS145.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md`

## Selected Starter Slice

`V53-C` selects one bounded repo-owned cumulative revision/register seam:

- live owner surface:
  - `packages/adeu_edge_ledger`
- live starter contract:
  - `adeu_edge_taxonomy_revision_register@1`
- governing released upstream inputs:
  - one released `adeu_edge_class_catalog@1`
  - one released `adeu_edge_probe_template_catalog@1`
  - one released `adeu_symbol_edge_applicability_frame@1`
  - one released `adeu_symbol_edge_adjudication_ledger@1`
- governing starter input channels:
  - one current released adjudication ledger
  - optional prior revision register for append-only accumulation

## Carry Forward As Support, Not Authority

The imported bundle contributes real revision-layer shape worth preserving, but not
live authority:

- one adjacent-package split instead of ambient widening inside `adeu_symbol_audit`
- one typed revision layer rather than prose-only review notes
- one real distinction between stable existing-class reuse and topology-changing split /
  merge pressure

The imported bundle does not carry live authority for:

- one-off revision judgments as sufficient cumulative history
- automatic taxonomy mutation from revision helper output
- unbounded new-class invention without explicit lineage and bounded vocabulary
- direct test-intent or broader probe integration

## Proto-Module Intake Posture

This slice follows the repo's package-first proto-module intake pattern:

- treat the external edge-ledger bundle as a bounded downstream proto-module claim,
  not as an already-authoritative continuation;
- preserve `ALIGNMENT.md` and `CLAIMED_SCOPE.md` as support-only intake evidence;
- mint repo-owned contract vocabulary, fail-closed law, and bounded deferments in repo
  docs and repo code rather than importing overlay semantics as-is.

## Re-Author Under Repo Control

`V53-C` should re-author the imported revision material in repo-native form as
follows:

- consume released `V53-B` adjudication ledgers exactly as authoritative upstream input
- emit one cumulative revision register that preserves prior entry order and appends
  new typed entries only:
  - same-lineage append is frozen as exact same bound released adjudication-ledger ref
    only
  - preserved and new entries must keep `supporting_adjudication_ledger_ref` equal to
    that same bound released adjudication-ledger ref
- freeze one exact starter decision vocabulary:
  - `stabilize_existing_class`
  - `split_existing_class`
  - `merge_existing_classes`
  - `deprecate_existing_class`
- freeze one exact starter decision-shape law:
  - `stabilize_existing_class` uses one existing subject ref only
  - `split_existing_class` uses one existing subject ref plus non-empty candidate refs
  - `merge_existing_classes` uses at least two existing subject refs plus one
    candidate ref
  - `deprecate_existing_class` uses one existing subject ref only
- freeze one exact append-only lineage-parent law:
  - parent refs resolve only to earlier admitted entries
  - forward refs, duplicates, and cycles fail closed
  - preserved prior history may not be rewritten
- freeze one exact adjudication-support law:
  - support binds to explicit released adjudication row refs from the one bound
    released adjudication ledger only
  - every starter revision entry must anchor on at least one `witness_found` or
    `checked_no_witness_found` row
  - `deferred` may appear only as supplementary context and cannot by itself mint
    `stabilize_existing_class`, `split_existing_class`, `merge_existing_classes`, or
    `deprecate_existing_class`
  - lexical adjacency, structural overlap, `applicable_unchecked`, `underdetermined`,
    and `not_applicable` are insufficient by themselves to mint revision entries
- freeze one exact candidate successor ref law:
  - admitted candidate refs use the same `edge_class:` ref family as released
    `V53-A` `edge_class_ref` values
  - candidate refs are non-empty, unique within an entry, and non-overlapping with
    that entry's `subject_edge_class_refs`
  - implementation must ship reject fixtures for duplicate, overlapping, or otherwise
    inadmissible candidate refs
- keep candidate successor refs explicit without mutating the released catalogs
- keep schema export parity between authoritative package exports and root `spec/`
  mirrors if schema files are committed

## Constrain But Not Mint

`V53-C` may constrain later `V53` lanes, but it may not mint them.

Allowed constrain actions here:

- freeze starter revision decision vocabulary
- freeze append-only lineage order, same-lineage append, and parent-ref law
- freeze exact adjudication-support law for register entries
- freeze exact candidate successor ref admissibility, uniqueness, and non-overlap law
- freeze the negative law against soft-evidence promotion into revision change
- freeze the live-taxonomy-boundary posture for split/merge/deprecate history

Not authorized here:

- direct joins to released `V45-D` test-intent artifacts
- probe/test-intent integration or execution helpers
- live taxonomy migration helpers or automatic catalog rewrites
- repo-wide scope widening
- second package owner surfaces

## Slice Seam Classification

### `instantiated_here`

- `adeu_edge_taxonomy_revision_register@1`
- deterministic starter fixtures for:
  - initial register materialization
  - append-only register extension
  - starter stabilize/split/merge/deprecate decisions
- deterministic reject fixtures for:
  - unknown lineage parent refs
  - lineage cycles
  - cross-ledger append or supporting-ledger drift
  - invalid decision-shape/lifecycle combinations
  - `deferred`-only revision support
  - unsupported adjudication support rows
  - duplicate, overlapping, or otherwise inadmissible candidate refs
- schema export parity between package and root `spec/` mirrors if schema files are
  released

### `deferred_to_later_family`

- `V53-D`:
  - direct test-intent integration with released `V45-D`
  - broader probe/test-intent integration posture

### `not_selected_yet`

- live taxonomy migration helpers or automatic catalog rewrites
- repo-wide widening beyond the released `V53-A` pilot scope and released `V53-B`
  consumption posture
- broader reviewer UX or mutation/enforcement surfaces
- benchmark-like or proof-grade evidence consumers
- second package owner surfaces

## Starter Validation Mapping

For the starter-doc phase, the truthful docs-only gate is:

- `make arc-start-check ARC=145`

For later implementation work, this slice still requires repo-native verification over
the live package path rather than extracted-bundle assumptions, and it must preserve
the released `V53-A` / released `V53-B` authority boundary instead of relitigating
taxonomy, adjudication, or test-intent law.
