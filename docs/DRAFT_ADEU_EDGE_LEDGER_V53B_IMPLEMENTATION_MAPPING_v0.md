# Draft ADEU Edge Ledger V53B Implementation Mapping v0

Status: support-layer starter-slice mapping for `V53-B`.

Authority layer: support only.

This note does not authorize implementation by itself. It narrows the broader `V53`
family mapping into the adjudication-hardening slice so the `vNext+143` draft bundle
can stay explicit about what is instantiated here, what is deferred, and what remains
for later `V53` slices.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md`
- `docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS141.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS143.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md`

## Selected Starter Slice

`V53-B` selects one bounded repo-owned adjudication seam:

- live owner surface:
  - `packages/adeu_edge_ledger`
- live starter contract:
  - `adeu_symbol_edge_adjudication_ledger@1`
- governing released upstream inputs:
  - one released `adeu_edge_class_catalog@1`
  - one released `adeu_edge_probe_template_catalog@1`
  - one released `adeu_symbol_edge_applicability_frame@1`
- governing explicit input channels:
  - `witness_summaries`
  - `checked_no_witness_edge_class_refs`

## Carry Forward As Support, Not Authority

The imported bundle contributes real adjudication shape worth preserving, but not live
authority:

- one explicit adjudication ledger rather than soft helper-only inference
- one explicit distinction between carried-forward applicability and stronger
  witness-oriented statuses
- one real fail-closed blocker cluster around explicit overrides

The imported bundle does not carry live authority for:

- silent precedence between contradictory overrides
- silent dropping of unknown override refs
- positive adjudication from lexical test adjacency alone
- positive adjudication from structural cue overlap alone

## Re-Author Under Repo Control

`V53-B` should re-author the imported adjudication material in repo-native form as
follows:

- consume released `V53-A` applicability rows exactly as authoritative upstream input
- emit one full-catalog adjudication row set in released catalog order
- freeze one exact starter mapping law:
  - `not_applicable` stays `not_applicable`
  - `applicable` with no explicit evidence becomes `applicable_unchecked`
  - `applicable` with typed witness evidence becomes `witness_found`
  - `applicable` with typed checked-no-witness evidence becomes
    `checked_no_witness_found`
  - `underdetermined` with no explicit evidence stays `underdetermined`
  - `underdetermined` with explicit evidence becomes `deferred`
- freeze one exact fail-closed override law:
  - contradictory overrides rejected
  - out-of-frame overrides rejected
  - overrides against `not_applicable` rows rejected
- freeze one exact support-field law per emitted adjudication status
- freeze one exact starter support-ref identity/order law:
  - `witness_summaries` is an ordered explicit witness-record channel with stable
    `witness_ref` values carried through into `supporting_witness_refs`
  - `checked_no_witness_edge_class_refs` is an ordered explicit edge-class channel
    carried through unchanged into `supporting_checked_no_witness_refs`
  - duplicates fail closed rather than being normalized away
- explicitly fence out soft-evidence statuses in the starter slice:
  - no `covered_by_existing_tests`
  - no `bounded_safe_by_structure`
- keep schema export parity between authoritative package exports and root `spec/`
  mirrors if schema files are committed

## Constrain But Not Mint

`V53-B` may constrain later `V53` lanes, but it may not mint them.

Allowed constrain actions here:

- freeze starter adjudication status vocabulary
- freeze exact explicit override channel behavior
- freeze exact status/support-field coupling
- freeze exact support-ref identity and input-order preservation
- freeze exact negative law for test-token adjacency and structural cue overlap
- freeze exact full-row coverage posture over released `V53-A`

Not authorized here:

- cumulative revision/register semantics
- split / merge / stabilize / deprecate history as live ledger semantics
- direct joins to released `V45-D` test-intent artifacts
- repo-wide scope widening
- second package owner surfaces
- promotion of soft evidence into positive adjudication outputs

## Slice Seam Classification

### `instantiated_here`

- `adeu_symbol_edge_adjudication_ledger@1`
- deterministic starter fixtures for each admitted adjudication status
- deterministic reject fixtures for the fail-closed override cluster
- schema export parity between package and root `spec/` mirrors if schema files are
  released

### `deferred_to_later_family`

- `V53-C`:
  - cumulative revision lineage/register surface
  - split / merge / deprecate / stabilize history as live contract semantics
- `V53-D`:
  - direct test-intent integration with released `V45-D`
  - broader probe/test-intent integration posture

### `not_selected_yet`

- repo-wide widening beyond the released `V53-A` pilot scope
- broader reviewer UX or mutation/enforcement surfaces
- benchmark-like or proof-grade evidence consumers
- second package owner surfaces

## Starter Validation Mapping

For the starter-doc phase, the truthful docs-only gate is:

- `make arc-start-check ARC=143`

For later implementation work, this slice still requires repo-native verification over
the live package path rather than extracted-bundle assumptions, and it must preserve
the `V53-A` authority boundary instead of relitigating taxonomy or applicability law.
