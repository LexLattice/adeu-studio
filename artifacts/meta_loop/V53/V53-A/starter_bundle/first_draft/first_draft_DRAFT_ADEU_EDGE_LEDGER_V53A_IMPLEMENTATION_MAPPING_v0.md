# Draft ADEU Edge Ledger V53A Implementation Mapping v0

Status: support-layer starter-slice mapping for `V53-A`.

Authority layer: support only.

This note does not authorize implementation by itself. It narrows the broader
`V53` family mapping into the first starter slice so the `vNext+141` draft bundle can
stay explicit about what is instantiated here, what is deferred, and what remains
unselected.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md`
- `docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS141.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md`

## Selected Starter Slice

`V53-A` selects one bounded repo-owned starter seam:

- live owner surface:
  - `packages/adeu_edge_ledger`
- live starter contracts:
  - `adeu_edge_class_catalog@1`
  - `adeu_edge_probe_template_catalog@1`
  - `adeu_symbol_edge_applicability_frame@1`
- governing released upstream inputs:
  - one released `adeu_symbol_audit_scope_manifest@1`
  - one released `adeu_symbol_census@1`
  - one released `adeu_symbol_audit_coverage_report@1` with `coverage_status =
    closed_clean`
  - one released `adeu_symbol_semantic_audit@1`
- bounded released pilot scope only:
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`

## Carry Forward As Support, Not Authority

The imported bundle contributes starter structure worth preserving, but not live
authority:

- one adjacent-package split instead of ambient `adeu_symbol_audit` widening
- one three-level taxonomy with `family`, `subfamily`, and `archetype`
- one declarative probe-template catalog bound to the taxonomy
- one symbol-local applicability frame rather than only informal reviewer cues
- one explicit distinction between starter taxonomy/applicability and later stronger
  adjudication or revision lanes

## Re-Author Under Repo Control

`V53-A` should re-author the imported material in repo-native form as follows:

- reuse one released symbol-id helper from the released `V45` / `V50` stack rather than
  duplicating identity law locally
- bind every applicability frame to exact released upstream refs and hashes
- keep the starter slice downstream-consumer-only with respect to released `V45` / `V50`
- require full archetype-addressable applicability rows rather than sparse positive-only
  witness rows
- keep probe templates declarative and advisory rather than executable/witness-bearing
- freeze starter vocabularies explicitly in the continuation lock rather than leaving
  them to implementation taste
- keep schema export parity between authoritative package exports and root `spec/`
  mirrors if schema files are committed

## Constrain But Not Mint

`V53-A` may constrain later `V53` lanes, but it may not mint them.

Allowed constrain actions here:

- freeze starter top-level family vocabulary
- freeze starter probe-template vocabulary
- freeze starter applicability status vocabulary
- freeze the exact released upstream-consumption posture
- freeze the exact starter pilot scope
- freeze the starter package owner and schema/export posture

Not authorized here:

- explicit override law
- adjudication ledger release
- proof-grade status promotion from lexical or structural cues
- cumulative revision/register semantics
- direct joins to released `V45-D` test-intent artifacts
- repo-wide scope widening
- probe execution, mutation, or broader reviewer-platform surfaces

## Slice Seam Classification

### `instantiated_here`

- `packages/adeu_edge_ledger` starter package scaffold
- `adeu_edge_class_catalog@1`
- `adeu_edge_probe_template_catalog@1`
- `adeu_symbol_edge_applicability_frame@1`
- deterministic starter fixtures for positive and fail-closed starter cases
- schema export parity between package and root `spec/` mirrors if schema files are
  released

### `deferred_to_later_family`

- `V53-B`:
  - `adeu_symbol_edge_adjudication_ledger@1`
  - explicit fail-closed override law
  - stronger evidence semantics for witness / checked-no-witness claims
- `V53-C`:
  - cumulative revision lineage/register surface
  - split / merge / deprecate / stabilize history as live contract semantics
- `V53-D`:
  - direct test-intent integration with released `V45-D`
  - broader probe/test-intent integration posture

### `not_selected_yet`

- repo-wide widening beyond the released `adeu_architecture_ir` pilot scope
- broad probe execution framework
- reviewer UX or mutation/enforcement platform surfaces
- second package owner surfaces

## Starter Validation Mapping

For the starter-doc phase, the truthful docs-only gate is:

- preferred canonical helper:
  - `make arc-start-check ARC=141`
- if the family worktree blocks the canonical helper because repo-root autodiscovery is
  tied to a `.git/` directory:
  - run `.venv/bin/python apps/api/scripts/lint_arc_bundle.py --arc 141 --phase start --repo-root .`
  - run `make instruction-policy-check`
  - record the exact worktree quirk as an operational note in the starter handoff docs

For later implementation work, this slice still requires repo-native verification over
the live package path rather than extracted-bundle assumptions.
