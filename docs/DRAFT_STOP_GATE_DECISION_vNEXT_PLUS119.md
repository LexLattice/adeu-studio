# Draft Stop-Gate Decision vNext+119

Status: proposed gate for `V49-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS119.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `adeu_semantic_forms` package remains the only live owner of the
  deterministic lowering lane;
- `transform_v48_seed.py` consumes exactly one released
  `adeu_semantic_normal_form@1` and exactly one released
  `adeu_semantic_transform_contract@1`;
- lowering is admissible only from:
  - one directly authored released `V49-A` normal form; or
  - one released `V49-B` parse result whose outcome is exactly
    `resolved_singleton`;
- no lowering silently selects one candidate out of `typed_alternatives`, and no
  lowering proceeds from `clarification_required` or `rejected_unsupported`;
- the lowering lane emits exactly one `adeu_taskpack_binding_spec_seed@1` and remains
  pre-bridge / pre-runtime;
- required singleton relations are projected deterministically and fail closed when
  missing or duplicated;
- `produce_artifact_kind` remains singleton in the starter slice and emits exactly one
  canonical artifact family as a single-item deterministic set;
- supported multi relations are deduped and ordered deterministically before seed
  emission;
- transform-contract mismatch, unsupported relation kinds, and fixed-default conflicts
  with relation-derived values fail closed;
- the emitted seed remains non-equivalent to a released `V48-A` binding profile and is
  not admissible as one before the later `V49-D` bridge;
- committed fixtures prove:
  - successful lowering replay;
  - missing-required reject posture;
  - duplicate-singleton reject posture;
  - transform mismatch reject posture;
  - byte-identical replay over repeated lowering;
- targeted Python tests cover deterministic lowering and reject posture;
- no `V48-A` binding helper, `V48-B` compile helper, or CLI/API/web consumer appears
  in the same slice.

## Do Not Accept If

- the slice quietly redefines `V49-A` or `V49-B` semantics instead of consuming them;
- the slice lowers from `typed_alternatives`, `clarification_required`, or
  `rejected_unsupported` outputs;
- lowering invents new relation kinds, domains, or downstream target schemas;
- support-only notices affect emitted seed identity;
- `produce_artifact_kind` silently widens from singleton starter posture into an
  ungoverned multi-value algebra;
- multi-relation output ordering depends on incidental iteration order;
- fixed defaults silently override conflicting relation-derived values;
- `V48` helper behavior leaks into the same slice;
- CLI, API, or web consumer surfaces appear in the same slice;
- prototype lowering code is imported wholesale into live package paths.

## Local Gate

- run `make arc-start-check ARC=119`
