# Draft Stop-Gate Decision vNext+81

Status: proposed gate for `V40-E`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS81.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the released `V40-A`, `V40-B`, `V40-C`, and `V40-D` surfaces are consumed explicitly
  and are not bypassed by free-floating UX fixtures;
- deterministic lowering emits canonical `ux_domain_packet@1` only and reuses the
  authoritative target-family schema under `packages/adeu_core_ir`;
- emitted UX packets validate against the released approved-profile and
  authority-boundary contract without local schema drift;
- no UX packet is emitted unless the released source projection state remains `ready`
  and source/projection lineage is explicit;
- one accepted ready fixture proves deterministic replay into `ux_domain_packet@1`;
- one accepted blocked/no-emit fixture proves blocked architecture or blocked
  projection state does not emit a UX packet;
- Python tests cover:
  - target-family validation,
  - deterministic replay,
  - approved-profile and authority-boundary compatibility,
  - fail-closed blocked/no-emit behavior,
  - rejection of `ux_morph_ir`, surface compiler export, workbench/API, and direct
    prompt-to-surface widening.

## Do Not Accept If

- UX lowering silently redefines `V40-A`, `V40-B`, `V40-C`, or `V40-D` semantics
  instead of consuming them;
- the slice mints a new UX target-family schema instead of consuming the released
  `ux_domain_packet@1` contract;
- blocked architecture or blocked projection state is misreported as a lawful emitted UX
  packet;
- the first UX slice widens into `ux_morph_ir`, rendered-surface export, workbench/API
  release, or prompt-to-surface generation;
- emitted UX packets appear without honest architecture/projection lineage;
- the formal Lean sidecar becomes a hidden prerequisite for mainline UX-lowering
  validity.

## Local Gate

- for the starter bundle: run `make arc-start-check ARC=81`
- for eventual implementation: run `make check`
