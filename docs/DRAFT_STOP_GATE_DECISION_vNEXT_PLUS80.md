# Draft Stop-Gate Decision vNext+80

Status: proposed gate for `V40-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS80.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the released `V40-A` semantic-root, `V40-B` conformance, and `V40-C`
  checkpoint-trace surfaces are consumed explicitly and are not bypassed by
  free-floating lowering fixtures;
- canonical `adeu_architecture_projection_bundle@1` and
  `adeu_architecture_projection_manifest@1` schemas validate and export cleanly;
- lowering is legal only to `adeu_core_ir@0.1` in this slice;
- ready units may emit authoritative `adeu_core_ir@0.1` artifacts in this slice, while
  blocked units may not emit any target-family artifact refs;
- projection units carry explicit:
  - `projection_id`
  - `target_family`
  - `source_refs`
  - `readiness`
  - `blocked_by_ambiguity_refs`
  - `output_artifact_refs`
  - `compiler_entrypoint`;
- no projection unit claims `readiness = ready` unless:
  - the released conformance report is `ready`; and
  - no active blocking ambiguity refs remain for that unit under released checkpoint
    trace lineage;
- blocked projection units carry `output_artifact_refs = []`;
- `checkpoint_trace_ref` is mandatory in this slice, including deterministic-ready
  lowerings, because released `V40-C` trace lineage remains a consumed input;
- no emitted artifact or manifest entry appears without explicit source-lineage and
  compiler-entrypoint provenance;
- one accepted ready lowering fixture proves deterministic replay into
  `adeu_core_ir@0.1`;
- one accepted blocked-honesty fixture proves blocked projection units do not imply
  emitted authoritative output;
- Python tests cover:
  - schema/model validation,
  - schema export parity,
  - deterministic lowering replay,
  - `adeu_core_ir` target-family-only enforcement,
  - manifest/source-lineage honesty,
  - fail-closed blocked-vs-ready behavior.

## Do Not Accept If

- lowering silently redefines `V40-A`, `V40-B`, or `V40-C` semantics instead of
  consuming them;
- lowering is attempted directly from semantic-root state without released conformance
  and checkpoint lineage;
- blocked projection state is misreported as ready or as emitted output;
- blocked projection units carry non-empty `output_artifact_refs`;
- emitted projection artifacts appear without honest source refs or compiler
  provenance;
- `V40-D` widens into UX lowerings, API/workbench routes, or broader target families;
- projection artifacts collapse final adjudication and projection readiness into one
  authority surface;
- the formal Lean sidecar becomes a hidden prerequisite for mainline lowering validity.

## Local Gate

- for the starter bundle: run `make arc-start-check ARC=80`
- for eventual implementation: run `make check`
