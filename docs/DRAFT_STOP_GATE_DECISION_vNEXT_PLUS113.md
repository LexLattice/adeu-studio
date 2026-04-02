# Draft Stop-Gate Decision vNext+113

Status: proposed gate for `V48-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS113.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- one canonical `compiled_policy_taskpack_binding@1` validates and exports cleanly;
- the committed reference compiled-binding fixture replays deterministically on repeated
  compile runs;
- every accepted compiled fixture binds exactly one released `V48-A` binding profile,
  one compiler selection, and one declared task identity;
- the bridge from released `anm_taskpack_binding_profile@1` into exactly one released
  `taskpack/pipeline_profile@1` plus exactly one released
  `taskpack_profile_registry@1` is explicit and deterministic;
- the released `compile_taskpack(...)` kernel entrypoint is reused unchanged through
  that intermediate bridge rather than bypassed by ad hoc emitted files;
- every accepted compiler request carries exactly one explicit `source_semantic_arc`;
- no accepted compiler entrypoint bypasses the released `V48-A` profile through raw
  `V45`, `V45-F`, `V47-E`, or raw `D-IR` starter inputs;
- one compiled boundary identity hash is emitted explicitly from binding-profile
  lineage, compiler selection, and declared task identity;
- one explicit worker subject kind and one worker subject ref are carried through the
  compiled artifact;
- actual taskpack components remain explicit and bounded to:
  - `TASKPACK.md`;
  - `ACCEPTANCE.json`;
  - `ALLOWLIST.json`;
  - `FORBIDDEN.json`;
  - `COMMANDS.json`;
  - `EVIDENCE_SLOTS.json`;
- one sibling `taskpack_manifest.json` is emitted under the released
  `taskpack/manifest@1` contract;
- emitted taskpack components remain released-kernel-shaped rather than ad hoc;
- `TASKPACK.md` preserves released section order, attribution-marker grammar, and
  section-termination posture exactly;
- released compiler authority inputs remain explicit rather than ambient:
  - `semantic_compiler_evidence_manifest@0.1`;
  - `semantic_compiler_surface_diff@0.1`;
  - `compiled_commitments_ir_path`;
- emitted manifest/component hashes and emitted bundle hash remain mutually consistent
  and replayable;
- unsupported compiler selections, stale lineage, unresolved lineage, and hash drift
  fail closed;
- Python tests cover:
  - released binding-profile resolution,
  - compiled boundary identity derivation,
  - deterministic emitted component replay,
  - manifest/component hash consistency,
  - raw-input-bypass fail-closed behavior,
  - schema export parity.

## Do Not Accept If

- the compiler accepts more than one binding profile source;
- the released `V48-A` profile can be bypassed by raw `V45`, `V45-F`, `V47-E`, or raw
  `D-IR` starter inputs;
- the `V48-A` binding profile to kernel-facing pipeline-profile / registry bridge is
  left implicit or implementation-defined;
- `compile_taskpack(...)` is effectively redefined instead of reused through one
  bounded wrapper path;
- compiled boundary identity is implied by local convention instead of explicit typed
  fields and deterministic hashing;
- `source_semantic_arc` or compiler authority inputs are smuggled in by ambient repo
  convention rather than explicit typed fields;
- taskpack component kinds widen beyond the released kernel component set in this
  slice;
- emitted components drift from the bound `V48-A` profile posture;
- `taskpack_manifest.json` is renamed, widened, or treated as an ad hoc component;
- markdown attribution-marker grammar, section order, or section-termination posture
  drift from the released compiler contract;
- manifest/component hash mismatch is tolerated;
- bundle-hash replayability is not explicit;
- the slice emits worker attestation, worker provenance, signature envelopes, runner
  results, or conformance reports as if later `V48` paths had already shipped;
- multi-worker topology or broader execution authority appears in the first compiler
  release;
- stale upstream lineage is tolerated as implementation-defined instead of fail
  closed.

## Local Gate

- run `make arc-start-check ARC=113`
