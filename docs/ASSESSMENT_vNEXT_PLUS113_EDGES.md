# Assessment vNext+113 Edges

Status: planning-edge assessment for `V48-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS113_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released `V48-A` Bypass

- Risk:
  the compiler lane could silently bypass the released `V48-A` binding profile and bind
  directly to raw `V45`, `V45-F`, `V47-E`, or raw `D-IR` carriers.
- Response:
  freeze one starter compiler-input kind only:
  `released_anm_taskpack_binding_profile_ref`.

### Edge 2: Binding-Profile Multiplicity Drift

- Risk:
  `V48-B` could quietly become a multi-profile composition lane instead of a bounded
  single-profile compiler seam.
- Response:
  require exactly one released binding-profile ref and leave multi-profile composition
  unselected in this slice.

### Edge 3: Compiler-Selection Drift

- Risk:
  the first compiler slice could admit multiple compiler-selection postures or vague
  local compiler choice instead of one explicit released compiler carrier.
- Response:
  freeze exactly one compiler-selection kind and require exactly one declared task
  identity per compiled boundary.

### Edge 4: Binding-Profile To Kernel-Profile Bridge Drift

- Risk:
  the slice could claim to reuse the released harness compiler while leaving the
  `V48-A` binding-profile to `taskpack/pipeline_profile@1` /
  `taskpack_profile_registry@1` bridge implicit.
- Response:
  freeze one explicit intermediate pipeline-profile plus registry bridge and require
  delegation to the unchanged released `compile_taskpack(...)` entrypoint.

### Edge 5: Boundary-Identity Ambiguity

- Risk:
  the compiled boundary could look deterministic while leaving the true identity
  function underdefined.
- Response:
  require one explicit compiled boundary identity hash over binding-profile lineage,
  compiler selection, and declared task identity.

### Edge 6: Manifest-Lineage Drift

- Risk:
  emitted manifests could detach from the compiled boundary and become weakly related
  packaging summaries rather than hash-consistent lineage carriers.
- Response:
  require one sibling `taskpack_manifest.json`, manifest/component hash consistency,
  and one replayable bundle hash.

### Edge 7: Component-Set Widening

- Risk:
  the first compiler slice could widen the emitted component set beyond released kernel
  taskpack carriers.
- Response:
  freeze the starter component set exactly to taskpack markdown, acceptance, allowlist,
  forbidden, commands, and evidence slots, with `taskpack_manifest.json` treated as a
  sibling emitted artifact rather than an ad hoc component.

### Edge 8: Projection-Meaning Drift

- Risk:
  emitted allowlist, forbidden, command, or evidence-slot carriers could drift from
  the released `V48-A` binding profile posture during compilation.
- Response:
  require emitted components to remain derivable from the bound `V48-A` profile without
  widening categories, commands, evidence slots, or forbidden effects.

### Edge 9: Markdown Attribution / Section-Order Drift

- Risk:
  `TASKPACK.md` could be treated as arbitrary markdown instead of preserving the
  released compiler’s section order, attribution-marker grammar, and section
  termination posture.
- Response:
  freeze released markdown section order, attribution-marker grammar, marker-position
  rule, and section-termination posture exactly.

### Edge 10: Compiler Authority-Input Ambience

- Risk:
  semantic compiler authority inputs could be smuggled in by local convention rather
  than explicit typed derivation.
- Response:
  require explicit `source_semantic_arc`, explicit `compiled_commitments_ir_path` in the
  intermediate pipeline profile, and explicit reuse of the released compiler’s
  evidence-manifest / surface-diff resolution path.

### Edge 11: Generic Kernel Redefinition

- Risk:
  a bridge-specific compiler slice could silently redefine generic taskpack compile or
  manifest semantics before the bridge family is stable.
- Response:
  keep `V48-B` bounded to bridge-specific derivation over already released kernel
  carriers and do not reopen generic compiler semantics in this slice.

### Edge 12: Stale Binding-Profile Reuse

- Risk:
  a stale or dangling released binding profile could still be compiled into a seemingly
  valid taskpack boundary.
- Response:
  require same snapshot identity, binding-profile semantic-hash match, and fail-closed
  rejection for stale or unresolved binding-profile lineage.

### Edge 13: Attestation Bleed

- Risk:
  because the compiler now emits actual taskpack carriers, the slice could be overread
  as if worker attestation or worker provenance had already shipped.
- Response:
  keep `V48-B` compiler-first and non-attestational; attestation and provenance remain
  later `V48-C` work.

### Edge 14: Conformance Bleed

- Risk:
  compiled taskpacks could be mistaken for proof that later worker behavior already
  stayed inside the boundary.
- Response:
  keep post-run conformance and replay diagnostics outside this slice and defer them to
  `V48-D`.

### Edge 15: Signature / Result Overread

- Risk:
  because released harness signing and runner surfaces already exist on `main`, the
  compiler slice could quietly widen into signature envelopes or execution results.
- Response:
  keep those surfaces as baseline context only and do not release signature or result
  carriers inside `V48-B`.

### Edge 16: Multi-Worker Topology Creep

- Risk:
  a first compiler slice could quietly grow worker-count, delegation, or topology
  semantics before the single-worker bridge is proven end to end.
- Response:
  keep topology and handoff doctrine deferred to `V48-E`.

### Edge 17: Authority Expansion Through Compilation

- Risk:
  because `V48-B` ends in runnable taskpack carriers, the compiler output could be
  overread as minting stronger execution or approval authority than the released
  binding profile allows.
- Response:
  keep the compiled surface constrain-only and non-executive apart from released
  upstream policy posture.

### Edge 18: Package-Boundary Sprawl

- Risk:
  the compiler lane could sprawl back into `adeu_repo_description`,
  `adeu_semantic_source`, or `adeu_commitments_ir` instead of first stabilizing as a
  harness-owned compiler bridge.
- Response:
  keep `V48-B` bounded to `adeu_agent_harness` and consume earlier released surfaces
  only through the released `V48-A` binding profile.

## Current Judgment

- `V48-B` is worth implementing now because `V48-A` already released the bounded
  binding doctrine on `main`, while deterministic lowering into actual taskpack
  carriers is still missing.
- the right next move is compiler-first rather than attestation-first or
  conformance-first, because ADEU should make the compiled boundary itself explicit
  before trying to prove which worker run used it.
