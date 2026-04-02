# Assessment vNext+113 Edges

Status: post-closeout edge assessment for `V48-B` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS113_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released `V48-A` Bypass

- Risk:
  the compiler lane could silently bypass the released `V48-A` binding profile and
  bind directly to raw `V45`, `V45-F`, `V47-E`, or raw `D-IR` carriers.
- Response:
  freeze one starter compiler-input kind only:
  `released_anm_taskpack_binding_profile_ref`.
- Closeout Evidence:
  input-source validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  reject fixture
  `packages/adeu_agent_harness/tests/fixtures/v48b/reject_raw_v47_bypass_spec.json`,
  and test `test_v48b_rejects_raw_v47_bypass`.

### Edge 2: Binding-Profile Multiplicity Drift

- Risk:
  `V48-B` could quietly become a multi-profile composition lane instead of a bounded
  single-profile compiler seam.
- Response:
  require exactly one released binding-profile ref and leave multi-profile composition
  unselected in this slice.
- Closeout Evidence:
  cardinality validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  reject fixture
  `packages/adeu_agent_harness/tests/fixtures/v48b/reject_multiple_binding_profile_refs_spec.json`,
  and test `test_v48b_rejects_multiple_binding_profile_refs`.

### Edge 3: Compiler-Selection / Task-Identity Drift

- Risk:
  the first compiler slice could admit vague local compiler choice or ambiguous task
  identity instead of one explicit released compiler carrier plus one declared task.
- Response:
  freeze exactly one compiler-selection kind and require exactly one declared task
  identity per compiled boundary.
- Closeout Evidence:
  compiler-selection and task-identity validation in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`
  and deterministic replay coverage in
  `test_v48b_reference_compiled_binding_replays_deterministically`.

### Edge 4: Binding-Profile To Kernel-Profile Bridge Drift

- Risk:
  the slice could claim to reuse the released harness compiler while leaving the
  `V48-A` binding-profile to `taskpack/pipeline_profile@1` /
  `taskpack_profile_registry@1` bridge implicit.
- Response:
  freeze one explicit intermediate pipeline profile plus registry bridge and require
  delegation to the unchanged released `compile_taskpack(...)` entrypoint.
- Closeout Evidence:
  bridge logic in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  committed fixtures
  `packages/adeu_agent_harness/tests/fixtures/v48b/reference_pipeline_profile.json`
  and
  `packages/adeu_agent_harness/tests/fixtures/v48b/reference_profile_registry.json`,
  and test `test_v48b_rejects_malformed_pipeline_profile_bridge`.

### Edge 5: Boundary-Identity Ambiguity

- Risk:
  the compiled boundary could look deterministic while leaving the true identity
  function underdefined.
- Response:
  require one explicit compiled boundary identity hash over binding-profile lineage,
  compiler selection, and declared task identity, and carry one worker subject kind
  and one worker subject ref through the compiled artifact.
- Closeout Evidence:
  identity derivation and worker-subject fields in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  authoritative/mirror schema pair, and committed reference fixture
  `packages/adeu_agent_harness/tests/fixtures/v48b/reference_compiled_policy_taskpack_binding.json`.

### Edge 6: Manifest-Lineage Drift

- Risk:
  emitted manifests could detach from the compiled boundary and become weakly related
  packaging summaries rather than hash-consistent lineage carriers.
- Response:
  require one sibling `taskpack_manifest.json`, manifest/component hash consistency,
  and one replayable bundle hash.
- Closeout Evidence:
  manifest-lineage logic in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  committed reference compiled-binding fixture, and deterministic replay in
  `test_v48b_reference_compiled_binding_replays_deterministically`.

### Edge 7: Component-Set Widening

- Risk:
  the first compiler slice could widen the emitted component set beyond released kernel
  taskpack carriers.
- Response:
  freeze the starter component set exactly to taskpack markdown, acceptance, allowlist,
  forbidden, commands, and evidence slots, with `taskpack_manifest.json` treated as a
  sibling emitted artifact rather than an ad hoc component.
- Closeout Evidence:
  emitted component refs in the committed compiled-binding fixture and compiler-output
  checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`.

### Edge 8: Projection-Meaning Drift

- Risk:
  emitted allowlist, forbidden, command, or evidence-slot carriers could drift from
  the released `V48-A` binding profile posture during compilation.
- Response:
  require emitted components to remain derivable from the bound `V48-A` profile without
  widening categories, commands, evidence slots, or forbidden effects.
- Closeout Evidence:
  lowering logic in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  committed reference fixtures, and deterministic replay test coverage.

### Edge 9: Markdown Attribution / Section-Order Drift

- Risk:
  `TASKPACK.md` could be treated as arbitrary markdown instead of preserving the
  released compiler’s section order, attribution-marker grammar, and section
  termination posture.
- Response:
  freeze released markdown section order, attribution-marker grammar, marker-position
  rule, and section-termination posture exactly.
- Closeout Evidence:
  unchanged `compile_taskpack(...)` reuse path in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`
  and deterministic emitted taskpack replay coverage in
  `packages/adeu_agent_harness/tests/test_taskpack_compile.py`.

### Edge 10: Compiler Authority-Input Ambience

- Risk:
  semantic compiler authority inputs could be smuggled in by local convention rather
  than explicit typed derivation.
- Response:
  require explicit `source_semantic_arc`, explicit `compiled_commitments_ir_path` in
  the intermediate pipeline profile, and explicit reuse of the released compiler’s
  evidence-manifest / surface-diff resolution path.
- Closeout Evidence:
  authority-input resolution in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  committed reference fixtures, and test
  `test_v48b_rejects_ambiguous_source_semantic_arc`.

### Edge 11: Repo-Escape Path Drift

- Risk:
  compiler outputs or semantic-authority input paths could escape the repo root by
  symlink or path-traversal manipulation while still looking structurally valid.
- Response:
  resolve output and semantic-authority paths under explicit rooted containment and
  fail closed on escape.
- Closeout Evidence:
  rooted path guards in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`
  and tests `test_v48b_rejects_out_dir_symlink_escape` plus
  `test_v48b_rejects_semantic_authority_symlink_escape`.

### Edge 12: Generic Kernel Redefinition

- Risk:
  a bridge-specific compiler slice could silently redefine generic taskpack compile or
  manifest semantics before the bridge family is stable.
- Response:
  keep `V48-B` bounded to bridge-specific derivation over already released kernel
  carriers and do not reopen generic compiler semantics in this slice.
- Closeout Evidence:
  bounded implementation footprint in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  authoritative/mirror schema pair, and absence of generic compiler-contract edits in
  the committed `v113` release.

### Edge 13: Stale Binding-Profile Reuse

- Risk:
  a stale or dangling released binding profile could still be compiled into a seemingly
  valid taskpack boundary.
- Response:
  require same snapshot identity, binding-profile semantic-hash match, and fail-closed
  rejection for stale or unresolved binding-profile lineage.
- Closeout Evidence:
  lineage checks in
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`,
  reject fixture
  `packages/adeu_agent_harness/tests/fixtures/v48b/reject_binding_profile_hash_mismatch_spec.json`,
  and test `test_v48b_rejects_binding_profile_hash_mismatch`.

### Edge 14: Attestation / Conformance Bleed

- Risk:
  because the compiler now emits actual taskpack carriers, the slice could be overread
  as if worker attestation, worker provenance, or post-run conformance had already
  shipped.
- Response:
  keep `V48-B` compiler-first and non-attestational; attestation/provenance remain
  later `V48-C` work and post-run conformance remains later `V48-D` work.
- Closeout Evidence:
  frozen lock scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS113.md`,
  bounded implementation footprint under
  `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`
  and `packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py`,
  and absence of new attestation/provenance/conformance schema surfaces in the
  committed `v113` release.

## Current Judgment

- `V48-B` was the right second `V48` move because `V48-A` had already released the
  typed binding doctrine on `main`, while deterministic lowering into actual kernel
  taskpack carriers remained a distinct and still-unshipped bridge seam.
- the shipped result is properly narrow: one released `V48-A` profile in, one explicit
  kernel-facing pipeline profile plus registry bridge, one unchanged `compile_taskpack`
  delegation path, one compiled binding out, and no worker-run attestation or
  conformance widening.
- `V48-C` is now the right next move because the bound compiled boundary is released on
  `main`, while explicit worker-run envelope identity, attestation, and provenance are
  still unshipped.
