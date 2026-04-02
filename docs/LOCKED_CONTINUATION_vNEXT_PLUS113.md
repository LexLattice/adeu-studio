# Locked Continuation vNext+113

Status: `V48-B` implementation contract.

## V113 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v48b_policy_to_taskpack_compiler_contract@1",
  "target_arc": "vNext+113",
  "target_path": "V48-B",
  "target_scope": "bounded_compiled_policy_taskpack_binding_and_deterministic_taskpack_derivation",
  "implementation_packages": [
    "adeu_agent_harness"
  ],
  "governing_released_stack": "V48A_released_binding_profile_plus_released_agent_harness_kernel_on_main",
  "governing_stack_consumption_mode": "released_binding_profile_to_compiled_taskpack_derivation_only_not_raw_policy_scope_binding_runner_attestation_conformance_signature_envelope_or_multi_worker_topology",
  "requires_released_v48a_binding_profile_surfaces": true,
  "released_v48a_profile_must_remain_single_policy_single_scope_single_worker": true,
  "no_raw_v45_or_v47_input_bypass_selected": true,
  "compiled_policy_taskpack_binding_schema": "compiled_policy_taskpack_binding@1",
  "exactly_one_binding_profile_ref_required": true,
  "exactly_one_compiler_selection_required": true,
  "exactly_one_declared_task_identity_required": true,
  "binding_profile_to_pipeline_profile_bridge_explicit_required": true,
  "intermediate_pipeline_profile_schema_required": "taskpack/pipeline_profile@1",
  "intermediate_profile_registry_schema_required": "taskpack_profile_registry@1",
  "existing_compile_taskpack_entrypoint_reuse_required": true,
  "source_semantic_arc_explicit_required": true,
  "compiler_authority_input_derivation_explicit_required": true,
  "binding_profile_semantic_hash_match_required": true,
  "binding_profile_to_compiled_boundary_identity_hash_required": true,
  "deterministic_taskpack_component_derivation_required": true,
  "deterministic_manifest_derivation_required": true,
  "taskpack_component_set_limited_to_released_kernel_components_required": true,
  "taskpack_manifest_sibling_artifact_required": true,
  "taskpack_bundle_hash_required": true,
  "compiled_boundary_component_lineage_required": true,
  "taskpack_markdown_attribution_and_section_order_preservation_required": true,
  "taskpack_markdown_and_manifest_emission_selected_here": true,
  "manifest_component_hash_consistency_required": true,
  "unsupported_compilation_request_fail_closed_required": true,
  "stale_or_unresolved_binding_profile_lineage_fail_closed_required": true,
  "same_snapshot_identity_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "compiled_fixture_examples_required": true,
  "no_worker_attestation_or_provenance_release_yet": true,
  "no_post_run_conformance_release_yet": true,
  "no_signature_envelope_or_execution_result_release_yet": true,
  "no_multi_worker_topology_yet": true,
  "no_execution_or_approval_authority_expansion": true,
  "no_automatic_waiver_or_deferral_issuance": true,
  "required_released_contracts": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS112.md"
  ],
  "source_architecture_doc": "docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md",
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v31.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v7.md",
    "docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v31.md"
}
```

## Slice

- Arc label: `vNext+113`
- Family label: `V48-B`
- Scope label: bounded compiled policy-to-taskpack binding and deterministic taskpack derivation

## Objective

Release the bounded `V48-B` policy-to-taskpack compiler lane by materializing one
canonical doctrine surface over the released `V48-A` binding profile and the released
agent-harness kernel on `main` that makes explicit:

- which single released `anm_taskpack_binding_profile@1` governs one compiled
  boundary;
- how that released binding profile is lowered into exactly one intermediate
  `taskpack/pipeline_profile@1` plus exactly one intermediate
  `taskpack_profile_registry@1` before delegating to the unchanged released
  `compile_taskpack(...)` kernel entrypoint;
- which single compiler selection and declared task identity participate in that
  compiled boundary;
- which single explicit `source_semantic_arc` governs semantic authority-input
  resolution for the unchanged released compiler;
- how one compiled boundary identity hash is derived from released binding-profile
  lineage, compiler selection, and task identity;
- how actual taskpack component carriers are deterministically derived for:
  - `TASKPACK.md`;
  - `ACCEPTANCE.json`;
  - `ALLOWLIST.json`;
  - `FORBIDDEN.json`;
  - `COMMANDS.json`;
  - `EVIDENCE_SLOTS.json`;
- how one sibling `taskpack_manifest.json` artifact, one manifest hash, and one bundle
  hash stay explicit and replayable;
- how released markdown section order, attribution-marker grammar, and
  section-termination posture are preserved exactly rather than reinterpreted locally;
- how released compiler authority inputs are obtained explicitly rather than ambiently:
  - `semantic_compiler_evidence_manifest@0.1`;
  - `semantic_compiler_surface_diff@0.1`;
  - `adeu_commitments_ir@0.1` at `compiled_commitments_ir_path`;
- what fail-closed rules prevent raw `V45` / `V47` bypass, stale binding-profile reuse,
  unsupported compiler selection, ad hoc component widening, or hash-drifted compiled
  output.

This slice is compiler-first and still non-attestational. It does not reopen released
`V48-A` binding semantics, released `V45` or `V47` semantics, generic taskpack-kernel
semantics, worker attestation semantics, worker provenance semantics, signature
verification semantics, post-run conformance semantics, or multi-worker topology
doctrine. It also does not widen into execution authority, approval authority, waiver /
deferral issuance, benchmark / contest / structural-assessment doctrine, or prompt-shaped
authority.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V48-B` releases one typed compiled-binding surface plus deterministic
     taskpack-component derivation over the already released `V48-A` binding-profile
     surface and the already released agent-harness kernel on `main`;
   - it does not reopen descriptive semantics, normative semantics, released
     `V48-A` binding semantics, or generic taskpack / runner / signing semantics.
2. Package-ownership strategy:
   - `adeu_agent_harness` remains the sole implementation owner in this slice;
   - released `adeu_repo_description`, `adeu_semantic_source`, and
     `adeu_commitments_ir` artifacts remain upstream inputs only through the released
     `V48-A` profile and are not reopened as direct compiler inputs here.
3. Input-source strategy:
   - the first `V48-B` release supports exactly one compiler input source kind:
     - `released_anm_taskpack_binding_profile_ref`
   - every accepted compiler input must resolve to exactly one released
     `anm_taskpack_binding_profile@1`;
   - no `V48-B` compile request may bypass the released `V48-A` profile by binding
     directly to raw `V45` scope artifacts, raw `V45-F` entries, raw `V47-E` rows, or
     raw `D-IR` clause refs;
   - the first `V48-B` release does not select:
     - multi-profile compile sets;
     - profile-composition algebra;
     - direct raw policy/scope starter carriers.
4. Compiler-selection strategy:
   - the first `V48-B` release supports exactly one compiler-selection kind:
     - `released_adeu_agent_harness_taskpack_compiler`
   - every accepted compile request must carry exactly one declared task identity and
     exactly one compiler selection;
   - unsupported compiler selections or ambiguous task identities must fail closed.
5. Bridge-to-kernel strategy:
   - `V48-B` does not redefine the released harness compiler input grammar;
   - instead, it must explicitly materialize exactly one intermediate
     `taskpack/pipeline_profile@1` plus exactly one intermediate
     `taskpack_profile_registry@1` from the resolved `anm_taskpack_binding_profile@1`
     and then delegate to the unchanged released `compile_taskpack(...)` entrypoint;
   - the intermediate pipeline profile must preserve the released frozen grammar,
     including:
     - `task_scope_title`;
     - `task_scope_summary`;
     - `compiled_commitments_ir_path`;
     - `acceptance_criteria`;
     - `allowlist_paths`;
     - `forbidden_paths`;
     - `forbidden_effects`;
     - `commands`;
     - `evidence_slots`;
   - `V48-B` may not compile directly from the `V48-A` profile into ad hoc emitted
     taskpack files without this explicit kernel-facing bridge.
6. Compiler-authority-input strategy:
   - every accepted compile request must carry exactly one explicit
     `source_semantic_arc`;
   - released compiler authority inputs must be obtained explicitly rather than
     ambiently:
     - `semantic_compiler_evidence_manifest@0.1` and
       `semantic_compiler_surface_diff@0.1` must resolve through the unchanged
       released compiler's `source_semantic_arc` selection path;
     - `compiled_commitments_ir_path` must be carried explicitly in the intermediate
       pipeline profile and must remain coherent with the resolved released binding
       profile lineage;
   - `V48-B` may not smuggle these authority inputs in by local convention or hidden
     repo search outside the released compiler path.
7. Compiled-boundary identity strategy:
   - each compiled artifact governs exactly:
     - one released binding profile;
     - one compiler selection;
     - one worker subject kind;
     - one worker subject ref;
     - one declared task identity;
     - one compiled boundary identity hash.
   - the compiled boundary identity hash must be derived explicitly from:
     - binding-profile semantic hash;
     - policy lineage hash;
     - scope lineage hash;
     - compiler selection;
     - declared task identity.
8. Output-surface strategy:
   - `V48-B` may emit exactly one compiled-binding artifact plus exactly one released
     taskpack component set containing:
     - `TASKPACK.md`;
     - `ACCEPTANCE.json`;
     - `ALLOWLIST.json`;
     - `FORBIDDEN.json`;
     - `COMMANDS.json`;
     - `EVIDENCE_SLOTS.json`.
   - `V48-B` may also emit exactly one sibling manifest artifact:
     - `taskpack_manifest.json`.
   - derived taskpack components must remain released-kernel-shaped rather than ad hoc:
     - `ALLOWLIST.json` must remain shaped like `taskpack/allowlist@1`;
     - `FORBIDDEN.json` must remain shaped like `taskpack/forbidden@1`;
     - `COMMANDS.json` must remain shaped like `taskpack/commands@1`;
     - `EVIDENCE_SLOTS.json` must remain shaped like `taskpack/evidence_slots@1`;
     - `taskpack_manifest.json` must remain shaped like `taskpack/manifest@1`.
   - `V48-B` does not yet emit:
     - worker attestation outputs;
     - worker provenance outputs;
     - signature envelopes;
     - execution results;
     - conformance reports.
9. Markdown-projection strategy:
   - `TASKPACK.md` derivation must preserve released markdown projection doctrine
     exactly rather than locally:
     - released semantic section order;
     - released attribution-marker grammar;
     - released attribution-marker position rule;
     - released section-termination posture.
   - markdown replayability may not be weakened into “equivalent prose” in this slice.
10. Manifest-lineage strategy:
   - every emitted manifest must remain component-hash-consistent with the emitted
     taskpack component set;
   - every emitted component set must remain derivable from the released `V48-A`
     profile without widening categories, commands, evidence slots, or forbidden
     effects beyond the bound profile posture;
   - one explicit `bundle_hash` must remain derivable over the verified emitted bundle;
   - manifest/component hash drift must fail closed.
11. Upstream-lineage strategy:
   - every compiled artifact must resolve coherently against:
     - one declared snapshot identity;
     - one released `anm_taskpack_binding_profile@1`;
     - one matching binding-profile semantic hash;
     - one policy lineage hash and one scope lineage hash inherited from the resolved
       binding profile.
   - stale, dangling, or unresolved binding-profile lineage must fail closed.
12. Anti-overreach strategy:
   - `V48-B` may not mint execution, approval, mutation, scheduling, waiver, or
     deferral authority;
   - `V48-B` may not silently redefine generic taskpack-kernel semantics;
   - `V48-B` may not silently widen into worker attestation, worker provenance,
     post-run conformance, signature issuance, or multi-worker topology.

## Bounded Compiler Vocabularies

The first `V48-B` release should freeze bounded compiler vocabularies rather than leave
compiled-boundary posture to implementation taste.

The intended bounded starter vocabularies are:

- `binding_profile_source_kind`:
  - `released_anm_taskpack_binding_profile_ref`
- `compiler_selection_kind`:
  - `released_adeu_agent_harness_taskpack_compiler`
- `kernel_bridge_posture`:
  - `released_pipeline_profile_and_registry_then_compile_taskpack`
- `compiled_component_set_kind`:
  - `released_taskpack_bundle_component_set`
- `taskpack_component_kind`:
  - `taskpack_markdown_component`
  - `taskpack_acceptance_component`
  - `taskpack_allowlist_component`
  - `taskpack_forbidden_component`
  - `taskpack_commands_component`
  - `taskpack_evidence_slots_component`
- `compiled_boundary_identity_posture`:
  - `binding_lineage_plus_task_identity_hash`
- `unsupported_compilation_posture`:
  - `fail_closed`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent doctrine creep.

The first `V48-B` release also freezes these compiler invariants:

- `binding_profile_source_kind = released_anm_taskpack_binding_profile_ref`:
  - exactly one `binding_profile_ref` is required
  - the resolved profile must carry schema `anm_taskpack_binding_profile@1`
  - the resolved profile must remain the only admitted starter carrier
- `compiler_selection_kind = released_adeu_agent_harness_taskpack_compiler`:
  - exactly one `compiler_selection` is required
  - exactly one `declared_task_identity` is required
- `compiled_component_set_kind = released_taskpack_bundle_component_set`:
  - exactly one emitted component set is required
  - component kinds may not widen beyond the released kernel component set

## Required Deliverables

1. New typed compiled-binding surface:
   - canonical `compiled_policy_taskpack_binding@1` artifact;
   - authoritative and mirrored schema export parity for that artifact.
2. Deterministic compiler entrypoint(s) that:
   - bind one declared snapshot identity;
   - consume exactly one released `anm_taskpack_binding_profile@1`;
   - materialize exactly one intermediate `taskpack/pipeline_profile@1` and exactly
     one intermediate `taskpack_profile_registry@1`;
   - delegate to the unchanged released `compile_taskpack(...)` entrypoint;
   - carry exactly one explicit `source_semantic_arc`;
   - emit one deterministic compiled boundary identity hash;
   - emit one deterministic taskpack component set over released kernel carriers only
     plus one sibling `taskpack_manifest.json`;
   - fail closed on raw `V45` / `V47` bypass, stale lineage, unsupported compiler
     selection, hash mismatch, manifest/component drift, or component widening.
3. Top-level schema anchors for `compiled_policy_taskpack_binding@1`:
   - `schema`
   - `compiled_binding_id`
   - `snapshot_id`
   - `snapshot_sha256`
   - `binding_profile_source_kind`
   - `binding_profile_ref`
   - `binding_profile_semantic_hash`
   - `policy_lineage_hash`
   - `scope_lineage_hash`
   - `binding_subject_id`
   - `worker_subject_kind`
   - `worker_subject_ref`
   - `compiler_selection_kind`
   - `compiler_selection`
   - `source_semantic_arc`
   - `declared_task_identity`
   - `kernel_bridge_posture`
   - `pipeline_profile_ref`
   - `pipeline_profile_sha256`
   - `profile_registry_ref`
   - `profile_registry_sha256`
   - `compiled_commitments_ir_path`
   - `semantic_compiler_evidence_manifest_path`
   - `semantic_compiler_surface_diff_path`
   - `compiled_boundary_identity_posture`
   - `compiled_boundary_identity_hash`
   - `compiled_component_set_kind`
   - `taskpack_markdown_ref`
   - `acceptance_ref`
   - `allowlist_ref`
   - `forbidden_ref`
   - `commands_ref`
   - `evidence_slots_ref`
   - `taskpack_manifest_ref`
   - `manifest_sha256`
   - `bundle_hash`
   - `unsupported_compilation_posture`
   - `semantic_hash`
4. Accepted doctrine fixtures:
   - at least one accepted compiled-binding fixture over the released `V48-A`
     reference binding profile;
   - at least one accepted deterministic taskpack-derivation fixture with emitted
     released kernel component carriers;
   - at least one accepted intermediate pipeline-profile / registry bridge fixture
     that delegates to the unchanged released compiler;
   - at least one accepted compiled-boundary-identity fixture over binding lineage,
     compiler selection, and declared task identity;
   - at least one accepted manifest-lineage fixture where emitted component hashes stay
     consistent with the compiled boundary output.
5. Reject fixtures that fail closed on:
   - more than one binding profile source;
   - raw `V45` or raw `V47` input bypass around the released `V48-A` profile;
   - missing, stale, or unresolved released binding-profile lineage;
   - binding-profile semantic-hash mismatch;
   - unsupported or ambiguous compiler selection;
   - missing or ambiguous declared task identity;
   - missing or malformed intermediate `taskpack/pipeline_profile@1` grammar;
   - missing or malformed intermediate `taskpack_profile_registry@1` grammar;
   - missing or ambiguous `source_semantic_arc`;
   - missing or ambient compiler authority inputs outside the explicit released path;
   - emitted component widening beyond the released kernel component set;
   - emitted component payloads that drift from the bound `V48-A` profile projections;
   - markdown section-order, attribution-marker, or section-termination drift;
   - manifest hash mismatch or component-hash inconsistency;
   - signature-envelope, runner-result, attestation, or conformance outputs emitted as
     if later `V48` paths had already shipped;
   - multi-worker, execution, approval, waiver, or deferral authority claims.
6. Deterministic targeted tests covering:
   - released `V48-A` profile resolution;
   - compiled boundary identity derivation;
   - deterministic emitted taskpack component replay;
   - manifest/component hash consistency;
   - raw-input-bypass fail-closed behavior;
   - schema export parity.

## Acceptance

Accept this slice only if:

1. canonical `compiled_policy_taskpack_binding@1` ships with authoritative / mirrored
   schema parity;
2. every accepted compiled artifact consumes exactly one released `V48-A` binding
   profile, one compiler selection, and one declared task identity;
3. released `V48-A` profile lineage remains explicit and no raw `V45` / `V47` bypass
   path is accepted;
4. one compiled boundary identity hash is emitted explicitly over released binding
   lineage, compiler selection, and declared task identity;
5. emitted taskpack components remain limited to released kernel carriers and stay
   consistent with the bound `V48-A` profile projections;
6. one explicit intermediate pipeline profile plus one explicit profile registry bridge
   bridge the released `V48-A` profile into the unchanged released
   `compile_taskpack(...)`
   entrypoint without redefining kernel grammar;
7. emitted `TASKPACK.md` preserves released section order, attribution-marker grammar,
   and section-termination posture exactly;
8. emitted manifest hash, emitted component hashes, and emitted bundle hash remain
   mutually consistent and replayable;
9. unsupported compilation requests, stale lineage, unresolved lineage, and hash drift
   fail closed;
10. the shipped slice remains non-attestational, non-conformance-bearing,
   non-signing-authoritative, non-executive, and non-multi-worker;
11. schema export parity, deterministic compile replay, and scoped Python tests pass.

Do not ship this slice if:

- the compiler accepts more than one binding profile source;
- raw `V45`, `V45-F`, `V47-E`, or raw `D-IR` carriers can bypass the released
  `V48-A` profile;
- the bridge from `anm_taskpack_binding_profile@1` to released
  `taskpack/pipeline_profile@1` plus `taskpack_profile_registry@1` is left implicit or
  implementation-defined;
- compiled boundary identity is implied by local convention instead of explicit typed
  fields and deterministic hashing;
- taskpack component kinds widen beyond the released kernel component set;
- emitted components drift from the bound `V48-A` profile posture;
- `taskpack_manifest.json` is renamed, widened, or treated as an ad hoc manifest
  carrier;
- markdown attribution-marker grammar, section order, or section-termination posture
  drift from the released compiler contract;
- manifest/component hash mismatch is tolerated;
- the compiler emits attestation, provenance, signature, runner-result, or conformance
  artifacts as if `V48-C` or `V48-D` had already shipped;
- the slice widens into multi-worker topology, execution authority, approval
  authority, waiver issuance, or deferral issuance.

## Local Gate

- run `make arc-start-check ARC=113` while the bundle remains docs-only;
- run targeted Python checks for `adeu_agent_harness` once code work begins;
- do not treat this starter bundle as a substitute for the Python lane once source code
  changes begin.
