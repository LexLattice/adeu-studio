# Draft ADEU Semantic Forms V49D Implementation Mapping v0

Status: support-layer implementation mapping for `V49-D`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the imported
`adeu_semantic_forms` prototype material to the repo-owned `V49-D` bridge slice so the
implementation can stay grounded without importing prototype bridge behavior as live
authority.

## Carry Forward Nearly As-Is

- starter bridge posture:
  - one released `adeu_taskpack_binding_spec_seed@1` in
  - one released `anm_taskpack_binding_profile@1` out
- starter seed anchor families:
  - `scope_anchor_ref`
  - `policy_anchor_ref`
  - `worker_subject_ref`
- starter seed projection families:
  - `allow_paths`
  - `forbid_paths`
  - `forbid_effects`
- seed fixed-default posture:
  - `lineage_resolution_posture`
  - `prompt_projection_posture`
  - `unsupported_mapping_posture`

## Re-Author With Repo Alignment

- live bridge owner:
  - `packages/adeu_semantic_forms/src/adeu_semantic_forms/bridge_v48.py`
- bridge contract surface:
  - repo-owned `adeu_semantic_seed_v48_bridge_contract@1`
  - explicit snapshot / scope / policy / worker anchors
  - explicit task scope summary
  - explicit prompt projection inputs
  - explicit command and evidence projections
  - explicit released-posture defaults only
- actual `V48` consumption:
  - call the released `build_v48a_taskpack_binding_profile(...)` surface directly
  - keep compatibility with the released `binding_profile_ref` carrier expected by
    `compile_v48b_taskpack_binding(...)`
- fail-closed doctrine:
  - seed-anchor mismatch
  - snapshot mismatch
  - worker-subject mismatch
  - task-scope / prompt-input synthesis attempt
  - local policy-clause repair attempt
  - fixed-default conflict
  - unsupported seed values
- repo-native fixtures and tests:
  - accepted bridge replay
  - mismatch rejects
  - byte-identical replay

## Defer To Later Slice Or Consumer

- new compile wrapper behavior:
  - not selected in `V49-D`
  - later consumers may call released `V48-B` directly
- worker runtime, conformance, and delegation:
  - remain downstream `V48` consumer behavior, not `V49-D`
- CLI / API / web consumers:
  - not selected here

## Do Not Import

- do not copy prototype bridge code wholesale into live package paths
- do not import any prototype-local binding-profile encoder as if it were released
  `V48-A`
- do not let prototype narrative text synthesize command or evidence projections
- do not let prototype narrative text synthesize task scope or prompt inputs
- do not let prototype helper defaults silently override released seed or bridge
  contract values
