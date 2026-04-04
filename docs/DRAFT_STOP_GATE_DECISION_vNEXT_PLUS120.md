# Draft Stop-Gate Decision vNext+120

Status: proposed gate for `V49-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS120.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `adeu_semantic_forms` package remains the only live owner of the
  semantic-seed bridge lane;
- `bridge_v48.py` consumes exactly one released `adeu_taskpack_binding_spec_seed@1`
  and exactly one repo-owned `adeu_semantic_seed_v48_bridge_contract@1`;
- bridge output is exactly one released `anm_taskpack_binding_profile@1` produced
  through released `build_v48a_taskpack_binding_profile(...)` semantics;
- the bridge contract freezes:
  - `schema`
  - `bridge_contract_id`
  - `snapshot_id`
  - `snapshot_sha256`
  - `profile_id`
  - `task_scope_summary`
  - `command_projection`
  - `evidence_slot_projection`
  - `prompt_projection_inputs`
  - released-posture defaults only
  - `semantic_hash`
- lowering lineage is not reopened:
  - no raw `V49-A` or `V49-B` bypass;
  - one released `V49-C` seed only;
  - no upstream `typed_alternatives`
  - no upstream `clarification_required`
  - no upstream `rejected_unsupported`
- seed-anchor mapping is explicit and fail closed:
  - `scope_anchor_ref`
  - `policy_anchor_ref`
  - `worker_subject_ref`
- snapshot and profile lineage must match exactly between seed and bridge contract;
- seed fixed defaults may restate only the released `V48-A` postures:
  - lineage resolution posture
  - prompt projection posture
  - unsupported mapping posture
- fixed-default conflict or unsupported seed values fail closed;
- `allow_paths`, `forbid_paths`, and `forbid_effects` map deterministically into the
  released `V48-A` projection families;
- `task_scope_summary` and `prompt_projection_inputs` come only from the bridge
  contract and are never synthesized;
- command, evidence, and prompt projections come only from the bridge contract and are
  passed unchanged into the released `V48-A` builder;
- `policy_authority_clause_ref` is resolved only through released `V47-E` / `V48-A`
  lineage and is never synthesized or repaired locally;
- bridge-contract defaults may restate released `V48-A` postures only and may never
  override seed-derived anchor or projection content;
- the emitted binding profile revalidates under the released
  `AnmTaskpackBindingProfile` model and recomputed `semantic_hash` matches the emitted
  value;
- the emitted binding profile is admissible as the released `binding_profile_ref`
  carrier for `compile_v48b_taskpack_binding(...)`, with the remaining released
  compiler inputs supplied separately;
- repeated bridge execution over the same released seed and bridge contract is
  byte-identical;
- committed fixtures prove:
  - successful bridge replay;
  - seed-anchor mismatch reject posture;
  - snapshot mismatch reject posture;
  - fixed-default conflict reject posture;
  - byte-identical replay;
- targeted Python tests cover deterministic bridge behavior and reject posture;
- no new compile wrapper, worker runtime surface, or CLI/API/web consumer appears in
  the same slice.

## Do Not Accept If

- the slice quietly redefines released `V48-A` validation logic instead of consuming
  the released builder;
- the slice bypasses the released `V49-C` seed and recovers authority from raw
  `V45` / `V47` surfaces by ambient repo search;
- bridge code silently repairs unresolved seed-anchor or snapshot conflicts into
  apparent success;
- bridge code invents new binding-profile semantics, new compile semantics, or a new
  runtime surface;
- seed fixed defaults are treated as heuristics rather than exact released-posture
  restatements;
- task scope, prompt, command, or evidence projections are synthesized from prompt
  prose, chat memory, or prototype text;
- bridge code would have to synthesize or repair `policy_authority_clause_ref`
  lineage locally;
- prototype bridge code is imported wholesale into live package paths.

## Local Gate

- run `make arc-start-check ARC=120`
