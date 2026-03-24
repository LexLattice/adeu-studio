# Locked Continuation vNext+79

Status: `V40-C` implementation contract.

## V79 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v40c_architecture_hybrid_checkpoint_contract@1",
  "target_arc": "vNext+79",
  "target_path": "V40-C",
  "target_scope": "architecture_hybrid_checkpoint_oracle_and_trace_baseline",
  "semantic_ir_schema": "adeu_architecture_semantic_ir@1",
  "conformance_report_schema": "adeu_architecture_conformance_report@1",
  "oracle_request_schema": "adeu_architecture_oracle_request@1",
  "oracle_resolution_schema": "adeu_architecture_oracle_resolution@1",
  "checkpoint_trace_schema": "adeu_architecture_checkpoint_trace@1",
  "ir_delta_schema": "adeu_architecture_ir_delta@1",
  "implementation_package": "adeu_architecture_compiler",
  "upstream_root_package": "adeu_architecture_ir",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v19.md",
  "hybrid_precedent_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md"
}
```

## Slice

- Arc label: `vNext+79`
- Family label: `V40-C`
- Scope label: architecture hybrid checkpoint, oracle, and trace baseline

## Objective

Introduce the first concrete ASIR hybrid ambiguity slice by extending the released
architecture compiler lane with typed checkpoint, oracle, and adjudication artifacts
that consume the released semantic-root and conformance surfaces without reopening
either one.

This slice establishes the first repo-native hybrid ambiguity substrate for:

- canonical `adeu_architecture_oracle_request@1`
- canonical `adeu_architecture_oracle_resolution@1`
- canonical `adeu_architecture_checkpoint_trace@1`
- canonical `adeu_architecture_ir_delta@1`
- deterministic checkpoint classification from released ASIR ambiguity and conformance
  surfaces
- exact replay identity and one-round oracle law
- advisory-only oracle output and deterministic final adjudication
- fail-closed contradiction, replay-mismatch, and escalation behavior

This slice remains deliberately prior to:

- `adeu_architecture_projection_bundle@1`
- `adeu_architecture_projection_manifest@1`
- `adeu_core_ir` lowering
- UX lowerings
- API or web human-review workbench routes
- direct repo mutation or patch-payload emission

Its job is to make bounded architecture ambiguity explicit and replayable before any
downstream lowering surface tries to consume hybrid disposition as if it were already a
projection or emitted artifact.

## Frozen Implementation Decisions

1. Hybrid package strategy:
   - keep `packages/adeu_architecture_compiler` as the active package for the first
     `V40-C` slice;
   - no separate hybrid package may be introduced in `vNext+79`;
   - `packages/adeu_architecture_ir` remains authoritative for released root-family
     schemas and may not be silently redefined here.
2. Upstream consumption strategy:
   - `vNext+79` must consume released `V40-A` semantic-root artifacts and released
     `V40-B` conformance outputs or exact validated derivatives thereof;
   - no checkpoint, oracle, or trace artifact may bypass those released surfaces with
     free-floating hybrid fixtures when released root and conformance inputs already
     exist;
   - every emitted hybrid artifact must bind back to released semantic-root and
     conformance lineage.
3. Hybrid artifact-release strategy:
   - the only newly released artifact families in this slice are:
     - `adeu_architecture_oracle_request@1`
     - `adeu_architecture_oracle_resolution@1`
     - `adeu_architecture_checkpoint_trace@1`
     - `adeu_architecture_ir_delta@1`
   - authoritative JSON schemas must live under
     `packages/adeu_architecture_compiler/schema/`;
   - mirrored exports must live under `spec/`;
   - none of these artifacts may collapse into projection-manifest, projection-bundle,
     or emitted-lowering authority.
4. Checkpoint-class strategy:
   - the canonical classifier in `vNext+79` must emit exactly:
     - `deterministic_pass`
     - `deterministic_fail`
     - `oracle_needed`
     - `human_needed`
   - legal `resolution_route -> checkpoint_class` mapping must be frozen exactly as:
     - `deterministic_only -> deterministic_pass | deterministic_fail`
     - `oracle_assisted -> oracle_needed`
     - `human_only -> human_needed`
   - no other `resolution_route -> checkpoint_class` mapping is allowed in the first
     baseline;
   - if a checkpoint is sourced from released `V40-B` deterministic
     `human_escalation_refs`, the classifier must emit `human_needed` directly and may
     not emit an oracle request;
   - no fifth fallback class is allowed in the first baseline.
5. Final-adjudication strategy:
   - the canonical `final_adjudication` vocabulary in `vNext+79` must be exactly:
     - `resolved_pass`
     - `resolved_fail`
     - `escalated_human`
   - legal transition law must be frozen exactly as:
     - `deterministic_pass -> resolved_pass`
     - `deterministic_fail -> resolved_fail`
     - `oracle_needed -> resolved_pass | resolved_fail | escalated_human`
     - `human_needed -> escalated_human`
   - no other `checkpoint_class -> final_adjudication` transition is allowed in the
     first baseline.
6. Deterministic-compiler boundary strategy:
   - failed required deterministic checks from released `V40-B` conformance outputs
     are not lawful oracle-repair checkpoints in this slice;
   - `vNext+79` may open checkpoints only for released ambiguity or escalation surfaces
     that are hybrid-eligible under the frozen route law above;
   - this slice may not reinterpret deterministic structural failures as oracle
     candidates or use the hybrid lane to weaken deterministic compiler authority.
7. Oracle-request replay strategy:
   - `adeu_architecture_oracle_request@1` may be emitted only when
     `checkpoint_class = oracle_needed`;
   - request identity must pin at least:
     - `intent_packet_hash`
     - `semantic_hash`
     - `conformance_report_ref`
     - `policy_source_hashes`
     - `model_id`
     - `model_version`
     - `reasoning_effort`
     - `prompt_template_version`
     - `compiler_version`
     - bounded local context identity
   - cache reuse is allowed only when the full pinned request identity matches exactly.
8. Oracle-resolution strategy:
   - `adeu_architecture_oracle_resolution@1` must bind one resolution to one exact
     request;
   - the starter `resolution_state` vocabulary must be exactly:
     - `advisory_support`
     - `advisory_reject`
     - `inconclusive`
     - `contradictory`
   - legal `resolution_state -> final_adjudication` mapping must be frozen exactly as:
     - `advisory_support -> resolved_pass`
     - `advisory_reject -> resolved_fail`
     - `inconclusive -> escalated_human`
     - `contradictory -> escalated_human`
     - replay mismatch -> `escalated_human`
   - the resolution must carry model/version provenance and `raw_output_hash`;
   - oracle output remains advisory only and may not mint new authority, new
     capability, new boundary class, or widened scope;
   - contradictory, unstable, or replay-mismatched resolutions must fail closed into
     human escalation.
9. Typed-repair strategy:
   - `adeu_architecture_ir_delta@1` is the only legal repair-shaped output in this
     slice;
   - every delta must bind back to the exact proposing oracle resolution;
   - it may propose edits only against already-existing ASIR refs or explicitly
     pre-authorized placeholder refs;
   - `operation_set` must remain typed and bounded;
   - it may not become direct repo mutation, patch payload emission, or scope widening
     in `vNext+79`;
   - it may not introduce new root ids except explicitly pre-authorized placeholders;
   - it may not silently delete or rewrite authority provenance;
   - any proposed delta becomes effective only after deterministic revalidation of the
     candidate ASIR in a later lawful lane.
10. Path decomposition strategy:
   - `vNext+79` is the first concrete `V40-C` arc;
   - broader hybrid-branch coverage, richer replay diagnostics, or deeper repair-delta
     handling may remain available for a later concrete `V40-C` slice if needed.

## Required Deliverables

1. New typed hybrid artifact surfaces inside the existing compiler package:
   - export the four activated hybrid artifact families from
     `packages/adeu_architecture_compiler`;
   - wire schema-export helpers needed for authoritative and mirrored JSON-schema
     output.
2. Canonical hybrid artifacts:
   - `adeu_architecture_oracle_request@1`
   - `adeu_architecture_oracle_resolution@1`
   - `adeu_architecture_checkpoint_trace@1`
   - `adeu_architecture_ir_delta@1`
3. Deterministic hybrid entrypoints that:
   - consume released `adeu_architecture_semantic_ir@1` and released
     `adeu_architecture_conformance_report@1` plus any exact released companion inputs
     needed for checkpoint context;
   - deterministically classify checkpoints from released ambiguity and escalation
     context;
   - materialize request, resolution, delta, and checkpoint-trace artifacts under the
     frozen vocabularies above;
   - keep the deterministic adjudicator authoritative over final checkpoint
     disposition;
   - fail closed on contradiction, replay mismatch, unsupported route/class
     combinations, or authority-drift attempts.
4. Top-level schema anchors for `adeu_architecture_oracle_request@1`:
   - `schema`
   - `request_id`
   - `architecture_id`
   - `semantic_hash`
   - `conformance_report_ref`
   - `checkpoint_id`
   - `ambiguity_ref`
   - `checkpoint_class`
   - `replay_identity`
   - `policy_source_hashes`
   - `model_id`
   - `model_version`
   - `reasoning_effort`
   - `prompt_template_version`
   - `compiler_version`
   - `context_refs`
5. Top-level schema anchors for `adeu_architecture_oracle_resolution@1`:
   - `schema`
   - `resolution_id`
   - `request_id`
   - `checkpoint_id`
   - `architecture_id`
   - `semantic_hash`
   - `model_id`
   - `model_version`
   - `reasoning_effort`
   - `raw_output_hash`
   - `resolution_state`
   - `proposed_delta_ref`
6. Top-level schema anchors for `adeu_architecture_ir_delta@1`:
   - `schema`
   - `delta_id`
   - `architecture_id`
   - `semantic_hash`
   - `checkpoint_id`
   - `source_resolution_id`
   - `scope_ref`
   - `target_refs`
   - `authorized_placeholder_refs`
   - `operation_set`
7. Top-level schema anchors for `adeu_architecture_checkpoint_trace@1`:
   - `schema`
   - `trace_id`
   - `architecture_id`
   - `semantic_hash`
   - `conformance_report_ref`
   - `compiler_version`
   - `hybrid_policy_hashes`
   - `adjudicator`
   - `checkpoint_entries`
   - every `checkpoint_entries` item must bind at least:
     - `checkpoint_id`
     - `ambiguity_ref`
     - `checkpoint_class`
     - `resolution_route`
      - `oracle_request_ref`
      - `oracle_resolution_ref`
      - `final_adjudication`
      - `replay_identity_hash`
   - oracle refs must obey exact nullability law in this slice:
     - for `deterministic_pass` and `deterministic_fail`, both refs must be absent or
       null;
     - for `human_needed`, both refs must be absent or null;
     - for `oracle_needed`, `oracle_request_ref` is required and
       `oracle_resolution_ref` is required only after a resolution exists in the
       recorded fixture or state.
8. Deterministic hybrid laws that fail closed on at least:
   - any `resolution_route -> checkpoint_class` transition outside the frozen legal
     route table;
   - an oracle request emitted for any checkpoint class other than `oracle_needed`;
   - any attempt to open a hybrid checkpoint from failed required deterministic checks
     that are not hybrid-eligible ambiguity or escalation surfaces;
   - a `human_needed` checkpoint that does not end in `escalated_human`;
   - any `checkpoint_class -> final_adjudication` transition outside the frozen legal
     table;
   - any `resolution_state -> final_adjudication` transition outside the frozen legal
     mapping above;
   - contradictory, inconclusive, or replay-mismatched oracle resolution claimed as
     `resolved_pass` or `resolved_fail`;
   - an oracle resolution or proposed delta that attempts to mint new authority, new
     capability, new boundary class, or widened scope;
   - more than one oracle round trip for a single checkpoint.
9. Committed reference fixtures:
   - one accepted deterministic-pass checkpoint trace with no oracle request;
   - one accepted oracle-assisted fixture set covering request, resolution, delta, and
     checkpoint trace artifacts;
   - one accepted human-needed direct-escalation checkpoint trace with no oracle
     request;
   - one rejected contradictory or invalid-replay fixture proving fail-closed hybrid
     behavior.
10. Python tests covering:
   - schema/model validation for all four activated hybrid artifacts;
   - authoritative/mirrored schema export parity;
   - deterministic classifier vocabulary and final-adjudication transition law;
   - exact replay-identity enforcement for request, resolution, and cache reuse;
   - one-round oracle enforcement;
   - advisory-only oracle boundary and fail-closed contradiction handling;
   - bounded `ir_delta` scope and authority guardrails;
   - rejection of projection, lowering, or workbench surfaces inside the hybrid lane.

## Hard Constraints

- `vNext+79` may not reopen or redefine the released `V40-A` semantic-root contract.
- `vNext+79` may not reopen or redefine the released `V40-B` conformance-report
  contract.
- `vNext+79` may not ship:
  - `adeu_architecture_projection_bundle@1`,
  - `adeu_architecture_projection_manifest@1`,
  - `adeu_core_ir` lowerings,
  - UX lowerings,
  - API or web human-review workbench routes,
  - direct repo mutation,
  - patch-payload emission,
  - direct prompt-to-code generation.
- Oracle output is advisory only in this slice:
  - it may interpret a checkpoint,
  - it may not itself authorize repo mutation or emitted downstream surfaces.
- `adeu_architecture_ir_delta@1` remains proposal-only in this slice and may not be
  treated as an applied mutation.
- The checkpoint trace may not be used to imply emitted projection surfaces exist or
  that lowering is already authorized.
- Multi-round oracle loops remain out of scope in the first baseline.
- The formal Lean sidecar may mirror frozen finite hybrid law only:
  - it is not required for slice validity,
  - it may not silently redefine the released hybrid contract.

## PR Shape

- Two tightly sequenced PRs within one arc.

Rationale:

- hybrid schema/model/export scaffolding is one natural seam;
- classifier, adjudication, replay/guard tests, and committed fixtures are a second
  seam;
- keeping them split preserves the repo’s usual arc scale without widening the slice
  itself.
