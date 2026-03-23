# Locked Continuation vNext+78

Status: `V40-B` implementation contract.

## V78 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v40b_architecture_deterministic_assembly_contract@1",
  "target_arc": "vNext+78",
  "target_path": "V40-B",
  "target_scope": "architecture_deterministic_assembly_conformance_and_gating_baseline",
  "semantic_ir_schema": "adeu_architecture_semantic_ir@1",
  "conformance_report_schema": "adeu_architecture_conformance_report@1",
  "implementation_package": "adeu_architecture_compiler",
  "upstream_root_package": "adeu_architecture_ir",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "decomposition_doc": "docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v18.md"
}
```

## Slice

- Arc label: `vNext+78`
- Family label: `V40-B`
- Scope label: architecture deterministic assembly, conformance, and gating baseline

## Objective

Introduce the first concrete ASIR deterministic compiler slice by activating the
compiler package and freezing the validation/conformance surface that consumes the
released `V40-A` semantic-root family without reopening it.

This slice establishes the first repo-native deterministic compiler substrate for:

- `packages/adeu_architecture_compiler`
- deterministic validation-context assembly from released root-family artifacts
- section-local validators for ontology, epistemics, deontics, and utility
- whole-ASIR integrity checks
- canonical `adeu_architecture_conformance_report@1`
- stable deterministic check ids
- pre-projection `blocked` vs `ready` gating

This slice remains deliberately prior to:

- checkpoint/oracle/human ambiguity execution;
- `adeu_architecture_checkpoint_trace@1`;
- `adeu_architecture_oracle_request@1` or
  `adeu_architecture_oracle_resolution@1`;
- `adeu_architecture_projection_bundle@1` or
  `adeu_architecture_projection_manifest@1`;
- `adeu_core_ir` or UX lowerings.

Its job is to make ASIR deterministically assemblable and gateable before any mixed-
confidence or downstream projection surface tries to consume it.

## Frozen Implementation Decisions

1. First active compiler package:
   - activate `packages/adeu_architecture_compiler` in `vNext+78`;
   - `packages/adeu_architecture_ir` remains authoritative for released root-family
     schemas and fixtures and may not be silently redefined by compiler-local
     vocabulary.
2. Upstream consumption strategy:
   - `vNext+78` must consume released `V40-A` semantic-root artifacts and committed
     v77 reference fixtures or exact validated derivatives thereof;
   - it may not bypass the released root family with free-floating checkpoint,
     projection, or lowering fixtures;
   - deterministic compiler context must bind back to released
     `adeu_architecture_semantic_ir@1` and its companion root artifacts.
3. Conformance report strategy:
   - `adeu_architecture_conformance_report@1` is the only newly released artifact
     family in this slice;
   - authoritative JSON schema must live under
     `packages/adeu_architecture_compiler/schema/`;
   - mirrored export must live under `spec/`;
   - the report must carry deterministic consumed-root lineage via repo-relative refs
     and hashes sufficient to replay the exact released root inputs it evaluated;
   - the `compiler` object in the report must carry compiler version and config/profile
     provenance sufficient for deterministic replay;
   - `human_escalation_refs` in this slice is static deterministic escalation lineage
     only and may not point to checkpoint trace ids, oracle artifacts, or hybrid-state
     surfaces;
   - the report carries deterministic readiness/gating only and must not collapse into
     checkpoint trace, projection manifest, or emitted lowering authority.
4. Deterministic validator strategy:
   - `vNext+78` must release section-local validator passes for:
     - ontology
     - epistemics
     - deontics
     - utility
   - it must also release one whole-ASIR integrity pass over the assembled semantic
     root;
   - stable check-id families must start with:
     - `ASIR-O-xxx`
     - `ASIR-E-xxx`
     - `ASIR-D-xxx`
     - `ASIR-U-xxx`
     - `ASIR-P-xxx`
   - in this slice, `ASIR-P-xxx` is limited to pre-projection readiness honesty,
     blocked/ready correctness, and empty emitted-artifact posture rather than
     projection-manifest integrity;
   - `ASIR-H-xxx` remains deferred to `V40-C`.
5. Gating strategy:
   - the conformance report must classify compile readiness as exactly:
     - `ready`
     - `blocked`
   - `ready` is legal only when no failed required checks and no blocking ambiguity refs
     remain;
   - every emitted `check_result` must carry `required: true|false`, and only failed
     `required = true` checks may block readiness;
   - `blocked` must carry explicit failed-check and blocking-ref lineage;
   - `ready` in this slice does not imply any emitted projection surface exists.
6. Path decomposition strategy:
   - `vNext+78` is the first concrete `V40-B` arc;
   - richer validator breadth, additional accepted fixture ladders, or wider diagnostic
     coverage may remain available for a later concrete `V40-B` slice if needed.

## Required Deliverables

1. New typed ASIR compiler package surface:
   - create `packages/adeu_architecture_compiler`;
   - export deterministic compiler helpers and the conformance-report artifact family;
   - wire schema export helpers needed for authoritative and mirrored JSON-schema output.
2. Canonical deterministic compiler artifact:
   - `adeu_architecture_conformance_report@1`
3. Deterministic compiler entrypoints that:
   - consume released `adeu_architecture_semantic_ir@1` plus any exact released
     companion root-family artifacts needed for validation context;
   - run section-local validators for ontology, epistemics, deontics, and utility;
   - run one whole-ASIR integrity pass;
   - materialize `adeu_architecture_conformance_report@1`;
   - record exact consumed-root lineage and any static deterministic human-escalation
     lineage in the report;
   - fail closed when root semantics are invalid or cross-section integrity is broken.
4. Top-level schema anchors for `adeu_architecture_conformance_report@1`:
   - `schema`
   - `architecture_id`
   - `semantic_hash`
   - `compiler`
   - `consumed_root_refs`
   - `projection_readiness`
   - `blocking_ambiguity_refs`
   - `failed_check_ids`
   - `human_escalation_refs`
   - `emitted_artifact_refs`
   - `check_results`
   - every `check_results` entry must bind at least:
     - `check_id`
     - `required`
     - `passed`
     - `subject_refs`
5. Deterministic validation laws that fail closed on at least:
   - a cross-boundary step with no declared boundary;
   - an authoritative decision with no `authority_source_ref`;
   - a missing evidence-before-commit rule where one is required;
   - broken cross-section references that should resolve within the assembled ASIR;
   - a high or critical ambiguity that remains unresolved while readiness is claimed as
     `ready`.
6. Conformance/gating law:
   - `projection_readiness = ready` must be impossible when:
     - `blocking_ambiguity_refs` is non-empty; or
     - `human_escalation_refs` is non-empty; or
     - any required deterministic check fails;
   - `projection_readiness = blocked` must preserve explicit failed-check and blocking
     ambiguity lineage;
   - `human_escalation_refs` must remain static deterministic escalation lineage only
     and may not cite checkpoint trace ids or hybrid artifact refs in this slice;
   - `emitted_artifact_refs` must be present but empty in this slice;
   - no projection bundle, projection manifest, or checkpoint trace artifact may be
     emitted in `vNext+78`.
7. Committed reference fixtures:
   - one accepted deterministic compiler fixture ladder under
     `apps/api/fixtures/architecture/vnext_plus78/` covering:
     - released root-family inputs
     - canonical conformance report output
   - the accepted fixture ladder must prove:
     - deterministic conformance replay,
     - stable check-id emission,
     - explicit blocked vs ready gating.
8. Python tests covering:
   - schema/model validation for `adeu_architecture_conformance_report@1`;
   - authoritative/mirrored schema export parity;
   - deterministic conformance replay from the accepted fixture ladder;
   - section-local and whole-ASIR fail-closed validation;
   - blocked/ready gating behavior;
   - rejection of hybrid, projection, or lowering artifacts inside the conformance lane.

## Hard Constraints

- `vNext+78` may not reopen or redefine the released `V40-A` root-family schema
  contract.
- `vNext+78` may not ship:
  - `adeu_architecture_checkpoint_trace@1`,
  - `adeu_architecture_oracle_request@1`,
  - `adeu_architecture_oracle_resolution@1`,
  - `adeu_architecture_projection_bundle@1`,
  - `adeu_architecture_projection_manifest@1`,
  - `adeu_core_ir` lowerings,
  - UX lowerings,
  - API or web workbench routes,
  - direct prompt-to-code generation.
- `ASIR-H-xxx` hybrid check ids remain out of scope in this slice.
- `ASIR-P-xxx` may not be used in this slice to imply released projection-manifest or
  bundle integrity checking.
- `projection_readiness = ready` may not be used to imply emitted downstream surfaces
  exist.
- `human_escalation_refs` may not point to checkpoint trace ids, oracle artifacts, or
  any implied `V40-C` release surface.
- The formal Lean sidecar may mirror frozen finite gating law only:
  - it is not required for slice validity,
  - it may not silently redefine the released compiler contract.

## PR Shape

- Two tightly sequenced PRs within one arc.

Rationale:

- deterministic compiler scaffolding and check-id/report grammar are one natural seam;
- committed conformance fixtures and replay/guard tests are a second seam;
- keeping them split preserves the repo’s usual arc scale without widening the slice
  itself.
