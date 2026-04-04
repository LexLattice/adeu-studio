# Locked Continuation vNext+127

Status: `V52-A` implementation contract.

## V127 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v52a_paper_semantic_contract_package@1",
  "target_arc": "vNext+127",
  "target_path": "V52-A",
  "target_scope": "bounded_repo_owned_paper_semantic_contract_package_for_abstract_scale_paper_artifacts",
  "implementation_packages": [
    "adeu_paper_semantics"
  ],
  "governing_released_stack": "V49_semantic_forms_as_required_substrate_plus_V50_V51_as_adjacent_context_on_main",
  "governing_stack_consumption_mode": "v49_identity_and_hash_law_reuse_or_explicit_narrow_paper_domain_delta_required_v50_v51_context_only_not_reopened",
  "source_intake_bundle": "examples/external_prototypes/adeu-paper-semantic-workbench-poc",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "paper_semantics_package_scaffold_required": true,
  "selected_schema_ids": [
    "adeu_paper_source_artifact@1",
    "adeu_paper_source_span@1",
    "adeu_paper_semantic_claim@1",
    "adeu_paper_semantic_lane_fragment@1",
    "adeu_paper_semantic_inference_bridge@1",
    "adeu_paper_semantic_diagnostic@1",
    "adeu_paper_semantic_projection@1",
    "adeu_paper_semantic_artifact@1",
    "adeu_paper_semantic_worker_request@1"
  ],
  "bounded_source_artifact_kinds_frozen": [
    "paper.abstract",
    "pasted.paragraph"
  ],
  "paper_abstract_digest_not_selected_here": true,
  "full_paper_semantics_not_selected_here": true,
  "source_authority_posture_frozen": "source_text_and_explicit_span_anchors_authoritative",
  "interpretation_authority_posture_frozen": "advisory_only_not_ground_truth_not_policy_authority",
  "worker_request_contract_models_required": true,
  "bounded_lane_vocabulary_frozen": [
    "O",
    "E",
    "D",
    "U"
  ],
  "requested_depth_vocabulary_frozen": [
    1,
    2
  ],
  "analysis_mode_frozen": "evidence_first",
  "preserve_source_anchor_required": true,
  "v49_canonical_hash_law_consumption_required": true,
  "explicit_paper_domain_identity_delta_declaration_required": true,
  "identity_projection_split_required": true,
  "diagnostic_and_projection_fields_excluded_from_semantic_hash": true,
  "schema_export_or_model_schema_coverage_required": true,
  "sample_artifact_validation_required": true,
  "web_surface_not_selected_here": true,
  "worker_bridge_not_selected_here": true,
  "advanced_visualization_not_selected_here": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v35.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md",
    "docs/DRAFT_ADEU_PAPER_SEMANTICS_V52A_IMPLEMENTATION_MAPPING_v0.md",
    "examples/external_prototypes/adeu-paper-semantic-workbench-poc/ALIGNMENT.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v35.md"
}
```

## Slice

- Arc label: `vNext+127`
- Family label: `V52-A`
- Scope label: bounded repo-owned paper semantic contract package for abstract-scale
  artifacts

## Objective

Release the bounded `V52-A` contract lane by creating the first repo-owned
`adeu_paper_semantics` package and freezing one typed paper semantic contract set rich
enough to:

- declare one bounded source-artifact family over:
  - `paper.abstract`
  - `pasted.paragraph`
- declare one explicit source-authority posture where source text plus explicit span
  anchors remain authoritative;
- declare one explicit advisory-only interpretation posture where semantic output is
  diagnostic and analytic rather than ground truth, policy authority, or workflow
  entitlement;
- declare first-class typed models for:
  - source artifacts;
  - source spans;
  - semantic claims;
  - O/E/D/U lane fragments;
  - inference bridges;
  - diagnostics;
  - bounded projections;
  - top-level paper semantic artifacts;
  - worker request contracts;
- prove the first bounded paper-domain consumer posture over released `V49` by
  reusing the released identity-vs-projection and canonical-hash law where selected,
  or declaring one narrow paper-domain delta explicitly instead of silently minting a
  parallel substrate;
- freeze the worker request operator posture as:
  - `analysis_mode = evidence_first`
  - `authority_mode = advisory_only`
  - `preserve_source_anchor = true`
- fail closed on malformed source anchors, malformed diagnostics, invalid request
  posture, or mismatched semantic hashes rather than repairing them ambiently.

This slice is package-first and pre-consumer. It does not authorize live web routes,
mock workbench consumers, worker/domain registration, advanced visualization, or
direct import of the prototype overlay into live repo paths.

## Frozen Implementation Decisions

1. Package-ownership strategy:
   - `packages/adeu_paper_semantics` is the sole implementation owner in this slice;
   - the imported intake bundle remains shaping evidence only and may not be treated
     as the live package surface.
2. Bounded source-artifact strategy:
   - the first released source-artifact kinds are exactly:
     - `paper.abstract`
     - `pasted.paragraph`
   - `paper.abstract_digest` is explicitly later;
   - full-paper and multi-section semantics are explicitly later;
   - the first slice should be read as abstract/paragraph scale only.
3. `V49` consumption strategy:
   - `V52-A` is the first bounded domain-proof consumer of the released `V49`
     substrate;
   - it must not silently invent a second semantic substrate;
   - it must either:
     - reuse released `V49` canonical identity and hash posture directly where
       selected; or
     - declare one narrow paper-domain delta explicitly and visibly in the contract;
   - projection/support fields must remain excluded from semantic identity and
     semantic hash.
4. Artifact-family strategy:
   - the first released package must keep the key paper-domain substructures as
     first-class typed models in `models.py`;
   - that first-class set must include:
     - `PaperSourceArtifact`
     - `PaperSourceSpan`
     - `PaperSemanticClaim`
     - `PaperSemanticLaneFragment`
     - `PaperSemanticInferenceBridge`
     - `PaperSemanticDiagnostic`
     - `PaperSemanticProjection`
     - `PaperSemanticArtifact`
     - `PaperSemanticWorkerRequest`
   - the slice may not collapse that ontology into one broad untyped workbench blob.
5. Authority-posture strategy:
   - source text and explicit span anchors remain authoritative;
   - inferred lane fragments and diagnostics remain advisory only;
   - diagnostics may summarize interpretation risk, contradiction, underdetermination,
     or missing bridges, but may not become semantic ground truth by themselves.
6. Worker-request strategy:
   - the first released request contract is contract-only and pre-execution;
   - it must preserve source anchoring and evidence-first analysis posture;
   - it must not authorize live worker execution, domain-template registration, or
     route widening in this slice.
7. Projection strategy:
   - bounded projections are allowed as typed package contracts only;
   - advanced spatial or richer visualization posture is explicitly later;
   - projection fields are support/projection only and excluded from semantic hash.
8. Widening strategy:
   - no `/papers/semantic-workbench` route here;
   - no `urm_domain_paper` or `urm_domain_adeu` bridge here;
   - no advanced visualization here;
   - no direct import of the prototype overlay schema or route tree into live repo
     paths here.

## Bounded Starter Vocabularies

The first `V52-A` release should freeze bounded starter vocabularies rather than leave
the family open-ended.

The intended bounded starter vocabularies are:

- `source_artifact_kind`:
  - `paper.abstract`
  - `pasted.paragraph`
- `lane_id`:
  - `O`
  - `E`
  - `D`
  - `U`
- `requested_depth`:
  - `1`
  - `2`
- `fragment_source_kind`:
  - `explicit`
  - `inferred`
- `fragment_status`:
  - `explicit`
  - `inferred`
  - `contested`
  - `underdetermined`
  - `missing`
- `claim_status`:
  - `stable`
  - `contested`
  - `underdetermined`
- `bridge_kind`:
  - `canonical_bridge`
  - `supporting_bridge`
  - `missing_bridge`
  - `contested_bridge`
  - `projection_bridge`
  - `contradiction_bridge`
- `diagnostic_kind`:
  - `contradiction`
  - `underdetermination`
  - `missing_bridge`
  - `overloaded_term`
  - `implicit_assumption`
  - `u_overreach`
- `diagnostic_severity`:
  - `critical`
  - `warning`
  - `advisory`
- `projection_surface`:
  - `artifact`
  - `local`

Out-of-scope constructs in this slice are:

- `paper.abstract_digest`
- full-paper section or citation-graph semantics
- live web rendering surfaces
- live worker execution or domain-template registration
- spatial / morphic visualization
- silent parallel semantic substrate invention

## Selected Schema Anchors

The first `V52-A` release should freeze the following contract anchors.

1. `adeu_paper_source_artifact@1`
   - `source_id`
   - `artifact_kind`
   - `title`
   - `authors`
   - `year`
   - `source_text`
   - `source_text_hash`
   - `paragraph_index`
2. `adeu_paper_source_span@1`
   - `span_id`
   - `start`
   - `end`
   - `quote`
   - `sentence_index`
   - `paragraph_index`
3. `adeu_paper_semantic_claim@1`
   - `claim_id`
   - `claim_text`
   - `status`
   - `span_ids`
   - `lane_fragment_ids`
4. `adeu_paper_semantic_lane_fragment@1`
   - `fragment_id`
   - `claim_id`
   - `lane_id`
   - `fragment_text`
   - `source_kind`
   - `status`
   - `confidence`
   - `warrant`
   - `span_ids`
   - `bridge_ids`
   - `diagnostic_ids`
5. `adeu_paper_semantic_inference_bridge@1`
   - `bridge_id`
   - `bridge_kind`
   - `from_fragment_ids`
   - `to_fragment_ids`
   - `rationale`
6. `adeu_paper_semantic_diagnostic@1`
   - `diagnostic_id`
   - `diagnostic_kind`
   - `severity`
   - `summary`
   - `span_ids`
   - `related_fragment_ids`
7. `adeu_paper_semantic_projection@1`
   - `projection_id`
   - `surface`
   - `lane_order`
   - `claim_order`
   - `diagnostic_summary`
8. `adeu_paper_semantic_artifact@1`
   - `artifact_id`
   - `source`
   - `spans`
   - `claims`
   - `lane_fragments`
   - `inference_bridges`
   - `diagnostics`
   - `projections`
   - `source_authority_posture`
   - `interpretation_authority_posture`
   - `semantic_identity_mode`
   - `semantic_hash`
9. `adeu_paper_semantic_worker_request@1`
   - `request_id`
   - `source_text`
   - `source_kind`
   - `requested_depth`
   - `return_schema`
   - `operator_posture`
   - `constraints`
   - `request_hash`

## Acceptance Fixtures

The first `V52-A` release should ship deterministic reference and reject fixtures.

Required accepted fixtures:

- one canonical `paper.abstract` worker request fixture;
- one canonical `pasted.paragraph` worker request fixture;
- one canonical abstract-scale paper semantic artifact fixture;
- one canonical paragraph-scale paper semantic artifact fixture.

Required reject or mutation fixtures:

- one malformed span-anchor fixture;
- one invalid diagnostic-kind fixture;
- one projection-only mutation fixture proving semantic hash stability;
- one identity-field mutation fixture proving semantic hash change;
- one invalid worker-request posture fixture.

## Acceptance Criteria

`V52-A` is ready to implement only if the slice can satisfy all of the following.

1. `packages/adeu_paper_semantics` is the sole live owner of the first paper semantic
   contract set.
2. The emitted contract family stays bounded to `paper.abstract` and
   `pasted.paragraph`.
3. The released `V49` identity-vs-projection and canonical-hash posture is reused or
   one narrow paper-domain delta is declared explicitly in live contract code.
4. Projection/support fields do not change `semantic_hash`.
5. Identity-field mutations do change `semantic_hash`.
6. Worker request posture is evidence-first, advisory-only, and
   `preserve_source_anchor = true`.
7. Sample artifact validation and model-schema coverage run through repo-native tests.
8. No live web route, worker bridge, or advanced visualization ships in this slice.

## Local Gate

The local gate for this slice is:

- relevant package lint and tests only for the bounded new package;
- broader Python and product lanes remain out of scope unless the implementation
  itself forces wider integration work.
