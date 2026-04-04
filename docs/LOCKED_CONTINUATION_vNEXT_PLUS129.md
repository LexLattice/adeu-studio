# Locked Continuation vNext+129

Status: `V52-C` implementation contract.

## V129 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v52c_paper_semantic_worker_bridge_contract@1",
  "target_arc": "vNext+129",
  "target_path": "V52-C",
  "target_scope": "bounded_repo_owned_live_worker_request_response_bridge_over_released_v52a_worker_request_contract",
  "implementation_packages": [
    "adeu_paper_semantics",
    "urm_domain_paper"
  ],
  "governing_released_stack": "V49_semantic_forms_plus_V52-A_paper_semantics_plus_V52-B_mock_workbench_on_main",
  "governing_stack_consumption_mode": "released_v52a_worker_request_consumption_only_v52b_route_not_authoritative_no_parallel_paper_substrate",
  "source_intake_bundle": "examples/external_prototypes/adeu-paper-semantic-workbench-poc",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "selected_schema_ids": [
    "adeu_paper_semantic_worker_request@1",
    "adeu_paper_semantic_worker_bridge_result@1"
  ],
  "bridge_owner_surface_selected": "urm_domain_paper",
  "bridge_owner_surface_mode": "additive_extension_of_existing_domain_pack",
  "bridge_owner_surfaces_not_selected": [
    "urm_domain_adeu"
  ],
  "existing_paper_domain_tools_must_remain_unchanged": [
    "paper.ingest_text",
    "paper.extract_abstract_candidate",
    "paper.check_constraints",
    "paper.emit_artifact"
  ],
  "existing_default_template_id_retained": "paper.abstract.pipeline.v0",
  "new_tool_is_additive_not_superseding": true,
  "selected_tool_names": [
    "paper.run_semantic_decomposition"
  ],
  "selected_template_id": "paper.semantic_decomposition.v0",
  "existing_api_surface_only": "urm_tool_call_endpoint",
  "new_dedicated_api_route_forbidden": true,
  "capability_policy_mapping_required": true,
  "released_v52a_worker_request_required": true,
  "released_v52b_route_context_not_authoritative": true,
  "worker_provider_frozen": "codex",
  "worker_role_frozen": "pipeline_worker",
  "worker_warrant_frozen": "checked",
  "return_schema_frozen": "adeu_paper_semantic_artifact@1",
  "bridge_status_vocabulary_frozen": [
    "completed_checked",
    "completed_checked_idempotent_replay",
    "fail_closed_invalid_request",
    "fail_closed_bridge_config_mismatch"
  ],
  "bridge_result_contains_worker_refs_only": true,
  "bridge_result_contains_artifact_ref_only": true,
  "bridge_result_contains_live_artifact_payload": false,
  "web_route_changes_forbidden": true,
  "prototype_workflow_overlay_import_forbidden": true,
  "advanced_visualization_forbidden": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v129_closeout.json",
    "artifacts/stop_gate/metrics_v129_closeout.json",
    "artifacts/stop_gate/report_v129_closeout.md"
  ]
}
```

## Objective

Release the bounded `V52-C` worker-bridge seam by adding one repo-owned
`paper.run_semantic_decomposition` domain-tool surface under `urm_domain_paper` that
consumes exactly one released `adeu_paper_semantic_worker_request@1`, delegates
through existing URM worker-run surfaces in read-only posture, and emits one typed
bridge result that carries worker/evidence refs only.

This slice extends the already released `urm_domain_paper` domain pack. It does not
instantiate a brand-new owner surface, and it must remain additive with respect to the
existing closed-world `paper.abstract` tool family already shipped from that package.

This slice must make explicit:

- one bridge-owner surface only:
  - `packages/urm_domain_paper`
- one admitted live bridge tool only:
  - `paper.run_semantic_decomposition`
- one admitted template id only:
  - `paper.semantic_decomposition.v0`
- one admitted input contract only:
  - released `adeu_paper_semantic_worker_request@1`
- one emitted success artifact only:
  - `adeu_paper_semantic_worker_bridge_result@1`
- one evidence-bearing live result posture only:
  - worker/evidence refs
  - artifact ref
  - warrant tag
  - request lineage
  - no rendered semantic artifact payload
- one explicit non-selection posture only:
  - `V52-B` route-local view config is not an authoritative bridge input in this slice.

This slice is bridge-first and still bounded. It does not authorize direct
`apps/web` fetch wiring, a new dedicated API route, prototype workflow-overlay
import, live artifact readback/rendering, or advanced visualization.

## Required Deliverables

The first `V52-C` release should add exactly these live implementation surfaces:

- `packages/urm_domain_paper/src/urm_domain_paper/models.py`
- `packages/urm_domain_paper/src/urm_domain_paper/adapters.py`
- `packages/urm_domain_paper/src/urm_domain_paper/__init__.py`
- targeted bridge/domain verification in:
  - `apps/api/tests/test_urm_domain_tools.py`
  - and/or bounded `packages/urm_domain_paper` tests if needed

This slice should not add:

- new `apps/web` route code or live fetch wiring;
- a new dedicated `apps/api` paper-semantics route;
- `packages/urm_domain_adeu` ownership of the bridge seam;
- direct imports of the prototype overlay workflow code;
- advanced visualization or spatial scene work.

## Frozen Implementation Decisions

1. Ownership

- `packages/urm_domain_paper` already exists on `main` and is extended here as the
  bridge-owner surface.
- `packages/urm_domain_adeu` is not selected for bridge ownership in this slice.
- `packages/adeu_paper_semantics` remains the sole owner of paper semantic contract
  authority.
- the existing closed-world `paper.abstract` tool family remains released and
  non-superseded in this slice.

2. Input posture

- admit only released `adeu_paper_semantic_worker_request@1` as authoritative bridge
  input
- do not admit browser-local `selected_surface`, `focus_claim_id`, or other `V52-B`
  route-local view state as authoritative bridge input
- do not synthesize or repair:
  - `return_schema`
  - `operator_posture`
  - `constraints`
  - `request_hash`

3. Bridge posture

- ship exactly one bounded live bridge tool:
  - `paper.run_semantic_decomposition`
- keep that tool additive with respect to the already released paper-domain tools:
  - `paper.ingest_text`
  - `paper.extract_abstract_candidate`
  - `paper.check_constraints`
  - `paper.emit_artifact`
- expose it only through the existing URM tool-call surface
- use exactly one admitted template id:
  - `paper.semantic_decomposition.v0`
- do not change the existing domain-pack default template:
  - `paper.abstract.pipeline.v0`
- keep provider/role frozen to:
  - `codex`
  - `pipeline_worker`
- keep the worker run read-only and artifact-subordinate
- keep the expected return schema frozen to:
  - `adeu_paper_semantic_artifact@1`
- require one explicit capability-policy action mapping for:
  - `paper.run_semantic_decomposition`
- require bounded regression coverage proving the existing paper-domain tools remain
  behaviorally unchanged

4. Result posture

- emit one typed success result:
  - `adeu_paper_semantic_worker_bridge_result@1`
- freeze emitted bridge-status vocabulary to:
  - `completed_checked`
  - `completed_checked_idempotent_replay`
  - `fail_closed_invalid_request`
  - `fail_closed_bridge_config_mismatch`
- preserve request lineage explicitly:
  - `request_ref`
  - `request_hash`
- preserve live artifact identity explicitly:
  - `artifact_ref`
- preserve live worker refs explicitly:
  - `worker_id`
  - `evidence_id`
  - `worker_status`
  - `idempotent_replay`
- preserve epistemic posture explicitly:
  - `warrant_tag`
- do not parse, reinterpret, or re-render the live semantic artifact payload in this
  slice
- repeated bridge result construction over the same request plus the same worker-run
  result must be byte-identical

5. Forbidden widening

- no direct `apps/web` fetch or worker-trigger surface
- no new dedicated paper-semantics API route
- no live artifact readback or workbench rendering changes
- no direct import of the prototype `urm_domain_adeu` overlay workflow code
- no ownership laundering into `adeu_core_ir` or imported overlay schema files
- no advanced visualization or spatial scene work

## Bounded Starter Vocabularies

The first `V52-C` release should freeze:

- `tool_name`:
  - `paper.run_semantic_decomposition`
- `template_id`:
  - `paper.semantic_decomposition.v0`
- `provider`:
  - `codex`
- `role`:
  - `pipeline_worker`
- admitted source kinds:
  - `paper.abstract`
  - `pasted.paragraph`
- admitted requested depth:
  - `1`
  - `2`
- `warrant_tag`:
  - `checked`

Out-of-scope constructs in this slice are:

- browser-originated live worker triggers;
- upload-driven bridge input;
- direct `V52-B` local view-config consumption as authority;
- direct artifact rendering/readback in the bridge result;
- prototype workflow overlay imports;
- advanced visualization.

## Selected Schema Anchors

The first `V52-C` release should freeze these consumed request anchors:

- `adeu_paper_semantic_worker_request@1`
  - `schema`
  - `request_id`
  - `source_text`
  - `source_kind`
  - `requested_depth`
  - `return_schema`
  - `operator_posture`
  - `constraints`
  - `request_hash`

The first `V52-C` release should freeze these emitted result anchors:

- `adeu_paper_semantic_worker_bridge_result@1`
  - `schema`
  - `bridge_result_id`
  - `bridge_status`
  - `request_ref`
  - `request_hash`
  - `tool_name`
  - `template_id`
  - `template_version`
  - `domain_pack_id`
  - `domain_pack_version`
  - `provider`
  - `role`
  - `warrant_tag`
  - `artifact_ref`
  - `worker_id`
  - `evidence_id`
  - `worker_status`
  - `idempotent_replay`
  - `return_schema`
  - `bridge_hash`

## Acceptance Fixture Set

The first `V52-C` release should ship accepted coverage for:

- the released abstract worker-request fixture:
  - `reference_paper_semantic_worker_request_abstract.json`
- the released paragraph worker-request fixture:
  - `reference_paper_semantic_worker_request_paragraph.json`
- one deterministic success bridge result per admitted request kind
- one deterministic idempotent-replay bridge result over the same admitted request
- one bounded regression proving the existing paper-domain closed-world abstract flow
  remains unchanged

The first `V52-C` release should also ship reject coverage for:

- raw request payload with invalid `return_schema`
- raw request payload with invalid operator/authority posture drift
- missing capability-policy action mapping for `paper.run_semantic_decomposition`
- attempted bridge ownership/template drift into `urm_domain_adeu` or imported
  template id
- attempted browser-local view payload used in place of a released worker request

## Local Gate

- docs-only starter validation:
  - `make arc-start-check ARC=129`
- once implementation starts:
  - run the relevant `urm_domain_paper` and `apps/api` lint/tests for the bounded
    `V52-C` bridge surface.
