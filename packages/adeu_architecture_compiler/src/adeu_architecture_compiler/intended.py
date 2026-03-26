from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from adeu_architecture_ir import (
    AdeuArchitectureAnalysisRequest,
    AdeuArchitectureAnalysisSettlementFrame,
    canonicalize_adeu_architecture_boundary_graph_payload,
    canonicalize_adeu_architecture_intent_packet_payload,
    canonicalize_adeu_architecture_ontology_frame_payload,
    canonicalize_adeu_architecture_world_hypothesis_payload,
    materialize_adeu_architecture_semantic_ir_payload,
)

from .conformance import (
    _normalize_repo_relative_path,
    _resolve_repository_root,
)
from .observation import AdeuArchitectureObservationFrame

V41D_V86_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS86.md#v41d_practical_analysis_intended_compile_contract@1"
)

_ROOT_POLICY = {
    "no_direct_brief_to_codegen": True,
    "projections_may_express_but_may_not_mint_authority": True,
    "deterministic_adjudicator_authoritative": True,
    "oracle_output_advisory_only": True,
    "fail_closed_on_high_impact_ambiguity": True,
}
_DEFAULT_COMPILER = {
    "name": "adeu_architecture_ir.root_family",
    "version": "1",
    "scope": "root_family_only",
    "canonicalization_profile": "adeu_architecture_ir.root_family.v1",
    "schema_bundle_version": "v86-intended-root-family",
}
_ALLOWED_SUBTREE_PREFIX = "packages/adeu_architecture_ir/src/adeu_architecture_ir"


@dataclass(frozen=True)
class V41DValidatedInputs:
    analysis_request: AdeuArchitectureAnalysisRequest
    analysis_request_path: str
    settlement_frame: AdeuArchitectureAnalysisSettlementFrame
    settlement_frame_path: str
    observation_frame: AdeuArchitectureObservationFrame
    observation_frame_path: str
    repository_root: Path


@dataclass(frozen=True)
class V41DIntendedCompileBundle:
    analysis_request_id: str
    analysis_request_ref: str
    settlement_frame_id: str
    settlement_frame_ref: str
    observation_frame_id: str
    observation_frame_ref: str
    source_set_hash: str
    authority_boundary_policy: dict[str, Any]
    intent_packet_payload: dict[str, Any]
    ontology_frame_payload: dict[str, Any]
    boundary_graph_payload: dict[str, Any]
    world_hypothesis_payload: dict[str, Any]
    semantic_ir_payload: dict[str, Any]


def _slug(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", value.lower()).strip("_")


def _artifact_ref_path(ref: str) -> str:
    return ref.split("#", 1)[0]


def _root_policy_from_request(request: AdeuArchitectureAnalysisRequest) -> dict[str, Any]:
    if request.authority_boundary_policy.inline_policy is not None:
        return request.authority_boundary_policy.inline_policy.model_dump(
            mode="json",
            exclude_none=True,
        )
    return dict(_ROOT_POLICY)


def _source_ref_id(path: str) -> str:
    return f"src_{_slug(path)}"


def _request_source_set_payload(request: AdeuArchitectureAnalysisRequest) -> dict[str, Any]:
    return {
        "sources": [
            {
                "source_ref_id": _source_ref_id(item.path),
                "path": item.path,
                "sha256": item.sha256,
            }
            for item in request.source_set.items
        ]
    }


def _source_ref_id_by_path(request: AdeuArchitectureAnalysisRequest) -> dict[str, str]:
    return {item.path: _source_ref_id(item.path) for item in request.source_set.items}


def _request_ref_source_ids(
    refs: list[str],
    *,
    request: AdeuArchitectureAnalysisRequest,
    field_name: str,
) -> list[str]:
    source_id_by_path = _source_ref_id_by_path(request)
    resolved: list[str] = []
    for ref in refs:
        path = _artifact_ref_path(ref)
        source_id = source_id_by_path.get(path)
        if source_id is None:
            raise ValueError(
                f"{field_name} must resolve to source_set items in this first V41-D baseline"
            )
        resolved.append(source_id)
    return sorted(set(resolved))


def _validate_v41d_inputs(
    *,
    analysis_request_payload: dict[str, Any],
    analysis_request_path: str,
    settlement_frame_payload: dict[str, Any],
    settlement_frame_path: str,
    observation_frame_payload: dict[str, Any],
    observation_frame_path: str,
    repository_root: Path | None = None,
) -> V41DValidatedInputs:
    root = _resolve_repository_root(repository_root)
    normalized_request_path = _normalize_repo_relative_path(
        analysis_request_path,
        field_name="analysis_request_path",
    )
    normalized_settlement_path = _normalize_repo_relative_path(
        settlement_frame_path,
        field_name="settlement_frame_path",
    )
    normalized_observation_path = _normalize_repo_relative_path(
        observation_frame_path,
        field_name="observation_frame_path",
    )

    request = AdeuArchitectureAnalysisRequest.model_validate(
        analysis_request_payload,
        context={"repository_root": root},
    )
    settlement = AdeuArchitectureAnalysisSettlementFrame.model_validate(
        settlement_frame_payload,
        context={"repository_root": root, "analysis_request": request},
    )
    observation = AdeuArchitectureObservationFrame.model_validate(
        observation_frame_payload,
        context={
            "repository_root": root,
            "analysis_request": request,
            "analysis_settlement": settlement,
        },
    )

    if settlement.analysis_request_ref != normalized_request_path:
        raise ValueError(
            "settlement_frame.analysis_request_ref must match the consumed analysis_request_path"
        )
    if observation.analysis_request_ref != normalized_request_path:
        raise ValueError(
            "observation_frame.analysis_request_ref must match the consumed analysis_request_path"
        )
    if observation.settlement_frame_ref != normalized_settlement_path:
        raise ValueError(
            "observation_frame.settlement_frame_ref must match the consumed settlement_frame_path"
        )
    if settlement.compile_entitlement != "entitled":
        raise ValueError(
            "V41-D intended compile requires released compile_entitlement=entitled"
        )
    if settlement.blocking_lineage:
        raise ValueError("entitled V41-D settlement must not carry blocking_lineage")
    if observation.upstream_compile_entitlement != "entitled":
        raise ValueError(
            "observation_frame must carry through upstream_compile_entitlement=entitled"
        )
    if observation.upstream_blocking_refs:
        raise ValueError("entitled V41-D observation_frame must not carry upstream_blocking_refs")
    if not request.accepted_doc_refs:
        raise ValueError("V41-D intended compile requires at least one accepted_doc_ref")
    if not request.maintainer_brief_refs:
        raise ValueError("V41-D intended compile requires at least one maintainer_brief_ref")
    if not request.request_scope.subtree_root.startswith(_ALLOWED_SUBTREE_PREFIX):
        raise ValueError(
            "v86 is intentionally bounded to the released adeu_architecture_ir package slice"
        )

    return V41DValidatedInputs(
        analysis_request=request,
        analysis_request_path=normalized_request_path,
        settlement_frame=settlement,
        settlement_frame_path=normalized_settlement_path,
        observation_frame=observation,
        observation_frame_path=normalized_observation_path,
        repository_root=root,
    )


def _bundle_ids(validated: V41DValidatedInputs) -> dict[str, str]:
    scope_slug = _slug(validated.analysis_request.request_scope.subtree_root)
    return {
        "intent_packet_id": f"intent_v86_{scope_slug}_repo_grounded_compile",
        "ontology_frame_id": f"ont_v86_{scope_slug}_repo_grounded_compile",
        "boundary_graph_id": f"bg_v86_{scope_slug}_repo_grounded_compile",
        "candidate_id": f"cand_v86_{scope_slug}_request_bound_intended_world",
        "architecture_id": f"asir_v86_{scope_slug}_repo_grounded_compile",
    }


def _build_intent_packet_payload(
    validated: V41DValidatedInputs,
    ids: dict[str, str],
) -> dict[str, Any]:
    request = validated.analysis_request
    package_name = Path(request.request_scope.subtree_root).name
    return canonicalize_adeu_architecture_intent_packet_payload(
        {
            "schema": "adeu_architecture_intent_packet@1",
            "intent_packet_id": ids["intent_packet_id"],
            "source_set": _request_source_set_payload(request),
            "requested_outcomes": [
                (
                    f"Compile request-bound intended semantic-root architecture for the "
                    f"{package_name} repo slice."
                ),
                (
                    "Keep the released request and settlement boundary authoritative "
                    "for intended compile."
                ),
                "Emit only the released V40-A root-family artifacts over one bounded repo world.",
            ],
            "non_goals": sorted(
                set(
                    [
                        *request.declared_non_goals,
                        "alignment_diagnostics",
                        "practical_runner_release",
                        "repo_grounded_checkpoint_oracle_reuse",
                    ]
                )
            ),
            "declared_constraints": [
                "Consume released compile_entitlement from V41-B as-is.",
                (
                    "Observation may constrain, block, or force ambiguity but may not "
                    "become the hidden source of intended truth."
                ),
                (
                    "Unresolved or derived observations that matter to intent must "
                    "remain explicit as ambiguity, advisory posture, or refusal to "
                    "settle."
                ),
            ],
            "authority_boundary_policy": _root_policy_from_request(request),
        },
        repository_root=validated.repository_root,
    )


def _build_ontology_frame_payload(
    validated: V41DValidatedInputs,
    ids: dict[str, str],
) -> dict[str, Any]:
    request = validated.analysis_request
    package_name = Path(request.request_scope.subtree_root).name
    return canonicalize_adeu_architecture_ontology_frame_payload(
        {
            "schema": "adeu_architecture_ontology_frame@1",
            "ontology_frame_id": ids["ontology_frame_id"],
            "intent_packet_id": ids["intent_packet_id"],
            "authority_boundary_policy": _root_policy_from_request(request),
            "actors": [
                {
                    "actor_id": "act_maintainer_brief_author",
                    "kind": "human_role",
                    "label": "Maintainer Brief Author",
                    "trust_domain": "maintainer_docs",
                    "authority_level": "intent_author",
                },
                {
                    "actor_id": "act_intended_compile_engine",
                    "kind": "service",
                    "label": "Intended Compile Engine",
                    "trust_domain": "repo_compiler_runtime",
                    "authority_level": "semantic_root_materializer",
                },
                {
                    "actor_id": "act_observation_companion_lane",
                    "kind": "service",
                    "label": "Observation Companion Lane",
                    "trust_domain": "repo_analysis_runtime",
                    "authority_level": "companion_evidence",
                },
                {
                    "actor_id": "act_validation_harness",
                    "kind": "service",
                    "label": "Validation Harness",
                    "trust_domain": "repo_test_runtime",
                    "authority_level": "evidence_recorder",
                },
            ],
            "surfaces": [
                {
                    "surface_id": "srf_request_boundary",
                    "kind": "documentation_surface",
                    "owner_ref": "act_maintainer_brief_author",
                    "authority_posture": "request_bound_intent_input",
                    "exposed_actions": ["bind_repo_world", "state_intent_scope"],
                },
                {
                    "surface_id": "srf_observation_companion",
                    "kind": "analysis_artifact_surface",
                    "owner_ref": "act_observation_companion_lane",
                    "authority_posture": "companion_evidence_surface",
                    "exposed_actions": ["surface_observed_facts", "carry_unresolved_observations"],
                },
                {
                    "surface_id": "srf_intended_compile_entry",
                    "kind": "compiler_surface",
                    "owner_ref": "act_intended_compile_engine",
                    "authority_posture": "authoritative_semantic_surface",
                    "exposed_actions": ["emit_root_family", "preserve_lane_separation"],
                },
                {
                    "surface_id": "srf_validation_harness",
                    "kind": "test_surface",
                    "owner_ref": "act_validation_harness",
                    "authority_posture": "evidence_surface",
                    "exposed_actions": ["replay_fixture", "validate_emitted_root"],
                },
            ],
            "data_objects": [
                {
                    "object_id": "obj_analysis_request_boundary",
                    "label": "Analysis Request Boundary",
                    "sensitivity_class": "repo_internal",
                    "source_of_truth_ref": "srf_request_boundary",
                },
                {
                    "object_id": "obj_settlement_frame_boundary",
                    "label": "Settlement Frame Boundary",
                    "sensitivity_class": "repo_internal",
                    "source_of_truth_ref": "srf_request_boundary",
                },
                {
                    "object_id": "obj_observation_frame_boundary",
                    "label": "Observation Frame Boundary",
                    "sensitivity_class": "repo_internal",
                    "source_of_truth_ref": "srf_observation_companion",
                },
                {
                    "object_id": "obj_intended_semantic_root",
                    "label": f"{package_name} Intended Semantic Root",
                    "sensitivity_class": "repo_internal",
                    "source_of_truth_ref": "srf_intended_compile_entry",
                },
            ],
            "boundaries": [
                {
                    "boundary_id": "bnd_request_to_compile",
                    "from_ref": "srf_request_boundary",
                    "to_ref": "srf_intended_compile_entry",
                    "boundary_class": "intent_governance_boundary",
                    "auth_required": True,
                    "audit_required": True,
                },
                {
                    "boundary_id": "bnd_observation_to_compile",
                    "from_ref": "srf_observation_companion",
                    "to_ref": "srf_intended_compile_entry",
                    "boundary_class": "companion_evidence_boundary",
                    "auth_required": True,
                    "audit_required": True,
                },
                {
                    "boundary_id": "bnd_compile_to_validation",
                    "from_ref": "srf_intended_compile_entry",
                    "to_ref": "srf_validation_harness",
                    "boundary_class": "validation_evidence_boundary",
                    "auth_required": True,
                    "audit_required": True,
                },
            ],
            "capabilities": [
                {
                    "capability_id": "cap_compile_intended_root",
                    "subject_ref": "act_intended_compile_engine",
                    "resource_ref": "obj_intended_semantic_root",
                    "action": "compile",
                    "granted_by_ref": "act_maintainer_brief_author",
                },
                {
                    "capability_id": "cap_validate_intended_root",
                    "subject_ref": "act_validation_harness",
                    "resource_ref": "obj_intended_semantic_root",
                    "action": "validate",
                    "granted_by_ref": "act_intended_compile_engine",
                },
            ],
            "workflows": [
                {
                    "workflow_id": "wf_repo_grounded_intended_compile",
                    "entry_ref": "step_consume_request_boundary",
                    "step_refs": [
                        "step_consume_request_boundary",
                        "step_consume_observation_companion",
                        "step_emit_intended_root",
                        "step_validate_emitted_root",
                    ],
                    "terminal_state_refs": [
                        "st_intended_compiled",
                        "st_intended_blocked",
                    ],
                }
            ],
            "states": [
                {
                    "state_id": "st_world_bound",
                    "state_kind": "world_bound",
                    "terminal": False,
                    "workflow_id": "wf_repo_grounded_intended_compile",
                },
                {
                    "state_id": "st_intended_compiled",
                    "state_kind": "compiled",
                    "terminal": True,
                    "workflow_id": "wf_repo_grounded_intended_compile",
                },
                {
                    "state_id": "st_intended_blocked",
                    "state_kind": "blocked",
                    "terminal": True,
                    "workflow_id": "wf_repo_grounded_intended_compile",
                },
            ],
            "transitions": [
                {
                    "transition_id": "tr_world_to_compiled",
                    "from_state_ref": "st_world_bound",
                    "to_state_ref": "st_intended_compiled",
                    "trigger_ref": "dec_emit_intended_root",
                    "guard_refs": ["gate_emit_intended_root"],
                },
                {
                    "transition_id": "tr_world_to_blocked",
                    "from_state_ref": "st_world_bound",
                    "to_state_ref": "st_intended_blocked",
                    "trigger_ref": "dec_refuse_intended_root",
                    "guard_refs": ["gate_emit_intended_root"],
                },
            ],
            "decisions": [
                {
                    "decision_id": "dec_emit_intended_root",
                    "decider_ref": "act_intended_compile_engine",
                    "authority_source_ref": "srf_intended_compile_entry",
                    "evidence_required_refs": ["ev_request_boundary_validation"],
                    "ambiguity_default": "escalate_human",
                },
                {
                    "decision_id": "dec_refuse_intended_root",
                    "decider_ref": "act_intended_compile_engine",
                    "authority_source_ref": "srf_intended_compile_entry",
                    "evidence_required_refs": ["ev_request_boundary_validation"],
                    "ambiguity_default": "escalate_human",
                }
            ],
            "failure_modes": [
                {
                    "failure_mode_id": "fail_unresolved_observation_carry",
                    "affected_refs": [
                        "dec_refuse_intended_root",
                        "obj_intended_semantic_root",
                    ],
                    "default_disposition": "block_until_ambiguity_carry_through",
                    "observable_surface_ref": "srf_validation_harness",
                }
            ],
            "flow_steps": [
                {
                    "step_id": "step_consume_request_boundary",
                    "actor_ref": "act_maintainer_brief_author",
                    "surface_ref": "srf_request_boundary",
                    "kind": "request_bind",
                    "inputs": ["obj_analysis_request_boundary"],
                    "outputs": ["obj_analysis_request_boundary"],
                    "preconditions": [
                        "Released analysis request and accepted docs are present."
                    ],
                    "postconditions": [
                        "The request-bound maintainer brief governs intended compile."
                    ],
                },
                {
                    "step_id": "step_consume_observation_companion",
                    "actor_ref": "act_observation_companion_lane",
                    "surface_ref": "srf_observation_companion",
                    "kind": "companion_observation_read",
                    "inputs": ["obj_observation_frame_boundary"],
                    "outputs": ["obj_observation_frame_boundary"],
                    "preconditions": [
                        "Released observation frame is available over the same repo world."
                    ],
                    "postconditions": [
                        "Observation constraints and unresolved findings are visible "
                        "to intended compile."
                    ],
                },
                {
                    "step_id": "step_emit_intended_root",
                    "actor_ref": "act_intended_compile_engine",
                    "surface_ref": "srf_intended_compile_entry",
                    "kind": "semantic_root_emit",
                    "inputs": [
                        "obj_analysis_request_boundary",
                        "obj_settlement_frame_boundary",
                        "obj_observation_frame_boundary",
                    ],
                    "outputs": ["obj_intended_semantic_root"],
                    "preconditions": [
                        "Released compile entitlement is entitled.",
                        "Observation does not replace request-bound intent."
                    ],
                    "postconditions": [
                        f"The intended semantic root for {package_name} is materialized."
                    ],
                },
                {
                    "step_id": "step_validate_emitted_root",
                    "actor_ref": "act_validation_harness",
                    "surface_ref": "srf_validation_harness",
                    "kind": "fixture_replay_validation",
                    "inputs": ["obj_intended_semantic_root"],
                    "outputs": ["obj_intended_semantic_root"],
                    "preconditions": [
                        "Emitted root-family artifacts are available for replay."
                    ],
                    "postconditions": [
                        "Released V40-A validation and replay evidence are preserved."
                    ],
                },
            ],
        },
        repository_root=validated.repository_root,
    )


def _build_boundary_graph_payload(
    validated: V41DValidatedInputs,
    ids: dict[str, str],
    *,
    ontology_frame_payload: dict[str, Any],
) -> dict[str, Any]:
    payload = {
        "schema": "adeu_architecture_boundary_graph@1",
        "boundary_graph_id": ids["boundary_graph_id"],
        "intent_packet_id": ids["intent_packet_id"],
        "authority_boundary_policy": _root_policy_from_request(validated.analysis_request),
            "node_refs": [
            "dec_refuse_intended_root",
            "act_intended_compile_engine",
            "act_maintainer_brief_author",
            "act_observation_companion_lane",
            "act_validation_harness",
            "dec_emit_intended_root",
            "obj_analysis_request_boundary",
            "obj_intended_semantic_root",
            "obj_observation_frame_boundary",
            "obj_settlement_frame_boundary",
            "srf_intended_compile_entry",
            "srf_observation_companion",
            "srf_request_boundary",
            "srf_validation_harness",
        ],
        "edge_set": [
            {
                "edge_id": "edge_request_to_compile",
                "from_ref": "srf_request_boundary",
                "to_ref": "srf_intended_compile_entry",
                "boundary_ref": "bnd_request_to_compile",
                "crossing_class": "authority_crossing",
            },
            {
                "edge_id": "edge_observation_to_compile",
                "from_ref": "srf_observation_companion",
                "to_ref": "srf_intended_compile_entry",
                "boundary_ref": "bnd_observation_to_compile",
                "crossing_class": "sensitivity_crossing",
            },
            {
                "edge_id": "edge_compile_to_validation",
                "from_ref": "srf_intended_compile_entry",
                "to_ref": "srf_validation_harness",
                "boundary_ref": "bnd_compile_to_validation",
                "crossing_class": "audit_crossing",
            },
        ],
        "authority_crossings": ["edge_request_to_compile"],
        "sensitivity_crossings": ["edge_observation_to_compile"],
    }
    return canonicalize_adeu_architecture_boundary_graph_payload(
        payload,
        repository_root=validated.repository_root,
        ontology_frame=ontology_frame_payload,
    )


def _evidence_requirement_payloads(
    observation: AdeuArchitectureObservationFrame,
) -> tuple[list[dict[str, Any]], str]:
    payloads: list[dict[str, Any]] = []
    ids: list[str] = []
    for hook in observation.observed_evidence_hooks:
        evidence_id = f"ev_{_slug(hook.evidence_hook_id)}"
        ids.append(evidence_id)
        payloads.append(
            {
                "evidence_id": evidence_id,
                "required_before_refs": [
                    "dec_emit_intended_root",
                    "gate_emit_intended_root",
                ],
                "evidence_kind": hook.hook_kind,
                "source_policy": "request_bound_test_artifact_required",
            }
        )
    if not payloads:
        payloads.append(
            {
                "evidence_id": "ev_request_boundary_validation",
                "required_before_refs": [
                    "dec_emit_intended_root",
                    "gate_emit_intended_root",
                ],
                "evidence_kind": "request_boundary_validation",
                "source_policy": "request_bound_validation_required",
            }
        )
        return payloads, "ev_request_boundary_validation"
    return payloads, ids[0]


def _observability_hook_payloads(
    observation: AdeuArchitectureObservationFrame,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    hooks: list[dict[str, Any]] = []
    metrics: list[dict[str, Any]] = []
    for item in observation.observed_observability_hooks:
        metric_id = f"metric_{_slug(item.observability_hook_id)}"
        hook_id = f"hook_{_slug(item.observability_hook_id)}"
        hooks.append(
            {
                "hook_id": hook_id,
                "subject_ref": "srf_validation_harness",
                "observable_kind": item.observable_kind,
                "required_for_metrics": [metric_id],
            }
        )
        metrics.append(
            {
                "metric_id": metric_id,
                "label": f"{item.observable_kind.replace('_', ' ').title()} continuity",
                "target_expression": "artifact_present_and_request_bound",
                "measured_by_refs": [hook_id],
            }
        )
    return hooks, metrics


def _assumption_payloads(observation: AdeuArchitectureObservationFrame) -> list[dict[str, Any]]:
    payloads: list[dict[str, Any]] = []
    for boundary in observation.observed_boundaries:
        if boundary.observation_mode != "derived":
            continue
        payloads.append(
            {
                "assumption_id": f"asm_{_slug(boundary.boundary_id)}",
                "statement": (
                    "The observed package boundary remains a useful companion constraint "
                    "for intended compile without becoming the source of intent."
                ),
                "impact_class": "medium",
                "touches_refs": [
                    "bnd_observation_to_compile",
                    "obj_observation_frame_boundary",
                ],
                "confidence_kind": "strongly_implied",
            }
        )
    for workflow in observation.observed_workflows:
        if workflow.observation_mode != "derived":
            continue
        payloads.append(
            {
                "assumption_id": f"asm_{_slug(workflow.workflow_id)}",
                "statement": (
                    "Observed workflow structure constrains intended compile ordering "
                    "without replacing request-bound semantic authority."
                ),
                "impact_class": "medium",
                "touches_refs": [
                    "wf_repo_grounded_intended_compile",
                    "obj_observation_frame_boundary",
                ],
                "confidence_kind": "strongly_implied",
            }
        )
    return payloads


def _ambiguity_payloads(observation: AdeuArchitectureObservationFrame) -> list[dict[str, Any]]:
    payloads: list[dict[str, Any]] = []
    for unresolved in observation.unresolved_observations:
        payloads.append(
            {
                "ambiguity_id": f"amb_{_slug(unresolved.observation_id)}",
                "question": (
                    f"How should intended compile account for unresolved observation "
                    f"{unresolved.observation_id}: {unresolved.rationale}"
                ),
                "impact_class": "medium",
                "touches_refs": [
                    "obj_observation_frame_boundary",
                    "fail_unresolved_observation_carry",
                ],
                "resolution_route": "human_only",
                "evaluable_as": "contextual",
            }
        )
    return payloads


def _build_world_hypothesis_payload(
    validated: V41DValidatedInputs,
    ids: dict[str, str],
    *,
    ambiguity_ids: list[str],
    metric_ids: list[str],
) -> dict[str, Any]:
    request = validated.analysis_request
    unresolved_questions = [
        unresolved.rationale for unresolved in validated.observation_frame.unresolved_observations
    ] or ["No unresolved observation remained material in the accepted fixture."]
    return canonicalize_adeu_architecture_world_hypothesis_payload(
        {
            "schema": "adeu_architecture_world_hypothesis@1",
            "candidate_id": ids["candidate_id"],
            "intent_packet_id": ids["intent_packet_id"],
            "authority_boundary_policy": _root_policy_from_request(request),
            "source_set": _request_source_set_payload(request),
            "coverage_summary": {
                "covered_topics": [
                    "request-bound intended compile",
                    "observation companion carry-through",
                    "released root-family emission",
                ],
                "unresolved_questions": unresolved_questions,
            },
            "ontology_bindings": [
                "dec_emit_intended_root",
                "srf_intended_compile_entry",
                "wf_repo_grounded_intended_compile",
            ],
            "epistemic_bindings": [
                "fact_request_bound_normative_driver",
                *ambiguity_ids,
            ],
            "deontic_bindings": [
                "gate_emit_intended_root",
                "inv_intended_observed_separation",
            ],
            "utility_bindings": [
                "goal_semantic_fidelity",
                *(metric_ids[:1] or ["metric_request_boundary_validation"]),
            ],
            "authoritative": False,
        },
        repository_root=validated.repository_root,
    )


def _build_semantic_ir_payload(
    validated: V41DValidatedInputs,
    ids: dict[str, str],
    *,
    intent_packet_payload: dict[str, Any],
    ontology_frame_payload: dict[str, Any],
    evidence_payloads: list[dict[str, Any]],
    primary_evidence_id: str,
    observability_hook_payloads: list[dict[str, Any]],
    observability_metric_payloads: list[dict[str, Any]],
    assumption_payloads: list[dict[str, Any]],
    ambiguity_payloads: list[dict[str, Any]],
) -> dict[str, Any]:
    request = validated.analysis_request
    accepted_doc_source_ids = _request_ref_source_ids(
        request.accepted_doc_refs,
        request=request,
        field_name="accepted_doc_refs",
    )
    brief_source_ids = _request_ref_source_ids(
        request.maintainer_brief_refs,
        request=request,
        field_name="maintainer_brief_refs",
    )
    facts = [
        {
            "fact_id": "fact_request_bound_normative_driver",
            "statement": (
                "Intended compile is governed by the released request-bound maintainer "
                "brief and accepted architecture docs under the released settlement frame."
            ),
            "source_refs": sorted({*accepted_doc_source_ids, *brief_source_ids}),
            "confidence_kind": "explicit",
            "evaluable_as": "semantic",
        },
        {
            "fact_id": "fact_entitled_compile_required",
            "statement": (
                "Authoritative intended root-family emission requires released "
                "compile_entitlement=entitled and may not be recomputed locally."
            ),
            "source_refs": accepted_doc_source_ids,
            "confidence_kind": "explicit",
            "evaluable_as": "deterministic",
        },
    ]
    annotations = [
        {
            "annotation_id": "ann_intended_compile_decision",
            "subject_ref": "dec_emit_intended_root",
            "confidence_kind": "explicit",
            "evaluable_as": "semantic",
        }
    ]
    permission_targets = ["act_intended_compile_engine", "dec_emit_intended_root"]
    unresolved_trigger_refs = [item["ambiguity_id"] for item in ambiguity_payloads] or [
        "fail_unresolved_observation_carry"
    ]
    utility_metrics = observability_metric_payloads or [
        {
            "metric_id": "metric_request_boundary_validation",
            "label": "Request boundary validation",
            "target_expression": "fixture_replay_passes",
            "measured_by_refs": [primary_evidence_id],
        }
    ]
    semantic_ir_without_hash = {
        "schema": "adeu_architecture_semantic_ir@1",
        "architecture_id": ids["architecture_id"],
        "intent_packet_id": ids["intent_packet_id"],
        "compiler": dict(_DEFAULT_COMPILER),
        "authority_boundary_policy": _root_policy_from_request(request),
        "source_set": _request_source_set_payload(request),
        "variant_lineage": {
            "accepted_candidate_id": ids["candidate_id"],
            "candidate_ids": [ids["candidate_id"]],
        },
        "ontology": {
            key: ontology_frame_payload[key]
            for key in (
                "actors",
                "surfaces",
                "data_objects",
                "boundaries",
                "capabilities",
                "workflows",
                "states",
                "transitions",
                "decisions",
                "failure_modes",
                "flow_steps",
            )
        },
        "epistemics": {
            "facts": facts,
            "assumptions": assumption_payloads,
            "ambiguities": ambiguity_payloads,
            "evidence_requirements": evidence_payloads,
            "observability_hooks": observability_hook_payloads,
            "hypothesis_bindings": [
                {
                    "candidate_id": ids["candidate_id"],
                    "accepted": True,
                    "coverage_summary": (
                        "Accepted as the request-bound intended compile world for the "
                        "released adeu_architecture_ir slice."
                    ),
                    "rejection_reasons": [],
                }
            ],
            "annotations": annotations,
        },
        "deontics": {
            "obligations": [
                {
                    "obligation_id": "obl_preserve_request_bound_intent",
                    "statement": (
                        "Emitted intended root artifacts must remain bound to the released "
                        "request, settlement, and observation lineage."
                    ),
                    "target_refs": [
                        "obj_analysis_request_boundary",
                        "obj_intended_semantic_root",
                        "step_emit_intended_root",
                    ],
                    "condition": "Released compile entitlement remains entitled.",
                }
            ],
            "prohibitions": [
                {
                    "prohibition_id": "proh_observation_as_hidden_intent",
                    "statement": (
                        "Observed implementation facts must not silently become intended "
                        "architecture truth."
                    ),
                    "target_refs": [
                        "obj_observation_frame_boundary",
                        "dec_emit_intended_root",
                    ],
                    "condition": "Observation is consumed only as companion input.",
                }
            ],
            "permissions": [
                {
                    "permission_id": "perm_emit_intended_root",
                    "statement": (
                        "The intended compile engine may emit root-family artifacts once "
                        "released entitlement is entitled and gate evidence is satisfied."
                    ),
                    "target_refs": permission_targets,
                    "condition": "Released settlement entitlement is entitled.",
                }
            ],
            "gates": [
                {
                    "gate_id": "gate_emit_intended_root",
                    "subject_ref": "dec_emit_intended_root",
                    "authority_source_ref": "srf_intended_compile_entry",
                    "required_refs": [
                        "fact_entitled_compile_required",
                        primary_evidence_id,
                    ],
                    "fail_closed": True,
                }
            ],
            "invariants": [
                {
                    "invariant_id": "inv_intended_observed_separation",
                    "statement": (
                        "Intended and observed lanes must remain separate even when "
                        "observation constrains compile."
                    ),
                    "scope_refs": [
                        "obj_observation_frame_boundary",
                        "obj_intended_semantic_root",
                    ],
                    "severity": "high",
                }
            ],
            "escalation_rules": [
                {
                    "rule_id": "rule_unresolved_observation_to_human",
                    "trigger_refs": unresolved_trigger_refs,
                    "escalate_to": "act_maintainer_brief_author",
                    "default_disposition": "human_review",
                }
            ],
        },
        "utility": {
            "goals": [
                {
                    "goal_id": "goal_semantic_fidelity",
                    "statement": (
                        "Preserve request-bound intended semantics without laundering "
                        "observation into hidden authority."
                    ),
                    "served_by_refs": [
                        "gate_emit_intended_root",
                        "step_emit_intended_root",
                    ],
                },
                {
                    "goal_id": "goal_deterministic_replay",
                    "statement": "Keep emitted intended artifacts replayable and fixture-stable.",
                    "served_by_refs": [
                        "step_validate_emitted_root",
                        *(
                            [observability_hook_payloads[0]["hook_id"]]
                            if observability_hook_payloads
                            else []
                        ),
                    ],
                },
            ],
            "metrics": utility_metrics,
            "priority_rules": [
                {
                    "priority_id": "priority_fidelity_over_convenience",
                    "higher_ref": "goal_semantic_fidelity",
                    "lower_ref": "goal_deterministic_replay",
                    "condition": (
                        "If observation pressure conflicts with request-bound intent, "
                        "preserve semantic fidelity first."
                    ),
                }
            ],
            "tradeoffs": [
                {
                    "tradeoff_id": "tradeoff_replay_vs_unknowns",
                    "between_refs": [
                        "goal_deterministic_replay",
                        "goal_semantic_fidelity",
                    ],
                    "adjudication_rule": (
                        "Prefer preserving explicit ambiguity or advisory posture over "
                        "forcing a cleaner but unjustified intended root."
                    ),
                }
            ],
        },
    }
    return materialize_adeu_architecture_semantic_ir_payload(
        semantic_ir_without_hash,
        repository_root=validated.repository_root,
    )


def derive_v41d_intended_root_bundle(
    *,
    analysis_request_payload: dict[str, Any],
    analysis_request_path: str,
    settlement_frame_payload: dict[str, Any],
    settlement_frame_path: str,
    observation_frame_payload: dict[str, Any],
    observation_frame_path: str,
    repository_root: Path | None = None,
) -> V41DIntendedCompileBundle:
    validated = _validate_v41d_inputs(
        analysis_request_payload=analysis_request_payload,
        analysis_request_path=analysis_request_path,
        settlement_frame_payload=settlement_frame_payload,
        settlement_frame_path=settlement_frame_path,
        observation_frame_payload=observation_frame_payload,
        observation_frame_path=observation_frame_path,
        repository_root=repository_root,
    )
    ids = _bundle_ids(validated)
    intent_packet_payload = _build_intent_packet_payload(validated, ids)
    ontology_frame_payload = _build_ontology_frame_payload(validated, ids)
    boundary_graph_payload = _build_boundary_graph_payload(
        validated,
        ids,
        ontology_frame_payload=ontology_frame_payload,
    )
    evidence_payloads, primary_evidence_id = _evidence_requirement_payloads(
        validated.observation_frame
    )
    observability_hook_payloads, observability_metric_payloads = _observability_hook_payloads(
        validated.observation_frame
    )
    assumption_payloads = _assumption_payloads(validated.observation_frame)
    ambiguity_payloads = _ambiguity_payloads(validated.observation_frame)
    world_hypothesis_payload = _build_world_hypothesis_payload(
        validated,
        ids,
        ambiguity_ids=[item["ambiguity_id"] for item in ambiguity_payloads],
        metric_ids=[item["metric_id"] for item in observability_metric_payloads],
    )
    semantic_ir_payload = _build_semantic_ir_payload(
        validated,
        ids,
        intent_packet_payload=intent_packet_payload,
        ontology_frame_payload=ontology_frame_payload,
        evidence_payloads=evidence_payloads,
        primary_evidence_id=primary_evidence_id,
        observability_hook_payloads=observability_hook_payloads,
        observability_metric_payloads=observability_metric_payloads,
        assumption_payloads=assumption_payloads,
        ambiguity_payloads=ambiguity_payloads,
    )
    return V41DIntendedCompileBundle(
        analysis_request_id=validated.analysis_request.analysis_request_id,
        analysis_request_ref=validated.analysis_request_path,
        settlement_frame_id=validated.settlement_frame.settlement_frame_id,
        settlement_frame_ref=validated.settlement_frame_path,
        observation_frame_id=validated.observation_frame.observation_frame_id,
        observation_frame_ref=validated.observation_frame_path,
        source_set_hash=validated.analysis_request.source_set_hash,
        authority_boundary_policy=_root_policy_from_request(validated.analysis_request),
        intent_packet_payload=intent_packet_payload,
        ontology_frame_payload=ontology_frame_payload,
        boundary_graph_payload=boundary_graph_payload,
        world_hypothesis_payload=world_hypothesis_payload,
        semantic_ir_payload=semantic_ir_payload,
    )


def derive_v41d_intent_packet(**kwargs: Any) -> dict[str, Any]:
    return derive_v41d_intended_root_bundle(**kwargs).intent_packet_payload


def derive_v41d_ontology_frame(**kwargs: Any) -> dict[str, Any]:
    return derive_v41d_intended_root_bundle(**kwargs).ontology_frame_payload


def derive_v41d_boundary_graph(**kwargs: Any) -> dict[str, Any]:
    return derive_v41d_intended_root_bundle(**kwargs).boundary_graph_payload


def derive_v41d_world_hypothesis(**kwargs: Any) -> dict[str, Any]:
    return derive_v41d_intended_root_bundle(**kwargs).world_hypothesis_payload


def derive_v41d_semantic_ir(**kwargs: Any) -> dict[str, Any]:
    return derive_v41d_intended_root_bundle(**kwargs).semantic_ir_payload
