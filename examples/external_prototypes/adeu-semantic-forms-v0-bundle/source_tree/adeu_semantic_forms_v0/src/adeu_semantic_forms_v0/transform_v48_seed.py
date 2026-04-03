from __future__ import annotations

from .models import (
    BlockingIssue,
    ScopeAnchor,
    PolicyAnchor,
    SemanticNormalForm,
    SemanticParseProfile,
    SemanticTransformContract,
    SemanticTransformResult,
    TaskpackBindingSpecSeed,
    sha256_canonical_json,
)


def build_reference_transform_contract(profile_id: str) -> SemanticTransformContract:
    return SemanticTransformContract.model_validate(
        {
            "contract_id": "repo_policy_work_v0_to_taskpack_binding_spec_seed@1",
            "source_schema": "adeu_semantic_normal_form@1",
            "target_schema": "adeu_taskpack_binding_spec_seed@1",
            "profile_id": profile_id,
            "required_singleton_relations": [
                "bind_policy_anchor",
                "bind_scope_anchor",
                "produce_artifact_kind",
                "set_mutation_posture",
                "use_worker_subject",
            ],
            "supported_multi_relations": [
                "allow_path",
                "forbid_effect",
                "forbid_path",
            ],
            "fixed_defaults": {
                "prompt_projection_posture": "projection_only_non_authoritative",
                "lineage_resolution_posture": "fail_closed_on_unresolved_or_stale_lineage",
                "unsupported_mapping_posture": "fail_closed",
            },
            "unsupported_relation_kinds": [],
            "semantic_hash": "derived-by-model-validator",
        }
    )


def _singleton_value(normal_form: SemanticNormalForm, relation_kind: str) -> tuple[str | None, list[BlockingIssue]]:
    matches = [clause.object_value for clause in normal_form.clauses if clause.relation_kind == relation_kind]
    if len(matches) != 1:
        return None, [
            BlockingIssue(
                code="ASL-TRANSFORM-CARDINALITY",
                message=f"{relation_kind} must occur exactly once",
                details={"relation_kind": relation_kind, "count": len(matches)},
            )
        ]
    return matches[0], []


def _scope_anchor(profile: SemanticParseProfile, anchor_id: str) -> ScopeAnchor | None:
    return next((anchor for anchor in profile.scope_anchors if anchor.anchor_id == anchor_id), None)


def _policy_anchor(profile: SemanticParseProfile, anchor_id: str) -> PolicyAnchor | None:
    return next((anchor for anchor in profile.policy_anchors if anchor.anchor_id == anchor_id), None)


def transform_normal_form_to_binding_seed(
    *,
    normal_form: SemanticNormalForm,
    profile: SemanticParseProfile,
    contract: SemanticTransformContract,
) -> SemanticTransformResult:
    blocking: list[BlockingIssue] = []

    scope_anchor_id, issues = _singleton_value(normal_form, "bind_scope_anchor")
    blocking.extend(issues)
    policy_anchor_id, issues = _singleton_value(normal_form, "bind_policy_anchor")
    blocking.extend(issues)
    worker_subject_ref, issues = _singleton_value(normal_form, "use_worker_subject")
    blocking.extend(issues)
    mutation_posture, issues = _singleton_value(normal_form, "set_mutation_posture")
    blocking.extend(issues)
    artifact_kind, issues = _singleton_value(normal_form, "produce_artifact_kind")
    blocking.extend(issues)

    if blocking:
        return SemanticTransformResult.model_validate(
            {
                "contract_id": contract.contract_id,
                "source_semantic_hash": normal_form.semantic_hash,
                "target_schema": contract.target_schema,
                "transform_status": "blocked_missing_required_relation",
                "blocking_issues": [issue.model_dump(mode="json") for issue in blocking],
                "target_payload": None,
                "target_semantic_hash": None,
                "transform_result_id": "derived-by-model-validator",
            }
        )

    if mutation_posture != "read_only":
        return SemanticTransformResult.model_validate(
            {
                "contract_id": contract.contract_id,
                "source_semantic_hash": normal_form.semantic_hash,
                "target_schema": contract.target_schema,
                "transform_status": "blocked_unsupported_relation",
                "blocking_issues": [
                    BlockingIssue(
                        code="ASL-TRANSFORM-MUTATION-POSTURE",
                        message="v0 only supports read_only mutation posture",
                        details={"mutation_posture": mutation_posture},
                    ).model_dump(mode="json")
                ],
                "target_payload": None,
                "target_semantic_hash": None,
                "transform_result_id": "derived-by-model-validator",
            }
        )

    if artifact_kind != "taskpack_binding_spec_seed":
        return SemanticTransformResult.model_validate(
            {
                "contract_id": contract.contract_id,
                "source_semantic_hash": normal_form.semantic_hash,
                "target_schema": contract.target_schema,
                "transform_status": "blocked_unsupported_relation",
                "blocking_issues": [
                    BlockingIssue(
                        code="ASL-TRANSFORM-ARTIFACT-KIND",
                        message="v0 only supports taskpack_binding_spec_seed target emission",
                        details={"artifact_kind": artifact_kind},
                    ).model_dump(mode="json")
                ],
                "target_payload": None,
                "target_semantic_hash": None,
                "transform_result_id": "derived-by-model-validator",
            }
        )

    scope_anchor = _scope_anchor(profile, scope_anchor_id or "")
    policy_anchor = _policy_anchor(profile, policy_anchor_id or "")
    if scope_anchor is None or policy_anchor is None:
        return SemanticTransformResult.model_validate(
            {
                "contract_id": contract.contract_id,
                "source_semantic_hash": normal_form.semantic_hash,
                "target_schema": contract.target_schema,
                "transform_status": "blocked_resolution_failure",
                "blocking_issues": [
                    BlockingIssue(
                        code="ASL-TRANSFORM-RESOLUTION",
                        message="semantic anchor could not be resolved through the parse profile",
                        details={
                            "scope_anchor_id": scope_anchor_id,
                            "policy_anchor_id": policy_anchor_id,
                        },
                    ).model_dump(mode="json")
                ],
                "target_payload": None,
                "target_semantic_hash": None,
                "transform_result_id": "derived-by-model-validator",
            }
        )

    allow_paths = sorted(
        clause.object_value
        for clause in normal_form.clauses
        if clause.relation_kind == "allow_path"
    )
    forbid_paths = sorted(
        clause.object_value
        for clause in normal_form.clauses
        if clause.relation_kind == "forbid_path"
    )
    forbid_effects = sorted(
        clause.object_value
        for clause in normal_form.clauses
        if clause.relation_kind == "forbid_effect"
    )

    binding_subject_id = f"binding_subject:{scope_anchor.anchor_id}:{policy_anchor.anchor_id.replace(':', '_')}_projection"
    seed = TaskpackBindingSpecSeed.model_validate(
        {
            "seed_id": "derived-by-model-validator",
            "profile_id": profile.profile_id,
            "snapshot_id": profile.snapshot_id,
            "snapshot_sha256": profile.snapshot_sha256,
            "binding_subject_id": binding_subject_id,
            "scope_anchor_id": scope_anchor.anchor_id,
            "scope_source_ref": scope_anchor.resolved_scope_ref,
            "scope_binding_entry_ref": scope_anchor.resolved_binding_entry_ref,
            "policy_anchor_id": policy_anchor.anchor_id,
            "policy_source_ref": policy_anchor.resolved_policy_consumer_ref,
            "policy_authority_clause_ref": policy_anchor.resolved_clause_ref,
            "worker_subject_ref": worker_subject_ref,
            "mutation_posture": "read_only",
            "allowlist_projection": allow_paths,
            "forbidden_projection": {
                "forbidden_paths": forbid_paths,
                "forbidden_effects": forbid_effects,
            },
            "prompt_projection_posture": contract.fixed_defaults["prompt_projection_posture"],
            "lineage_resolution_posture": contract.fixed_defaults["lineage_resolution_posture"],
            "unsupported_mapping_posture": contract.fixed_defaults["unsupported_mapping_posture"],
            "semantic_hash": "derived-by-model-validator",
        }
    )
    payload = seed.model_dump(mode="json", exclude_none=True)
    return SemanticTransformResult.model_validate(
        {
            "contract_id": contract.contract_id,
            "source_semantic_hash": normal_form.semantic_hash,
            "target_schema": contract.target_schema,
            "transform_status": "transformed",
            "blocking_issues": [],
            "target_payload": payload,
            "target_semantic_hash": seed.semantic_hash,
            "transform_result_id": "derived-by-model-validator",
        }
    )
