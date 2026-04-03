from __future__ import annotations

from typing import Any

from .models import (
    ADEU_SEMANTIC_NORMAL_FORM_SCHEMA,
    ADEU_TASKPACK_BINDING_SPEC_SEED_SCHEMA,
    SemanticNormalForm,
    SemanticParseResult,
    SemanticTransformContract,
    TaskpackBindingSpecSeed,
    canonical_json,
)

ADEU_SEMANTIC_FORMS_LOWERING_ERROR_SCHEMA = "adeu_semantic_forms_lowering_error@1"

ASF5901_INPUT_INVALID = "ASF5901"
ASF5902_SOURCE_NOT_ADMISSIBLE = "ASF5902"
ASF5903_CONTRACT_MISMATCH = "ASF5903"
ASF5904_REQUIRED_RELATION_MISSING = "ASF5904"
ASF5905_SINGLETON_CONFLICT = "ASF5905"
ASF5906_UNSUPPORTED_RELATION = "ASF5906"
ASF5907_FIXED_DEFAULT_CONFLICT = "ASF5907"


class SemanticFormsLoweringError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": ADEU_SEMANTIC_FORMS_LOWERING_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *,
    code: str,
    message: str,
    details: dict[str, Any] | None = None,
) -> SemanticFormsLoweringError:
    raise SemanticFormsLoweringError(code=code, message=message, details=details)


def _relation_values(
    normal_form: SemanticNormalForm,
    relation_kind: str,
) -> list[str]:
    return [
        core.object_value
        for core in normal_form.statement_cores
        if core.relation_kind == relation_kind
    ]


def _required_singleton_value(
    normal_form: SemanticNormalForm,
    relation_kind: str,
) -> str:
    values = _relation_values(normal_form, relation_kind)
    if not values:
        _fail(
            code=ASF5904_REQUIRED_RELATION_MISSING,
            message="required singleton relation is missing",
            details={"relation_kind": relation_kind},
        )
    if len(values) != 1:
        _fail(
            code=ASF5905_SINGLETON_CONFLICT,
            message="required singleton relation must occur exactly once",
            details={"relation_kind": relation_kind, "values": values},
        )
    return values[0]


def _supported_multi_values(
    normal_form: SemanticNormalForm,
    relation_kind: str,
) -> list[str]:
    return _relation_values(normal_form, relation_kind)


def lower_semantic_normal_form_to_taskpack_binding_spec_seed(
    *,
    normal_form: SemanticNormalForm,
    transform_contract: SemanticTransformContract,
) -> TaskpackBindingSpecSeed:
    if normal_form.schema != ADEU_SEMANTIC_NORMAL_FORM_SCHEMA:
        _fail(
            code=ASF5903_CONTRACT_MISMATCH,
            message="normal form schema does not match the released V49-A source schema",
            details={"normal_form_schema": normal_form.schema},
        )
    if transform_contract.source_schema != ADEU_SEMANTIC_NORMAL_FORM_SCHEMA:
        _fail(
            code=ASF5903_CONTRACT_MISMATCH,
            message="transform contract source_schema must be adeu_semantic_normal_form@1",
            details={"source_schema": transform_contract.source_schema},
        )
    if transform_contract.target_schema != ADEU_TASKPACK_BINDING_SPEC_SEED_SCHEMA:
        _fail(
            code=ASF5903_CONTRACT_MISMATCH,
            message="transform contract target_schema must be adeu_taskpack_binding_spec_seed@1",
            details={"target_schema": transform_contract.target_schema},
        )
    if normal_form.profile_id != transform_contract.profile_id:
        _fail(
            code=ASF5903_CONTRACT_MISMATCH,
            message="normal form and transform contract must share the same profile_id",
            details={
                "normal_form_profile_id": normal_form.profile_id,
                "transform_contract_profile_id": transform_contract.profile_id,
            },
        )
    if normal_form.domain_kind != "repo_policy_work":
        _fail(
            code=ASF5903_CONTRACT_MISMATCH,
            message="starter V49-C lowering supports only repo_policy_work",
            details={"domain_kind": normal_form.domain_kind},
        )

    allowed_relations = set(transform_contract.required_singleton_relations) | set(
        transform_contract.supported_multi_relations
    )
    unsupported_relations = set(transform_contract.unsupported_relation_kinds)
    for core in normal_form.statement_cores:
        if core.relation_kind in unsupported_relations:
            _fail(
                code=ASF5906_UNSUPPORTED_RELATION,
                message="normal form contains an explicitly unsupported relation kind",
                details={"relation_kind": core.relation_kind},
            )
        if core.relation_kind not in allowed_relations:
            _fail(
                code=ASF5906_UNSUPPORTED_RELATION,
                message=(
                    "normal form contains a relation kind not admitted by the transform "
                    "contract"
                ),
                details={"relation_kind": core.relation_kind},
            )

    required_singleton_values = {
        relation_kind: _required_singleton_value(normal_form, relation_kind)
        for relation_kind in transform_contract.required_singleton_relations
    }
    unsupported_required_singleton_relations = sorted(
        set(required_singleton_values) - {
            "bind_scope_anchor",
            "bind_policy_anchor",
            "use_worker_subject",
            "set_mutation_posture",
            "produce_artifact_kind",
        }
    )
    if unsupported_required_singleton_relations:
        _fail(
            code=ASF5906_UNSUPPORTED_RELATION,
            message=(
                "transform contract declares required singleton relations not supported "
                "by starter V49-C lowering"
            ),
            details={
                "required_singleton_relations": unsupported_required_singleton_relations,
            },
        )

    scope_anchor_ref = required_singleton_values["bind_scope_anchor"]
    policy_anchor_ref = required_singleton_values["bind_policy_anchor"]
    worker_subject_ref = required_singleton_values["use_worker_subject"]
    mutation_posture = required_singleton_values["set_mutation_posture"]
    artifact_kind = required_singleton_values["produce_artifact_kind"]

    if mutation_posture != "read_only":
        _fail(
            code=ASF5906_UNSUPPORTED_RELATION,
            message="starter V49-C lowering supports only read_only mutation posture",
            details={"mutation_posture": mutation_posture},
        )
    if artifact_kind != "taskpack_binding_spec_seed":
        _fail(
            code=ASF5906_UNSUPPORTED_RELATION,
            message=(
                "starter V49-C lowering supports only "
                "taskpack_binding_spec_seed artifact emission"
            ),
            details={"artifact_kind": artifact_kind},
        )

    projected_values: dict[str, str] = {
        "scope_anchor_ref": scope_anchor_ref,
        "policy_anchor_ref": policy_anchor_ref,
        "worker_subject_ref": worker_subject_ref,
        "mutation_posture": mutation_posture,
    }
    for key, value in transform_contract.fixed_defaults.items():
        if key in projected_values and projected_values[key] != value:
            _fail(
                code=ASF5907_FIXED_DEFAULT_CONFLICT,
                message="fixed default conflicts with relation-derived lowering value",
                details={
                    "field": key,
                    "fixed_default": value,
                    "relation_value": projected_values[key],
                },
            )

    return TaskpackBindingSpecSeed.model_validate(
        {
            "seed_id": "derived-by-model-validator",
            "profile_id": normal_form.profile_id,
            "source_normal_form_hash": normal_form.semantic_hash,
            "transform_contract_id": transform_contract.contract_id,
            "transform_contract_hash": transform_contract.semantic_hash,
            "scope_anchor_ref": scope_anchor_ref,
            "policy_anchor_ref": policy_anchor_ref,
            "worker_subject_ref": worker_subject_ref,
            "mutation_posture": mutation_posture,
            "allow_paths": _supported_multi_values(normal_form, "allow_path"),
            "forbid_paths": _supported_multi_values(normal_form, "forbid_path"),
            "forbid_effects": _supported_multi_values(normal_form, "forbid_effect"),
            "artifact_kinds": [artifact_kind],
            "fixed_defaults": transform_contract.fixed_defaults,
            "seed_hash": "derived-by-model-validator",
        }
    )


def lower_parse_result_to_taskpack_binding_spec_seed(
    *,
    parse_result: SemanticParseResult,
    transform_contract: SemanticTransformContract,
) -> TaskpackBindingSpecSeed:
    if parse_result.parse_status != "resolved_singleton" or len(parse_result.candidates) != 1:
        _fail(
            code=ASF5902_SOURCE_NOT_ADMISSIBLE,
            message=(
                "lowering is admissible only from a V49-B parse result with "
                "parse_status=resolved_singleton"
            ),
            details={
                "parse_status": parse_result.parse_status,
                "candidate_count": len(parse_result.candidates),
            },
        )
    if parse_result.profile_id != transform_contract.profile_id:
        _fail(
            code=ASF5903_CONTRACT_MISMATCH,
            message="parse result and transform contract must share the same profile_id",
            details={
                "parse_result_profile_id": parse_result.profile_id,
                "transform_contract_profile_id": transform_contract.profile_id,
            },
        )
    return lower_semantic_normal_form_to_taskpack_binding_spec_seed(
        normal_form=parse_result.candidates[0].normal_form,
        transform_contract=transform_contract,
    )
