from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA = (
    "synthetic_pressure_mismatch_rule_registry@1"
)
V39B_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md"
    "#v39b_synthetic_pressure_mismatch_registry_contract@1"
)

SyntheticPressureMismatchRuleRegistrySchemaVersion = Literal[
    "synthetic_pressure_mismatch_rule_registry@1"
]
SyntheticPressureMismatchSignalKind = Literal[
    "state_model_drift",
    "abstraction_pressure_drift",
    "semantic_communication_drift",
    "shape_regularity_drift",
    "meta_intent_failure",
]
SyntheticPressureMismatchHarmKind = Literal[
    "correctness_risk",
    "failure_signal_loss",
    "trust_boundary_blur",
    "maintainability_drag",
    "semantic_density_loss",
    "reviewer_load_inflation",
    "intent_opacity",
]
SyntheticPressureMismatchEvidenceMode = Literal[
    "ast_shape",
    "control_flow_shape",
    "exception_flow_shape",
    "nullability_or_presence_inference",
    "duplicate_invariant_path",
    "lexical_naming_pattern",
    "comment_text_pattern",
    "error_text_pattern",
    "commit_text_pattern",
    "diff_shape_heuristic",
    "review_only_human_judgment",
]
SyntheticPressureMismatchEvidenceRegime = Literal[
    "deterministic_local",
    "static_contextual",
    "semantic_ambiguous",
    "meta_governance",
]
SyntheticPressureMismatchAllowedAction = Literal[
    "safe_autofix",
    "deterministic_finding",
    "review_only_finding",
    "forbid",
    "discourage",
    "allow_with_justification",
    "meta_artifact_correction",
]
SyntheticPressureMismatchResolutionRoute = Literal[
    "deterministic_only",
    "oracle_assisted",
    "human_only",
]
SyntheticPressureMismatchSubjectKind = Literal[
    "code_span",
    "diff_hunk",
    "function_or_method",
    "test_case_or_fixture",
    "comment_block",
    "error_message",
    "commit_message",
    "review_note",
    "recap_artifact",
]
SyntheticPressureMismatchExpectedUtilityGain = Literal[
    "correctness_protection",
    "failure_signal_recovery",
    "trust_boundary_clarity",
    "maintainability_improvement",
    "semantic_density_gain",
    "review_load_reduction",
    "intent_clarity_gain",
]
SyntheticPressureMismatchFalsePositiveRisk = Literal["low", "medium", "high"]
SyntheticPressureMismatchRewriteRisk = Literal["low", "medium", "high"]
SyntheticPressureMismatchRequiredContextScope = Literal[
    "code_span_scope",
    "function_scope",
    "module_scope",
    "call_path_scope",
    "hunk_scope",
    "artifact_scope",
]
SyntheticPressureMismatchForwardAgentPolicy = str
SyntheticPressureMismatchPostOptimizerPolicy = str
SyntheticPressureMismatchContextScope = SyntheticPressureMismatchRequiredContextScope
SyntheticPressureMismatchRiskLevel = Literal["low", "medium", "high"]


def _assert_sorted_unique(
    values: list[str],
    *,
    field_name: str,
    allow_empty: bool = False,
) -> None:
    if not allow_empty and not values:
        raise ValueError(f"{field_name} must not be empty")
    if any(not value for value in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _assert_non_empty_text(value: str, *, field_name: str) -> None:
    if not value.strip():
        raise ValueError(f"{field_name} must not be empty")


class SyntheticPressureMismatchCounterexamplePolicy(BaseModel):
    model_config = ConfigDict(extra="forbid")

    when_rule_does_not_apply: str
    defeating_evidence: str
    exemption_requires_review: bool

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchCounterexamplePolicy":
        _assert_non_empty_text(
            self.when_rule_does_not_apply,
            field_name="counterexample_policy.when_rule_does_not_apply",
        )
        _assert_non_empty_text(
            self.defeating_evidence,
            field_name="counterexample_policy.defeating_evidence",
        )
        return self


class SyntheticPressureMismatchRule(BaseModel):
    model_config = ConfigDict(
        extra="forbid",
        json_schema_extra={
            "allOf": [
                {
                    "if": {
                        "properties": {
                            "allowed_action": {"const": "safe_autofix"},
                        },
                        "required": ["allowed_action"],
                    },
                    "then": {
                        "properties": {
                            "evidence_regime": {"const": "deterministic_local"},
                            "resolution_route": {"const": "deterministic_only"},
                        }
                    },
                },
                {
                    "not": {
                        "properties": {
                            "allowed_action": {"const": "safe_autofix"},
                            "signal_kind": {"const": "shape_regularity_drift"},
                        },
                        "required": ["allowed_action", "signal_kind"],
                    }
                },
                {
                    "not": {
                        "properties": {
                            "allowed_action": {"const": "safe_autofix"},
                            "evidence_regime": {"const": "semantic_ambiguous"},
                        },
                        "required": ["allowed_action", "evidence_regime"],
                    }
                },
                {
                    "not": {
                        "properties": {
                            "allowed_action": {"const": "safe_autofix"},
                            "evidence_regime": {"const": "meta_governance"},
                        },
                        "required": ["allowed_action", "evidence_regime"],
                    }
                },
            ]
        },
    )

    rule_id: str = Field(min_length=1)
    signal_kind: SyntheticPressureMismatchSignalKind
    subpattern: str = Field(min_length=1)
    harm_kind: SyntheticPressureMismatchHarmKind
    evidence_mode: SyntheticPressureMismatchEvidenceMode
    evidence_regime: SyntheticPressureMismatchEvidenceRegime
    allowed_action: SyntheticPressureMismatchAllowedAction
    applicable_subject_kinds: list[SyntheticPressureMismatchSubjectKind] = Field(min_length=1)
    false_positive_risk: SyntheticPressureMismatchFalsePositiveRisk
    required_context_scope: SyntheticPressureMismatchRequiredContextScope
    expected_utility_gains: list[SyntheticPressureMismatchExpectedUtilityGain] = Field(
        min_length=1
    )
    rewrite_risk: SyntheticPressureMismatchRewriteRisk
    counterexample_policy: SyntheticPressureMismatchCounterexamplePolicy
    resolution_route: SyntheticPressureMismatchResolutionRoute
    forward_agent_policy: SyntheticPressureMismatchForwardAgentPolicy = Field(min_length=1)
    post_optimizer_policy: SyntheticPressureMismatchPostOptimizerPolicy = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchRule":
        _assert_non_empty_text(self.rule_id, field_name="rules[].rule_id")
        _assert_non_empty_text(self.subpattern, field_name=f"rules[{self.rule_id}].subpattern")
        _assert_sorted_unique(
            self.applicable_subject_kinds,
            field_name=f"rules[{self.rule_id}].applicable_subject_kinds",
            allow_empty=False,
        )
        _assert_sorted_unique(
            self.expected_utility_gains,
            field_name=f"rules[{self.rule_id}].expected_utility_gains",
            allow_empty=False,
        )
        _assert_non_empty_text(
            self.forward_agent_policy,
            field_name=f"rules[{self.rule_id}].forward_agent_policy",
        )
        _assert_non_empty_text(
            self.post_optimizer_policy,
            field_name=f"rules[{self.rule_id}].post_optimizer_policy",
        )
        if self.allowed_action == "safe_autofix":
            if self.evidence_regime != "deterministic_local":
                raise ValueError(
                    "rules[].allowed_action safe_autofix requires evidence_regime "
                    "deterministic_local"
                )
            if self.resolution_route != "deterministic_only":
                raise ValueError(
                    "rules[].allowed_action safe_autofix requires resolution_route "
                    "deterministic_only"
                )
            if self.signal_kind == "shape_regularity_drift":
                raise ValueError(
                    "rules[].allowed_action safe_autofix is forbidden for "
                    "shape_regularity_drift"
                )
        if self.evidence_regime == "semantic_ambiguous" and self.allowed_action == "safe_autofix":
            raise ValueError(
                "rules[].allowed_action safe_autofix is forbidden for semantic_ambiguous rules"
            )
        if self.evidence_regime == "meta_governance" and self.allowed_action == "safe_autofix":
            raise ValueError(
                "rules[].allowed_action safe_autofix is forbidden for meta_governance rules"
            )
        if self.signal_kind == "meta_intent_failure" and any(
            subject_kind not in ("commit_message", "review_note", "recap_artifact")
            for subject_kind in self.applicable_subject_kinds
        ):
            raise ValueError(
                "meta_intent_failure rules must use only meta-artifact subject kinds"
            )
        return self


class SyntheticPressureMismatchRuleRegistry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: SyntheticPressureMismatchRuleRegistrySchemaVersion = (
        SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA
    )
    registry_id: str = Field(min_length=1)
    target_arc: str = Field(pattern=r"^vNext\+[0-9]+$")
    target_path: Literal["V39-B"] = "V39-B"
    contract_source: Literal[
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md#v39b_synthetic_pressure_mismatch_registry_contract@1"
    ] = V39B_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE
    implementation_package: Literal["adeu_core_ir"] = "adeu_core_ir"
    glossary_strategy: Literal["registry_local_vocabulary"] = "registry_local_vocabulary"
    rules: list[SyntheticPressureMismatchRule] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "SyntheticPressureMismatchRuleRegistry":
        _assert_non_empty_text(self.registry_id, field_name="registry_id")
        if not self.rules:
            raise ValueError("rules must not be empty")
        rule_ids = [rule.rule_id for rule in self.rules]
        if len(rule_ids) != len(set(rule_ids)):
            raise ValueError("rules.rule_id must not contain duplicates")
        for rule in self.rules:
            if not rule.applicable_subject_kinds:
                raise ValueError(f"rules[{rule.rule_id}] must declare subject applicability")
        return self


def canonicalize_synthetic_pressure_mismatch_rule_registry_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = SyntheticPressureMismatchRuleRegistry.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


__all__ = [
    "SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA",
    "V39B_SYNTHETIC_PRESSURE_MISMATCH_CONTRACT_SOURCE",
    "SyntheticPressureMismatchAllowedAction",
    "SyntheticPressureMismatchContextScope",
    "SyntheticPressureMismatchCounterexamplePolicy",
    "SyntheticPressureMismatchEvidenceMode",
    "SyntheticPressureMismatchEvidenceRegime",
    "SyntheticPressureMismatchExpectedUtilityGain",
    "SyntheticPressureMismatchForwardAgentPolicy",
    "SyntheticPressureMismatchHarmKind",
    "SyntheticPressureMismatchPostOptimizerPolicy",
    "SyntheticPressureMismatchResolutionRoute",
    "SyntheticPressureMismatchRiskLevel",
    "SyntheticPressureMismatchRule",
    "SyntheticPressureMismatchRuleRegistry",
    "SyntheticPressureMismatchSignalKind",
    "SyntheticPressureMismatchSubjectKind",
    "canonicalize_synthetic_pressure_mismatch_rule_registry_payload",
]
