from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_semantic_forms import (
    SemanticFormsLoweringError,
    SemanticNormalForm,
    SemanticParseResult,
    SemanticTransformContract,
    TaskpackBindingSpecSeed,
    lower_parse_result_to_taskpack_binding_spec_seed,
    lower_semantic_normal_form_to_taskpack_binding_spec_seed,
)


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v49c" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def _read_v49a_json(name: str) -> dict[str, object]:
    path = Path(__file__).parent / "fixtures" / "v49a" / name
    return json.loads(path.read_text(encoding="utf-8"))


def _read_v49b_json(name: str) -> dict[str, object]:
    path = Path(__file__).parent / "fixtures" / "v49b" / name
    return json.loads(path.read_text(encoding="utf-8"))


def test_reference_lowering_replays_committed_seed_fixture() -> None:
    normal_form = SemanticNormalForm.model_validate(
        _read_v49a_json("reference_semantic_normal_form.json")
    )
    transform_contract = SemanticTransformContract.model_validate(
        _read_v49a_json("reference_semantic_transform_contract.json")
    )
    fixture = _read_json("reference_taskpack_binding_spec_seed.json")

    seed = lower_semantic_normal_form_to_taskpack_binding_spec_seed(
        normal_form=normal_form,
        transform_contract=transform_contract,
    )

    assert isinstance(seed, TaskpackBindingSpecSeed)
    assert seed.model_dump(mode="json", by_alias=True, exclude_none=True) == fixture


def test_resolved_singleton_parse_result_lowering_replays_same_seed_fixture() -> None:
    parse_result = SemanticParseResult.model_validate(
        _read_v49b_json("reference_semantic_parse_result_resolved_singleton.json")
    )
    transform_contract = SemanticTransformContract.model_validate(
        _read_v49a_json("reference_semantic_transform_contract.json")
    )
    fixture = _read_json("reference_taskpack_binding_spec_seed.json")

    seed = lower_parse_result_to_taskpack_binding_spec_seed(
        parse_result=parse_result,
        transform_contract=transform_contract,
    )

    assert seed.model_dump(mode="json", by_alias=True, exclude_none=True) == fixture


def test_typed_alternatives_parse_result_is_not_admissible_for_lowering() -> None:
    parse_result = SemanticParseResult.model_validate(
        _read_v49b_json("reference_semantic_parse_result_typed_alternatives.json")
    )
    transform_contract = SemanticTransformContract.model_validate(
        _read_v49a_json("reference_semantic_transform_contract.json")
    )

    with pytest.raises(SemanticFormsLoweringError) as excinfo:
        lower_parse_result_to_taskpack_binding_spec_seed(
            parse_result=parse_result,
            transform_contract=transform_contract,
        )

    assert excinfo.value.code == "ASF5902"


def test_missing_required_relation_fails_closed() -> None:
    normal_form = SemanticNormalForm.model_validate(
        _read_json("mutation_semantic_normal_form_missing_policy_anchor.json")
    )
    transform_contract = SemanticTransformContract.model_validate(
        _read_v49a_json("reference_semantic_transform_contract.json")
    )

    with pytest.raises(SemanticFormsLoweringError) as excinfo:
        lower_semantic_normal_form_to_taskpack_binding_spec_seed(
            normal_form=normal_form,
            transform_contract=transform_contract,
        )

    assert excinfo.value.code == "ASF5904"


def test_duplicate_singleton_relation_fails_closed() -> None:
    normal_form = SemanticNormalForm.model_validate(
        _read_json("mutation_semantic_normal_form_duplicate_worker_subject.json")
    )
    transform_contract = SemanticTransformContract.model_validate(
        _read_v49a_json("reference_semantic_transform_contract.json")
    )

    with pytest.raises(SemanticFormsLoweringError) as excinfo:
        lower_semantic_normal_form_to_taskpack_binding_spec_seed(
            normal_form=normal_form,
            transform_contract=transform_contract,
        )

    assert excinfo.value.code == "ASF5905"


def test_transform_contract_profile_mismatch_fails_closed() -> None:
    normal_form = SemanticNormalForm.model_validate(
        _read_v49a_json("reference_semantic_normal_form.json")
    )
    transform_contract = SemanticTransformContract.model_validate(
        _read_json("mutation_semantic_transform_contract_profile_mismatch.json")
    )

    with pytest.raises(SemanticFormsLoweringError) as excinfo:
        lower_semantic_normal_form_to_taskpack_binding_spec_seed(
            normal_form=normal_form,
            transform_contract=transform_contract,
        )

    assert excinfo.value.code == "ASF5903"


def test_fixed_default_conflict_fails_closed() -> None:
    normal_form = SemanticNormalForm.model_validate(
        _read_v49a_json("reference_semantic_normal_form.json")
    )
    transform_contract = SemanticTransformContract.model_validate(
        _read_json("mutation_semantic_transform_contract_fixed_default_conflict.json")
    )

    with pytest.raises(SemanticFormsLoweringError) as excinfo:
        lower_semantic_normal_form_to_taskpack_binding_spec_seed(
            normal_form=normal_form,
            transform_contract=transform_contract,
        )

    assert excinfo.value.code == "ASF5907"


def test_repeated_lowering_is_byte_identical() -> None:
    normal_form = SemanticNormalForm.model_validate(
        _read_v49a_json("reference_semantic_normal_form.json")
    )
    transform_contract = SemanticTransformContract.model_validate(
        _read_v49a_json("reference_semantic_transform_contract.json")
    )

    first = lower_semantic_normal_form_to_taskpack_binding_spec_seed(
        normal_form=normal_form,
        transform_contract=transform_contract,
    )
    second = lower_semantic_normal_form_to_taskpack_binding_spec_seed(
        normal_form=normal_form,
        transform_contract=transform_contract,
    )

    assert first.model_dump(mode="json", by_alias=True, exclude_none=True) == second.model_dump(
        mode="json", by_alias=True, exclude_none=True
    )
