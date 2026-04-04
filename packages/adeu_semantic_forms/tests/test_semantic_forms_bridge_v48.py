from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agent_harness import compile_v48b_taskpack_binding
from adeu_ir.repo import repo_root
from adeu_semantic_forms import (
    ADEU_SEMANTIC_SEED_V48_BRIDGE_CONTRACT_SCHEMA,
    SemanticFormsV48BridgeError,
    SemanticSeedV48BridgeContract,
    TaskpackBindingSpecSeed,
    bridge_seed_to_v48a_taskpack_binding_profile,
    build_reference_repo_policy_work_profile,
    build_reference_v48_bridge_contract,
)
from urm_runtime.hashing import canonical_json


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v49d" / name


def _read_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_fixture(name: str) -> dict[str, object]:
    return _read_json(_fixture_path(name))


def _read_v48a_json(name: str) -> dict[str, object]:
    return _read_json(
        _repo_root()
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48a"
        / name
    )


def _read_v48b_json(name: str) -> dict[str, object]:
    return _read_json(
        _repo_root()
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48b"
        / name
    )


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _seed_reference_repo(tmp_path: Path, *, binding_profile: dict[str, object]) -> Path:
    root = tmp_path / "repo"
    root.mkdir()
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    (root / "pyproject.toml").write_text("[tool.ruff]\nline-length = 100\n", encoding="utf-8")

    source_root = _repo_root()
    for rel_path in (
        "packages/adeu_commitments_ir/tests/fixtures/v47e/reference_anm_policy_consumer_binding_profile.json",
        "apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json",
        "apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json",
        "artifacts/semantic_compiler/v41/evidence_manifest.json",
        "artifacts/semantic_compiler/v41/surface_diff.json",
    ):
        destination = root / rel_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_root / rel_path, destination)

    _write_json(
        root
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48a"
        / "reference_anm_taskpack_binding_profile.json",
        binding_profile,
    )
    _write_json(
        root / "artifacts" / "semantic_compiler" / "v40" / "commitments_ir.json",
        {
            "schema": "adeu_commitments_ir@0.1",
            "modules": [],
            "locks": [],
        },
    )

    return root


def test_reference_bridge_contract_builder_replays_committed_fixture() -> None:
    profile = build_reference_repo_policy_work_profile()
    fixture = _read_fixture("reference_semantic_seed_v48_bridge_contract.json")

    contract = build_reference_v48_bridge_contract(profile.profile_id)

    assert contract.schema == ADEU_SEMANTIC_SEED_V48_BRIDGE_CONTRACT_SCHEMA
    assert contract.model_dump(mode="json", by_alias=True, exclude_none=True) == fixture


def test_reference_bridge_contract_fixture_validates() -> None:
    fixture = _read_fixture("reference_semantic_seed_v48_bridge_contract.json")

    contract = SemanticSeedV48BridgeContract.model_validate(fixture)

    assert contract.semantic_hash == fixture["semantic_hash"]


def test_reference_bridge_replays_released_v48a_binding_profile() -> None:
    seed = TaskpackBindingSpecSeed.model_validate(
        _read_fixture("reference_taskpack_binding_spec_seed.json")
    )
    contract = SemanticSeedV48BridgeContract.model_validate(
        _read_fixture("reference_semantic_seed_v48_bridge_contract.json")
    )
    reference_binding_profile = _read_v48a_json("reference_anm_taskpack_binding_profile.json")

    binding_profile = bridge_seed_to_v48a_taskpack_binding_profile(
        seed=seed,
        bridge_contract=contract,
        repo_root_path=_repo_root(),
    )

    assert binding_profile.model_dump(mode="json", exclude_none=True) == reference_binding_profile


def test_repeated_bridge_is_byte_identical() -> None:
    seed = TaskpackBindingSpecSeed.model_validate(
        _read_fixture("reference_taskpack_binding_spec_seed.json")
    )
    contract = SemanticSeedV48BridgeContract.model_validate(
        _read_fixture("reference_semantic_seed_v48_bridge_contract.json")
    )

    first = bridge_seed_to_v48a_taskpack_binding_profile(
        seed=seed,
        bridge_contract=contract,
        repo_root_path=_repo_root(),
    )
    second = bridge_seed_to_v48a_taskpack_binding_profile(
        seed=seed,
        bridge_contract=contract,
        repo_root_path=_repo_root(),
    )

    assert first.model_dump(mode="json", exclude_none=True) == second.model_dump(
        mode="json", exclude_none=True
    )


def test_scope_anchor_mismatch_fails_closed() -> None:
    seed = TaskpackBindingSpecSeed.model_validate(
        _read_fixture("reference_taskpack_binding_spec_seed.json")
    )
    contract = SemanticSeedV48BridgeContract.model_validate(
        _read_fixture("mutation_semantic_seed_v48_bridge_contract_scope_anchor_mismatch.json")
    )

    with pytest.raises(SemanticFormsV48BridgeError) as excinfo:
        bridge_seed_to_v48a_taskpack_binding_profile(
            seed=seed,
            bridge_contract=contract,
            repo_root_path=_repo_root(),
        )

    assert excinfo.value.code == "ASF6003"


def test_snapshot_mismatch_fails_closed() -> None:
    seed = TaskpackBindingSpecSeed.model_validate(
        _read_fixture("reference_taskpack_binding_spec_seed.json")
    )
    contract = SemanticSeedV48BridgeContract.model_validate(
        _read_fixture("mutation_semantic_seed_v48_bridge_contract_snapshot_mismatch.json")
    )

    with pytest.raises(SemanticFormsV48BridgeError) as excinfo:
        bridge_seed_to_v48a_taskpack_binding_profile(
            seed=seed,
            bridge_contract=contract,
            repo_root_path=_repo_root(),
        )

    assert excinfo.value.code == "ASF6006"
    assert excinfo.value.details["upstream_code"] == "AHK5605"


def test_prompt_authority_drift_fails_closed() -> None:
    seed = TaskpackBindingSpecSeed.model_validate(
        _read_fixture("reference_taskpack_binding_spec_seed.json")
    )
    contract = SemanticSeedV48BridgeContract.model_validate(
        _read_fixture("mutation_semantic_seed_v48_bridge_contract_prompt_authority_drift.json")
    )

    with pytest.raises(SemanticFormsV48BridgeError) as excinfo:
        bridge_seed_to_v48a_taskpack_binding_profile(
            seed=seed,
            bridge_contract=contract,
            repo_root_path=_repo_root(),
        )

    assert excinfo.value.code == "ASF6006"
    assert excinfo.value.details["upstream_code"] == "AHK5607"


def test_fixed_default_conflict_fails_closed() -> None:
    seed = TaskpackBindingSpecSeed.model_validate(
        _read_fixture("mutation_taskpack_binding_spec_seed_fixed_default_conflict.json")
    )
    contract = SemanticSeedV48BridgeContract.model_validate(
        _read_fixture("reference_semantic_seed_v48_bridge_contract.json")
    )

    with pytest.raises(SemanticFormsV48BridgeError) as excinfo:
        bridge_seed_to_v48a_taskpack_binding_profile(
            seed=seed,
            bridge_contract=contract,
            repo_root_path=_repo_root(),
        )

    assert excinfo.value.code == "ASF6004"


@pytest.mark.parametrize("field_name", ["allow_paths", "forbid_paths", "forbid_effects"])
def test_empty_seed_projection_fails_closed(field_name: str) -> None:
    seed_payload = _read_fixture("reference_taskpack_binding_spec_seed.json")
    seed_payload[field_name] = []
    seed_payload["seed_id"] = "derived-by-model-validator"
    seed_payload["seed_hash"] = "derived-by-model-validator"
    seed = TaskpackBindingSpecSeed.model_validate(seed_payload)
    contract = SemanticSeedV48BridgeContract.model_validate(
        _read_fixture("reference_semantic_seed_v48_bridge_contract.json")
    )

    with pytest.raises(SemanticFormsV48BridgeError) as excinfo:
        bridge_seed_to_v48a_taskpack_binding_profile(
            seed=seed,
            bridge_contract=contract,
            repo_root_path=_repo_root(),
        )

    assert excinfo.value.code == "ASF6005"
    assert excinfo.value.details["missing_projection_fields"] == [field_name]


def test_reference_bridge_output_is_compile_compatible(tmp_path: Path) -> None:
    seed = TaskpackBindingSpecSeed.model_validate(
        _read_fixture("reference_taskpack_binding_spec_seed.json")
    )
    contract = SemanticSeedV48BridgeContract.model_validate(
        _read_fixture("reference_semantic_seed_v48_bridge_contract.json")
    )
    bridge_output = bridge_seed_to_v48a_taskpack_binding_profile(
        seed=seed,
        bridge_contract=contract,
        repo_root_path=_repo_root(),
    )
    bridge_payload = bridge_output.model_dump(mode="json", exclude_none=True)
    root = _seed_reference_repo(tmp_path, binding_profile=bridge_payload)
    spec = _read_v48b_json("reference_compiled_taskpack_binding_spec.json")

    compiled = compile_v48b_taskpack_binding(
        **spec,
        repo_root_path=root,
    )

    assert compiled.compiled_binding.binding_profile_semantic_hash == bridge_output.semantic_hash
    assert compiled.compiled_binding.model_dump(mode="json", exclude_none=True) == _read_v48b_json(
        "reference_compiled_policy_taskpack_binding.json"
    )
