from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agent_harness.compiled_taskpack_binding import (
    AHK5701_INPUT_INVALID,
    AHK5702_SCHEMA_MISMATCH,
    AHK5703_CARDINALITY_VIOLATION,
    AHK5704_LINEAGE_UNRESOLVED,
    AHK5705_LINEAGE_MISMATCH,
    AHK5706_BRIDGE_INVALID,
    COMPILED_POLICY_TASKPACK_BINDING_SCHEMA,
    CompiledPolicyTaskpackBinding,
    CompiledPolicyTaskpackBindingError,
    compile_v48b_taskpack_binding,
)
from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v48b" / name


def _read_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_fixture(name: str) -> dict[str, object]:
    return _read_json(_fixture_path(name))


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _seed_reference_repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    root.mkdir()
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    (root / "pyproject.toml").write_text("[tool.ruff]\nline-length = 100\n", encoding="utf-8")

    source_root = _repo_root()
    for rel_path in (
        "packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json",
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
        root / "artifacts" / "semantic_compiler" / "v40" / "commitments_ir.json",
        {
            "schema": "adeu_commitments_ir@0.1",
            "modules": [],
            "locks": [],
        },
    )

    return root


def test_v48b_reference_compiled_binding_replays_deterministically(tmp_path: Path) -> None:
    root = _seed_reference_repo(tmp_path)
    spec = _read_fixture("reference_compiled_taskpack_binding_spec.json")

    first = compile_v48b_taskpack_binding(
        **spec,
        repo_root_path=root,
    )
    first_bytes = {
        "compiled_binding": first.compiled_binding_path.read_bytes(),
        "pipeline_profile": first.pipeline_profile_path.read_bytes(),
        "profile_registry": first.profile_registry_path.read_bytes(),
        "taskpack_markdown": (root / spec["out_dir"] / "TASKPACK.md").read_bytes(),
        "taskpack_manifest": (root / spec["out_dir"] / "taskpack_manifest.json").read_bytes(),
    }
    second = compile_v48b_taskpack_binding(
        **spec,
        repo_root_path=root,
    )

    assert (
        first.compiled_binding.model_dump(mode="json", exclude_none=True)
        == _read_fixture("reference_compiled_policy_taskpack_binding.json")
    )
    assert _read_json(first.pipeline_profile_path) == _read_fixture(
        "reference_pipeline_profile.json"
    )
    assert _read_json(first.profile_registry_path) == _read_fixture(
        "reference_profile_registry.json"
    )

    assert first_bytes["compiled_binding"] == second.compiled_binding_path.read_bytes()
    assert first_bytes["pipeline_profile"] == second.pipeline_profile_path.read_bytes()
    assert first_bytes["profile_registry"] == second.profile_registry_path.read_bytes()
    assert first_bytes["taskpack_markdown"] == (root / spec["out_dir"] / "TASKPACK.md").read_bytes()
    assert first_bytes["taskpack_manifest"] == (
        root / spec["out_dir"] / "taskpack_manifest.json"
    ).read_bytes()


def test_v48b_model_accepts_committed_reference_payload() -> None:
    payload = _read_fixture("reference_compiled_policy_taskpack_binding.json")

    compiled_binding = CompiledPolicyTaskpackBinding.model_validate(payload)

    assert compiled_binding.schema == COMPILED_POLICY_TASKPACK_BINDING_SCHEMA
    assert compiled_binding.compiler_selection == "python -m adeu_agent_harness.compile"


def test_v48b_rejects_multiple_binding_profile_refs(tmp_path: Path) -> None:
    root = _seed_reference_repo(tmp_path)
    spec = _read_fixture("reject_multiple_binding_profile_refs_spec.json")

    with pytest.raises(CompiledPolicyTaskpackBindingError, match=AHK5703_CARDINALITY_VIOLATION):
        compile_v48b_taskpack_binding(
            **spec,
            repo_root_path=root,
        )


def test_v48b_rejects_raw_v47_bypass(tmp_path: Path) -> None:
    root = _seed_reference_repo(tmp_path)
    spec = _read_fixture("reject_raw_v47_bypass_spec.json")

    with pytest.raises(CompiledPolicyTaskpackBindingError, match=AHK5702_SCHEMA_MISMATCH):
        compile_v48b_taskpack_binding(
            **spec,
            repo_root_path=root,
        )


def test_v48b_rejects_binding_profile_hash_mismatch(tmp_path: Path) -> None:
    root = _seed_reference_repo(tmp_path)
    spec = _read_fixture("reject_binding_profile_hash_mismatch_spec.json")

    with pytest.raises(CompiledPolicyTaskpackBindingError, match=AHK5705_LINEAGE_MISMATCH):
        compile_v48b_taskpack_binding(
            **spec,
            repo_root_path=root,
        )


def test_v48b_rejects_ambiguous_source_semantic_arc(tmp_path: Path) -> None:
    root = _seed_reference_repo(tmp_path)
    spec = _read_fixture("reject_source_semantic_arc_ambiguous_spec.json")

    with pytest.raises(CompiledPolicyTaskpackBindingError, match=AHK5703_CARDINALITY_VIOLATION):
        compile_v48b_taskpack_binding(
            **spec,
            repo_root_path=root,
        )


def test_v48b_rejects_malformed_pipeline_profile_bridge(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = _seed_reference_repo(tmp_path)
    spec = _read_fixture("reference_compiled_taskpack_binding_spec.json")

    from adeu_agent_harness import compiled_taskpack_binding as compiled_binding_mod

    original_builder = compiled_binding_mod._build_pipeline_profile_payload

    def _malformed_pipeline_profile(**kwargs: object) -> dict[str, object]:
        payload = original_builder(**kwargs)
        payload.pop("commands")
        return payload

    monkeypatch.setattr(
        compiled_binding_mod,
        "_build_pipeline_profile_payload",
        _malformed_pipeline_profile,
    )

    with pytest.raises(CompiledPolicyTaskpackBindingError, match=AHK5706_BRIDGE_INVALID):
        compile_v48b_taskpack_binding(
            **spec,
            repo_root_path=root,
        )


def test_v48b_rejects_out_dir_symlink_escape(tmp_path: Path) -> None:
    root = _seed_reference_repo(tmp_path)
    spec = _read_fixture("reference_compiled_taskpack_binding_spec.json")
    external = tmp_path / "external_out"
    external.mkdir()
    (root / "leak").symlink_to(external, target_is_directory=True)
    spec["out_dir"] = "leak/out"

    with pytest.raises(CompiledPolicyTaskpackBindingError, match=AHK5701_INPUT_INVALID):
        compile_v48b_taskpack_binding(
            **spec,
            repo_root_path=root,
        )


def test_v48b_rejects_semantic_authority_symlink_escape(tmp_path: Path) -> None:
    root = _seed_reference_repo(tmp_path)
    spec = _read_fixture("reference_compiled_taskpack_binding_spec.json")
    shutil.rmtree(root / "artifacts" / "semantic_compiler" / "v41")

    external = tmp_path / "external_semantic_arc"
    external.mkdir()
    _write_json(
        external / "evidence_manifest.json",
        {
            "schema": "semantic_compiler_evidence_manifest@0.1",
            "arc": "vnext_plus41",
            "compiler_entrypoint": "python -m adeu_semantic_compiler.compile",
            "source_set_hash": "0" * 64,
            "required_evidence": [],
            "artifacts": {},
            "artifact_hashes": {},
        },
    )
    _write_json(
        external / "surface_diff.json",
        {
            "schema": "semantic_compiler_surface_diff@0.1",
            "baseline_present": True,
            "delta_eval_mode": "exact_set",
            "adds": [],
            "removes": [],
            "changes": [],
        },
    )
    (root / "artifacts" / "semantic_compiler" / "v41").symlink_to(
        external,
        target_is_directory=True,
    )

    with pytest.raises(CompiledPolicyTaskpackBindingError, match=AHK5704_LINEAGE_UNRESOLVED):
        compile_v48b_taskpack_binding(
            **spec,
            repo_root_path=root,
        )
