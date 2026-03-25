from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA,
    V40FArchitectureReleaseIntegrationEvidence,
    canonicalize_v40f_architecture_release_integration_evidence_payload,
    derive_v40f_release_integration_evidence,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v82_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus82"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v82(name: str) -> dict[str, object]:
    return _load_json(_v82_root() / name)


def _sha256_text(path: str) -> str:
    import hashlib

    file_path = _repo_root() / path
    return hashlib.sha256(file_path.read_text(encoding="utf-8").encode("utf-8")).hexdigest()


def _schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_architecture_compiler"
            / "schema"
            / "v40f_architecture_release_integration_evidence.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v40f_family_evidence_reference_fixture_replays() -> None:
    fixture = _load_v82("v40f_architecture_release_integration_evidence_v82_reference.json")

    evidence = V40FArchitectureReleaseIntegrationEvidence.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )
    assert evidence.schema == V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA

    derived = derive_v40f_release_integration_evidence(repository_root=_repo_root())
    assert derived == fixture
    assert (
        canonicalize_v40f_architecture_release_integration_evidence_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v40f_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator().validate(_load_v82("v40f_architecture_release_integration_evidence_v82_reference.json"))


def test_v40f_rejects_missing_path_closure() -> None:
    payload = deepcopy(
        _load_v82("v40f_architecture_release_integration_evidence_v82_reference.json")
    )
    del payload["per_path_release_closure"]["V40-E"]

    with pytest.raises(
        ValueError,
        match="per_path_release_closure must provide exact keyed closure for V40-A..V40-E",
    ):
        V40FArchitectureReleaseIntegrationEvidence.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40f_rejects_deferred_surface_overclaiming() -> None:
    payload = deepcopy(
        _load_v82("v40f_architecture_release_integration_evidence_v82_reference.json")
    )
    deferred_surface = "packages/adeu_core_ir/schema/ux_morph_ir.v1.json"
    payload["family_release_surface_refs"] = sorted(
        set(payload["family_release_surface_refs"]) | {deferred_surface}
    )

    with pytest.raises(
        ValueError,
        match=(
            "family_release_surface_refs may point only to already released "
            "V40-A through V40-E surfaces"
        ),
    ):
        V40FArchitectureReleaseIntegrationEvidence.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40f_rejects_formal_sidecar_authority_inflation() -> None:
    payload = deepcopy(
        _load_v82("v40f_architecture_release_integration_evidence_v82_reference.json")
    )
    formal_ref = "docs/formal/asir/ASIR_FORMAL_KERNEL.md"
    payload["per_path_release_closure"]["V40-E"]["release_surface_refs"].append(formal_ref)
    payload["per_path_release_closure"]["V40-E"]["release_surface_hashes"][formal_ref] = (
        _sha256_text(formal_ref)
    )
    payload["family_release_surface_refs"] = sorted(
        set(payload["family_release_surface_refs"]) | {formal_ref}
    )

    with pytest.raises(
        ValueError,
        match="formal-sidecar files may not be admitted as family release surfaces",
    ):
        V40FArchitectureReleaseIntegrationEvidence.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40f_rejects_metric_key_drift() -> None:
    payload = deepcopy(
        _load_v82("v40f_architecture_release_integration_evidence_v82_reference.json")
    )
    payload["metric_keys"] = payload["metric_keys"][:-1]
    payload["metric_key_cardinality"] = len(payload["metric_keys"])

    with pytest.raises(
        ValueError,
        match="metric_keys must match the exact v81 stop-gate metric key set",
    ):
        V40FArchitectureReleaseIntegrationEvidence.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40f_rejects_release_hash_drift() -> None:
    payload = deepcopy(
        _load_v82("v40f_architecture_release_integration_evidence_v82_reference.json")
    )
    payload["per_path_release_closure"]["V40-A"]["evidence_hash"] = "0" * 64

    with pytest.raises(
        ValueError,
        match="evidence_hash must match the referenced evidence_ref contents",
    ):
        V40FArchitectureReleaseIntegrationEvidence.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )
