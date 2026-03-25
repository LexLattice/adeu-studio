from __future__ import annotations

import json
import subprocess
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_ir import (
    ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA,
    AdeuArchitectureAnalysisRequest,
    canonicalize_adeu_architecture_analysis_request_payload,
    compute_adeu_architecture_analysis_source_set_hash,
    materialize_adeu_architecture_analysis_request_payload,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError
from urm_runtime.hashing import sha256_text


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixtures_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus83"


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def _load_exported_schema(name: str) -> Draft202012Validator:
    schema = json.loads(
        (_repo_root() / "packages" / "adeu_architecture_ir" / "schema" / name).read_text(
            encoding="utf-8"
        )
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _fixture_commit_sha() -> str:
    fixture = _load_json("adeu_architecture_analysis_request_v83_reference.json")
    return str(fixture["snapshot_identity"]["commit_sha"])


def _sha256_committed_text(path: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(_repo_root()), "show", f"{_fixture_commit_sha()}:{path}"],
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return sha256_text(result.stdout)


def test_v41a_analysis_request_fixture_validates_and_replays() -> None:
    fixture = _load_json("adeu_architecture_analysis_request_v83_reference.json")
    request = AdeuArchitectureAnalysisRequest.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert request.schema == ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA
    assert request.snapshot_mode == "committed_tree"
    assert request.source_set_hash == compute_adeu_architecture_analysis_source_set_hash(
        fixture["source_set"]
    )
    assert (
        canonicalize_adeu_architecture_analysis_request_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v41a_materialize_reference_fixture_replays() -> None:
    fixture = _load_json("adeu_architecture_analysis_request_v83_reference.json")
    payload = deepcopy(fixture)
    payload.pop("source_set")
    payload.pop("source_set_hash")

    materialized = materialize_adeu_architecture_analysis_request_payload(
        payload,
        repository_root=_repo_root(),
    )

    assert materialized == fixture


def test_v41a_exported_schema_accepts_reference_fixture() -> None:
    validator = _load_exported_schema("adeu_architecture_analysis_request.v1.json")
    validator.validate(_load_json("adeu_architecture_analysis_request_v83_reference.json"))


def test_v41a_rejects_unsupported_snapshot_mode() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    payload["snapshot_mode"] = "working_tree"

    with pytest.raises(ValidationError):
        AdeuArchitectureAnalysisRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41a_rejects_missing_committed_tree_identity() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    payload["snapshot_identity"] = {}

    with pytest.raises(ValidationError, match="committed_tree requires"):
        AdeuArchitectureAnalysisRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41a_rejects_source_item_outside_scope() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    payload["source_set"]["items"].append(
        {
            "path": "README.md",
            "artifact_kind": "documentation",
            "sha256": _sha256_committed_text("README.md"),
        }
    )
    payload["source_set_hash"] = compute_adeu_architecture_analysis_source_set_hash(
        payload["source_set"]
    )

    with pytest.raises(ValidationError, match="outside request_scope"):
        AdeuArchitectureAnalysisRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41a_rejects_scope_escape_path() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    payload["request_scope"]["include_paths"] = ["../README.md"]

    with pytest.raises(ValidationError, match="must not escape repository root"):
        canonicalize_adeu_architecture_analysis_request_payload(
            payload,
            repository_root=_repo_root(),
        )


def test_v41a_rejects_artifact_kind_mismatch() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    payload["source_set"]["items"][0]["artifact_kind"] = "source_code"

    with pytest.raises(ValidationError, match="artifact_kind"):
        AdeuArchitectureAnalysisRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41a_rejects_unbound_brief_ref() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    payload["maintainer_brief_refs"] = ["missing_brief.md"]

    with pytest.raises(
        ValidationError,
        match="must resolve to source_set content or captured_inputs",
    ):
        AdeuArchitectureAnalysisRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41a_rejects_missing_policy_pinning() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    del payload["authority_boundary_policy"]

    with pytest.raises(ValidationError):
        AdeuArchitectureAnalysisRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41a_rejects_request_level_drift_authority_claim() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    payload["drift_claim_authority"] = True

    with pytest.raises(ValidationError):
        AdeuArchitectureAnalysisRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41a_canonicalizes_source_set_order_by_normalized_path() -> None:
    payload = deepcopy(_load_json("adeu_architecture_analysis_request_v83_reference.json"))
    payload["source_set"]["items"] = list(reversed(payload["source_set"]["items"]))

    canonical = canonicalize_adeu_architecture_analysis_request_payload(
        payload,
        repository_root=_repo_root(),
    )

    assert canonical["source_set"]["items"] == sorted(
        canonical["source_set"]["items"],
        key=lambda item: item["path"],
    )
