from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    ADEU_ARCHITECTURE_PROJECTION_BUNDLE_SCHEMA,
    ADEU_ARCHITECTURE_PROJECTION_MANIFEST_SCHEMA,
    ADEU_CORE_IR_TARGET_FAMILY,
    AdeuArchitectureProjectionBundle,
    AdeuArchitectureProjectionManifest,
    canonicalize_adeu_architecture_projection_bundle_payload,
    canonicalize_adeu_architecture_projection_manifest_payload,
    derive_v40d_adeu_core_ir,
    derive_v40d_projection_bundle,
    derive_v40d_projection_manifest,
)
from adeu_core_ir import AdeuCoreIR
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v77_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus77"


def _v78_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus78"


def _v79_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus79"


def _v80_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus80"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v77(name: str) -> dict[str, object]:
    return _load_json(_v77_root() / name)


def _load_v78(name: str) -> dict[str, object]:
    return _load_json(_v78_root() / name)


def _load_v79(name: str) -> dict[str, object]:
    return _load_json(_v79_root() / name)


def _load_v80(name: str) -> dict[str, object]:
    return _load_json(_v80_root() / name)


def _schema_validator(stem: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_architecture_compiler" / "schema" / f"{stem}.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v40d_ready_projection_reference_fixtures_validate_and_replay() -> None:
    bundle_fixture = _load_v80("adeu_architecture_projection_bundle_v80_ready_reference.json")
    manifest_fixture = _load_v80("adeu_architecture_projection_manifest_v80_ready_reference.json")
    core_ir_fixture = _load_v80("adeu_core_ir_v80_ready_reference.json")

    bundle = AdeuArchitectureProjectionBundle.model_validate(
        bundle_fixture,
        context={"repository_root": _repo_root()},
    )
    manifest = AdeuArchitectureProjectionManifest.model_validate(
        manifest_fixture,
        context={"repository_root": _repo_root()},
    )
    core_ir = AdeuCoreIR.model_validate(core_ir_fixture)

    assert bundle.schema == ADEU_ARCHITECTURE_PROJECTION_BUNDLE_SCHEMA
    assert manifest.schema == ADEU_ARCHITECTURE_PROJECTION_MANIFEST_SCHEMA
    assert core_ir.schema == ADEU_CORE_IR_TARGET_FAMILY

    derived_core_ir = derive_v40d_adeu_core_ir(
        semantic_ir_payload=_load_v78("adeu_architecture_semantic_ir_v78_ready_derivative.json"),
        conformance_report_payload=_load_v78(
            "adeu_architecture_conformance_report_v78_ready_reference.json"
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
        checkpoint_trace_payload=_load_v79(
            "adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json"
        ),
        checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
        repository_root=_repo_root(),
    )
    derived_bundle = derive_v40d_projection_bundle(
        semantic_ir_payload=_load_v78("adeu_architecture_semantic_ir_v78_ready_derivative.json"),
        conformance_report_payload=_load_v78(
            "adeu_architecture_conformance_report_v78_ready_reference.json"
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
        checkpoint_trace_payload=_load_v79(
            "adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json"
        ),
        checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
        core_ir_output_path="apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json",
        repository_root=_repo_root(),
    )
    derived_manifest = derive_v40d_projection_manifest(
        semantic_ir_payload=_load_v78("adeu_architecture_semantic_ir_v78_ready_derivative.json"),
        conformance_report_payload=_load_v78(
            "adeu_architecture_conformance_report_v78_ready_reference.json"
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
        checkpoint_trace_payload=_load_v79(
            "adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json"
        ),
        checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
        core_ir_output_path="apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json",
        repository_root=_repo_root(),
    )

    assert derived_core_ir == core_ir_fixture
    assert derived_bundle == bundle_fixture
    assert derived_manifest == manifest_fixture
    assert (
        canonicalize_adeu_architecture_projection_bundle_payload(
            bundle_fixture,
            repository_root=_repo_root(),
        )
        == bundle_fixture
    )
    assert (
        canonicalize_adeu_architecture_projection_manifest_payload(
            manifest_fixture,
            repository_root=_repo_root(),
        )
        == manifest_fixture
    )


def test_v40d_blocked_projection_reference_fixtures_validate_and_replay() -> None:
    bundle_fixture = _load_v80("adeu_architecture_projection_bundle_v80_blocked_reference.json")
    manifest_fixture = _load_v80("adeu_architecture_projection_manifest_v80_blocked_reference.json")

    bundle = AdeuArchitectureProjectionBundle.model_validate(
        bundle_fixture,
        context={"repository_root": _repo_root()},
    )
    manifest = AdeuArchitectureProjectionManifest.model_validate(
        manifest_fixture,
        context={"repository_root": _repo_root()},
    )

    assert bundle.projection_units[0].readiness == "blocked"
    assert bundle.projection_units[0].output_artifact_refs == []
    assert manifest.touched_artifact_refs == []
    assert manifest.blocked_by_ambiguity_refs == ["amb_auto_approve_threshold"]

    derived_bundle = derive_v40d_projection_bundle(
        semantic_ir_payload=_load_v77("adeu_architecture_semantic_ir_v77_reference.json"),
        conformance_report_payload=_load_v78(
            "adeu_architecture_conformance_report_v78_blocked_reference.json"
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json",
        checkpoint_trace_payload=_load_v79(
            "adeu_architecture_checkpoint_trace_v79_human_needed_reference.json"
        ),
        checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
        repository_root=_repo_root(),
    )
    derived_manifest = derive_v40d_projection_manifest(
        semantic_ir_payload=_load_v77("adeu_architecture_semantic_ir_v77_reference.json"),
        conformance_report_payload=_load_v78(
            "adeu_architecture_conformance_report_v78_blocked_reference.json"
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json",
        checkpoint_trace_payload=_load_v79(
            "adeu_architecture_checkpoint_trace_v79_human_needed_reference.json"
        ),
        checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
        repository_root=_repo_root(),
    )

    assert derived_bundle == bundle_fixture
    assert derived_manifest == manifest_fixture


def test_v40d_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("adeu_architecture_projection_bundle").validate(
        _load_v80("adeu_architecture_projection_bundle_v80_ready_reference.json")
    )
    _schema_validator("adeu_architecture_projection_bundle").validate(
        _load_v80("adeu_architecture_projection_bundle_v80_blocked_reference.json")
    )
    _schema_validator("adeu_architecture_projection_manifest").validate(
        _load_v80("adeu_architecture_projection_manifest_v80_ready_reference.json")
    )
    _schema_validator("adeu_architecture_projection_manifest").validate(
        _load_v80("adeu_architecture_projection_manifest_v80_blocked_reference.json")
    )


def test_v40d_ready_core_ir_fixture_has_oedu_layers_and_allowed_edges_only() -> None:
    fixture = _load_v80("adeu_core_ir_v80_ready_reference.json")
    core_ir = AdeuCoreIR.model_validate(fixture)

    assert {node.layer for node in core_ir.nodes} == {"O", "E", "D", "U"}
    assert {edge.type for edge in core_ir.edges} <= {
        "depends_on",
        "gates",
        "justifies",
        "prioritizes",
        "serves_goal",
    }
    assert "gate_decide" in {node.id for node in core_ir.nodes}
    assert "goal_trust" in {node.id for node in core_ir.nodes}


def test_v40d_projection_bundle_rejects_nonempty_outputs_for_blocked_unit() -> None:
    payload = deepcopy(_load_v80("adeu_architecture_projection_bundle_v80_blocked_reference.json"))
    payload["projection_units"][0]["output_artifact_refs"] = [
        "apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json"
    ]

    with pytest.raises(
        ValidationError,
        match="blocked projection units must carry empty output_artifact_refs",
    ):
        AdeuArchitectureProjectionBundle.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40d_projection_bundle_rejects_non_core_target_family() -> None:
    payload = deepcopy(_load_v80("adeu_architecture_projection_bundle_v80_ready_reference.json"))
    payload["target_family"] = "ux_domain_packet@1"

    with pytest.raises(ValidationError):
        AdeuArchitectureProjectionBundle.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40d_projection_manifest_rejects_touched_artifact_refs_mismatch() -> None:
    payload = deepcopy(_load_v80("adeu_architecture_projection_manifest_v80_ready_reference.json"))
    payload["touched_artifact_refs"] = []

    with pytest.raises(
        ValidationError,
        match="touched_artifact_refs must match the union of projection_unit output_artifact_refs",
    ):
        AdeuArchitectureProjectionManifest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40d_ready_projection_requires_ready_conformance_and_no_blockers() -> None:
    with pytest.raises(
        ValueError,
        match="blocked V40-D projection units may not emit core_ir_output_path",
    ):
        derive_v40d_projection_bundle(
            semantic_ir_payload=_load_v77("adeu_architecture_semantic_ir_v77_reference.json"),
            conformance_report_payload=_load_v78(
                "adeu_architecture_conformance_report_v78_blocked_reference.json"
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json",
            checkpoint_trace_payload=_load_v79(
                "adeu_architecture_checkpoint_trace_v79_human_needed_reference.json"
            ),
            checkpoint_trace_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
            core_ir_output_path="apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json",
            repository_root=_repo_root(),
        )
