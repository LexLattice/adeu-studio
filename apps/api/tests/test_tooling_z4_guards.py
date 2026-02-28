from __future__ import annotations

import hashlib
import json
import socket
from contextlib import ExitStack
from pathlib import Path
from typing import Any
from unittest.mock import patch

import adeu_api.openai_provider as openai_provider
import pytest
from adeu_api.hashing import sha256_canonical_json
from adeu_api.read_surface_runtime_guards import NoProviderCallsGuard
from urm_runtime.core_ir_proposer_transfer_report_vnext_plus25 import (
    CORE_IR_PROPOSER_TRANSFER_REPORT_VNEXT_PLUS25_SCHEMA,
    build_core_ir_proposer_transfer_report_vnext_plus25_payload,
)
from urm_runtime.extraction_fidelity_transfer_report_vnext_plus24 import (
    EXTRACTION_FIDELITY_TRANSFER_REPORT_VNEXT_PLUS24_SCHEMA,
    build_extraction_fidelity_transfer_report_vnext_plus24_payload,
)
from urm_runtime.stop_gate_registry import (
    ACTIVE_STOP_GATE_MANIFEST_VERSIONS,
    default_stop_gate_manifest_path,
)
from urm_runtime.stop_gate_tools import STOP_GATE_SCHEMA, build_stop_gate_metrics

_MATERIALIZATION_POLICY_FLOW_TARGETS: tuple[str, ...] = (
    "adeu_api.main.create_artifact",
    "adeu_api.main.create_concept_artifact",
    "adeu_api.main.create_document",
    "adeu_api.main.create_explain_artifact",
    "adeu_api.main.create_proof_artifact",
    "adeu_api.main.create_semantic_depth_report",
    "adeu_api.main.create_validator_run",
    "adeu_api.main.emit_governance_event",
    "adeu_api.storage.create_artifact",
    "adeu_api.storage.create_concept_artifact",
    "adeu_api.storage.create_document",
    "adeu_api.storage.create_explain_artifact",
    "adeu_api.storage.create_proof_artifact",
    "adeu_api.storage.create_semantic_depth_report",
    "adeu_api.storage.create_validator_run",
)
_NON_ENFORCEMENT_FIELD_NAMES: frozenset[str] = frozenset(
    {"enforce", "block", "gate", "allow", "deny"}
)
_TRUST_LANE_FIELD_NAMES: frozenset[str] = frozenset(
    {"mapping_trust", "solver_trust", "proof_trust"}
)
_ToolingReports = tuple[dict[str, Any], dict[str, Any], dict[str, Any]]


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _stop_gate_manifest_path(version: int) -> Path:
    return default_stop_gate_manifest_path(version).resolve()


def _base_stop_gate_kwargs() -> dict[str, Any]:
    repo_root = _repo_root()
    return {
        "incident_packet_paths": [
            repo_root / "examples" / "eval" / "stop_gate" / "incident_packet_case_a_1.json",
            repo_root / "examples" / "eval" / "stop_gate" / "incident_packet_case_a_2.json",
        ],
        "event_stream_paths": [
            repo_root / "apps" / "api" / "tests" / "fixtures" / "urm_events" / "sample_valid.ndjson"
        ],
        "connector_snapshot_paths": [
            repo_root / "examples" / "eval" / "stop_gate" / "connector_snapshot_case_a_1.json",
            repo_root / "examples" / "eval" / "stop_gate" / "connector_snapshot_case_a_2.json",
        ],
        "validator_evidence_packet_paths": [
            repo_root
            / "examples"
            / "eval"
            / "stop_gate"
            / "validator_evidence_packet_case_a_1.json",
            repo_root
            / "examples"
            / "eval"
            / "stop_gate"
            / "validator_evidence_packet_case_a_2.json",
            repo_root
            / "examples"
            / "eval"
            / "stop_gate"
            / "validator_evidence_packet_case_a_3.json",
        ],
        "semantics_diagnostics_paths": [
            repo_root / "examples" / "eval" / "stop_gate" / "semantics_diagnostics_case_a_1.json",
            repo_root / "examples" / "eval" / "stop_gate" / "semantics_diagnostics_case_a_2.json",
            repo_root / "examples" / "eval" / "stop_gate" / "semantics_diagnostics_case_a_3.json",
        ],
        "quality_current_path": repo_root / "artifacts" / "quality_dashboard_v25_closeout.json",
        "quality_baseline_path": repo_root / "artifacts" / "quality_dashboard_v24_closeout.json",
        **{
            f"vnext_plus{version}_manifest_path": _stop_gate_manifest_path(version)
            for version in ACTIVE_STOP_GATE_MANIFEST_VERSIONS
        },
    }


def _resolve_manifest_payload_path(*, base_paths: tuple[Path, ...], raw_path: str) -> Path:
    payload_path = Path(raw_path)
    if payload_path.is_absolute():
        return payload_path.resolve()
    for base_path in base_paths:
        candidate = (base_path / payload_path).resolve()
        if candidate.exists():
            return candidate
    return (base_paths[0] / payload_path).resolve()


def _collect_manifest_path_refs(value: object) -> list[str]:
    refs: list[str] = []
    if isinstance(value, dict):
        for key, child in value.items():
            if key.endswith("_path") and isinstance(child, str):
                refs.append(child)
                continue
            refs.extend(_collect_manifest_path_refs(child))
        return refs
    if isinstance(value, list):
        for child in value:
            refs.extend(_collect_manifest_path_refs(child))
    return refs


def _manifest_referenced_paths(manifest_path: Path) -> set[Path]:
    repo_root = _repo_root()
    manifest = _load_json(manifest_path)
    refs = _collect_manifest_path_refs(manifest)
    base_paths = (
        manifest_path.parent,
        repo_root / "apps" / "api" / "fixtures" / "extraction_fidelity",
        repo_root / "apps" / "api" / "fixtures" / "stop_gate",
    )
    return {
        _resolve_manifest_payload_path(base_paths=base_paths, raw_path=raw_path)
        for raw_path in refs
    }


def _json_paths_under(path: Path) -> set[Path]:
    if not path.exists():
        return set()
    return {entry.resolve() for entry in path.rglob("*.json") if entry.is_file()}


def _z4_mutable_surface_paths() -> list[Path]:
    repo_root = _repo_root()
    v24_manifest_path = _stop_gate_manifest_path(24)
    v25_manifest_path = _stop_gate_manifest_path(25)
    v26_manifest_path = _stop_gate_manifest_path(26)
    paths: set[Path] = {
        v24_manifest_path,
        v25_manifest_path,
        v26_manifest_path,
        repo_root
        / "apps"
        / "api"
        / "fixtures"
        / "provider_parity"
        / "vnext_plus25_provider_matrix.json",
        repo_root / "docs" / "EXTRACTION_FIDELITY_TRANSFER_REPORT_vNEXT_PLUS24.md",
        repo_root / "docs" / "CORE_IR_PROPOSER_TRANSFER_REPORT_vNEXT_PLUS25.md",
    }
    tooling_transfer_report_path = repo_root / "docs" / "TOOLING_TRANSFER_REPORT_vNEXT_PLUS26.md"
    if tooling_transfer_report_path.exists():
        paths.add(tooling_transfer_report_path)
    paths.update(_manifest_referenced_paths(v24_manifest_path))
    paths.update(_manifest_referenced_paths(v25_manifest_path))
    paths.update(_manifest_referenced_paths(v26_manifest_path))

    paths.update(_json_paths_under(repo_root / "apps" / "api" / "fixtures" / "read_surface"))
    paths.update(_json_paths_under(repo_root / "apps" / "api" / "fixtures" / "cross_ir"))
    paths.update(_json_paths_under(repo_root / "apps" / "api" / "fixtures" / "extraction_fidelity"))
    paths.update(
        _json_paths_under(
            repo_root / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus21"
        )
    )
    paths.update(
        _json_paths_under(
            repo_root / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus22"
        )
    )
    paths.update(
        _json_paths_under(
            repo_root / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus23"
        )
    )

    return sorted(paths, key=lambda path: str(path))


def _path_snapshot_hash(path: Path) -> str:
    if not path.exists():
        raise AssertionError(f"locked-surface artifact missing: {path}")
    if path.suffix.lower() == ".json":
        return sha256_canonical_json(_load_json(path))
    payload = path.read_bytes()
    return hashlib.sha256(payload).hexdigest()


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {str(path): _path_snapshot_hash(path) for path in _z4_mutable_surface_paths()}


def _raise_materialization_policy_flow_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            "tooling z4 fail-closed: materialization/policy flow invoked: " f"{target}"
        )

    return _fail


def _assert_payload_has_no_disallowed_fields(
    value: object,
    *,
    field_names: frozenset[str],
    _path: tuple[str | int, ...] = (),
) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in field_names:
                key_path = "/".join(str(part) for part in (*_path, key)) or "<root>"
                raise AssertionError(f"disallowed field '{key}' found at path '{key_path}'")
            _assert_payload_has_no_disallowed_fields(
                child,
                field_names=field_names,
                _path=(*_path, key),
            )
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _assert_payload_has_no_disallowed_fields(
                child,
                field_names=field_names,
                _path=(*_path, index),
            )


def _exercise_tooling_paths_under_z4_guards() -> _ToolingReports:
    repo_root = _repo_root()
    with NoProviderCallsGuard():
        with ExitStack() as stack:
            for target in _MATERIALIZATION_POLICY_FLOW_TARGETS:
                stack.enter_context(
                    patch(target, new=_raise_materialization_policy_flow_call(target=target))
                )
            stop_gate_report = build_stop_gate_metrics(**_base_stop_gate_kwargs())
            extraction_transfer_report = (
                build_extraction_fidelity_transfer_report_vnext_plus24_payload(
                    vnext_plus24_manifest_path=_stop_gate_manifest_path(24),
                    stop_gate_metrics_path=repo_root
                    / "artifacts"
                    / "stop_gate"
                    / "metrics_v24_closeout.json",
                )
            )
            proposer_transfer_report = (
                build_core_ir_proposer_transfer_report_vnext_plus25_payload(
                    vnext_plus25_manifest_path=_stop_gate_manifest_path(25),
                    provider_matrix_path=repo_root
                    / "apps"
                    / "api"
                    / "fixtures"
                    / "provider_parity"
                    / "vnext_plus25_provider_matrix.json",
                    stop_gate_metrics_path=repo_root
                    / "artifacts"
                    / "stop_gate"
                    / "metrics_v25_closeout.json",
                )
            )
    return stop_gate_report, extraction_transfer_report, proposer_transfer_report


@pytest.fixture(scope="module")
def _tooling_execution_result() -> tuple[
    dict[str, str],
    _ToolingReports,
    dict[str, str],
]:
    before_snapshot = _mutable_surface_snapshot_hashes()
    reports = _exercise_tooling_paths_under_z4_guards()
    after_snapshot = _mutable_surface_snapshot_hashes()
    return before_snapshot, reports, after_snapshot


def test_no_provider_calls_guard_fails_closed_on_provider_entrypoint_for_tooling() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="provider client entrypoint invoked"):
            openai_provider.propose_openai()  # type: ignore[call-arg]


def test_no_provider_calls_guard_denies_outbound_network_for_tooling() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="outbound network call denied"):
            socket.create_connection(("example.com", 443), timeout=0.01)


def test_tooling_paths_are_provider_network_and_materialization_policy_guarded(
    _tooling_execution_result: tuple[
        dict[str, str],
        _ToolingReports,
        dict[str, str],
    ],
) -> None:
    _, reports, _ = _tooling_execution_result
    stop_gate_report, extraction_transfer_report, proposer_transfer_report = reports
    assert stop_gate_report["schema"] == STOP_GATE_SCHEMA
    assert (
        extraction_transfer_report["schema"]
        == EXTRACTION_FIDELITY_TRANSFER_REPORT_VNEXT_PLUS24_SCHEMA
    )
    assert (
        proposer_transfer_report["schema"] == CORE_IR_PROPOSER_TRANSFER_REPORT_VNEXT_PLUS25_SCHEMA
    )


def test_tooling_paths_do_not_mutate_vnext_plus26_locked_surface(
    _tooling_execution_result: tuple[
        dict[str, str],
        _ToolingReports,
        dict[str, str],
    ],
) -> None:
    before_snapshot, _, after_snapshot = _tooling_execution_result
    assert before_snapshot == after_snapshot


def test_tooling_payloads_remain_non_enforcing_and_trust_lane_stable(
    _tooling_execution_result: tuple[
        dict[str, str],
        _ToolingReports,
        dict[str, str],
    ],
) -> None:
    _, reports, _ = _tooling_execution_result
    stop_gate_report, extraction_transfer_report, proposer_transfer_report = reports
    for payload in (stop_gate_report, extraction_transfer_report, proposer_transfer_report):
        _assert_payload_has_no_disallowed_fields(
            payload,
            field_names=_NON_ENFORCEMENT_FIELD_NAMES,
        )
        _assert_payload_has_no_disallowed_fields(
            payload,
            field_names=_TRUST_LANE_FIELD_NAMES,
        )
