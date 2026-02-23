from __future__ import annotations

import json
import socket
from contextlib import ExitStack
from functools import partial
from pathlib import Path
from typing import Any, Literal
from unittest.mock import patch

import adeu_api.main as api_main
import adeu_api.openai_provider as openai_provider
import adeu_api.semantics_v4_candidate_vnext_plus23 as semantics_v4
import pytest
from adeu_api.cross_ir_bridge_vnext_plus20 import CROSS_IR_CATALOG_PATH, CrossIRCatalog
from adeu_api.hashing import canonical_json, sha256_canonical_json
from adeu_api.read_surface_runtime_guards import NoProviderCallsGuard
from adeu_api.storage import create_artifact, create_concept_artifact, create_validator_run
from adeu_concepts import ConceptIR
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode
from fastapi import Response
from pydantic import BaseModel

_MATERIALIZATION_FLOW_TARGETS: tuple[str, ...] = (
    "adeu_api.main.create_artifact",
    "adeu_api.main.create_concept_artifact",
    "adeu_api.main.create_document",
    "adeu_api.main.create_explain_artifact",
    "adeu_api.main.create_proof_artifact",
    "adeu_api.main.create_semantic_depth_report",
    "adeu_api.main.create_validator_run",
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


class _TrustInvariantPacketRun(BaseModel):
    trust_invariant_packet_path: str


class _TrustInvariantPacketFixture(BaseModel):
    runs: list[_TrustInvariantPacketRun]


class _TrustInvariantProjectionRun(BaseModel):
    trust_invariant_projection_path: str


class _TrustInvariantProjectionFixture(BaseModel):
    runs: list[_TrustInvariantProjectionRun]


class _VnextPlus22ManifestForV4(BaseModel):
    schema: Literal["stop_gate.vnext_plus22_manifest@1"]
    trust_invariant_packet_fixtures: list[_TrustInvariantPacketFixture]
    trust_invariant_projection_fixtures: list[_TrustInvariantProjectionFixture]


class _SemanticsV4CandidatePacketRun(BaseModel):
    semantics_v4_candidate_packet_path: str


class _SemanticsV4CandidatePacketFixture(BaseModel):
    semantics_v3_path: str
    semantics_v4_candidate_path: str
    runs: list[_SemanticsV4CandidatePacketRun]


class _SemanticsV4CandidateProjectionRun(BaseModel):
    semantics_v4_candidate_projection_path: str


class _SemanticsV4CandidateProjectionFixture(BaseModel):
    runs: list[_SemanticsV4CandidateProjectionRun]


class _VnextPlus23ManifestForV4(BaseModel):
    schema: Literal["stop_gate.vnext_plus23_manifest@1"]
    semantics_v4_candidate_packet_fixtures: list[_SemanticsV4CandidatePacketFixture]
    semantics_v4_candidate_projection_fixtures: list[_SemanticsV4CandidateProjectionFixture]


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.fixture(autouse=True)
def _clear_semantics_v4_manifest_caches() -> None:
    semantics_v4._trust_packet_fixture_index_for_manifest.cache_clear()
    semantics_v4._semantics_fixture_index_for_manifest.cache_clear()
    yield
    semantics_v4._trust_packet_fixture_index_for_manifest.cache_clear()
    semantics_v4._semantics_fixture_index_for_manifest.cache_clear()


def _fail_materialization_flow_call(target: str, *args: Any, **kwargs: Any) -> Any:
    del args, kwargs
    raise AssertionError(
        "semantics-v4 v4 fail-closed: materialization flow invoked: " f"{target}"
    )


def _exercise_semantics_v4_builders() -> None:
    pairs = semantics_v4.list_cross_ir_catalog_pairs_vnext_plus20()
    with semantics_v4.semantics_v4_candidate_non_enforcement_context():
        for pair in pairs:
            semantics_v4.build_semantics_v4_candidate_packet_vnext_plus23(
                source_text_hash=pair["source_text_hash"],
                core_ir_artifact_id=pair["core_ir_artifact_id"],
                concept_artifact_id=pair["concept_artifact_id"],
            )
        semantics_v4.build_semantics_v4_candidate_projection_vnext_plus23()


def _exercise_semantics_v4_endpoints() -> None:
    pairs = semantics_v4.list_cross_ir_catalog_pairs_vnext_plus20()
    for pair in pairs:
        api_main.get_urm_semantics_v4_pair_endpoint(
            source_text_hash=pair["source_text_hash"],
            core_ir_artifact_id=pair["core_ir_artifact_id"],
            concept_artifact_id=pair["concept_artifact_id"],
            response=Response(),
        )
    api_main.get_urm_semantics_v4_projection_endpoint(response=Response())


def _exercise_semantics_v4_paths_under_v4_guards() -> None:
    with NoProviderCallsGuard():
        with ExitStack() as stack:
            for target in _MATERIALIZATION_FLOW_TARGETS:
                stack.enter_context(
                    patch(
                        target,
                        new=partial(_fail_materialization_flow_call, target=target),
                    )
                )
            _exercise_semantics_v4_builders()
            _exercise_semantics_v4_endpoints()


def _vnext_plus22_manifest_path() -> Path:
    return (
        Path(__file__).resolve().parents[1]
        / "fixtures"
        / "stop_gate"
        / "vnext_plus22_manifest.json"
    )


def _vnext_plus23_manifest_path() -> Path:
    return (
        Path(__file__).resolve().parents[1]
        / "fixtures"
        / "stop_gate"
        / "vnext_plus23_manifest.json"
    )


def _resolve_manifest_payload_path(*, manifest_path: Path, raw_path: str) -> Path:
    payload_path = Path(raw_path)
    if not payload_path.is_absolute():
        payload_path = manifest_path.parent / payload_path
    return payload_path.resolve()


def _semantics_v4_mutable_surface_paths() -> list[Path]:
    catalog_path = CROSS_IR_CATALOG_PATH.resolve()
    catalog = CrossIRCatalog.model_validate(_load_json(catalog_path))

    paths: set[Path] = {catalog_path}
    for artifact_ref in catalog.artifact_refs:
        artifact_path = Path(artifact_ref.path)
        if not artifact_path.is_absolute():
            artifact_path = catalog_path.parent / artifact_path
        paths.add(artifact_path.resolve())

    v22_manifest_path = _vnext_plus22_manifest_path().resolve()
    v22_manifest = _VnextPlus22ManifestForV4.model_validate(_load_json(v22_manifest_path))
    paths.add(v22_manifest_path)
    for fixture in v22_manifest.trust_invariant_packet_fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=v22_manifest_path,
                    raw_path=run.trust_invariant_packet_path,
                )
            )
    for fixture in v22_manifest.trust_invariant_projection_fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=v22_manifest_path,
                    raw_path=run.trust_invariant_projection_path,
                )
            )

    v23_manifest_path = _vnext_plus23_manifest_path().resolve()
    v23_manifest = _VnextPlus23ManifestForV4.model_validate(_load_json(v23_manifest_path))
    paths.add(v23_manifest_path)
    for fixture in v23_manifest.semantics_v4_candidate_packet_fixtures:
        paths.add(
            _resolve_manifest_payload_path(
                manifest_path=v23_manifest_path,
                raw_path=fixture.semantics_v3_path,
            )
        )
        paths.add(
            _resolve_manifest_payload_path(
                manifest_path=v23_manifest_path,
                raw_path=fixture.semantics_v4_candidate_path,
            )
        )
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=v23_manifest_path,
                    raw_path=run.semantics_v4_candidate_packet_path,
                )
            )
    for fixture in v23_manifest.semantics_v4_candidate_projection_fixtures:
        for run in fixture.runs:
            paths.add(
                _resolve_manifest_payload_path(
                    manifest_path=v23_manifest_path,
                    raw_path=run.semantics_v4_candidate_projection_path,
                )
            )

    return sorted(paths, key=lambda path: str(path))


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {
        str(path): sha256_canonical_json(_load_json(path))
        for path in _semantics_v4_mutable_surface_paths()
    }


def _assert_non_enforcement_payload(
    value: object,
    *,
    _path: tuple[str | int, ...] = (),
) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in _NON_ENFORCEMENT_FIELD_NAMES:
                key_path = "/".join(str(part) for part in (*_path, key)) or "<root>"
                raise AssertionError(
                    f"disallowed non-enforcement key '{key}' found at path '{key_path}'"
                )
            _assert_non_enforcement_payload(child, _path=(*_path, key))
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _assert_non_enforcement_payload(child, _path=(*_path, index))


def _guard_fixture_payload(name: str) -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    path = (
        root
        / "examples"
        / "concepts"
        / "fixtures"
        / "claim_resolution_and_span_guard"
        / "proposals"
        / name
    )
    return json.loads(path.read_text(encoding="utf-8"))


def _guard_source_text() -> str:
    root = repo_root(anchor=Path(__file__))
    path = (
        root
        / "examples"
        / "concepts"
        / "fixtures"
        / "claim_resolution_and_span_guard"
        / "source.txt"
    )
    return path.read_text(encoding="utf-8").strip()


def test_no_provider_calls_guard_fails_closed_on_provider_entrypoint_for_semantics_v4() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="provider client entrypoint invoked"):
            openai_provider.propose_openai()  # type: ignore[call-arg]


def test_no_provider_calls_guard_denies_outbound_network_for_semantics_v4() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="outbound network call denied"):
            socket.create_connection(("example.com", 443), timeout=0.01)


def test_semantics_v4_paths_are_provider_network_and_materialization_guarded() -> None:
    _exercise_semantics_v4_paths_under_v4_guards()


def test_semantics_v4_paths_do_not_mutate_vnext_plus23_fixture_surface() -> None:
    before_snapshot = _mutable_surface_snapshot_hashes()

    _exercise_semantics_v4_paths_under_v4_guards()

    after_snapshot = _mutable_surface_snapshot_hashes()
    assert before_snapshot == after_snapshot


def test_semantics_v4_payloads_are_recommendation_only() -> None:
    pairs = semantics_v4.list_cross_ir_catalog_pairs_vnext_plus20()
    with semantics_v4.semantics_v4_candidate_non_enforcement_context():
        projection = semantics_v4.build_semantics_v4_candidate_projection_vnext_plus23()
    _assert_non_enforcement_payload(projection.model_dump(mode="json"))

    for pair in pairs:
        packet_payload = api_main.get_urm_semantics_v4_pair_endpoint(
            source_text_hash=pair["source_text_hash"],
            core_ir_artifact_id=pair["core_ir_artifact_id"],
            concept_artifact_id=pair["concept_artifact_id"],
            response=Response(),
        ).model_dump(mode="json")
        _assert_non_enforcement_payload(packet_payload)


def test_default_v3_semantics_diagnostics_endpoints_remain_byte_stable(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    artifact = create_artifact(
        clause_text="default-v3-semantic-stability",
        doc_id="doc:v3-stability",
        jurisdiction="US-CA",
        status="PASS",
        num_errors=0,
        num_warns=0,
        ir_json={},
        check_report_json={},
    )
    create_validator_run(
        artifact_id=artifact.artifact_id,
        concept_artifact_id=None,
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options_json={"seed": 1},
        request_hash="a" * 64,
        formula_hash="b" * 64,
        status="UNSAT",
        assurance=None,
        evidence_json={},
        atom_map_json={},
    )

    concept_artifact = create_concept_artifact(
        schema_version="adeu.concepts.v0",
        artifact_version=1,
        source_text="default-v3-semantic-stability",
        doc_id="doc:v3-stability",
        status="PASS",
        num_errors=0,
        num_warns=0,
        ir_json={},
        check_report_json={},
        analysis_json=None,
    )
    create_validator_run(
        artifact_id=None,
        concept_artifact_id=concept_artifact.artifact_id,
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options_json={"seed": 2},
        request_hash="c" * 64,
        formula_hash="d" * 64,
        status="SAT",
        assurance="solver_backed",
        evidence_json={},
        atom_map_json={},
    )

    artifact_baseline = api_main.get_artifact_semantics_diagnostics_endpoint(
        artifact.artifact_id
    ).model_dump(mode="json")
    concept_baseline = api_main.get_concept_artifact_semantics_diagnostics_endpoint(
        concept_artifact.artifact_id
    ).model_dump(mode="json")

    _exercise_semantics_v4_paths_under_v4_guards()

    artifact_after = api_main.get_artifact_semantics_diagnostics_endpoint(
        artifact.artifact_id
    ).model_dump(mode="json")
    concept_after = api_main.get_concept_artifact_semantics_diagnostics_endpoint(
        concept_artifact.artifact_id
    ).model_dump(mode="json")

    assert canonical_json(
        semantics_v4._strip_created_at_recursive(artifact_after)
    ) == canonical_json(
        semantics_v4._strip_created_at_recursive(artifact_baseline)
    )
    assert canonical_json(
        semantics_v4._strip_created_at_recursive(concept_after)
    ) == canonical_json(
        semantics_v4._strip_created_at_recursive(concept_baseline)
    )


def test_default_v3_kernel_mode_strict_lax_behavior_remains_unchanged() -> None:
    source_text = _guard_source_text()
    ir = ConceptIR.model_validate(_guard_fixture_payload("var2.json"))

    strict_report = api_main.check_concept_variant(
        api_main.ConceptCheckRequest(
            ir=ir,
            source_text=source_text,
            mode=KernelMode.STRICT,
        )
    )
    lax_report = api_main.check_concept_variant(
        api_main.ConceptCheckRequest(
            ir=ir,
            source_text=source_text,
            mode=KernelMode.LAX,
        )
    )

    assert strict_report.status == "REFUSE"
    assert any(reason.code == "CONCEPT_PROVENANCE_MISSING" for reason in strict_report.reason_codes)
    assert lax_report.status == "WARN"
    lax_reasons = [
        reason for reason in lax_report.reason_codes if reason.code == "CONCEPT_PROVENANCE_MISSING"
    ]
    assert lax_reasons
    assert lax_reasons[0].severity == "ERROR"
