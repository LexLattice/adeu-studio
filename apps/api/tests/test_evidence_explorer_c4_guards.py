from __future__ import annotations

import json
import re
import socket
from contextlib import ExitStack
from pathlib import Path
from typing import Any, Iterable
from unittest.mock import patch

import adeu_api.extraction_fidelity_vnext_plus24 as extraction_fidelity
import adeu_api.main as api_main
import adeu_api.normative_advice_vnext_plus21 as normative_advice
import adeu_api.openai_provider as openai_provider
import adeu_api.semantics_v4_candidate_vnext_plus23 as semantics_v4
import adeu_api.trust_invariant_vnext_plus22 as trust_invariant
import pytest
from adeu_api.cross_ir_bridge_vnext_plus20 import CROSS_IR_CATALOG_PATH, CrossIRCatalog
from adeu_api.hashing import sha256_canonical_json
from adeu_api.read_surface_runtime_guards import NoProviderCallsGuard
from fastapi import Response
from fastapi.routing import APIRoute

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
_FROZEN_FAMILY_TRUST_LABELS: dict[str, str] = {
    "read_surface": "mapping_trust",
    "normative_advice": "mapping_trust",
    "proof_trust": "proof_trust",
    "semantics_v4_candidate": "solver_trust",
    "extraction_fidelity": "mapping_trust",
}
_NON_ENFORCEMENT_LABEL = (
    "Evidence-only surface; no automatic policy enforcement or mutation is performed."
)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.fixture(autouse=True)
def _clear_explorer_guard_caches() -> None:
    api_main._read_surface_catalog_index.cache_clear()
    normative_advice._coherence_fixture_index_for_manifest.cache_clear()
    trust_invariant._coherence_fixture_index_for_manifest.cache_clear()
    trust_invariant._normative_advice_fixture_index_for_manifest.cache_clear()
    semantics_v4._trust_packet_fixture_index_for_manifest.cache_clear()
    semantics_v4._semantics_fixture_index_for_manifest.cache_clear()
    extraction_fidelity._catalog_index_for_path.cache_clear()
    yield
    api_main._read_surface_catalog_index.cache_clear()
    normative_advice._coherence_fixture_index_for_manifest.cache_clear()
    trust_invariant._coherence_fixture_index_for_manifest.cache_clear()
    trust_invariant._normative_advice_fixture_index_for_manifest.cache_clear()
    semantics_v4._trust_packet_fixture_index_for_manifest.cache_clear()
    semantics_v4._semantics_fixture_index_for_manifest.cache_clear()
    extraction_fidelity._catalog_index_for_path.cache_clear()


def _raise_materialization_flow_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            "evidence explorer c4 fail-closed: materialization flow invoked: " f"{target}"
        )

    return _fail


def _entry_sort_key(entry: api_main.EvidenceExplorerCatalogEntry) -> tuple[str, str, str, str]:
    return (
        entry.source_text_hash,
        entry.core_ir_artifact_id,
        entry.concept_artifact_id,
        entry.artifact_id or "",
    )


def _exercise_entry_detail_endpoint(
    *,
    family: api_main.EvidenceExplorerFamily,
    entry: api_main.EvidenceExplorerCatalogEntry,
) -> None:
    if family == "read_surface":
        if not entry.artifact_id:
            raise AssertionError("read_surface entry must include artifact_id")
        payload = api_main.get_urm_core_ir_artifact_endpoint(
            artifact_id=entry.artifact_id,
            response=Response(),
        ).model_dump(mode="json")
        assert payload["artifact_id"] == entry.artifact_id
        return

    if family == "normative_advice":
        api_main.get_urm_normative_advice_pair_endpoint(
            source_text_hash=entry.source_text_hash,
            core_ir_artifact_id=entry.core_ir_artifact_id,
            concept_artifact_id=entry.concept_artifact_id,
            response=Response(),
        )
        return

    if family == "proof_trust":
        api_main.get_urm_proof_trust_pair_endpoint(
            source_text_hash=entry.source_text_hash,
            core_ir_artifact_id=entry.core_ir_artifact_id,
            concept_artifact_id=entry.concept_artifact_id,
            response=Response(),
        )
        return

    if family == "semantics_v4_candidate":
        api_main.get_urm_semantics_v4_pair_endpoint(
            source_text_hash=entry.source_text_hash,
            core_ir_artifact_id=entry.core_ir_artifact_id,
            concept_artifact_id=entry.concept_artifact_id,
            response=Response(),
        )
        return

    if family == "extraction_fidelity":
        api_main.get_urm_extraction_fidelity_source_endpoint(
            source_text_hash=entry.source_text_hash,
            response=Response(),
        )
        return

    raise AssertionError(f"unexpected explorer family: {family}")


def _exercise_projection_endpoint(
    *,
    family: api_main.EvidenceExplorerFamily,
    entry: api_main.EvidenceExplorerCatalogEntry,
) -> None:
    if family == "read_surface":
        if not entry.artifact_id:
            raise AssertionError("read_surface entry must include artifact_id")
        api_main.get_urm_core_ir_lane_projection_endpoint(
            artifact_id=entry.artifact_id,
            response=Response(),
        )
        return

    if family == "normative_advice":
        api_main.get_urm_normative_advice_projection_endpoint(response=Response())
        return

    if family == "proof_trust":
        api_main.get_urm_proof_trust_projection_endpoint(response=Response())
        return

    if family == "semantics_v4_candidate":
        api_main.get_urm_semantics_v4_projection_endpoint(response=Response())
        return

    if family == "extraction_fidelity":
        api_main.get_urm_extraction_fidelity_projection_endpoint(response=Response())
        return

    raise AssertionError(f"unexpected explorer family: {family}")


def _exercise_explorer_endpoints() -> None:
    catalog = api_main.get_urm_evidence_explorer_catalog_endpoint(response=Response())
    ordered_families = [item.family for item in catalog.families]
    assert ordered_families == sorted(api_main._EVIDENCE_EXPLORER_FAMILIES_SORTED)
    assert len(ordered_families) == len(api_main._EVIDENCE_EXPLORER_FAMILIES_SORTED)

    for family in ordered_families:
        family_payload = api_main.get_urm_evidence_explorer_catalog_family_endpoint(
            family=family,
            response=Response(),
        )
        ordering = [_entry_sort_key(entry) for entry in family_payload.entries]
        assert ordering == sorted(ordering)
        if not family_payload.entries:
            raise AssertionError(
                f"explorer family '{family}' has no entries and cannot satisfy availability probe"
            )

        selected_entry = family_payload.entries[0]
        _exercise_entry_detail_endpoint(family=family, entry=selected_entry)
        _exercise_projection_endpoint(family=family, entry=selected_entry)


def _exercise_explorer_paths_under_c4_guards() -> None:
    with NoProviderCallsGuard():
        with ExitStack() as stack:
            for target in _MATERIALIZATION_FLOW_TARGETS:
                stack.enter_context(
                    patch(target, new=_raise_materialization_flow_call(target=target))
                )
            _exercise_explorer_endpoints()


def _resolve_relative_path(*, base_paths: tuple[Path, ...], raw_path: str) -> Path:
    payload_path = Path(raw_path)
    if payload_path.is_absolute():
        return payload_path.resolve()
    for base_path in base_paths:
        resolved = (base_path / payload_path).resolve()
        if resolved.exists():
            return resolved
    return (base_paths[0] / payload_path).resolve()


def _iter_json_path_values(value: object) -> Iterable[str]:
    if isinstance(value, dict):
        for key, child in value.items():
            if key.endswith("_path") and isinstance(child, str) and child:
                yield child
            yield from _iter_json_path_values(child)
        return
    if isinstance(value, list):
        for child in value:
            yield from _iter_json_path_values(child)


def _tests_stop_gate_manifest_paths() -> tuple[Path, ...]:
    stop_gate_root = Path(__file__).resolve().parents[1] / "fixtures" / "stop_gate"
    return (
        (stop_gate_root / "vnext_plus21_manifest.json").resolve(),
        (stop_gate_root / "vnext_plus22_manifest.json").resolve(),
        (stop_gate_root / "vnext_plus23_manifest.json").resolve(),
        (stop_gate_root / "vnext_plus24_manifest.json").resolve(),
    )


def _evidence_explorer_mutable_surface_paths() -> list[Path]:
    paths: set[Path] = set()

    read_surface_catalog_path = api_main._READ_SURFACE_CATALOG_PATH.resolve()
    read_surface_catalog_payload = _load_json(read_surface_catalog_path)
    if read_surface_catalog_payload.get("schema") != "read_surface.vnext_plus19_catalog@1":
        raise AssertionError("expected read_surface.vnext_plus19_catalog@1 schema")
    paths.add(read_surface_catalog_path)
    read_surface_refs = read_surface_catalog_payload.get("artifact_refs")
    if not isinstance(read_surface_refs, list):
        raise AssertionError("read_surface catalog artifact_refs must be a list")
    for artifact_ref in read_surface_refs:
        if not isinstance(artifact_ref, dict):
            raise AssertionError("read_surface catalog artifact_refs entries must be objects")
        raw_path = artifact_ref.get("path")
        if not isinstance(raw_path, str) or not raw_path:
            raise AssertionError(
                "read_surface catalog artifact_ref path must be a non-empty string"
            )
        paths.add(
            _resolve_relative_path(
                base_paths=(read_surface_catalog_path.parent,),
                raw_path=raw_path,
            )
        )

    cross_ir_catalog_path = CROSS_IR_CATALOG_PATH.resolve()
    cross_ir_catalog = CrossIRCatalog.model_validate(_load_json(cross_ir_catalog_path))
    paths.add(cross_ir_catalog_path)
    for artifact_ref in cross_ir_catalog.artifact_refs:
        artifact_path = Path(artifact_ref.path)
        if not artifact_path.is_absolute():
            artifact_path = cross_ir_catalog_path.parent / artifact_path
        paths.add(artifact_path.resolve())

    extraction_catalog_path = extraction_fidelity.VNEXT_PLUS24_CATALOG_PATH.resolve()
    extraction_catalog = extraction_fidelity.ExtractionFidelityCatalog.model_validate(
        _load_json(extraction_catalog_path)
    )
    paths.add(extraction_catalog_path)
    for entry in extraction_catalog.entries:
        paths.add(
            _resolve_relative_path(
                base_paths=(extraction_catalog_path.parent,),
                raw_path=entry.projection_alignment_path,
            )
        )
        paths.add(
            _resolve_relative_path(
                base_paths=(extraction_catalog_path.parent,),
                raw_path=entry.projection_alignment_fidelity_input_path,
            )
        )

    manifest_paths = _tests_stop_gate_manifest_paths()
    for manifest_path in manifest_paths:
        manifest_payload = _load_json(manifest_path)
        paths.add(manifest_path)
        for raw_path in _iter_json_path_values(manifest_payload):
            paths.add(
                _resolve_relative_path(
                    base_paths=(
                        manifest_path.parent,
                        read_surface_catalog_path.parent,
                        cross_ir_catalog_path.parent,
                        extraction_catalog_path.parent,
                    ),
                    raw_path=raw_path,
                )
            )

    sorted_paths = sorted(paths, key=lambda path: str(path))
    missing_paths = [path for path in sorted_paths if not path.exists()]
    if missing_paths:
        missing_list = ", ".join(str(path) for path in missing_paths)
        raise AssertionError(f"expected explorer fixture paths to exist: {missing_list}")
    return sorted_paths


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {
        str(path): sha256_canonical_json(_load_json(path))
        for path in _evidence_explorer_mutable_surface_paths()
    }


def _route_methods_for_path(path: str) -> set[str]:
    methods: set[str] = set()
    for route in api_main.app.routes:
        if isinstance(route, APIRoute) and route.path == path:
            methods.update(route.methods or set())
    return methods


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def test_no_provider_calls_guard_fails_closed_on_provider_entrypoint_for_evidence_explorer(
) -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="provider client entrypoint invoked"):
            openai_provider.propose_openai()  # type: ignore[call-arg]


def test_no_provider_calls_guard_denies_outbound_network_for_evidence_explorer() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="outbound network call denied"):
            socket.create_connection(("example.com", 443), timeout=0.01)


def test_evidence_explorer_paths_are_provider_network_and_materialization_guarded() -> None:
    _exercise_explorer_paths_under_c4_guards()


def test_evidence_explorer_paths_do_not_mutate_fixture_surface() -> None:
    before_snapshot = _mutable_surface_snapshot_hashes()

    _exercise_explorer_paths_under_c4_guards()

    after_snapshot = _mutable_surface_snapshot_hashes()
    assert before_snapshot == after_snapshot


def test_evidence_explorer_catalog_replay_is_byte_identical_and_ordered() -> None:
    first_catalog = api_main.get_urm_evidence_explorer_catalog_endpoint(
        response=Response()
    ).model_dump(mode="json")
    second_catalog = api_main.get_urm_evidence_explorer_catalog_endpoint(
        response=Response()
    ).model_dump(mode="json")
    assert sha256_canonical_json(first_catalog) == sha256_canonical_json(second_catalog)

    first_families = [item["family"] for item in first_catalog["families"]]
    assert first_families == sorted(first_families)
    assert first_families == list(api_main._EVIDENCE_EXPLORER_FAMILIES_SORTED)

    for family in api_main._EVIDENCE_EXPLORER_FAMILIES_SORTED:
        first_family_payload = api_main.get_urm_evidence_explorer_catalog_family_endpoint(
            family=family,
            response=Response(),
        ).model_dump(mode="json")
        second_family_payload = api_main.get_urm_evidence_explorer_catalog_family_endpoint(
            family=family,
            response=Response(),
        ).model_dump(mode="json")
        assert sha256_canonical_json(first_family_payload) == sha256_canonical_json(
            second_family_payload
        )
        ordering = [
            (
                entry["source_text_hash"],
                entry["core_ir_artifact_id"],
                entry["concept_artifact_id"],
                entry.get("artifact_id", ""),
            )
            for entry in first_family_payload["entries"]
        ]
        assert ordering == sorted(ordering)


def test_evidence_explorer_frozen_families_have_detail_and_projection_surfaces() -> None:
    _exercise_explorer_endpoints()


def test_evidence_explorer_catalog_routes_are_get_only() -> None:
    for path in (
        "/urm/evidence-explorer/catalog",
        "/urm/evidence-explorer/catalog/{family}",
    ):
        methods = _route_methods_for_path(path)
        assert methods
        assert "GET" in methods
        assert not methods.intersection({"POST", "PUT", "PATCH", "DELETE"})


def test_evidence_explorer_renderer_static_coverage_and_read_only_contract() -> None:
    source_path = (
        _repo_root()
        / "apps"
        / "web"
        / "src"
        / "app"
        / "evidence-explorer"
        / "page.tsx"
    )
    source = source_path.read_text(encoding="utf-8")

    for family, trust_lane in _FROZEN_FAMILY_TRUST_LABELS.items():
        assert f'{family}: "{trust_lane}"' in source

    assert _NON_ENFORCEMENT_LABEL in source
    for family in api_main._EVIDENCE_EXPLORER_FAMILIES_SORTED:
        assert f"renderer_family: {family}" in source

    assert source.count('method: "GET"') >= 3
    assert not re.search(r'method:\s*"(POST|PUT|PATCH|DELETE)"', source)
    assert "/urm/core-ir/propose" not in source

    for projection_path in (
        "/urm/core-ir/artifacts/${encodeURIComponent(artifactId)}/lane-projection",
        "/urm/normative-advice/projection",
        "/urm/proof-trust/projection",
        "/urm/semantics-v4/projection",
        "/urm/extraction-fidelity/projection",
    ):
        assert projection_path in source
