from __future__ import annotations

import json
import socket
from contextlib import ExitStack
from pathlib import Path
from typing import Any
from unittest.mock import patch

import adeu_api.openai_provider as openai_provider
import pytest
from adeu_api.cross_ir_bridge_vnext_plus20 import (
    CROSS_IR_CATALOG_PATH,
    CrossIRCatalog,
    build_cross_ir_bridge_manifest_vnext_plus20,
    list_cross_ir_catalog_pairs_vnext_plus20,
)
from adeu_api.cross_ir_coherence_vnext_plus20 import (
    build_cross_ir_coherence_diagnostics_vnext_plus20,
    build_cross_ir_quality_projection_vnext_plus20,
)
from adeu_api.hashing import sha256_canonical_json
from adeu_api.read_surface_runtime_guards import NoProviderCallsGuard

_MATERIALIZATION_FLOW_TARGETS: tuple[str, ...] = (
    "adeu_api.main.create_artifact",
    "adeu_api.main.create_concept_artifact",
    "adeu_api.main.create_explain_artifact",
    "adeu_api.main.create_semantic_depth_report",
    "adeu_api.storage.create_artifact",
    "adeu_api.storage.create_concept_artifact",
    "adeu_api.storage.create_explain_artifact",
    "adeu_api.storage.create_semantic_depth_report",
)


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _raise_materialization_flow_call(*, target: str) -> Any:
    def _fail(*args: Any, **kwargs: Any) -> Any:
        raise AssertionError(
            "cross-ir c4 fail-closed: materialization flow invoked: " f"{target}"
        )

    return _fail


def _exercise_cross_ir_builders() -> None:
    for pair in list_cross_ir_catalog_pairs_vnext_plus20():
        build_cross_ir_bridge_manifest_vnext_plus20(**pair)
        build_cross_ir_coherence_diagnostics_vnext_plus20(**pair)
        build_cross_ir_quality_projection_vnext_plus20(**pair)


def _exercise_cross_ir_builders_under_c4_guards() -> None:
    with NoProviderCallsGuard():
        with ExitStack() as stack:
            for target in _MATERIALIZATION_FLOW_TARGETS:
                stack.enter_context(
                    patch(target, new=_raise_materialization_flow_call(target=target))
                )
            _exercise_cross_ir_builders()


def _cross_ir_mutable_surface_paths() -> list[Path]:
    catalog_path = CROSS_IR_CATALOG_PATH.resolve()
    catalog = CrossIRCatalog.model_validate(_load_json(catalog_path))

    paths: set[Path] = {catalog_path}
    for artifact_ref in catalog.artifact_refs:
        artifact_path = Path(artifact_ref.path)
        if not artifact_path.is_absolute():
            artifact_path = catalog_path.parent / artifact_path
        paths.add(artifact_path.resolve())

    return sorted(paths, key=lambda path: str(path))


def _mutable_surface_snapshot_hashes() -> dict[str, str]:
    return {
        str(path): sha256_canonical_json(_load_json(path))
        for path in _cross_ir_mutable_surface_paths()
    }


def test_no_provider_calls_guard_fails_closed_on_provider_entrypoint_for_cross_ir() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="provider client entrypoint invoked"):
            openai_provider.propose_openai()  # type: ignore[call-arg]


def test_no_provider_calls_guard_denies_outbound_network_for_cross_ir() -> None:
    with NoProviderCallsGuard():
        with pytest.raises(AssertionError, match="outbound network call denied"):
            socket.create_connection(("example.com", 443), timeout=0.01)


def test_cross_ir_builders_are_provider_network_and_materialization_guarded() -> None:
    _exercise_cross_ir_builders_under_c4_guards()


def test_cross_ir_builders_do_not_mutate_vnext_plus20_fixture_surface() -> None:
    before_snapshot = _mutable_surface_snapshot_hashes()

    _exercise_cross_ir_builders_under_c4_guards()

    after_snapshot = _mutable_surface_snapshot_hashes()
    assert before_snapshot == after_snapshot
