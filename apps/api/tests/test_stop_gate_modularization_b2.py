from __future__ import annotations

import ast
import inspect
import json
from pathlib import Path
from typing import Any

import adeu_api.hashing as api_hashing
import adeu_api.semantics_v4_candidate_vnext_plus23 as semantics_v4
import adeu_api.trust_invariant_vnext_plus22 as trust_invariant
import urm_runtime.stop_gate_tools as stop_gate_tools
from urm_runtime.stop_gate_normalization import strip_created_at_recursive


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _signature_shape(obj: object) -> dict[str, Any]:
    signature = inspect.signature(obj)
    params: list[dict[str, str]] = []
    for parameter in signature.parameters.values():
        default = "__required__" if parameter.default is inspect._empty else repr(parameter.default)
        params.append(
            {
                "name": parameter.name,
                "kind": parameter.kind.name,
                "default": default,
            }
        )
    return {"params": params}


def _load_signature_snapshot() -> dict[str, Any]:
    snapshot_path = (
        _repo_root()
        / "apps"
        / "api"
        / "tests"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus27_facade_signature_snapshot.json"
    )
    return json.loads(snapshot_path.read_text(encoding="utf-8"))


def test_stop_gate_facade_public_symbols_are_stable() -> None:
    assert stop_gate_tools.STOP_GATE_SCHEMA == "stop_gate_metrics@1"
    for symbol_name in (
        "StopGateMetricsInput",
        "build_stop_gate_metrics_from_input",
        "build_stop_gate_metrics",
        "stop_gate_markdown",
    ):
        assert hasattr(stop_gate_tools, symbol_name), f"missing facade symbol: {symbol_name}"


def test_stop_gate_facade_signatures_match_v27_snapshot() -> None:
    expected = _load_signature_snapshot()
    assert expected["schema"] == "stop_gate_facade_signature_snapshot@1"
    actual = {
        "schema": "stop_gate_facade_signature_snapshot@1",
        "symbols": {
            "StopGateMetricsInput": _signature_shape(stop_gate_tools.StopGateMetricsInput),
            "build_stop_gate_metrics_from_input": _signature_shape(
                stop_gate_tools.build_stop_gate_metrics_from_input
            ),
            "build_stop_gate_metrics": _signature_shape(stop_gate_tools.build_stop_gate_metrics),
            "stop_gate_markdown": _signature_shape(stop_gate_tools.stop_gate_markdown),
        },
    }
    assert actual == expected


def test_created_at_normalization_helper_matches_legacy_helpers_on_corpus() -> None:
    repo_root = _repo_root()
    fixture_corpus_paths = (
        repo_root / "examples" / "eval" / "stop_gate" / "connector_snapshot_case_a_1.json",
        repo_root / "examples" / "eval" / "stop_gate" / "explain_diff_case_a_1.json",
        repo_root / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus19_manifest.json",
        repo_root
        / "apps"
        / "api"
        / "fixtures"
        / "stop_gate"
        / "vnext_plus25"
        / "core_ir_proposer_response_case_a_codex.json",
    )
    corpus: list[object] = [
        {},
        {"created_at": "2026-01-01T00:00:00Z"},
        {
            "created_at": "2026-01-01T00:00:00Z",
            "artifact": {
                "id": "a1",
                "created_at": "2026-01-02T00:00:00Z",
                "payload": [{"x": 1, "created_at": "drop"}, {"nested": {"created_at": "drop"}}],
            },
            "z": [1, 2, {"created_at": "drop", "k": "v"}],
        },
        {
            "runs": [
                {"baseline_path": "a.json", "created_at": "drop", "meta": {"n": 1}},
                {"candidate_path": "b.json", "meta": {"created_at": "drop", "n": 2}},
            ],
            "order": {"b": 1, "a": 2},
        },
    ]
    corpus.extend(
        json.loads(path.read_text(encoding="utf-8"))
        for path in fixture_corpus_paths
        if path.is_file()
    )
    helpers = (
        strip_created_at_recursive,
        stop_gate_tools._strip_created_at_fields,
        api_hashing.strip_created_at_recursive,
        trust_invariant._strip_created_at_recursive,
        semantics_v4._strip_created_at_recursive,
    )
    for payload in corpus:
        expected = strip_created_at_recursive(payload)
        for helper in helpers:
            assert helper(payload) == expected


def test_created_at_normalization_fails_closed_on_string_key_collisions() -> None:
    payload = {1: "alpha", "1": "beta"}
    try:
        strip_created_at_recursive(payload)
    except TypeError as exc:
        assert str(exc) == "mapping contains keys that collide when converted to string"
    else:
        raise AssertionError("expected TypeError for string-key collision")


def test_stop_gate_created_at_paths_use_shared_runtime_helper() -> None:
    source = Path(stop_gate_tools.__file__).read_text(encoding="utf-8")
    module = ast.parse(source)

    strip_def = next(
        node
        for node in module.body
        if isinstance(node, ast.FunctionDef) and node.name == "_strip_created_at_fields"
    )
    assert len(strip_def.body) == 1
    return_stmt = strip_def.body[0]
    assert isinstance(return_stmt, ast.Return)
    assert isinstance(return_stmt.value, ast.Call)
    assert isinstance(return_stmt.value.func, ast.Name)
    assert return_stmt.value.func.id == "strip_created_at_recursive"

    private_strip_calls = [
        node
        for node in ast.walk(module)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "_strip_created_at_fields"
    ]
    assert not private_strip_calls

    shared_helper_calls = [
        node
        for node in ast.walk(module)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "strip_created_at_recursive"
    ]
    assert len(shared_helper_calls) >= 4


def test_stop_gate_tooling_modules_do_not_import_api_server_runtime_modules() -> None:
    forbidden_prefixes = ("adeu_api.main", "adeu_api.storage")
    module_paths = (
        _repo_root() / "packages" / "urm_runtime" / "src" / "urm_runtime" / "stop_gate_tools.py",
        _repo_root()
        / "packages"
        / "urm_runtime"
        / "src"
        / "urm_runtime"
        / "stop_gate_registry.py",
        _repo_root()
        / "packages"
        / "urm_runtime"
        / "src"
        / "urm_runtime"
        / "stop_gate_normalization.py",
    )
    for module_path in module_paths:
        module = ast.parse(module_path.read_text(encoding="utf-8"))
        imported: set[str] = set()
        for node in ast.walk(module):
            if isinstance(node, ast.Import):
                imported.update(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module is not None:
                imported.add(node.module)
        for name in sorted(imported):
            assert not name.startswith(forbidden_prefixes), (
                f"forbidden stop-gate import boundary violation in {module_path.name}: {name}"
            )
