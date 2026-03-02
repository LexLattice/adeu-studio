from __future__ import annotations

import ast
import hashlib
import importlib
import importlib.util
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

import pytest
from adeu_ir.repo import repo_root as canonical_repo_root

_CANONICAL_SYMBOLS = frozenset({"canonical_json", "_canonical_json"})
_SHA256_SYMBOL = "sha256_canonical_json"

_CONFORMANCE_CORPUS: tuple[Any, ...] = (
    {},
    [],
    {"a": 1, "b": 2, "nested": {"x": True, "y": None}},
    {
        "unicode": "zăpadă",
        "list": [3, 2, 1, {"k": "v"}],
        "bool": False,
        "float": 1.25,
        "text": "line1\\nline2",
    },
    {
        "deep": {
            "layer1": {
                "layer2": [{"id": "a", "score": 0.0}, {"id": "b", "score": 42.75}]
            }
        },
        "paths": {"posix": "a/b/c", "windows_like": "a\\\\b\\\\c"},
    },
)


@dataclass(frozen=True)
class _FrozenEntrypoint:
    repo_path: str
    module: str
    symbol: str

    @property
    def entrypoint(self) -> str:
        return f"{self.repo_path}::{self.symbol}"


_FROZEN_HELPER_ENTRYPOINTS: tuple[_FrozenEntrypoint, ...] = (
    _FrozenEntrypoint(
        repo_path="apps/api/src/adeu_api/hashing.py",
        module="adeu_api.hashing",
        symbol="canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="apps/api/src/adeu_api/hashing.py",
        module="adeu_api.hashing",
        symbol="sha256_canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="packages/urm_runtime/src/urm_runtime/hashing.py",
        module="urm_runtime.hashing",
        symbol="canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="packages/urm_runtime/src/urm_runtime/hashing.py",
        module="urm_runtime.hashing",
        symbol="sha256_canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="packages/adeu_kernel/src/adeu_kernel/validator_evidence.py",
        module="adeu_kernel.validator_evidence",
        symbol="_canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="packages/adeu_kernel/src/adeu_kernel/semantics_diagnostics.py",
        module="adeu_kernel.semantics_diagnostics",
        symbol="_canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="packages/adeu_kernel/src/adeu_kernel/proof_evidence.py",
        module="adeu_kernel.proof_evidence",
        symbol="_canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="packages/adeu_core_ir/src/adeu_core_ir/pipeline.py",
        module="adeu_core_ir.pipeline",
        symbol="_canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="packages/adeu_explain/src/adeu_explain/explain_diff.py",
        module="adeu_explain.explain_diff",
        symbol="_canonical_json",
    ),
    _FrozenEntrypoint(
        repo_path="packages/adeu_semantic_depth/src/adeu_semantic_depth/semantic_depth.py",
        module="adeu_semantic_depth.semantic_depth",
        symbol="_canonical_json",
    ),
)

_EXPECTED_DISCOVERY_ENTRYPOINTS: tuple[str, ...] = tuple(
    sorted(
        entry.entrypoint
        for entry in _FROZEN_HELPER_ENTRYPOINTS
        if entry.symbol in _CANONICAL_SYMBOLS
    )
)
_RUNTIME_DEPS_AVAILABLE = importlib.util.find_spec("pydantic") is not None


def _repo_root() -> Path:
    return canonical_repo_root(anchor=Path(__file__).resolve())


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _ensure_repo_src_on_syspath() -> None:
    repo_root = _repo_root()
    src_paths = [repo_root / "apps" / "api" / "src"]
    src_paths.extend(sorted((repo_root / "packages").glob("*/src")))
    for path in src_paths:
        path_str = str(path.resolve())
        if path_str not in sys.path:
            sys.path.insert(0, path_str)


def _assert_json_serializable_only(value: Any, *, path: str = "$") -> None:
    if value is None:
        return
    if isinstance(value, bool):
        return
    if isinstance(value, int):
        return
    if isinstance(value, float):
        assert math.isfinite(value), f"non-finite float at {path}: {value!r}"
        return
    if isinstance(value, str):
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _assert_json_serializable_only(item, path=f"{path}[{index}]")
        return
    if isinstance(value, dict):
        for key, item in value.items():
            assert isinstance(key, str), f"non-string key at {path}: {key!r}"
            _assert_json_serializable_only(item, path=f"{path}.{key}")
        return
    pytest.fail(f"non-JSON runtime object at {path}: {type(value).__name__}")


def _load_frozen_callables() -> dict[str, Callable[[Any], str]]:
    repo_root = _repo_root()
    _ensure_repo_src_on_syspath()
    loaded: dict[str, Callable[[Any], str]] = {}
    for entry in _FROZEN_HELPER_ENTRYPOINTS:
        module = importlib.import_module(entry.module)
        module_file = Path(module.__file__ or "").resolve()
        expected_path = (repo_root / entry.repo_path).resolve()
        assert module_file == expected_path, (
            f"entrypoint moved for {entry.entrypoint}: "
            f"expected file {entry.repo_path}, got {module_file}"
        )
        function = getattr(module, entry.symbol, None)
        assert callable(function), f"missing callable entrypoint: {entry.entrypoint}"
        loaded[entry.entrypoint] = function
    return loaded


def _discover_canonical_definitions() -> list[dict[str, Any]]:
    repo_root = _repo_root()
    roots = (repo_root / "apps" / "api" / "src", repo_root / "packages")
    discovered: list[dict[str, Any]] = []

    for root in roots:
        for file_path in sorted(root.rglob("*.py")):
            tree = ast.parse(file_path.read_text(encoding="utf-8"))
            relative_path = file_path.relative_to(repo_root).as_posix()
            for node in tree.body:
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if node.name not in _CANONICAL_SYMBOLS:
                        continue
                    discovered.append(
                        {
                            "entrypoint": f"{relative_path}::{node.name}",
                            "path": relative_path,
                            "symbol": node.name,
                            "line": node.lineno,
                        }
                    )

    discovered.sort(key=lambda item: item["entrypoint"])
    return discovered


def test_vnext_plus27_conformance_corpus_is_json_serializable_only() -> None:
    for item in _CONFORMANCE_CORPUS:
        _assert_json_serializable_only(item)


@pytest.mark.skipif(
    not _RUNTIME_DEPS_AVAILABLE,
    reason="runtime dependencies not available in local test environment",
)
def test_vnext_plus27_canonical_json_conformance_text_and_hash_equality() -> None:
    callables = _load_frozen_callables()
    canonical_entrypoints = tuple(
        entry.entrypoint
        for entry in _FROZEN_HELPER_ENTRYPOINTS
        if entry.symbol in _CANONICAL_SYMBOLS
    )
    sha_entrypoints = tuple(
        entry.entrypoint for entry in _FROZEN_HELPER_ENTRYPOINTS if entry.symbol == _SHA256_SYMBOL
    )

    for payload in _CONFORMANCE_CORPUS:
        canonical_texts: dict[str, str] = {}
        for entrypoint in canonical_entrypoints:
            value = callables[entrypoint](payload)
            assert isinstance(value, str), f"canonical output must be str: {entrypoint}"
            assert not value.endswith("\n"), f"trailing newline is invalid: {entrypoint}"
            canonical_texts[entrypoint] = value

        baseline_text = canonical_texts[canonical_entrypoints[0]]
        baseline_hash = _sha256_text(baseline_text)

        for entrypoint, value in canonical_texts.items():
            assert value == baseline_text, f"canonical text mismatch for {entrypoint}"
            assert _sha256_text(value) == baseline_hash, f"canonical hash mismatch for {entrypoint}"

        for entrypoint in sha_entrypoints:
            digest = callables[entrypoint](payload)
            assert isinstance(digest, str), f"sha output must be str: {entrypoint}"
            assert digest == baseline_hash, f"sha256_canonical_json mismatch for {entrypoint}"


@pytest.mark.skipif(
    not _RUNTIME_DEPS_AVAILABLE,
    reason="runtime dependencies not available in local test environment",
)
def test_vnext_plus27_conformance_coverage_guard_exercises_frozen_entrypoints() -> None:
    loaded = _load_frozen_callables()
    expected_entrypoints = tuple(entry.entrypoint for entry in _FROZEN_HELPER_ENTRYPOINTS)

    assert tuple(loaded.keys()) == expected_entrypoints
    assert len(loaded) == len(_FROZEN_HELPER_ENTRYPOINTS) == 10


def test_vnext_plus27_canonical_definition_discovery_report_is_deterministic() -> None:
    discovered = _discover_canonical_definitions()
    discovered_entrypoints = tuple(item["entrypoint"] for item in discovered)
    report = json.dumps(discovered, ensure_ascii=False, separators=(",", ":"), sort_keys=True)

    assert discovered_entrypoints == tuple(sorted(discovered_entrypoints))
    assert discovered_entrypoints == _EXPECTED_DISCOVERY_ENTRYPOINTS, (
        "canonical definition discovery drift detected; report="
        f"{report}"
    )
