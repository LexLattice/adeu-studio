from __future__ import annotations

import json
from pathlib import Path

import adeu_repo_description.test_selection_v0 as test_selection_module
from adeu_repo_description.test_selection_v0 import select_python_tests_v0

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "test_selection_v0"


def _root_pyproject() -> str:
    return '[tool.pytest.ini_options]\naddopts = "-q"\n'


def _package_pyproject(name: str, *, deps: tuple[str, ...] = ()) -> str:
    dependency_lines = "\n".join(f'  "{dependency}",' for dependency in deps)
    if dependency_lines:
        dependency_lines = f"\n{dependency_lines}\n"
    return (
        "[build-system]\n"
        'requires = ["hatchling"]\n'
        'build-backend = "hatchling.build"\n\n'
        "[project]\n"
        f'name = "{name}"\n'
        'version = "0.0.0"\n'
        f"dependencies = [{dependency_lines}]\n\n"
        "[tool.hatch.build.targets.wheel]\n"
        f'packages = ["src/{name}"]\n'
    )


def _bootstrap_repo(tmp_path: Path, files: dict[str, str]) -> Path:
    base_files = {
        "pyproject.toml": _root_pyproject(),
        "packages/urm_runtime/pyproject.toml": _package_pyproject("urm_runtime"),
        "packages/urm_runtime/src/urm_runtime/__init__.py": "__all__ = []\n",
    }
    base_files.update(files)
    for relative_path, content in base_files.items():
        path = tmp_path / relative_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    return tmp_path


def _reasons_for_test(payload: dict[str, object], *, test_path: str) -> list[dict[str, object]]:
    return [row for row in payload["selection_reasons"] if row["test_path"] == test_path]


def _reason_kinds(payload: dict[str, object], *, test_path: str) -> set[str]:
    return {row["reason_kind"] for row in _reasons_for_test(payload, test_path=test_path)}


def _selection_stages(payload: dict[str, object], *, test_path: str) -> set[str]:
    return {row["selection_stage"] for row in _reasons_for_test(payload, test_path=test_path)}


def _witness_status(payload: dict[str, object], witness_id: str) -> str:
    for witness in payload["dependency_class_statuses"]:
        if witness["witness_id"] == witness_id:
            return witness["status"]
    raise AssertionError(f"missing witness_id: {witness_id}")


def _load_fixture_payload(name: str) -> dict[str, object]:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def test_changed_test_file_is_selected_directly(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "from .core import VALUE\n",
            "packages/pkg_a/src/pkg_a/core.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": (
                "from pkg_a import VALUE\n\ndef test_value() -> None:\n    assert VALUE == 1\n"
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/tests/test_core.py"],
        intent_matrix_path=None,
    )

    assert payload["selected_test_paths"] == ["packages/pkg_a/tests/test_core.py"]
    assert payload["evidence_selected_test_paths"] == ["packages/pkg_a/tests/test_core.py"]
    assert payload["fallback_selected_test_paths"] == []
    assert payload["risk_posture"] == "narrow"
    assert _witness_status(payload, "test_file:packages/pkg_a/tests/test_core.py") == "changed"
    assert _reason_kinds(payload, test_path="packages/pkg_a/tests/test_core.py") == {
        "changed_test_file"
    }
    assert _selection_stages(payload, test_path="packages/pkg_a/tests/test_core.py") == {"evidence"}


def test_direct_source_import_closure_wins_before_owner_fallback(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "from .api import get_value\n",
            "packages/pkg_a/src/pkg_a/core.py": "VALUE = 1\n",
            "packages/pkg_a/src/pkg_a/api.py": (
                "from pkg_a.core import VALUE\n\ndef get_value() -> int:\n    return VALUE\n"
            ),
            "packages/pkg_a/src/pkg_a/other.py": (
                "def identity(value: int) -> int:\n    return value\n"
            ),
            "packages/pkg_a/tests/test_api.py": (
                "from pkg_a.api import get_value\n\n"
                "def test_get_value() -> None:\n"
                "    assert get_value() == 1\n"
            ),
            "packages/pkg_a/tests/test_other.py": (
                "from pkg_a.other import identity\n\n"
                "def test_identity() -> None:\n"
                "    assert identity(3) == 3\n"
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/src/pkg_a/core.py"],
        intent_matrix_path=None,
    )

    assert payload["selected_test_paths"] == ["packages/pkg_a/tests/test_api.py"]
    assert payload["evidence_selected_test_paths"] == ["packages/pkg_a/tests/test_api.py"]
    assert payload["fallback_selected_test_paths"] == []
    assert payload["risk_posture"] == "narrow"
    assert _witness_status(payload, "source_module:pkg_a.core") == "changed"
    assert _reason_kinds(payload, test_path="packages/pkg_a/tests/test_api.py") == {
        "direct_import_dependency"
    }


def test_package_root_reexport_relative_imports_propagate_to_tests(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "from .core import VALUE\n",
            "packages/pkg_a/src/pkg_a/core.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": (
                "from pkg_a import VALUE\n\n"
                "def test_value() -> None:\n"
                "    assert VALUE == 1\n"
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/src/pkg_a/core.py"],
        intent_matrix_path=None,
    )

    assert payload["selected_test_paths"] == ["packages/pkg_a/tests/test_core.py"]
    assert payload["evidence_selected_test_paths"] == ["packages/pkg_a/tests/test_core.py"]
    assert payload["fallback_selected_test_paths"] == []
    assert _reason_kinds(payload, test_path="packages/pkg_a/tests/test_core.py") == {
        "direct_import_dependency"
    }


def test_cross_package_source_import_closure_selects_only_reached_dependent_tests(
    tmp_path: Path,
) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "from .core import VALUE\n",
            "packages/pkg_a/src/pkg_a/core.py": "VALUE = 1\n",
            "packages/pkg_b/pyproject.toml": _package_pyproject("pkg_b", deps=("pkg_a>=0.0.0",)),
            "packages/pkg_b/src/pkg_b/__init__.py": "from .service import read_marker\n",
            "packages/pkg_b/src/pkg_b/service.py": (
                "from pkg_a.core import VALUE\n\ndef read_marker() -> int:\n    return VALUE\n"
            ),
            "packages/pkg_b/src/pkg_b/other.py": ('def read_other() -> str:\n    return "ok"\n'),
            "packages/pkg_b/tests/test_service.py": (
                "from pkg_b.service import read_marker\n\n"
                "def test_service() -> None:\n"
                "    assert read_marker() == 1\n"
            ),
            "packages/pkg_b/tests/test_other.py": (
                "from pkg_b.other import read_other\n\n"
                "def test_other() -> None:\n"
                '    assert read_other() == "ok"\n'
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/src/pkg_a/core.py"],
        intent_matrix_path=None,
    )

    assert payload["selected_test_paths"] == ["packages/pkg_b/tests/test_service.py"]
    assert payload["fallback_selected_test_paths"] == []
    assert _reason_kinds(payload, test_path="packages/pkg_b/tests/test_service.py") == {
        "direct_import_dependency"
    }


def test_owner_pyproject_change_selects_owner_and_reverse_dependents(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": (
                "from pkg_a import VALUE\n\ndef test_value() -> None:\n    assert VALUE == 1\n"
            ),
            "packages/pkg_b/pyproject.toml": _package_pyproject("pkg_b", deps=("pkg_a>=0.0.0",)),
            "packages/pkg_b/src/pkg_b/__init__.py": "MARKER = 'ok'\n",
            "packages/pkg_b/tests/test_service.py": (
                "from pkg_b import MARKER\n\n"
                "def test_marker() -> None:\n"
                '    assert MARKER == "ok"\n'
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/pyproject.toml"],
        intent_matrix_path=None,
    )

    assert sorted(payload["selected_test_paths"]) == [
        "packages/pkg_a/tests/test_core.py",
        "packages/pkg_b/tests/test_service.py",
    ]
    assert payload["evidence_selected_test_paths"] == []
    assert sorted(payload["fallback_selected_test_paths"]) == [
        "packages/pkg_a/tests/test_core.py",
        "packages/pkg_b/tests/test_service.py",
    ]
    assert _reason_kinds(payload, test_path="packages/pkg_a/tests/test_core.py") == {
        "owner_fallback_widening"
    }
    assert _reason_kinds(payload, test_path="packages/pkg_b/tests/test_service.py") == {
        "reverse_local_package_dependency"
    }


def test_intent_matrix_binding_narrows_without_owner_fallback(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "__all__ = []\n",
            "packages/pkg_a/src/pkg_a/core.py": "VALUE = 1\n",
            "packages/pkg_b/pyproject.toml": _package_pyproject("pkg_b"),
            "packages/pkg_b/src/pkg_b/__init__.py": "__all__ = []\n",
            "packages/pkg_b/tests/test_contract.py": (
                "def test_contract() -> None:\n    assert True\n"
            ),
            "packages/pkg_b/tests/test_other.py": (
                "def test_other() -> None:\n    assert True\n"
            ),
            (
                "apps/api/fixtures/repo_description/vnext_plus103/"
                "repo_test_intent_matrix_v103_reference.json"
            ): json.dumps(
                {
                    "test_intent_entries": [
                        {
                            "test_ref": "test:packages/pkg_b/tests/test_contract.py#test_contract",
                            "guarded_surface_ref": {
                                "guarded_surface_ref_kind": "internal_module_boundary",
                                "guarded_surface_ref_value": (
                                    "module:packages/pkg_a/src/pkg_a/core.py"
                                ),
                            },
                        }
                    ]
                }
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/src/pkg_a/core.py"],
    )

    assert payload["selected_test_paths"] == ["packages/pkg_b/tests/test_contract.py"]
    assert payload["fallback_selected_test_paths"] == []
    assert _witness_status(payload, "intent_guard:packages/pkg_a/src/pkg_a/core.py") == "changed"
    assert _reason_kinds(payload, test_path="packages/pkg_b/tests/test_contract.py") == {
        "guarded_surface_binding"
    }


def test_owner_fallback_occurs_only_when_no_direct_evidence(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "from .api import call_api\n",
            "packages/pkg_a/src/pkg_a/latent.py": "FLAG = True\n",
            "packages/pkg_a/src/pkg_a/api.py": ('def call_api() -> str:\n    return "ok"\n'),
            "packages/pkg_a/tests/test_api.py": (
                "from pkg_a.api import call_api\n\n"
                "def test_api() -> None:\n"
                '    assert call_api() == "ok"\n'
            ),
            "packages/pkg_a/tests/test_smoke.py": ("def test_smoke() -> None:\n    assert True\n"),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/src/pkg_a/latent.py"],
        intent_matrix_path=None,
    )

    assert sorted(payload["selected_test_paths"]) == [
        "packages/pkg_a/tests/test_api.py",
        "packages/pkg_a/tests/test_smoke.py",
    ]
    assert payload["evidence_selected_test_paths"] == []
    assert sorted(payload["fallback_selected_test_paths"]) == [
        "packages/pkg_a/tests/test_api.py",
        "packages/pkg_a/tests/test_smoke.py",
    ]
    assert payload["risk_posture"] == "widened"
    assert "owner_fallback_widening" in _reason_kinds(
        payload,
        test_path="packages/pkg_a/tests/test_api.py",
    )


def test_source_parse_error_keeps_direct_evidence_without_owner_fallback_when_reach_is_recovered(
    tmp_path: Path,
) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "from .api import get_value\n",
            "packages/pkg_a/src/pkg_a/core.py": "def broken(:\n",
            "packages/pkg_a/src/pkg_a/api.py": (
                "from pkg_a.core import VALUE\n\ndef get_value() -> int:\n    return VALUE\n"
            ),
            "packages/pkg_a/src/pkg_a/other.py": ('def read_other() -> str:\n    return "ok"\n'),
            "packages/pkg_a/tests/test_api.py": (
                "from pkg_a.api import get_value\n\n"
                "def test_api() -> None:\n"
                "    assert get_value() == 1\n"
            ),
            "packages/pkg_a/tests/test_other.py": (
                "from pkg_a.other import read_other\n\n"
                "def test_other() -> None:\n"
                '    assert read_other() == "ok"\n'
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/src/pkg_a/core.py"],
        intent_matrix_path=None,
    )

    assert payload["selected_test_paths"] == ["packages/pkg_a/tests/test_api.py"]
    assert payload["fallback_selected_test_paths"] == []
    assert payload["risk_posture"] == "widened"
    assert _witness_status(payload, "source_module:pkg_a.core") == "unknown"
    assert _reason_kinds(payload, test_path="packages/pkg_a/tests/test_api.py") == {
        "direct_import_dependency"
    }


def test_support_module_imports_are_propagated_to_tests(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "apps/api/pyproject.toml": _package_pyproject("adeu_api"),
            "apps/api/src/adeu_api/__init__.py": "from .core import VALUE\n",
            "apps/api/src/adeu_api/core.py": "VALUE = 1\n",
            "apps/api/tests/path_helpers.py": "from adeu_api.core import VALUE\n",
            "apps/api/tests/test_tool.py": (
                "from path_helpers import VALUE\n\n"
                "def test_value() -> None:\n"
                "    assert VALUE == 1\n"
            ),
            "apps/api/tests/test_other.py": ("def test_other() -> None:\n    assert True\n"),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["apps/api/src/adeu_api/core.py"],
        intent_matrix_path=None,
    )

    assert payload["selected_test_paths"] == ["apps/api/tests/test_tool.py"]
    assert payload["fallback_selected_test_paths"] == []
    assert _reason_kinds(payload, test_path="apps/api/tests/test_tool.py") == {
        "direct_import_dependency"
    }


def test_app_script_path_consumers_can_flow_through_support_modules(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "apps/api/pyproject.toml": _package_pyproject("adeu_api"),
            "apps/api/src/adeu_api/__init__.py": "__all__ = []\n",
            "apps/api/scripts/tool.py": "def main() -> int:\n    return 0\n",
            "apps/api/tests/path_helpers.py": (
                "from pathlib import Path\n\n"
                "def script_path(root: Path) -> Path:\n"
                '    return root / "apps" / "api" / "scripts" / "tool.py"\n'
            ),
            "apps/api/tests/test_tool.py": (
                "from pathlib import Path\n"
                "from path_helpers import script_path\n\n"
                "def test_script_path() -> None:\n"
                "    assert script_path(Path('.'))\n"
            ),
            "apps/api/tests/test_other.py": ("def test_other() -> None:\n    assert True\n"),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["apps/api/scripts/tool.py"],
        intent_matrix_path=None,
    )

    assert payload["selected_test_paths"] == ["apps/api/tests/test_tool.py"]
    assert payload["fallback_selected_test_paths"] == []
    assert _reason_kinds(payload, test_path="apps/api/tests/test_tool.py") == {
        "artifact_consumer_dependency"
    }


def test_long_repo_like_literal_is_ignored_without_failing_path_recovery(tmp_path: Path) -> None:
    long_literal = "packages/" + ("segment/" * 40) + "not-a-real-path.json"
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "__all__ = []\n",
            "packages/pkg_a/src/pkg_a/core.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": (
                f"LONG_LITERAL = {long_literal!r}\n\n"
                "def test_value() -> None:\n"
                "    assert LONG_LITERAL.startswith('packages/')\n"
            ),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["packages/pkg_a/tests/test_core.py"],
        intent_matrix_path=None,
    )

    assert payload["selected_test_paths"] == ["packages/pkg_a/tests/test_core.py"]
    assert payload["warnings"] == []


def test_foundational_root_config_change_still_escalates(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": _package_pyproject("pkg_a"),
            "packages/pkg_a/src/pkg_a/__init__.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": (
                "from pkg_a import VALUE\n\ndef test_value() -> None:\n    assert VALUE == 1\n"
            ),
            "apps/api/pyproject.toml": _package_pyproject("adeu_api", deps=("pkg_a>=0.0.0",)),
            "apps/api/src/adeu_api/__init__.py": "__all__ = []\n",
            "apps/api/tests/test_health.py": ("def test_health() -> None:\n    assert True\n"),
        },
    )

    payload = select_python_tests_v0(
        repo_root=repo_root,
        changed_paths=["pyproject.toml"],
        intent_matrix_path=None,
    )

    assert payload["full_suite_recommended"] is True
    assert payload["risk_posture"] == "escalated"
    assert sorted(payload["selected_test_paths"]) == [
        "apps/api/tests/test_health.py",
        "packages/pkg_a/tests/test_core.py",
    ]
    assert payload["evidence_selected_test_paths"] == []
    assert payload["fallback_selected_test_paths"] == []
    assert sorted(payload["escalation_selected_test_paths"]) == [
        "apps/api/tests/test_health.py",
        "packages/pkg_a/tests/test_core.py",
    ]
    assert _witness_status(payload, "root_config:pyproject.toml") == "changed"
    assert _witness_status(payload, "escalation:full_suite") == "unknown"
    assert payload["escalation_reasons"] == ["foundational repo config changed: pyproject.toml"]


def test_main_uses_process_argv_when_argv_is_none(monkeypatch, capsys) -> None:
    observed: dict[str, object] = {}

    def _fake_selector(
        *,
        changed_paths: list[str],
        repo_root: Path | None,
        intent_matrix_path: str | None,
    ) -> dict[str, object]:
        observed["changed_paths"] = changed_paths
        observed["repo_root"] = repo_root
        observed["intent_matrix_path"] = intent_matrix_path
        return {"selected_test_paths": []}

    monkeypatch.setattr(test_selection_module, "select_python_tests_v0", _fake_selector)
    monkeypatch.setattr(
        "sys.argv",
        [
            "select_tests_v0.py",
            "--changed-path",
            "packages/pkg_a/tests/test_core.py",
            "--stdout-format",
            "paths",
            "--no-intent-matrix",
        ],
    )

    assert test_selection_module.main() == 0
    assert observed["changed_paths"] == ["packages/pkg_a/tests/test_core.py"]
    assert observed["repo_root"] is None
    assert observed["intent_matrix_path"] is None
    assert capsys.readouterr().out == ""


def test_selection_example_fixtures_are_parseable_and_stably_normalized() -> None:
    narrow = _load_fixture_payload("selection_narrow_example.json")
    fallback = _load_fixture_payload("selection_fallback_example.json")
    escalation = _load_fixture_payload("selection_escalation_example.json")

    for payload in (narrow, fallback, escalation):
        assert payload["schema"] == "repo_test_selection_plan@2"
        assert payload["selection_algorithm"] == "dependency_witness_selector_v0_2"
        assert payload["repo_root"] == "<repo-root>"
        assert all(not path.startswith("/") for path in payload["changed_paths"])

    assert narrow["risk_posture"] == "narrow"
    assert narrow["summary"]["evidence_selected_test_count"] == 1
    assert narrow["summary"]["fallback_selected_test_count"] == 0

    assert fallback["risk_posture"] == "widened"
    assert fallback["summary"]["evidence_selected_test_count"] == 0
    assert fallback["summary"]["fallback_selected_test_count"] == 2

    assert escalation["risk_posture"] == "escalated"
    assert escalation["full_suite_recommended"] is True
    assert escalation["summary"]["escalation_selected_test_count"] == 2
