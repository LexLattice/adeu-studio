from __future__ import annotations

import json
import shutil
from pathlib import Path
from typing import Any

import pytest
from adeu_agent_harness._v47_packaging_common import (
    AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION,
    AHK4711_SUBPROCESS_MODE_POLICY_VIOLATION,
    TaskpackPackagingError,
)
from adeu_agent_harness.package_ux import (
    DEPLOYMENT_MODE_INTEGRATED,
    DEPLOYMENT_MODE_STANDALONE,
    PACKAGING_MANIFEST_SCHEMA,
    package_ux_surface,
)
from adeu_ir.repo import repo_root
from urm_runtime.hashing import sha256_canonical_json


@pytest.fixture(autouse=True)
def _enforce_deterministic_env(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TZ", "UTC")
    monkeypatch.setenv("LC_ALL", "C")
    monkeypatch.setenv("PYTHONHASHSEED", "0")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _copy_file(root: Path, source_root: Path, rel_path: str) -> None:
    src = source_root / rel_path
    dst = root / rel_path
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def _pick_single(glob_pattern: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    matches = sorted(root.glob(glob_pattern))
    if len(matches) != 1:
        raise AssertionError(
            f"Expected exactly one match for {glob_pattern!r}, got {len(matches)}"
        )
    return matches[0]


@pytest.fixture
def packaging_repo(tmp_path: Path) -> dict[str, str]:
    source_root = repo_root(anchor=Path(__file__))
    root = tmp_path / "repo"
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    (root / "pyproject.toml").write_text("[tool.ruff]\nline-length = 100\n", encoding="utf-8")

    taskpack_rel = "artifacts/agent_harness/v46/taskpacks/v41/v46_closeout"
    shutil.copytree(source_root / taskpack_rel, root / taskpack_rel)

    verification_file = _pick_single("artifacts/agent_harness/v46/verification/*.json")
    evidence_candidates = sorted(
        (source_root / "artifacts/agent_harness/v46/evidence").glob("*.json")
    )
    evidence_bundle_candidates = [
        path for path in evidence_candidates if not path.name.endswith(".sha256.json")
    ]
    if len(evidence_bundle_candidates) != 1:
        raise AssertionError(
            f"Expected exactly one bundle json, got {len(evidence_bundle_candidates)}"
        )
    evidence_bundle_file = evidence_bundle_candidates[0]
    provenance_file = _pick_single("artifacts/agent_harness/v46/evidence/provenance/*.json")

    verification_rel = verification_file.relative_to(source_root).as_posix()
    evidence_bundle_rel = evidence_bundle_file.relative_to(source_root).as_posix()
    provenance_rel = provenance_file.relative_to(source_root).as_posix()

    for rel in (
        verification_rel,
        evidence_bundle_rel,
        provenance_rel,
        "artifacts/agent_harness/v46/evidence_inputs/runtime_observability_comparison_v46.json",
        "artifacts/agent_harness/v46/evidence_inputs/metric_key_continuity_assertion_v46.json",
        "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v47.json",
    ):
        _copy_file(root, source_root, rel)

    return {
        "repo_root": str(root),
        "taskpack_dir": taskpack_rel,
        "verified_result": verification_rel,
        "evidence_bundle": evidence_bundle_rel,
        "verifier_provenance": provenance_rel,
        "runtime_observability": (
            "artifacts/agent_harness/v46/evidence_inputs/"
            "runtime_observability_comparison_v46.json"
        ),
        "metric_key_continuity": (
            "artifacts/agent_harness/v46/evidence_inputs/"
            "metric_key_continuity_assertion_v46.json"
        ),
        "diagnostic_registry": (
            "packages/adeu_agent_harness/src/adeu_agent_harness/"
            "diagnostic_registry_v47.json"
        ),
        "packaging_output_root": "artifacts/agent_harness/v47/packaging_test",
    }


def test_package_ux_integrated_is_deterministic(packaging_repo: dict[str, str]) -> None:
    result1 = package_ux_surface(
        expected_mode=DEPLOYMENT_MODE_INTEGRATED,
        deployment_mode=DEPLOYMENT_MODE_INTEGRATED,
        taskpack_dir=packaging_repo["taskpack_dir"],
        verified_result_path=packaging_repo["verified_result"],
        evidence_bundle_path=packaging_repo["evidence_bundle"],
        verifier_provenance_path=packaging_repo["verifier_provenance"],
        runtime_observability_comparison_path=packaging_repo["runtime_observability"],
        metric_key_continuity_assertion_path=packaging_repo["metric_key_continuity"],
        packaging_output_root=packaging_repo["packaging_output_root"],
        diagnostic_registry_path=packaging_repo["diagnostic_registry"],
        dry_run=True,
        repo_root_path=packaging_repo["repo_root"],
    )
    result2 = package_ux_surface(
        expected_mode=DEPLOYMENT_MODE_INTEGRATED,
        deployment_mode=DEPLOYMENT_MODE_INTEGRATED,
        taskpack_dir=packaging_repo["taskpack_dir"],
        verified_result_path=packaging_repo["verified_result"],
        evidence_bundle_path=packaging_repo["evidence_bundle"],
        verifier_provenance_path=packaging_repo["verifier_provenance"],
        runtime_observability_comparison_path=packaging_repo["runtime_observability"],
        metric_key_continuity_assertion_path=packaging_repo["metric_key_continuity"],
        packaging_output_root=packaging_repo["packaging_output_root"],
        diagnostic_registry_path=packaging_repo["diagnostic_registry"],
        dry_run=True,
        repo_root_path=packaging_repo["repo_root"],
    )

    manifest_payload = _load_json(result1.packaging_manifest_path)
    assert manifest_payload["schema"] == PACKAGING_MANIFEST_SCHEMA
    assert manifest_payload["deployment_mode"] == DEPLOYMENT_MODE_INTEGRATED

    emitted_records = manifest_payload["emitted_files"]
    assert emitted_records == sorted(emitted_records, key=lambda row: row["path"])
    for record in emitted_records:
        assert set(record.keys()) == {"path", "sha256"}
        assert "\\" not in record["path"]
        assert not record["path"].startswith("/")

    recomputed_bundle_hash = sha256_canonical_json(emitted_records)
    assert recomputed_bundle_hash == manifest_payload["packaging_bundle_hash"]
    assert result1.packaging_bundle_hash == result2.packaging_bundle_hash

    assert (
        result1.packaging_manifest_path.read_bytes()
        == result2.packaging_manifest_path.read_bytes()
    )
    assert (
        result1.packaging_provenance_path.read_bytes()
        == result2.packaging_provenance_path.read_bytes()
    )


def test_package_ux_mode_mismatch_fails_closed(packaging_repo: dict[str, str]) -> None:
    with pytest.raises(TaskpackPackagingError) as exc_info:
        package_ux_surface(
            expected_mode=DEPLOYMENT_MODE_STANDALONE,
            deployment_mode=DEPLOYMENT_MODE_INTEGRATED,
            taskpack_dir=packaging_repo["taskpack_dir"],
            verified_result_path=packaging_repo["verified_result"],
            evidence_bundle_path=packaging_repo["evidence_bundle"],
            verifier_provenance_path=packaging_repo["verifier_provenance"],
            runtime_observability_comparison_path=packaging_repo["runtime_observability"],
            metric_key_continuity_assertion_path=packaging_repo["metric_key_continuity"],
            packaging_output_root=packaging_repo["packaging_output_root"],
            diagnostic_registry_path=packaging_repo["diagnostic_registry"],
            dry_run=True,
            repo_root_path=packaging_repo["repo_root"],
        )
    assert exc_info.value.code == AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION


def test_package_ux_env_override_is_forbidden(
    packaging_repo: dict[str, str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_DEPLOYMENT_MODE_OVERRIDE", DEPLOYMENT_MODE_INTEGRATED)

    with pytest.raises(TaskpackPackagingError) as exc_info:
        package_ux_surface(
            expected_mode=DEPLOYMENT_MODE_INTEGRATED,
            deployment_mode=DEPLOYMENT_MODE_INTEGRATED,
            taskpack_dir=packaging_repo["taskpack_dir"],
            verified_result_path=packaging_repo["verified_result"],
            evidence_bundle_path=packaging_repo["evidence_bundle"],
            verifier_provenance_path=packaging_repo["verifier_provenance"],
            runtime_observability_comparison_path=packaging_repo["runtime_observability"],
            metric_key_continuity_assertion_path=packaging_repo["metric_key_continuity"],
            packaging_output_root=packaging_repo["packaging_output_root"],
            diagnostic_registry_path=packaging_repo["diagnostic_registry"],
            dry_run=True,
            repo_root_path=packaging_repo["repo_root"],
        )
    assert exc_info.value.code == AHK4711_SUBPROCESS_MODE_POLICY_VIOLATION
