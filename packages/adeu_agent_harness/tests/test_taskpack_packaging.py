from __future__ import annotations

import ast
import json
from pathlib import Path
from typing import Any

import adeu_agent_harness.package_ux as packaging_mod
import adeu_agent_harness.package_ux_integrated as integrated_entry_mod
import adeu_agent_harness.package_ux_standalone as standalone_entry_mod
import pytest
from adeu_agent_harness._test_signing_handoff import seed_signing_handoff_fixture
from adeu_agent_harness._v47_packaging_common import (
    AHK4703_ARTIFACT_INVALID,
    AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
    AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION,
    AHK4708_CONTRACT_REGISTRY_INVALID,
    AHK4709_PACKAGING_REJECTION_DIAGNOSTIC_INVALID,
    AHK4711_SUBPROCESS_MODE_POLICY_VIOLATION,
    PackagingIssue,
    TaskpackPackagingError,
    emit_rejection_diagnostic,
    load_diagnostic_registry,
)
from adeu_agent_harness.compile import (
    PIPELINE_PROFILE_SCHEMA,
    TASKPACK_PROFILE_REGISTRY_SCHEMA,
    compile_taskpack,
)
from adeu_agent_harness.package_ux import (
    DEPLOYMENT_MODE_INTEGRATED,
    DEPLOYMENT_MODE_STANDALONE,
    PACKAGING_MANIFEST_SCHEMA,
    PACKAGING_PROVENANCE_SCHEMA,
    package_ux_surface,
)
from adeu_agent_harness.run_taskpack import RUNNER_RESULT_SCHEMA, run_taskpack
from adeu_agent_harness.verify_taskpack_run import verify_taskpack_run
from adeu_agent_harness.write_closeout_evidence import write_closeout_evidence
from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json

_OUT_DIR = "artifacts/agent_harness/v46/taskpacks/v41/v46_default"
_V46_DIAGNOSTIC_REGISTRY_REL = "artifacts/agent_harness/v46/diagnostic_registry_v46.json"
_V47_DIAGNOSTIC_REGISTRY_REL = (
    "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v47.json"
)


@pytest.fixture(autouse=True)
def _enforce_deterministic_env(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TZ", "UTC")
    monkeypatch.setenv("LC_ALL", "C")
    monkeypatch.setenv("PYTHONHASHSEED", "0")


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    _write(path, canonical_json(payload) + "\n")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _error_payload(exc: TaskpackPackagingError) -> dict[str, Any]:
    payload = json.loads(str(exc))
    assert payload["schema"] == "taskpack_packaging_error@1"
    return payload


def _relative(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def _repo_root_path(packaging_repo: dict[str, str]) -> Path:
    return Path(packaging_repo["repo_root"])


def _artifact_path(packaging_repo: dict[str, str], key: str) -> Path:
    return _repo_root_path(packaging_repo) / packaging_repo[key]


def _run_packaging(
    packaging_repo: dict[str, str],
    *,
    expected_mode: str = DEPLOYMENT_MODE_INTEGRATED,
    deployment_mode: str = DEPLOYMENT_MODE_INTEGRATED,
    dry_run: bool = True,
    taskpack_dir: str | None = None,
    signature_verification_result_path: str | None = None,
    signature_envelope_path: str | None = None,
    trust_anchor_registry_path: str | None = None,
    verification_reference_time_utc: str | None = None,
    verified_result_path: str | None = None,
    evidence_bundle_path: str | None = None,
    verifier_provenance_path: str | None = None,
    runtime_observability_comparison_path: str | None = None,
    metric_key_continuity_assertion_path: str | None = None,
    packaging_output_root: str | None = None,
    diagnostic_registry_path: str | None = None,
) -> Any:
    return package_ux_surface(
        expected_mode=expected_mode,
        deployment_mode=deployment_mode,
        taskpack_dir=taskpack_dir or packaging_repo["taskpack_dir"],
        signature_verification_result_path=(
            signature_verification_result_path or packaging_repo["signature_verification_result"]
        ),
        signature_envelope_path=signature_envelope_path or packaging_repo["signature_envelope"],
        trust_anchor_registry_path=trust_anchor_registry_path or packaging_repo["trust_anchor_registry"],
        verification_reference_time_utc=(
            verification_reference_time_utc or packaging_repo["verification_reference_time_utc"]
        ),
        verified_result_path=verified_result_path or packaging_repo["verified_result"],
        evidence_bundle_path=evidence_bundle_path or packaging_repo["evidence_bundle"],
        verifier_provenance_path=verifier_provenance_path or packaging_repo["verifier_provenance"],
        runtime_observability_comparison_path=(
            runtime_observability_comparison_path or packaging_repo["runtime_observability"]
        ),
        metric_key_continuity_assertion_path=(
            metric_key_continuity_assertion_path or packaging_repo["metric_key_continuity"]
        ),
        packaging_output_root=packaging_output_root or packaging_repo["packaging_output_root"],
        diagnostic_registry_path=diagnostic_registry_path or packaging_repo["diagnostic_registry"],
        dry_run=dry_run,
        repo_root_path=packaging_repo["repo_root"],
    )


def _base_repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    _write(root / "pyproject.toml", "[tool.ruff]\nline-length = 100\n")
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    return root


def _seed_semantic_authority_artifacts(root: Path) -> None:
    _write_json(
        root / "artifacts" / "semantic_compiler" / "v41" / "evidence_manifest.json",
        {
            "schema": "semantic_compiler_evidence_manifest@0.1",
            "arc": "vnext_plus41",
            "compiler_entrypoint": "python -m adeu_semantic_compiler.compile",
            "source_set_hash": "0" * 64,
            "required_evidence": [],
            "artifacts": {
                "surface_snapshot": "artifacts/semantic_compiler/v41/surface_snapshot.json",
                "surface_diff": "artifacts/semantic_compiler/v41/surface_diff.json",
                "evidence_manifest": "artifacts/semantic_compiler/v41/evidence_manifest.json",
            },
            "artifact_hashes": {
                "surface_snapshot": "1" * 64,
                "surface_diff": "2" * 64,
            },
        },
    )
    _write_json(
        root / "artifacts" / "semantic_compiler" / "v41" / "surface_diff.json",
        {
            "schema": "semantic_compiler_surface_diff@0.1",
            "baseline_present": True,
            "delta_eval_mode": "exact_set",
            "adds": [],
            "removes": [],
            "changes": [],
        },
    )
    _write_json(
        root / "artifacts" / "semantic_compiler" / "v40" / "commitments_ir.json",
        {
            "schema": "adeu_commitments_ir@0.1",
            "modules": [],
            "locks": [],
        },
    )


def _seed_profile_and_registry(root: Path) -> Path:
    profile_payload = {
        "schema": PIPELINE_PROFILE_SCHEMA,
        "profile_id": "v46_default",
        "task_scope_title": "V46 U1 Verifier/Evidence MVP",
        "task_scope_summary": "Compile deterministic taskpack for verifier lane.",
        "compiled_commitments_ir_path": "artifacts/semantic_compiler/v40/commitments_ir.json",
        "acceptance_criteria": [
            "Verifier cross-checks runner artifacts before evidence emission.",
            "Evidence writer emits deterministic canonical bundle/provenance.",
        ],
        "allowlist_paths": [
            "packages/adeu_agent_harness/src/adeu_agent_harness",
            "packages/adeu_agent_harness/tests",
            "artifacts/stop_gate",
        ],
        "forbidden_paths": ["apps/api"],
        "forbidden_effects": ["network_calls"],
        "commands": [
            {
                "command_id": "noop",
                "run": "true",
                "working_directory_or_repo_root": "repo_root",
                "env_overrides": {},
            }
        ],
        "evidence_slots": [
            {
                "slot_id": "runtime_observability_comparison",
                "description": "Runtime observability comparison row.",
                "required": True,
            },
            {
                "slot_id": "metric_key_continuity_assertion",
                "description": "Metric key continuity assertion block.",
                "required": True,
            },
            {
                "slot_id": "v33c_verifier_wiring_evidence",
                "description": "Verifier wiring evidence block.",
                "required": True,
            },
        ],
    }
    profile_path = root / "artifacts" / "agent_harness" / "v46" / "profiles" / "v46_default.json"
    _write_json(profile_path, profile_payload)

    registry_path = root / "artifacts" / "agent_harness" / "v46" / "taskpack_profile_registry.json"
    _write_json(
        registry_path,
        {
            "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
            "profiles": [
                {
                    "profile_id": "v46_default",
                    "profile_sha256": sha256_canonical_json(profile_payload),
                    "profile_payload_path": "artifacts/agent_harness/v46/profiles/v46_default.json",
                }
            ],
        },
    )
    return registry_path


def _compile_taskpack(root: Path, *, registry_path: Path) -> Path:
    result = compile_taskpack(
        profile_registry_path=_relative(root, registry_path),
        profile_id="v46_default",
        source_semantic_arc="v41",
        out_dir=_OUT_DIR,
        repo_root_path=root,
    )
    return result.out_dir


def _seed_adapter_registry(root: Path) -> Path:
    path = root / "artifacts" / "agent_harness" / "v45" / "taskpack_runner_adapter_registry.json"
    _write_json(
        path,
        {
            "schema": "taskpack_runner_adapter_registry@1",
            "adapters": [
                {
                    "adapter_id": "default",
                    "adapter_kind": "candidate_plan_passthrough",
                }
            ],
        },
    )
    return path


def _seed_v46_diagnostic_registry(root: Path) -> str:
    path = root / _V46_DIAGNOSTIC_REGISTRY_REL
    _write_json(
        path,
        {
            "schema": "taskpack_verifier_diagnostic_registry@1",
            "codes": [
                {
                    "issue_code": f"AHK46{index:02d}",
                    "title": f"V46_{index:02d}",
                    "description": "v46 verifier diagnostic code",
                }
                for index in range(16)
            ],
        },
    )
    return _V46_DIAGNOSTIC_REGISTRY_REL


def _seed_v47_diagnostic_registry(root: Path) -> str:
    path = root / _V47_DIAGNOSTIC_REGISTRY_REL
    _write_json(
        path,
        {
            "schema": "taskpack_packaging_diagnostic_registry@1",
            "codes": [
                {
                    "issue_code": f"AHK47{index:02d}",
                    "title": f"V47_{index:02d}",
                    "description": "v47 packaging diagnostic code",
                }
                for index in range(14)
            ],
        },
    )
    return _V47_DIAGNOSTIC_REGISTRY_REL


def _write_candidate_change_plan(root: Path, *, rel_path: str) -> Path:
    path = root / "artifacts" / "agent_harness" / "v46" / "candidate_change_plan.json"
    _write_json(
        path,
        {
            "schema": "candidate_change_plan@1",
            "file_operations": [
                {
                    "path": rel_path,
                    "operation_kind": "update",
                    "unified_diff": (
                        f"--- a/{rel_path}\n"
                        f"+++ b/{rel_path}\n"
                        "@@ -1,1 +1,1 @@\n"
                        "-before\n"
                        "+after\n"
                    ),
                }
            ],
            "proposed_commands": [],
        },
    )
    return path


def _write_runner_result_artifact(root: Path, *, run_result: Any) -> Path:
    path = root / "artifacts" / "agent_harness" / "v46" / "runner_result.json"
    payload = {
        "schema": RUNNER_RESULT_SCHEMA,
        "dry_run": run_result.dry_run,
        "candidate_change_plan_hash": run_result.candidate_change_plan_hash,
        "dry_run_preview_path": (
            _relative(root, run_result.dry_run_preview_path)
            if run_result.dry_run_preview_path is not None
            else None
        ),
        "provenance_path": _relative(root, run_result.provenance_path),
        "provenance_hash": run_result.provenance_hash,
        "rejection_diagnostic_path": (
            _relative(root, run_result.rejection_diagnostic_path)
            if run_result.rejection_diagnostic_path is not None
            else None
        ),
    }
    _write_json(path, payload)
    return path


def _seed_evidence_payloads(root: Path) -> tuple[Path, Path, Path]:
    runtime_path = root / "artifacts" / "stop_gate" / "runtime_observability_comparison_v46.json"
    _write_json(
        runtime_path,
        {
            "schema": "runtime_observability_comparison@1",
            "baseline_arc": "v45",
            "target_arc": "v46",
            "rows": [{"metric": "bytes_hashed_total", "baseline": 204690, "target": 204690}],
        },
    )

    continuity_path = root / "artifacts" / "stop_gate" / "metric_key_continuity_assertion_v46.json"
    _write_json(
        continuity_path,
        {
            "schema": "metric_key_continuity_assertion@1",
            "expected_cardinality": 80,
            "observed_cardinality": 80,
            "exact_set_equal": True,
        },
    )

    wiring_path = root / "artifacts" / "stop_gate" / "v33c_verifier_wiring_evidence_v46.json"
    _write_json(
        wiring_path,
        {
            "schema": "v33c_verifier_wiring_evidence@1",
            "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
            "evidence_writer_entrypoint": "python -m adeu_agent_harness.write_closeout_evidence",
            "verification_passed": True,
            "required_evidence_slots_filled": True,
        },
    )

    return runtime_path, continuity_path, wiring_path


@pytest.fixture
def packaging_repo(tmp_path: Path) -> dict[str, str]:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)

    v46_diagnostic_registry_rel = _seed_v46_diagnostic_registry(root)
    v47_diagnostic_registry_rel = _seed_v47_diagnostic_registry(root)

    registry_path = _seed_profile_and_registry(root)
    taskpack_dir = _compile_taskpack(root, registry_path=registry_path)
    adapter_registry_path = _seed_adapter_registry(root)
    signing = seed_signing_handoff_fixture(root, taskpack_dir=taskpack_dir)

    rel_path = "packages/adeu_agent_harness/src/adeu_agent_harness/v47_packaging_fixture.txt"
    fixture_path = root / rel_path
    _write(fixture_path, "before\n")

    candidate_path = _write_candidate_change_plan(root, rel_path=rel_path)
    run_result = run_taskpack(
        taskpack_dir=_relative(root, taskpack_dir),
        adapter_registry_path=_relative(root, adapter_registry_path),
        adapter_id="default",
        candidate_change_plan_path=_relative(root, candidate_path),
        **signing.as_kwargs(),
        dry_run=True,
        repo_root_path=root,
    )

    assert fixture_path.read_text(encoding="utf-8") == "before\n"

    runner_result_path = _write_runner_result_artifact(root, run_result=run_result)
    verify_result = verify_taskpack_run(
        taskpack_dir=_relative(root, taskpack_dir),
        candidate_change_plan_path=_relative(root, candidate_path),
        runner_result_path=_relative(root, runner_result_path),
        runner_provenance_path=_relative(root, run_result.provenance_path),
        policy_rejection_diagnostics_path=None,
        **signing.as_kwargs(),
        verification_output_root="artifacts/agent_harness/v46/verification",
        diagnostic_registry_path=v46_diagnostic_registry_rel,
        repo_root_path=root,
    )

    runtime_path, continuity_path, wiring_path = _seed_evidence_payloads(root)
    evidence_result = write_closeout_evidence(
        taskpack_dir=_relative(root, taskpack_dir),
        verified_result_path=_relative(root, verify_result.verification_result_path),
        runtime_observability_comparison_path=_relative(root, runtime_path),
        metric_key_continuity_assertion_path=_relative(root, continuity_path),
        verifier_wiring_evidence_path=_relative(root, wiring_path),
        evidence_output_root="artifacts/agent_harness/v46/evidence",
        diagnostic_registry_path=v46_diagnostic_registry_rel,
        repo_root_path=root,
    )

    return {
        "repo_root": str(root),
        "taskpack_dir": _relative(root, taskpack_dir),
        "signature_verification_result": signing.signature_verification_result_path,
        "signature_envelope": signing.signature_envelope_path,
        "trust_anchor_registry": signing.trust_anchor_registry_path,
        "verification_reference_time_utc": signing.verification_reference_time_utc,
        "verified_result": _relative(root, verify_result.verification_result_path),
        "evidence_bundle": _relative(root, evidence_result.evidence_bundle_path),
        "verifier_provenance": _relative(root, evidence_result.verifier_provenance_path),
        "runtime_observability": _relative(root, runtime_path),
        "metric_key_continuity": _relative(root, continuity_path),
        "diagnostic_registry": v47_diagnostic_registry_rel,
        "packaging_output_root": "artifacts/agent_harness/v47/packaging_test",
    }


def test_package_ux_integrated_is_deterministic(packaging_repo: dict[str, str]) -> None:
    result1 = _run_packaging(packaging_repo)
    result2 = _run_packaging(packaging_repo)

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
        _run_packaging(
            packaging_repo,
            expected_mode=DEPLOYMENT_MODE_STANDALONE,
            deployment_mode=DEPLOYMENT_MODE_INTEGRATED,
        )
    assert exc_info.value.code == AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION


def test_package_ux_env_override_is_forbidden(
    packaging_repo: dict[str, str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_DEPLOYMENT_MODE_OVERRIDE", DEPLOYMENT_MODE_INTEGRATED)

    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(packaging_repo)
    assert exc_info.value.code == AHK4711_SUBPROCESS_MODE_POLICY_VIOLATION


def test_packaging_entrypoints_are_present() -> None:
    assert callable(packaging_mod.package_ux_surface)
    assert callable(packaging_mod.main_for_mode)
    assert callable(integrated_entry_mod.main)
    assert callable(standalone_entry_mod.main)


def test_packaging_kernel_has_no_apps_api_imports() -> None:
    module_root = (
        repo_root(anchor=Path(__file__))
        / "packages"
        / "adeu_agent_harness"
        / "src"
        / "adeu_agent_harness"
    )
    targets = [
        module_root / "_v47_packaging_common.py",
        module_root / "package_ux.py",
        module_root / "package_ux_integrated.py",
        module_root / "package_ux_standalone.py",
    ]
    violations: list[str] = []
    for path in targets:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name.startswith("apps.api"):
                        violations.append(f"{path}:{alias.name}")
            if isinstance(node, ast.ImportFrom):
                module = node.module or ""
                if module.startswith("apps.api"):
                    violations.append(f"{path}:{module}")
    assert not violations, f"direct apps/api imports found: {violations}"


def test_package_ux_fails_closed_on_deterministic_env_drift(
    packaging_repo: dict[str, str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("TZ", "Europe/Bucharest")

    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(packaging_repo)

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4703_ARTIFACT_INVALID
    assert payload["details"]["required_deterministic_env"]["TZ"] == "UTC"


def test_package_ux_rejects_unknown_deployment_mode(packaging_repo: dict[str, str]) -> None:
    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(
            packaging_repo,
            expected_mode=DEPLOYMENT_MODE_INTEGRATED,
            deployment_mode="unknown_mode",
        )
    assert exc_info.value.code == AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION


def test_package_ux_rejects_non_exact_case_mode_value(packaging_repo: dict[str, str]) -> None:
    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(
            packaging_repo,
            expected_mode=DEPLOYMENT_MODE_INTEGRATED,
            deployment_mode="ADEU_INTEGRATED",
        )
    assert exc_info.value.code == AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION


def test_package_ux_fails_closed_on_verified_result_schema_drift(
    packaging_repo: dict[str, str],
) -> None:
    verified_result_path = _artifact_path(packaging_repo, "verified_result")
    verified_result_payload = _load_json(verified_result_path)
    verified_result_payload["schema"] = "taskpack_verification_result@999"
    _write_json(verified_result_path, verified_result_payload)

    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(packaging_repo)
    assert _error_payload(exc_info.value)["code"] == "AHK4702"


def test_package_ux_fails_closed_on_evidence_bundle_schema_drift(
    packaging_repo: dict[str, str],
) -> None:
    evidence_bundle_path = _artifact_path(packaging_repo, "evidence_bundle")
    evidence_bundle_payload = _load_json(evidence_bundle_path)
    evidence_bundle_payload["schema"] = "taskpack_closeout_evidence_bundle@999"
    _write_json(evidence_bundle_path, evidence_bundle_payload)

    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(packaging_repo)
    assert _error_payload(exc_info.value)["code"] == "AHK4702"


def test_package_ux_fails_closed_on_verifier_provenance_schema_drift(
    packaging_repo: dict[str, str],
) -> None:
    verifier_provenance_path = _artifact_path(packaging_repo, "verifier_provenance")
    verifier_provenance_payload = _load_json(verifier_provenance_path)
    verifier_provenance_payload["schema"] = "taskpack_verifier_provenance@999"
    _write_json(verifier_provenance_path, verifier_provenance_payload)

    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(packaging_repo)
    assert _error_payload(exc_info.value)["code"] == "AHK4702"


def test_package_ux_fails_closed_on_missing_required_input_artifact(
    packaging_repo: dict[str, str],
) -> None:
    evidence_bundle_path = _artifact_path(packaging_repo, "evidence_bundle")
    evidence_bundle_path.unlink()

    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(packaging_repo)
    payload = _error_payload(exc_info.value)
    assert payload["code"] == "AHK4700"
    assert "rejection_diagnostic_path" in payload["details"]


def test_package_ux_fails_closed_on_missing_signature_handoff(
    packaging_repo: dict[str, str],
) -> None:
    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(
            packaging_repo,
            signature_verification_result_path="artifacts/agent_harness/v49/test_signing/missing.json",
        )
    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4703_ARTIFACT_INVALID
    assert payload["details"]["signing_error_code"] == "AHK4800"


def test_package_ux_emits_rejection_diagnostic_and_no_partial_package_on_failure(
    packaging_repo: dict[str, str],
) -> None:
    verified_result_path = _artifact_path(packaging_repo, "verified_result")
    verified_result_payload = _load_json(verified_result_path)
    verified_result_payload["verified_result_hash"] = "f" * 64
    _write_json(verified_result_path, verified_result_payload)

    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(packaging_repo)

    payload = _error_payload(exc_info.value)
    assert payload["code"] == AHK4704_CROSS_ARTIFACT_HASH_MISMATCH

    rejection_path = Path(payload["details"]["rejection_diagnostic_path"])
    rejection_payload = _load_json(rejection_path)
    assert rejection_payload["schema"] == "v33d_packaging_rejection_diagnostic@1"
    assert rejection_payload["issues"][0]["issue_code"] == AHK4704_CROSS_ARTIFACT_HASH_MISMATCH

    packaging_output_root = (
        _repo_root_path(packaging_repo) / packaging_repo["packaging_output_root"]
    )
    mode_output_path = packaging_output_root / DEPLOYMENT_MODE_INTEGRATED
    assert not mode_output_path.exists() or not any(mode_output_path.iterdir())


def test_package_ux_fails_closed_on_registry_prefix_drift(
    packaging_repo: dict[str, str],
) -> None:
    registry_path = _artifact_path(packaging_repo, "diagnostic_registry")
    registry_payload = _load_json(registry_path)
    registry_payload["codes"][0]["issue_code"] = "AHK9900"
    _write_json(registry_path, registry_payload)

    with pytest.raises(TaskpackPackagingError) as exc_info:
        _run_packaging(packaging_repo)
    assert _error_payload(exc_info.value)["code"] == AHK4708_CONTRACT_REGISTRY_INVALID


def test_package_ux_cross_mode_parity_domain_and_bundle_boundary(
    packaging_repo: dict[str, str],
) -> None:
    integrated_result = _run_packaging(
        packaging_repo,
        expected_mode=DEPLOYMENT_MODE_INTEGRATED,
        deployment_mode=DEPLOYMENT_MODE_INTEGRATED,
    )
    standalone_result = _run_packaging(
        packaging_repo,
        expected_mode=DEPLOYMENT_MODE_STANDALONE,
        deployment_mode=DEPLOYMENT_MODE_STANDALONE,
    )

    output_root = _repo_root_path(packaging_repo) / packaging_repo["packaging_output_root"]
    integrated_canonical = output_root / DEPLOYMENT_MODE_INTEGRATED / "canonical"
    standalone_canonical = output_root / DEPLOYMENT_MODE_STANDALONE / "canonical"

    integrated_files = sorted(
        path.relative_to(integrated_canonical).as_posix()
        for path in integrated_canonical.rglob("*")
        if path.is_file()
    )
    standalone_files = sorted(
        path.relative_to(standalone_canonical).as_posix()
        for path in standalone_canonical.rglob("*")
        if path.is_file()
    )
    assert integrated_files == standalone_files
    for rel_path in integrated_files:
        assert (integrated_canonical / rel_path).read_bytes() == (
            standalone_canonical / rel_path
        ).read_bytes()

    integrated_bundle = output_root / DEPLOYMENT_MODE_INTEGRATED / "bundle" / "launcher.txt"
    standalone_bundle = output_root / DEPLOYMENT_MODE_STANDALONE / "bundle" / "launcher.txt"
    assert integrated_bundle.read_text(encoding="utf-8") != standalone_bundle.read_text(
        encoding="utf-8"
    )

    integrated_provenance = _load_json(integrated_result.packaging_provenance_path)
    standalone_provenance = _load_json(standalone_result.packaging_provenance_path)
    assert (
        integrated_provenance["parity_result"]["policy_equivalence"]
        == standalone_provenance["parity_result"]["policy_equivalence"]
    )


def test_packaging_manifest_and_bundle_hash_subject_are_deterministic(
    packaging_repo: dict[str, str],
) -> None:
    result = _run_packaging(packaging_repo)
    manifest_payload = _load_json(result.packaging_manifest_path)
    assert set(manifest_payload.keys()) == {
        "schema",
        "deployment_mode",
        "authority_artifact_hashes",
        "emitted_files",
        "packaging_bundle_hash",
    }
    assert manifest_payload["schema"] == PACKAGING_MANIFEST_SCHEMA

    emitted_files = manifest_payload["emitted_files"]
    assert emitted_files == sorted(emitted_files, key=lambda row: row["path"])
    assert all(set(row.keys()) == {"path", "sha256"} for row in emitted_files)
    assert all("\\" not in row["path"] for row in emitted_files)

    recomputed_bundle_hash = sha256_canonical_json(
        [{"path": row["path"], "sha256": row["sha256"]} for row in emitted_files]
    )
    assert recomputed_bundle_hash == manifest_payload["packaging_bundle_hash"]


def test_packaging_provenance_excludes_nondeterministic_fields(
    packaging_repo: dict[str, str],
) -> None:
    result = _run_packaging(packaging_repo)
    provenance_payload = _load_json(result.packaging_provenance_path)
    assert provenance_payload["schema"] == PACKAGING_PROVENANCE_SCHEMA
    assert set(provenance_payload.keys()) == {
        "schema",
        "taskpack_manifest_hash",
        "verified_result_hash",
        "evidence_bundle_hash",
        "deployment_mode",
        "parity_result",
        "exit_status",
        "provenance_hash",
    }
    for forbidden in ("wall_clock_timestamp", "host_identity", "absolute_paths"):
        assert forbidden not in provenance_payload


def test_emit_rejection_diagnostic_orders_and_normalizes_paths(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    registry_rel = _seed_v47_diagnostic_registry(root)
    _, registry_codes = load_diagnostic_registry(root=root, registry_rel_path=registry_rel)

    emitted = emit_rejection_diagnostic(
        root=root,
        output_root_rel="artifacts/agent_harness/v47/rejections",
        taskpack_manifest_hash="a" * 64,
        verified_result_hash="b" * 64,
        issues=[
            PackagingIssue(
                issue_code="AHK4702",
                reason="later policy source",
                artifact_path="b/./x/../file.json",
                deployment_mode="standalone",
                policy_source="stop_gate_metrics",
            ),
            PackagingIssue(
                issue_code="AHK4702",
                reason="earlier policy source",
                artifact_path="b/file.json",
                deployment_mode="standalone",
                policy_source="packaging_manifest",
            ),
            PackagingIssue(
                issue_code="AHK4701",
                reason="first by code/path",
                artifact_path="a/file.json",
                deployment_mode="adeu_integrated",
                policy_source="verified_result",
            ),
        ],
        allowed_codes=registry_codes,
    )

    emitted_payload = _load_json(emitted)
    rows = emitted_payload["issues"]
    assert rows == [
        {
            "issue_code": "AHK4701",
            "reason": "first by code/path",
            "artifact_path": "a/file.json",
            "deployment_mode": "adeu_integrated",
            "policy_source": "verified_result",
        },
        {
            "issue_code": "AHK4702",
            "reason": "earlier policy source",
            "artifact_path": "b/file.json",
            "deployment_mode": "standalone",
            "policy_source": "packaging_manifest",
        },
        {
            "issue_code": "AHK4702",
            "reason": "later policy source",
            "artifact_path": "b/file.json",
            "deployment_mode": "standalone",
            "policy_source": "stop_gate_metrics",
        },
    ]


def test_emit_rejection_diagnostic_fails_on_policy_source_outside_closed_enum(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    registry_rel = _seed_v47_diagnostic_registry(root)
    _, registry_codes = load_diagnostic_registry(root=root, registry_rel_path=registry_rel)

    with pytest.raises(TaskpackPackagingError) as exc_info:
        emit_rejection_diagnostic(
            root=root,
            output_root_rel="artifacts/agent_harness/v47/rejections",
            taskpack_manifest_hash="a" * 64,
            verified_result_hash="b" * 64,
            issues=[
                PackagingIssue(
                    issue_code="AHK4702",
                    reason="invalid policy source",
                    artifact_path="a/file.json",
                    deployment_mode="adeu_integrated",
                    policy_source="free_text",
                )
            ],
            allowed_codes=registry_codes,
        )
    assert _error_payload(exc_info.value)["code"] == AHK4709_PACKAGING_REJECTION_DIAGNOSTIC_INVALID


def test_packaging_cli_returns_non_zero_on_required_violation(
    packaging_repo: dict[str, str],
) -> None:
    verified_result_path = _artifact_path(packaging_repo, "verified_result")
    verified_result_payload = _load_json(verified_result_path)
    verified_result_payload["verified_result_hash"] = "f" * 64
    _write_json(verified_result_path, verified_result_payload)

    exit_code = integrated_entry_mod.main(
        [
            "--deployment-mode",
            DEPLOYMENT_MODE_INTEGRATED,
            "--taskpack-dir",
            packaging_repo["taskpack_dir"],
            "--signature-verification-result",
            packaging_repo["signature_verification_result"],
            "--signature-envelope",
            packaging_repo["signature_envelope"],
            "--trust-anchor-registry",
            packaging_repo["trust_anchor_registry"],
            "--verification-reference-time-utc",
            packaging_repo["verification_reference_time_utc"],
            "--verified-result",
            packaging_repo["verified_result"],
            "--evidence-bundle",
            packaging_repo["evidence_bundle"],
            "--verifier-provenance",
            packaging_repo["verifier_provenance"],
            "--runtime-observability-comparison",
            packaging_repo["runtime_observability"],
            "--metric-key-continuity-assertion",
            packaging_repo["metric_key_continuity"],
            "--packaging-output-root",
            packaging_repo["packaging_output_root"],
            "--diagnostic-registry",
            packaging_repo["diagnostic_registry"],
            "--repo-root",
            packaging_repo["repo_root"],
            "--dry-run",
        ]
    )
    assert exit_code == 1


def test_packaging_cli_requires_explicit_deployment_mode_flag(
    packaging_repo: dict[str, str],
) -> None:
    with pytest.raises(SystemExit) as exc_info:
        integrated_entry_mod.main(
            [
                "--taskpack-dir",
                packaging_repo["taskpack_dir"],
                "--signature-verification-result",
                packaging_repo["signature_verification_result"],
                "--signature-envelope",
                packaging_repo["signature_envelope"],
                "--trust-anchor-registry",
                packaging_repo["trust_anchor_registry"],
                "--verification-reference-time-utc",
                packaging_repo["verification_reference_time_utc"],
                "--verified-result",
                packaging_repo["verified_result"],
                "--evidence-bundle",
                packaging_repo["evidence_bundle"],
                "--verifier-provenance",
                packaging_repo["verifier_provenance"],
                "--runtime-observability-comparison",
                packaging_repo["runtime_observability"],
                "--metric-key-continuity-assertion",
                packaging_repo["metric_key_continuity"],
                "--packaging-output-root",
                packaging_repo["packaging_output_root"],
                "--diagnostic-registry",
                packaging_repo["diagnostic_registry"],
                "--repo-root",
                packaging_repo["repo_root"],
            ]
        )
    assert exc_info.value.code == 2


def test_stop_gate_v46_metric_key_baseline_is_stable() -> None:
    resolved_repo_root = repo_root(anchor=Path(__file__))
    v46_payload = _load_json(resolved_repo_root / "artifacts/stop_gate/metrics_v46_closeout.json")
    assert v46_payload["schema"] == "stop_gate_metrics@1"
    assert len(set(v46_payload["metrics"].keys())) == 80
