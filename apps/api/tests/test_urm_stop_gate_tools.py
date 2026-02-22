from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest
import urm_runtime.stop_gate_tools as stop_gate_tools_module
from adeu_kernel import (
    build_proof_evidence_packet,
    build_semantics_diagnostics,
    build_validator_evidence_packet,
)
from urm_runtime.hashing import sha256_canonical_json
from urm_runtime.stop_gate_tools import build_stop_gate_metrics, main


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _example_stop_gate_path(name: str) -> Path:
    return _repo_root() / "examples" / "eval" / "stop_gate" / name


def _event_fixture_path(name: str) -> Path:
    return _repo_root() / "apps" / "api" / "tests" / "fixtures" / "urm_events" / name


def _validator_evidence_fixture_path(name: str) -> Path:
    return _repo_root() / "examples" / "eval" / "stop_gate" / name


def _semantics_diagnostics_fixture_path(name: str) -> Path:
    return _repo_root() / "examples" / "eval" / "stop_gate" / name


def _vnext_plus7_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus7_manifest.json"


def _vnext_plus8_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus8_manifest.json"


def _vnext_plus9_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus9_manifest.json"


def _vnext_plus10_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus10_manifest.json"


def _vnext_plus11_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus11_manifest.json"


def _vnext_plus13_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus13_manifest.json"


def _vnext_plus14_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus14_manifest.json"


def _vnext_plus15_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus15_manifest.json"


def _vnext_plus16_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus16_manifest.json"


def _vnext_plus17_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus17_manifest.json"


def _vnext_plus18_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus18_manifest.json"


def _vnext_plus19_manifest_path() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "stop_gate" / "vnext_plus19_manifest.json"


_DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELDS = {
    "domain_conformance_hash",
    "hash_excluded_fields",
    "generated_at",
    "runtime_root_path",
    "missing_runtime_root_path",
    "operator_note",
}


def _strip_nonsemantic_domain_conformance_fields(value: object) -> object:
    if isinstance(value, dict):
        normalized: dict[str, object] = {}
        for key in sorted(value):
            key_str = str(key)
            if key_str in _DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELDS:
                continue
            normalized[key_str] = _strip_nonsemantic_domain_conformance_fields(value[key])
        return normalized
    if isinstance(value, list):
        return [_strip_nonsemantic_domain_conformance_fields(item) for item in value]
    return value


def _domain_conformance_hash(payload: dict[str, object]) -> str:
    semantic_payload = _strip_nonsemantic_domain_conformance_fields(payload)
    serialized = json.dumps(semantic_payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(serialized.encode("utf-8")).hexdigest()


def _quality_metrics_v3(*, overrides: dict[str, float] | None = None) -> dict[str, float]:
    metrics = {
        "redundancy_rate": 0.2,
        "top_k_stability@10": 1.0,
        "evidence_coverage_rate": 1.0,
        "bridge_loss_utilization_rate": 0.0,
        "coherence_alert_count": 0.0,
    }
    metrics.update(overrides or {})
    return metrics


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")


def _legacy_quality_payload() -> dict[str, object]:
    return {
        "dashboard_version": "quality.dashboard.v1",
        "metrics": {"question_stability_pct": 100.0},
    }


def _write_policy_lineage_replay_paths(tmp_path: Path) -> list[Path]:
    policy_lineage_paths = [
        tmp_path / "policy_lineage_1.json",
        tmp_path / "policy_lineage_2.json",
        tmp_path / "policy_lineage_3.json",
    ]
    for idx, path in enumerate(policy_lineage_paths, start=1):
        payload = json.loads(
            _example_stop_gate_path(f"policy_lineage_case_a_{idx}.json").read_text()
        )
        if idx == 2:
            payload["profile_version"] = "profile.v2"
        _write_json(path, payload)
    return policy_lineage_paths


def _write_proof_replay_paths_with_drift(tmp_path: Path) -> list[Path]:
    base_packet = json.loads(_example_stop_gate_path("proof_evidence_case_a_1.json").read_text())
    drift_packet = build_proof_evidence_packet(
        proof_id="proof-stop-gate-drift",
        artifact_id=str(base_packet["artifact_id"]),
        created_at="1970-01-01T00:00:11Z",
        backend=str(base_packet["backend"]),
        theorem_id=str(base_packet["theorem_id"]),
        status=str(base_packet["status"]),
        proof_hash=str(base_packet["proof_hash"]),
        inputs=list(base_packet["inputs"]),
        details={
            **dict(base_packet["details"]),
            "obligation_kind": "pred_closed_world",
        },
    )
    proof_paths = [
        tmp_path / "proof_evidence_1.json",
        tmp_path / "proof_evidence_2.json",
        tmp_path / "proof_evidence_3.json",
    ]
    _write_json(proof_paths[0], base_packet)
    _write_json(proof_paths[1], drift_packet)
    _write_json(proof_paths[2], base_packet)
    return proof_paths


def _vnext_plus7_manifest_payload(
    *,
    policy_lint_event_paths: list[Path],
    proof_paths: list[Path],
    policy_lineage_paths: list[Path],
) -> dict[str, object]:
    return {
        "schema": "stop_gate.vnext_plus7_manifest@1",
        "replay_count": 3,
        "metrics": {
            "policy_lint_determinism_pct": [
                {
                    "fixture_id": "policy_lint_case_a",
                    "runs": [
                        {"policy_lint_event_path": str(policy_lint_event_paths[0])},
                        {"policy_lint_event_path": str(policy_lint_event_paths[1])},
                        {"policy_lint_event_path": str(policy_lint_event_paths[2])},
                    ],
                }
            ],
            "proof_replay_determinism_pct": [
                {
                    "fixture_id": "proof_case_a",
                    "runs": [
                        {"proof_evidence_path": str(proof_paths[0])},
                        {"proof_evidence_path": str(proof_paths[1])},
                        {"proof_evidence_path": str(proof_paths[2])},
                    ],
                }
            ],
            "policy_proof_packet_hash_stability_pct": [
                {
                    "fixture_id": "policy_proof_case_a",
                    "runs": [
                        {
                            "policy_lineage_path": str(policy_lineage_paths[0]),
                            "proof_evidence_path": str(proof_paths[0]),
                        },
                        {
                            "policy_lineage_path": str(policy_lineage_paths[1]),
                            "proof_evidence_path": str(proof_paths[1]),
                        },
                        {
                            "policy_lineage_path": str(policy_lineage_paths[2]),
                            "proof_evidence_path": str(proof_paths[2]),
                        },
                    ],
                }
            ],
        },
    }


def _explain_semantic_packet_fixture() -> dict[str, object]:
    payload = json.loads(
        (
            _repo_root()
            / "apps"
            / "api"
            / "tests"
            / "fixtures"
            / "explain_parity"
            / "semantic_diff_golden_v1.json"
        ).read_text(encoding="utf-8")
    )
    return dict(payload["expected_packet"])


def _explain_concepts_packet_fixture() -> dict[str, object]:
    payload = json.loads(
        (
            _repo_root()
            / "apps"
            / "api"
            / "tests"
            / "fixtures"
            / "explain_parity"
            / "concepts_diff_golden_v1.json"
        ).read_text(encoding="utf-8")
    )
    return dict(payload["expected_packet"])


def _write_explain_replay_paths(tmp_path: Path) -> tuple[list[Path], list[Path], list[Path]]:
    packet = _explain_semantic_packet_fixture()
    diff_paths = [tmp_path / f"explain_diff_{idx}.json" for idx in (1, 2, 3)]
    api_paths = [tmp_path / f"explain_api_{idx}.json" for idx in (1, 2, 3)]
    cli_paths = [tmp_path / f"explain_cli_{idx}.json" for idx in (1, 2, 3)]
    for path in [*diff_paths, *api_paths, *cli_paths]:
        _write_json(path, packet)
    return diff_paths, api_paths, cli_paths


def _vnext_plus8_manifest_payload(
    *,
    explain_diff_paths: list[Path],
    api_paths: list[Path],
    cli_paths: list[Path],
) -> dict[str, object]:
    payload = {
        "schema": "stop_gate.vnext_plus8_manifest@1",
        "replay_count": 3,
        "metrics": {
            "explain_diff_determinism_pct": [
                {
                    "fixture_id": "explain_diff_case_a",
                    "runs": [
                        {"explain_diff_path": str(explain_diff_paths[0])},
                        {"explain_diff_path": str(explain_diff_paths[1])},
                        {"explain_diff_path": str(explain_diff_paths[2])},
                    ],
                }
            ],
            "explain_api_cli_parity_pct": [
                {
                    "fixture_id": "explain_api_cli_parity_case_a",
                    "runs": [
                        {
                            "api_explain_path": str(api_paths[0]),
                            "cli_explain_path": str(cli_paths[0]),
                        },
                        {
                            "api_explain_path": str(api_paths[1]),
                            "cli_explain_path": str(cli_paths[1]),
                        },
                        {
                            "api_explain_path": str(api_paths[2]),
                            "cli_explain_path": str(cli_paths[2]),
                        },
                    ],
                }
            ],
            "explain_hash_stability_pct": [
                {
                    "fixture_id": "explain_hash_stability_case_a",
                    "runs": [
                        {"explain_diff_path": str(explain_diff_paths[0])},
                        {"explain_diff_path": str(explain_diff_paths[1])},
                        {"explain_diff_path": str(explain_diff_paths[2])},
                    ],
                }
            ],
        },
    }
    manifest_blob = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["manifest_hash"] = hashlib.sha256(manifest_blob.encode("utf-8")).hexdigest()
    return payload


def _write_ndjson(path: Path, records: list[dict[str, object]]) -> None:
    payload = "\n".join(
        json.dumps(record, sort_keys=True, separators=(",", ":")) for record in records
    )
    path.write_text(payload + "\n", encoding="utf-8")


def _write_vnext_plus9_budget_cancel_paths_with_drift(tmp_path: Path) -> list[Path]:
    base_records = [
        json.loads(line)
        for line in _example_stop_gate_path("concurrent_budget_cancel_events_case_a_1.ndjson")
        .read_text(encoding="utf-8")
        .splitlines()
        if line.strip()
    ]
    run1 = json.loads(json.dumps(base_records))
    run2 = json.loads(json.dumps(base_records))
    run3 = json.loads(json.dumps(base_records))

    for record in run2:
        if record.get("event") != "WORKER_FAIL":
            continue
        detail = record.get("detail")
        if isinstance(detail, dict) and detail.get("code") == "URM_CHILD_BUDGET_EXCEEDED":
            detail["dispatch_seq"] = detail.get("dispatch_seq", 0) + 10
            detail["lease_id"] = f"{detail.get('lease_id')}-drift"
            break

    run_paths = [tmp_path / f"budget_cancel_{idx}.ndjson" for idx in (1, 2, 3)]
    _write_ndjson(run_paths[0], run1)
    _write_ndjson(run_paths[1], run2)
    _write_ndjson(run_paths[2], run3)
    return run_paths


def _vnext_plus9_manifest_payload(
    *,
    scheduler_dispatch_paths: list[Path],
    orphan_recovery_paths: list[Path],
    budget_cancel_paths: list[Path],
) -> dict[str, object]:
    payload = {
        "schema": "stop_gate.vnext_plus9_manifest@1",
        "replay_count": 3,
        "metrics": {
            "scheduler_dispatch_replay_determinism_pct": [
                {
                    "fixture_id": "scheduler_dispatch_case_a",
                    "runs": [
                        {"dispatch_token_path": str(scheduler_dispatch_paths[0])},
                        {"dispatch_token_path": str(scheduler_dispatch_paths[1])},
                        {"dispatch_token_path": str(scheduler_dispatch_paths[2])},
                    ],
                }
            ],
            "orphan_lease_recovery_determinism_pct": [
                {
                    "fixture_id": "orphan_lease_recovery_case_a",
                    "runs": [
                        {"orphan_recovery_event_path": str(orphan_recovery_paths[0])},
                        {"orphan_recovery_event_path": str(orphan_recovery_paths[1])},
                        {"orphan_recovery_event_path": str(orphan_recovery_paths[2])},
                    ],
                }
            ],
            "concurrent_budget_cancel_stability_pct": [
                {
                    "fixture_id": "concurrent_budget_cancel_case_a",
                    "runs": [
                        {"budget_cancel_event_path": str(budget_cancel_paths[0])},
                        {"budget_cancel_event_path": str(budget_cancel_paths[1])},
                        {"budget_cancel_event_path": str(budget_cancel_paths[2])},
                    ],
                }
            ],
        },
    }
    manifest_blob = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["manifest_hash"] = hashlib.sha256(manifest_blob.encode("utf-8")).hexdigest()
    return payload


def _semantic_depth_report_fixture() -> dict[str, object]:
    return json.loads(
        _example_stop_gate_path("semantic_depth_report_case_a_1.json").read_text(encoding="utf-8")
    )


def _semantic_depth_expected_conflicts_fixture() -> dict[str, object]:
    return json.loads(
        _example_stop_gate_path("semantic_depth_expected_conflicts_case_a.json").read_text(
            encoding="utf-8"
        )
    )


def _write_semantic_depth_replay_paths(tmp_path: Path) -> tuple[list[Path], list[Path]]:
    report_payload = _semantic_depth_report_fixture()
    expected_payload = _semantic_depth_expected_conflicts_fixture()
    report_paths = [tmp_path / f"semantic_depth_report_{idx}.json" for idx in (1, 2, 3)]
    expected_paths = [tmp_path / f"semantic_depth_expected_{idx}.json" for idx in (1, 2, 3)]
    for report_path in report_paths:
        _write_json(report_path, report_payload)
    for expected_path in expected_paths:
        _write_json(expected_path, expected_payload)
    return report_paths, expected_paths


def _vnext_plus10_manifest_payload(
    *,
    precision_runs: list[dict[str, str]],
    recall_runs: list[dict[str, str]],
    coherence_runs: list[dict[str, str]],
    baseline_precision_pct: float = 99.0,
    baseline_recall_pct: float = 99.0,
    plateau_epsilon_pct: float = 0.1,
) -> dict[str, object]:
    payload = {
        "schema": "stop_gate.vnext_plus10_manifest@1",
        "replay_count": 3,
        "baseline_concept_conflict_precision_pct": baseline_precision_pct,
        "baseline_concept_conflict_recall_pct": baseline_recall_pct,
        "plateau_epsilon_pct": plateau_epsilon_pct,
        "metrics": {
            "concept_conflict_precision_pct": [
                {
                    "fixture_id": "concept_conflict_precision_case_a",
                    "runs": precision_runs,
                }
            ],
            "concept_conflict_recall_pct": [
                {
                    "fixture_id": "concept_conflict_recall_case_a",
                    "runs": recall_runs,
                }
            ],
            "coherence_permutation_stability_pct": [
                {
                    "fixture_id": "coherence_permutation_stability_case_a",
                    "runs": coherence_runs,
                }
            ],
        },
    }
    manifest_blob = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["manifest_hash"] = hashlib.sha256(manifest_blob.encode("utf-8")).hexdigest()
    return payload


def _vnext_plus11_manifest_payload(
    *,
    replay_runs: list[dict[str, str]],
    parity_runs: list[dict[str, str]],
    coupling_runs: list[dict[str, str]],
) -> dict[str, object]:
    payload = {
        "schema": "stop_gate.vnext_plus11_manifest@1",
        "replay_count": 3,
        "coverage": [],
        "metrics": {
            "domain_conformance_replay_determinism_pct": [
                {
                    "fixture_id": "domain_conformance_replay.case_a",
                    "runs": replay_runs,
                }
            ],
            "cross_domain_artifact_parity_pct": [
                {
                    "fixture_id": "cross_domain_artifact_parity.case_a",
                    "runs": parity_runs,
                }
            ],
            "runtime_domain_coupling_guard_pct": [
                {
                    "fixture_id": "runtime_domain_coupling_guard.case_a",
                    "runs": coupling_runs,
                }
            ],
        },
    }
    manifest_blob = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["manifest_hash"] = hashlib.sha256(manifest_blob.encode("utf-8")).hexdigest()
    return payload


def _vnext_plus13_manifest_payload(
    *,
    replay_runs: list[dict[str, str]],
    ledger_runs: list[dict[str, str]],
    lane_runs: list[dict[str, str]],
) -> dict[str, object]:
    payload = {
        "schema": "stop_gate.vnext_plus13_manifest@1",
        "replay_count": 3,
        "core_ir_replay_fixtures": [
            {
                "fixture_id": "adeu_core_ir_replay.case_a",
                "runs": replay_runs,
            }
        ],
        "ledger_recompute_fixtures": [
            {
                "fixture_id": "adeu_claim_ledger_recompute.case_a",
                "runs": ledger_runs,
            }
        ],
        "lane_projection_fixtures": [
            {
                "fixture_id": "adeu_lane_projection.case_a",
                "runs": lane_runs,
            }
        ],
    }
    manifest_blob = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["manifest_hash"] = hashlib.sha256(manifest_blob.encode("utf-8")).hexdigest()
    return payload


def _vnext_plus14_manifest_payload() -> dict[str, object]:
    return json.loads(_vnext_plus14_manifest_path().read_text(encoding="utf-8"))


def _vnext_plus15_manifest_payload() -> dict[str, object]:
    return json.loads(_vnext_plus15_manifest_path().read_text(encoding="utf-8"))


def _vnext_plus16_manifest_payload() -> dict[str, object]:
    return json.loads(_vnext_plus16_manifest_path().read_text(encoding="utf-8"))


def _vnext_plus17_manifest_payload() -> dict[str, object]:
    return json.loads(_vnext_plus17_manifest_path().read_text(encoding="utf-8"))


def _vnext_plus18_manifest_payload() -> dict[str, object]:
    return json.loads(_vnext_plus18_manifest_path().read_text(encoding="utf-8"))


def _vnext_plus19_manifest_payload() -> dict[str, object]:
    return json.loads(_vnext_plus19_manifest_path().read_text(encoding="utf-8"))


def _write_vnext_plus14_manifest_payload(
    *,
    tmp_path: Path,
    payload: dict[str, object],
    filename: str = "vnext_plus14_manifest.json",
) -> Path:
    normalized_payload = json.loads(json.dumps(payload))
    if not isinstance(normalized_payload, dict):
        raise AssertionError("vnext+14 manifest payload must be an object")
    fixture_manifest_root = _vnext_plus14_manifest_path().parent
    for fixture_key in (
        "provider_route_contract_parity_fixtures",
        "codex_candidate_contract_valid_fixtures",
        "provider_parity_replay_determinism_fixtures",
    ):
        raw_fixtures = normalized_payload.get(fixture_key)
        if not isinstance(raw_fixtures, list):
            continue
        for fixture in raw_fixtures:
            if not isinstance(fixture, dict):
                continue
            runs = fixture.get("runs")
            if not isinstance(runs, list):
                continue
            for run in runs:
                if not isinstance(run, dict):
                    continue
                artifact_ref = run.get("artifact_ref")
                if not isinstance(artifact_ref, str) or not artifact_ref:
                    continue
                artifact_path = Path(artifact_ref)
                if artifact_path.is_absolute():
                    continue
                run["artifact_ref"] = str((fixture_manifest_root / artifact_path).resolve())
    normalized_payload.pop("manifest_hash", None)
    manifest_blob = json.dumps(normalized_payload, sort_keys=True, separators=(",", ":"))
    normalized_payload["manifest_hash"] = hashlib.sha256(
        manifest_blob.encode("utf-8")
    ).hexdigest()
    manifest_path = tmp_path / filename
    _write_json(manifest_path, normalized_payload)
    return manifest_path


def _write_vnext_plus15_manifest_payload(
    *,
    tmp_path: Path,
    payload: dict[str, object],
    filename: str = "vnext_plus15_manifest.json",
) -> Path:
    normalized_payload = json.loads(json.dumps(payload))
    if not isinstance(normalized_payload, dict):
        raise AssertionError("vnext+15 manifest payload must be an object")
    fixture_manifest_root = _vnext_plus15_manifest_path().parent
    for fixture_key, run_keys in (
        ("lane_report_replay_fixtures", ("lane_report_path",)),
        ("projection_alignment_fixtures", ("projection_alignment_path",)),
        (
            "depth_report_replay_fixtures",
            ("lane_report_path", "projection_alignment_path"),
        ),
    ):
        raw_fixtures = normalized_payload.get(fixture_key)
        if not isinstance(raw_fixtures, list):
            continue
        for fixture in raw_fixtures:
            if not isinstance(fixture, dict):
                continue
            runs = fixture.get("runs")
            if not isinstance(runs, list):
                continue
            for run in runs:
                if not isinstance(run, dict):
                    continue
                for run_key in run_keys:
                    raw_ref = run.get(run_key)
                    if not isinstance(raw_ref, str) or not raw_ref:
                        continue
                    artifact_path = Path(raw_ref)
                    if artifact_path.is_absolute():
                        continue
                    run[run_key] = str((fixture_manifest_root / artifact_path).resolve())
    normalized_payload.pop("manifest_hash", None)
    manifest_blob = json.dumps(normalized_payload, sort_keys=True, separators=(",", ":"))
    normalized_payload["manifest_hash"] = hashlib.sha256(
        manifest_blob.encode("utf-8")
    ).hexdigest()
    manifest_path = tmp_path / filename
    _write_json(manifest_path, normalized_payload)
    return manifest_path


def _rewrite_manifest_relative_run_paths(
    *,
    normalized_payload: dict[str, object],
    fixture_manifest_root: Path,
    fixture_specs: tuple[tuple[str, tuple[str, ...]], ...],
) -> None:
    for fixture_key, run_keys in fixture_specs:
        raw_fixtures = normalized_payload.get(fixture_key)
        if not isinstance(raw_fixtures, list):
            continue
        for fixture in raw_fixtures:
            if not isinstance(fixture, dict):
                continue
            runs = fixture.get("runs")
            if not isinstance(runs, list):
                continue
            for run in runs:
                if not isinstance(run, dict):
                    continue
                for run_key in run_keys:
                    raw_ref = run.get(run_key)
                    if not isinstance(raw_ref, str) or not raw_ref:
                        continue
                    artifact_path = Path(raw_ref)
                    if artifact_path.is_absolute():
                        continue
                    run[run_key] = str((fixture_manifest_root / artifact_path).resolve())


def _write_manifest_payload_with_rewritten_runs(
    *,
    tmp_path: Path,
    payload: dict[str, object],
    filename: str,
    manifest_label: str,
    fixture_manifest_root: Path,
    fixture_specs: tuple[tuple[str, tuple[str, ...]], ...],
) -> Path:
    normalized_payload = json.loads(json.dumps(payload))
    if not isinstance(normalized_payload, dict):
        raise AssertionError(f"{manifest_label} manifest payload must be an object")
    _rewrite_manifest_relative_run_paths(
        normalized_payload=normalized_payload,
        fixture_manifest_root=fixture_manifest_root,
        fixture_specs=fixture_specs,
    )
    normalized_payload.pop("manifest_hash", None)
    normalized_payload["manifest_hash"] = sha256_canonical_json(normalized_payload)
    manifest_path = tmp_path / filename
    _write_json(manifest_path, normalized_payload)
    return manifest_path


def _write_vnext_plus16_manifest_payload(
    *,
    tmp_path: Path,
    payload: dict[str, object],
    filename: str = "vnext_plus16_manifest.json",
) -> Path:
    return _write_manifest_payload_with_rewritten_runs(
        tmp_path=tmp_path,
        payload=payload,
        filename=filename,
        manifest_label="vnext+16",
        fixture_manifest_root=_vnext_plus16_manifest_path().parent,
        fixture_specs=(
            ("dangling_reference_fixtures", ("dangling_reference_path",)),
            ("cycle_policy_fixtures", ("cycle_policy_path",)),
            ("deontic_conflict_fixtures", ("deontic_conflict_path",)),
        ),
    )


def _write_vnext_plus17_manifest_payload(
    *,
    tmp_path: Path,
    payload: dict[str, object],
    filename: str = "vnext_plus17_manifest.json",
) -> Path:
    return _write_manifest_payload_with_rewritten_runs(
        tmp_path=tmp_path,
        payload=payload,
        filename=filename,
        manifest_label="vnext+17",
        fixture_manifest_root=_vnext_plus17_manifest_path().parent,
        fixture_specs=(
            (
                "reference_integrity_extended_fixtures",
                ("reference_integrity_extended_path",),
            ),
            ("cycle_policy_extended_fixtures", ("cycle_policy_extended_path",)),
            ("deontic_conflict_extended_fixtures", ("deontic_conflict_extended_path",)),
        ),
    )


def _write_vnext_plus18_manifest_payload(
    *,
    tmp_path: Path,
    payload: dict[str, object],
    filename: str = "vnext_plus18_manifest.json",
) -> Path:
    return _write_manifest_payload_with_rewritten_runs(
        tmp_path=tmp_path,
        payload=payload,
        filename=filename,
        manifest_label="vnext+18",
        fixture_manifest_root=_vnext_plus18_manifest_path().parent,
        fixture_specs=(
            ("validation_parity_fixtures", ("baseline_path", "candidate_path")),
            ("transfer_report_parity_fixtures", ("baseline_path", "candidate_path")),
            ("ci_budget_fixtures", ("report_path",)),
        ),
    )


def _write_vnext_plus19_manifest_payload(
    *,
    tmp_path: Path,
    payload: dict[str, object],
    filename: str = "vnext_plus19_manifest.json",
) -> Path:
    return _write_manifest_payload_with_rewritten_runs(
        tmp_path=tmp_path,
        payload=payload,
        filename=filename,
        manifest_label="vnext+19",
        fixture_manifest_root=_vnext_plus19_manifest_path().parent,
        fixture_specs=(
            ("core_ir_read_surface_fixtures", ("core_ir_read_surface_path",)),
            ("lane_read_surface_fixtures", ("lane_read_surface_path",)),
            ("integrity_read_surface_fixtures", ("integrity_read_surface_path",)),
        ),
    )


def _normalize_runtime_observability(report: dict[str, object]) -> dict[str, object]:
    normalized = json.loads(json.dumps(report))
    runtime_observability = normalized.get("runtime_observability")
    if isinstance(runtime_observability, dict):
        runtime_observability["elapsed_ms"] = 0
    return normalized


def _base_stop_gate_kwargs(
    *,
    quality_current: Path,
    quality_baseline: Path,
) -> dict[str, object]:
    return {
        "incident_packet_paths": [
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        "event_stream_paths": [_event_fixture_path("sample_valid.ndjson")],
        "connector_snapshot_paths": [
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        "validator_evidence_packet_paths": [
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        "semantics_diagnostics_paths": [
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        "quality_current_path": quality_current,
        "quality_baseline_path": quality_baseline,
        "vnext_plus7_manifest_path": _vnext_plus7_manifest_path(),
        "vnext_plus8_manifest_path": _vnext_plus8_manifest_path(),
        "vnext_plus9_manifest_path": _vnext_plus9_manifest_path(),
        "vnext_plus10_manifest_path": _vnext_plus10_manifest_path(),
        "vnext_plus11_manifest_path": _vnext_plus11_manifest_path(),
    }


def _vnext_plus13_to_17_manifest_kwargs() -> dict[str, Path]:
    return {
        "vnext_plus13_manifest_path": _vnext_plus13_manifest_path(),
        "vnext_plus14_manifest_path": _vnext_plus14_manifest_path(),
        "vnext_plus15_manifest_path": _vnext_plus15_manifest_path(),
        "vnext_plus16_manifest_path": _vnext_plus16_manifest_path(),
        "vnext_plus17_manifest_path": _vnext_plus17_manifest_path(),
    }


def _vnext_plus13_to_19_manifest_kwargs() -> dict[str, Path]:
    return {
        **_vnext_plus13_to_17_manifest_kwargs(),
        "vnext_plus18_manifest_path": _vnext_plus18_manifest_path(),
        "vnext_plus19_manifest_path": _vnext_plus19_manifest_path(),
    }


def test_build_stop_gate_metrics_is_deterministic_and_passes(tmp_path: Path) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_current.write_text(
        json.dumps(
            {
                "dashboard_version": "quality.dashboard.v1",
                "metrics": {"question_stability_pct": 100.0},
            }
        ),
        encoding="utf-8",
    )
    quality_baseline.write_text(
        json.dumps(
            {
                "dashboard_version": "quality.dashboard.v1",
                "metrics": {"question_stability_pct": 100.0},
            }
        ),
        encoding="utf-8",
    )

    kwargs = {
        "incident_packet_paths": [
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        "event_stream_paths": [_event_fixture_path("sample_valid.ndjson")],
        "connector_snapshot_paths": [
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        "validator_evidence_packet_paths": [
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        "semantics_diagnostics_paths": [
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        "quality_current_path": quality_current,
        "quality_baseline_path": quality_baseline,
        "vnext_plus7_manifest_path": _vnext_plus7_manifest_path(),
        "vnext_plus8_manifest_path": _vnext_plus8_manifest_path(),
        "vnext_plus9_manifest_path": _vnext_plus9_manifest_path(),
        "vnext_plus10_manifest_path": _vnext_plus10_manifest_path(),
        "vnext_plus11_manifest_path": _vnext_plus11_manifest_path(),
        "vnext_plus13_manifest_path": _vnext_plus13_manifest_path(),
        "vnext_plus14_manifest_path": _vnext_plus14_manifest_path(),
        "vnext_plus15_manifest_path": _vnext_plus15_manifest_path(),
        "vnext_plus16_manifest_path": _vnext_plus16_manifest_path(),
        "vnext_plus17_manifest_path": _vnext_plus17_manifest_path(),
        "vnext_plus18_manifest_path": _vnext_plus18_manifest_path(),
        "vnext_plus19_manifest_path": _vnext_plus19_manifest_path(),
    }
    first = build_stop_gate_metrics(**kwargs)
    second = build_stop_gate_metrics(**kwargs)
    assert _normalize_runtime_observability(first) == _normalize_runtime_observability(second)
    assert first["schema"] == "stop_gate_metrics@1"
    assert first["valid"] is True
    assert first["all_passed"] is True
    assert first["metrics"]["policy_incident_reproducibility_pct"] == 100.0
    assert first["metrics"]["child_lifecycle_replay_determinism_pct"] == 100.0
    assert first["metrics"]["runtime_failure_code_stability_pct"] == 100.0
    assert first["metrics"]["connector_snapshot_replay_stability_pct"] == 100.0
    assert first["metrics"]["validator_packet_determinism_pct"] == 100.0
    assert first["metrics"]["witness_reconstruction_determinism_pct"] == 100.0
    assert first["metrics"]["semantics_diagnostics_determinism_pct"] == 100.0
    assert first["metrics"]["policy_lint_determinism_pct"] == 100.0
    assert first["metrics"]["proof_replay_determinism_pct"] == 100.0
    assert first["metrics"]["policy_proof_packet_hash_stability_pct"] == 100.0
    assert first["metrics"]["explain_diff_determinism_pct"] == 100.0
    assert first["metrics"]["explain_api_cli_parity_pct"] == 100.0
    assert first["metrics"]["explain_hash_stability_pct"] == 100.0
    assert first["metrics"]["scheduler_dispatch_replay_determinism_pct"] == 100.0
    assert first["metrics"]["orphan_lease_recovery_determinism_pct"] == 100.0
    assert first["metrics"]["concurrent_budget_cancel_stability_pct"] == 100.0
    assert first["metrics"]["concept_conflict_precision_pct"] == 100.0
    assert first["metrics"]["concept_conflict_recall_pct"] == 100.0
    assert first["metrics"]["coherence_permutation_stability_pct"] == 100.0
    assert first["metrics"]["domain_conformance_replay_determinism_pct"] == 100.0
    assert first["metrics"]["cross_domain_artifact_parity_pct"] == 100.0
    assert first["metrics"]["runtime_domain_coupling_guard_pct"] == 100.0
    assert first["metrics"]["adeu_core_ir_replay_determinism_pct"] == 100.0
    assert first["metrics"]["adeu_claim_ledger_recompute_match_pct"] == 100.0
    assert first["metrics"]["adeu_lane_projection_determinism_pct"] == 100.0
    assert first["metrics"]["provider_route_contract_parity_pct"] == 100.0
    assert first["metrics"]["codex_candidate_contract_valid_pct"] == 100.0
    assert first["metrics"]["provider_parity_replay_determinism_pct"] == 100.0
    assert first["metrics"]["adeu_lane_report_replay_determinism_pct"] == 100.0
    assert first["metrics"]["adeu_projection_alignment_determinism_pct"] == 100.0
    assert first["metrics"]["adeu_depth_report_replay_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_dangling_reference_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_cycle_policy_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_deontic_conflict_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_reference_integrity_extended_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_cycle_policy_extended_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_deontic_conflict_extended_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_validation_consolidation_parity_pct"] == 100.0
    assert first["metrics"]["artifact_transfer_report_consolidation_parity_pct"] == 100.0
    assert first["metrics"]["artifact_stop_gate_ci_budget_within_ceiling_pct"] == 100.0
    assert first["metrics"]["artifact_core_ir_read_surface_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_lane_read_surface_determinism_pct"] == 100.0
    assert first["metrics"]["artifact_integrity_read_surface_determinism_pct"] == 100.0
    assert first["metrics"]["semantic_depth_improvement_lock_passed"] is True
    assert first["metrics"]["quality_delta_non_negative"] is True
    assert isinstance(first["vnext_plus8_manifest_hash"], str)
    assert len(first["vnext_plus8_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus9_manifest_hash"], str)
    assert len(first["vnext_plus9_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus10_manifest_hash"], str)
    assert len(first["vnext_plus10_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus11_manifest_hash"], str)
    assert len(first["vnext_plus11_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus13_manifest_hash"], str)
    assert len(first["vnext_plus13_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus14_manifest_hash"], str)
    assert len(first["vnext_plus14_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus15_manifest_hash"], str)
    assert len(first["vnext_plus15_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus16_manifest_hash"], str)
    assert len(first["vnext_plus16_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus17_manifest_hash"], str)
    assert len(first["vnext_plus17_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus18_manifest_hash"], str)
    assert len(first["vnext_plus18_manifest_hash"]) == 64
    assert isinstance(first["vnext_plus19_manifest_hash"], str)
    assert len(first["vnext_plus19_manifest_hash"]) == 64
    runtime_observability = first["runtime_observability"]
    assert runtime_observability["total_fixtures"] == 3
    assert runtime_observability["total_replays"] == 9
    assert isinstance(runtime_observability["elapsed_ms"], int)
    assert runtime_observability["elapsed_ms"] >= 0
    assert first["gates"]["artifact_stop_gate_ci_budget_within_ceiling"] is True
    assert first["gates"]["artifact_core_ir_read_surface_determinism"] is True
    assert first["gates"]["artifact_lane_read_surface_determinism"] is True
    assert first["gates"]["artifact_integrity_read_surface_determinism"] is True


def test_build_stop_gate_metrics_fails_when_runtime_budget_exceeds_ceiling(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    ceiling_ms = int(stop_gate_tools_module.VNEXT_PLUS18_CI_BUDGET_CEILING_MS)
    ticks = iter([0.0, (ceiling_ms + 1) / 1000.0])

    def _fake_monotonic() -> float:
        return next(ticks, (ceiling_ms + 1) / 1000.0)

    monkeypatch.setattr(stop_gate_tools_module.time, "monotonic", _fake_monotonic)

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        **_vnext_plus13_to_19_manifest_kwargs(),
    )

    assert report["valid"] is False
    assert report["all_passed"] is False
    assert report["metrics"]["artifact_stop_gate_ci_budget_within_ceiling_pct"] == 0.0
    assert report["gates"]["artifact_stop_gate_ci_budget_within_ceiling"] is False
    runtime_observability = report["runtime_observability"]
    assert runtime_observability["elapsed_ms"] > ceiling_ms
    assert any(
        issue.get("code") == "URM_ADEU_TOOLING_RUNTIME_BUDGET_EXCEEDED"
        and issue.get("message") == "stop-gate runtime budget exceeded frozen ceiling"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_replay_hash_drift_for_semantics_metrics(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    base_packet = json.loads(
        _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json").read_text(
            encoding="utf-8"
        )
    )
    drift_packet = build_validator_evidence_packet(
        validator_run_id=str(base_packet["validator_run_id"]),
        backend=str(base_packet["backend"]),
        backend_version=(
            None
            if base_packet.get("backend_version") is None
            else str(base_packet["backend_version"])
        ),
        timeout_ms=int(base_packet["timeout_ms"]),
        options=dict(base_packet.get("options", {})),
        request_hash="c" * 64,
        formula_hash=str(base_packet["formula_hash"]),
        status=str(base_packet["status"]),
        evidence=dict(base_packet["evidence"]),
        atom_map={},
        assurance=str(base_packet.get("assurance", "solver_backed")),
    )
    base_diagnostics = build_semantics_diagnostics(
        artifact_ref="artifact:stop-gate-case-a",
        validator_evidence_packets=[base_packet],
    )
    drift_diagnostics = build_semantics_diagnostics(
        artifact_ref="artifact:stop-gate-case-a",
        validator_evidence_packets=[drift_packet],
    )

    packet_paths = [
        tmp_path / "validator_packet_1.json",
        tmp_path / "validator_packet_2.json",
        tmp_path / "validator_packet_3.json",
    ]
    diagnostics_paths = [
        tmp_path / "semantics_diagnostics_1.json",
        tmp_path / "semantics_diagnostics_2.json",
        tmp_path / "semantics_diagnostics_3.json",
    ]
    _write_json(packet_paths[0], base_packet)
    _write_json(packet_paths[1], drift_packet)
    _write_json(packet_paths[2], base_packet)
    _write_json(diagnostics_paths[0], base_diagnostics)
    _write_json(diagnostics_paths[1], drift_diagnostics)
    _write_json(diagnostics_paths[2], base_diagnostics)

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=packet_paths,
        semantics_diagnostics_paths=diagnostics_paths,
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
    )

    assert report["valid"] is True
    assert report["metrics"]["validator_packet_determinism_pct"] == 0.0
    assert report["metrics"]["witness_reconstruction_determinism_pct"] == 0.0
    assert report["metrics"]["semantics_diagnostics_determinism_pct"] == 0.0
    assert report["gates"]["validator_packet_determinism"] is False
    assert report["gates"]["witness_reconstruction_determinism"] is False
    assert report["gates"]["semantics_diagnostics_determinism"] is False


def test_build_stop_gate_metrics_detects_vnext_plus7_proof_replay_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    policy_lineage_paths = _write_policy_lineage_replay_paths(tmp_path)
    proof_paths = _write_proof_replay_paths_with_drift(tmp_path)

    lint_event_paths = [
        _example_stop_gate_path("policy_lint_events_case_a_1.ndjson"),
        _example_stop_gate_path("policy_lint_events_case_a_2.ndjson"),
        _example_stop_gate_path("policy_lint_events_case_a_3.ndjson"),
    ]
    manifest_path = tmp_path / "vnext_plus7_manifest.json"
    _write_json(
        manifest_path,
        _vnext_plus7_manifest_payload(
            policy_lint_event_paths=lint_event_paths,
            proof_paths=proof_paths,
            policy_lineage_paths=policy_lineage_paths,
        ),
    )

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=manifest_path,
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
    )

    assert report["valid"] is True
    assert report["metrics"]["policy_lint_determinism_pct"] == 100.0
    assert report["metrics"]["proof_replay_determinism_pct"] == 0.0
    assert report["metrics"]["policy_proof_packet_hash_stability_pct"] == 0.0
    assert report["gates"]["policy_lint_determinism"] is True
    assert report["gates"]["proof_replay_determinism"] is False
    assert report["gates"]["policy_proof_packet_hash_stability"] is False


def test_build_stop_gate_metrics_detects_vnext_plus8_explain_api_cli_parity_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    explain_diff_paths, api_paths, cli_paths = _write_explain_replay_paths(tmp_path)
    _write_json(cli_paths[1], _explain_concepts_packet_fixture())

    manifest_path = tmp_path / "vnext_plus8_manifest.json"
    _write_json(
        manifest_path,
        _vnext_plus8_manifest_payload(
            explain_diff_paths=explain_diff_paths,
            api_paths=api_paths,
            cli_paths=cli_paths,
        ),
    )

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=manifest_path,
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
    )

    assert report["valid"] is True
    assert report["metrics"]["explain_diff_determinism_pct"] == 100.0
    assert report["metrics"]["explain_api_cli_parity_pct"] == 0.0
    assert report["metrics"]["explain_hash_stability_pct"] == 100.0
    assert report["gates"]["explain_diff_determinism"] is True
    assert report["gates"]["explain_api_cli_parity"] is False
    assert report["gates"]["explain_hash_stability"] is True


def test_build_stop_gate_metrics_rejects_vnext_plus8_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    explain_diff_paths, api_paths, cli_paths = _write_explain_replay_paths(tmp_path)
    manifest_payload = _vnext_plus8_manifest_payload(
        explain_diff_paths=explain_diff_paths,
        api_paths=api_paths,
        cli_paths=cli_paths,
    )
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus8_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=manifest_path,
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
    )

    assert report["valid"] is False
    assert report["metrics"]["explain_diff_determinism_pct"] == 0.0
    assert report["metrics"]["explain_api_cli_parity_pct"] == 0.0
    assert report["metrics"]["explain_hash_stability_pct"] == 0.0
    assert report["vnext_plus8_manifest_hash"] == ""
    assert any(
        issue.get("message") == "vnext+8 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus9_budget_cancel_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    scheduler_dispatch_paths = [
        _example_stop_gate_path("scheduler_dispatch_token_case_a_1.json"),
        _example_stop_gate_path("scheduler_dispatch_token_case_a_2.json"),
        _example_stop_gate_path("scheduler_dispatch_token_case_a_3.json"),
    ]
    orphan_recovery_paths = [
        _example_stop_gate_path("orphan_lease_recovery_events_case_a_1.ndjson"),
        _example_stop_gate_path("orphan_lease_recovery_events_case_a_2.ndjson"),
        _example_stop_gate_path("orphan_lease_recovery_events_case_a_3.ndjson"),
    ]
    budget_cancel_paths = _write_vnext_plus9_budget_cancel_paths_with_drift(tmp_path)
    manifest_path = tmp_path / "vnext_plus9_manifest.json"
    _write_json(
        manifest_path,
        _vnext_plus9_manifest_payload(
            scheduler_dispatch_paths=scheduler_dispatch_paths,
            orphan_recovery_paths=orphan_recovery_paths,
            budget_cancel_paths=budget_cancel_paths,
        ),
    )

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=manifest_path,
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
    )

    assert report["valid"] is True
    assert report["metrics"]["scheduler_dispatch_replay_determinism_pct"] == 100.0
    assert report["metrics"]["orphan_lease_recovery_determinism_pct"] == 100.0
    assert report["metrics"]["concurrent_budget_cancel_stability_pct"] == 0.0
    assert report["gates"]["scheduler_dispatch_replay_determinism"] is True
    assert report["gates"]["orphan_lease_recovery_determinism"] is True
    assert report["gates"]["concurrent_budget_cancel_stability"] is False


def test_build_stop_gate_metrics_rejects_vnext_plus9_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    scheduler_dispatch_paths = [
        _example_stop_gate_path("scheduler_dispatch_token_case_a_1.json"),
        _example_stop_gate_path("scheduler_dispatch_token_case_a_2.json"),
        _example_stop_gate_path("scheduler_dispatch_token_case_a_3.json"),
    ]
    orphan_recovery_paths = [
        _example_stop_gate_path("orphan_lease_recovery_events_case_a_1.ndjson"),
        _example_stop_gate_path("orphan_lease_recovery_events_case_a_2.ndjson"),
        _example_stop_gate_path("orphan_lease_recovery_events_case_a_3.ndjson"),
    ]
    budget_cancel_paths = [
        _example_stop_gate_path("concurrent_budget_cancel_events_case_a_1.ndjson"),
        _example_stop_gate_path("concurrent_budget_cancel_events_case_a_2.ndjson"),
        _example_stop_gate_path("concurrent_budget_cancel_events_case_a_3.ndjson"),
    ]
    manifest_payload = _vnext_plus9_manifest_payload(
        scheduler_dispatch_paths=scheduler_dispatch_paths,
        orphan_recovery_paths=orphan_recovery_paths,
        budget_cancel_paths=budget_cancel_paths,
    )
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus9_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=manifest_path,
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
    )

    assert report["valid"] is False
    assert report["metrics"]["scheduler_dispatch_replay_determinism_pct"] == 0.0
    assert report["metrics"]["orphan_lease_recovery_determinism_pct"] == 0.0
    assert report["metrics"]["concurrent_budget_cancel_stability_pct"] == 0.0
    assert report["vnext_plus9_manifest_hash"] == ""
    assert any(
        issue.get("message") == "vnext+9 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus10_recall_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    report_paths, expected_paths = _write_semantic_depth_replay_paths(tmp_path)
    drift_expected = _semantic_depth_expected_conflicts_fixture()
    drift_expected["expected_conflict_ids"] = sorted(
        [*drift_expected["expected_conflict_ids"], "conflict:synthetic-drift"]
    )
    _write_json(expected_paths[1], drift_expected)

    precision_runs = [
        {
            "semantic_depth_report_path": str(report_paths[0]),
            "expected_conflict_ids_path": str(expected_paths[0]),
        },
        {
            "semantic_depth_report_path": str(report_paths[1]),
            "expected_conflict_ids_path": str(expected_paths[0]),
        },
        {
            "semantic_depth_report_path": str(report_paths[2]),
            "expected_conflict_ids_path": str(expected_paths[0]),
        },
    ]
    recall_runs = [
        {
            "semantic_depth_report_path": str(report_paths[0]),
            "expected_conflict_ids_path": str(expected_paths[0]),
        },
        {
            "semantic_depth_report_path": str(report_paths[1]),
            "expected_conflict_ids_path": str(expected_paths[1]),
        },
        {
            "semantic_depth_report_path": str(report_paths[2]),
            "expected_conflict_ids_path": str(expected_paths[2]),
        },
    ]
    coherence_runs = [
        {"semantic_depth_report_path": str(report_paths[0])},
        {"semantic_depth_report_path": str(report_paths[1])},
        {"semantic_depth_report_path": str(report_paths[2])},
    ]

    manifest_path = tmp_path / "vnext_plus10_manifest.json"
    _write_json(
        manifest_path,
        _vnext_plus10_manifest_payload(
            precision_runs=precision_runs,
            recall_runs=recall_runs,
            coherence_runs=coherence_runs,
        ),
    )

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=manifest_path,
    )

    assert report["valid"] is True
    assert report["metrics"]["concept_conflict_precision_pct"] == 100.0
    assert report["metrics"]["concept_conflict_recall_pct"] == 0.0
    assert report["metrics"]["coherence_permutation_stability_pct"] == 100.0
    assert report["metrics"]["semantic_depth_improvement_lock_passed"] is False
    assert report["gates"]["concept_conflict_precision"] is True
    assert report["gates"]["concept_conflict_recall"] is False
    assert report["gates"]["coherence_permutation_stability"] is True
    assert report["gates"]["semantic_depth_improvement_lock"] is False


def test_build_stop_gate_metrics_rejects_vnext_plus10_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    report_paths, expected_paths = _write_semantic_depth_replay_paths(tmp_path)
    precision_runs = [
        {
            "semantic_depth_report_path": str(report_paths[0]),
            "expected_conflict_ids_path": str(expected_paths[0]),
        },
        {
            "semantic_depth_report_path": str(report_paths[1]),
            "expected_conflict_ids_path": str(expected_paths[1]),
        },
        {
            "semantic_depth_report_path": str(report_paths[2]),
            "expected_conflict_ids_path": str(expected_paths[2]),
        },
    ]
    recall_runs = list(precision_runs)
    coherence_runs = [
        {"semantic_depth_report_path": str(report_paths[0])},
        {"semantic_depth_report_path": str(report_paths[1])},
        {"semantic_depth_report_path": str(report_paths[2])},
    ]
    manifest_payload = _vnext_plus10_manifest_payload(
        precision_runs=precision_runs,
        recall_runs=recall_runs,
        coherence_runs=coherence_runs,
    )
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus10_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["concept_conflict_precision_pct"] == 0.0
    assert report["metrics"]["concept_conflict_recall_pct"] == 0.0
    assert report["metrics"]["coherence_permutation_stability_pct"] == 0.0
    assert report["vnext_plus10_manifest_hash"] == ""
    assert any(
        issue.get("message") == "vnext+10 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus11_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    replay_runs = [
        {
            "domain_conformance_path": str(
                _example_stop_gate_path("domain_conformance_case_a_1.json")
            )
        },
        {
            "domain_conformance_path": str(
                _example_stop_gate_path("domain_conformance_case_a_2.json")
            )
        },
        {
            "domain_conformance_path": str(
                _example_stop_gate_path("domain_conformance_case_a_3.json")
            )
        },
    ]
    manifest_payload = _vnext_plus11_manifest_payload(
        replay_runs=replay_runs,
        parity_runs=list(replay_runs),
        coupling_runs=list(replay_runs),
    )
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus11_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
        vnext_plus11_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["domain_conformance_replay_determinism_pct"] == 0.0
    assert report["metrics"]["cross_domain_artifact_parity_pct"] == 0.0
    assert report["metrics"]["runtime_domain_coupling_guard_pct"] == 0.0
    assert report["vnext_plus11_manifest_hash"] == ""
    assert any(
        issue.get("code") == "URM_CONFORMANCE_MANIFEST_HASH_MISMATCH"
        and issue.get("message") == "vnext+11 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus11_runtime_coupling_guard_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    base_1 = json.loads(
        _example_stop_gate_path("domain_conformance_case_a_1.json").read_text(encoding="utf-8")
    )
    drift_2 = json.loads(
        _example_stop_gate_path("domain_conformance_case_a_2.json").read_text(encoding="utf-8")
    )
    base_3 = json.loads(
        _example_stop_gate_path("domain_conformance_case_a_3.json").read_text(encoding="utf-8")
    )
    assert isinstance(drift_2.get("import_audit"), dict)
    drift_2["import_audit"]["valid"] = False
    drift_2["domain_conformance_hash"] = _domain_conformance_hash(drift_2)

    drift_paths = [
        tmp_path / "domain_conformance_coupling_1.json",
        tmp_path / "domain_conformance_coupling_2.json",
        tmp_path / "domain_conformance_coupling_3.json",
    ]
    _write_json(drift_paths[0], base_1)
    _write_json(drift_paths[1], drift_2)
    _write_json(drift_paths[2], base_3)

    stable_runs = [
        {
            "domain_conformance_path": str(
                _example_stop_gate_path("domain_conformance_case_a_1.json")
            )
        },
        {
            "domain_conformance_path": str(
                _example_stop_gate_path("domain_conformance_case_a_2.json")
            )
        },
        {
            "domain_conformance_path": str(
                _example_stop_gate_path("domain_conformance_case_a_3.json")
            )
        },
    ]
    coupling_runs = [
        {"domain_conformance_path": str(drift_paths[0])},
        {"domain_conformance_path": str(drift_paths[1])},
        {"domain_conformance_path": str(drift_paths[2])},
    ]
    manifest_path = tmp_path / "vnext_plus11_manifest.json"
    _write_json(
        manifest_path,
        _vnext_plus11_manifest_payload(
            replay_runs=stable_runs,
            parity_runs=stable_runs,
            coupling_runs=coupling_runs,
        ),
    )

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
        vnext_plus11_manifest_path=manifest_path,
    )

    assert report["valid"] is True
    assert report["metrics"]["domain_conformance_replay_determinism_pct"] == 100.0
    assert report["metrics"]["cross_domain_artifact_parity_pct"] == 100.0
    assert report["metrics"]["runtime_domain_coupling_guard_pct"] == 0.0
    assert report["gates"]["domain_conformance_replay_determinism"] is True
    assert report["gates"]["cross_domain_artifact_parity"] is True
    assert report["gates"]["runtime_domain_coupling_guard"] is False


def test_build_stop_gate_metrics_rejects_vnext_plus13_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    replay_runs = [
        {
            "core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_1.json")),
        },
        {
            "core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_2.json")),
        },
        {
            "core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_3.json")),
        },
    ]
    manifest_payload = _vnext_plus13_manifest_payload(
        replay_runs=replay_runs,
        ledger_runs=list(replay_runs),
        lane_runs=list(replay_runs),
    )
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus13_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["adeu_core_ir_replay_determinism_pct"] == 0.0
    assert report["metrics"]["adeu_claim_ledger_recompute_match_pct"] == 0.0
    assert report["metrics"]["adeu_lane_projection_determinism_pct"] == 0.0
    assert report["vnext_plus13_manifest_hash"] == ""
    assert any(
        issue.get("code") == "URM_ADEU_CORE_MANIFEST_HASH_MISMATCH"
        and issue.get("message") == "vnext+13 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus13_ledger_recompute_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    drift_payload = json.loads(
        _example_stop_gate_path("adeu_core_ir_case_a_2.json").read_text(encoding="utf-8")
    )
    for node in drift_payload.get("nodes", []):
        if node.get("id") == "c1":
            node["R_milli"] = 999
            node["R"] = "0.999"
            break
    drift_path = tmp_path / "adeu_core_ir_drift_2.json"
    _write_json(drift_path, drift_payload)

    replay_runs = [
        {
            "core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_1.json")),
        },
        {
            "core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_2.json")),
        },
        {
            "core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_3.json")),
        },
    ]
    ledger_runs = [
        {
            "core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_1.json")),
        },
        {"core_ir_path": str(drift_path)},
        {
            "core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_3.json")),
        },
    ]
    manifest_path = tmp_path / "vnext_plus13_manifest.json"
    _write_json(
        manifest_path,
        _vnext_plus13_manifest_payload(
            replay_runs=replay_runs,
            ledger_runs=ledger_runs,
            lane_runs=replay_runs,
        ),
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["adeu_core_ir_replay_determinism_pct"] == 100.0
    assert report["metrics"]["adeu_claim_ledger_recompute_match_pct"] == 0.0
    assert report["metrics"]["adeu_lane_projection_determinism_pct"] == 100.0
    assert report["gates"]["adeu_core_ir_replay_determinism"] is True
    assert report["gates"]["adeu_claim_ledger_recompute_match"] is False
    assert report["gates"]["adeu_lane_projection_determinism"] is True
    assert any(
        issue.get("code") == "URM_ADEU_CORE_LEDGER_RECOMPUTE_MISMATCH"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus13_invalid_core_ir_node_shape(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    invalid_payload = json.loads(
        _example_stop_gate_path("adeu_core_ir_case_a_2.json").read_text(encoding="utf-8")
    )
    for node in invalid_payload.get("nodes", []):
        if node.get("id") == "c1":
            node.pop("text", None)
            break
    invalid_path = tmp_path / "adeu_core_ir_invalid_2.json"
    _write_json(invalid_path, invalid_payload)

    replay_runs = [
        {"core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_1.json"))},
        {"core_ir_path": str(invalid_path)},
        {"core_ir_path": str(_example_stop_gate_path("adeu_core_ir_case_a_3.json"))},
    ]
    manifest_path = tmp_path / "vnext_plus13_manifest_invalid_core_ir.json"
    _write_json(
        manifest_path,
        _vnext_plus13_manifest_payload(
            replay_runs=replay_runs,
            ledger_runs=replay_runs,
            lane_runs=replay_runs,
        ),
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["adeu_core_ir_replay_determinism_pct"] == 0.0
    assert report["metrics"]["adeu_claim_ledger_recompute_match_pct"] == 0.0
    assert report["metrics"]["adeu_lane_projection_determinism_pct"] == 0.0
    assert any(
        issue.get("message") == "core IR E-node must include non-empty text"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus14_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    manifest_payload = _vnext_plus14_manifest_payload()
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus14_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["provider_route_contract_parity_pct"] == 0.0
    assert report["metrics"]["codex_candidate_contract_valid_pct"] == 0.0
    assert report["metrics"]["provider_parity_replay_determinism_pct"] == 0.0
    assert report["vnext_plus14_manifest_hash"] == ""
    assert any(
        issue.get("code") == "URM_PROVIDER_PARITY_MANIFEST_HASH_MISMATCH"
        and issue.get("message") == "vnext+14 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus14_codex_fixture_non_codex_provider(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    manifest_payload = _vnext_plus14_manifest_payload()
    codex_fixtures = manifest_payload.get("codex_candidate_contract_valid_fixtures")
    assert isinstance(codex_fixtures, list) and codex_fixtures
    first_fixture = codex_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_fixture["provider"] = "openai"
    manifest_path = _write_vnext_plus14_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
        filename="vnext_plus14_manifest_codex_provider_invalid.json",
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["provider_route_contract_parity_pct"] == 0.0
    assert report["metrics"]["codex_candidate_contract_valid_pct"] == 0.0
    assert report["metrics"]["provider_parity_replay_determinism_pct"] == 0.0
    assert report["vnext_plus14_manifest_hash"] == ""
    assert any(
        issue.get("message") == "codex candidate fixtures must use provider='codex'"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus14_replay_fixture_missing_provider(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    manifest_payload = _vnext_plus14_manifest_payload()
    replay_fixtures = manifest_payload.get("provider_parity_replay_determinism_fixtures")
    assert isinstance(replay_fixtures, list) and replay_fixtures
    first_fixture = replay_fixtures[0]
    assert isinstance(first_fixture, dict)
    fixture_id = first_fixture.get("fixture_id")
    first_fixture.pop("provider", None)
    manifest_path = _write_vnext_plus14_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
        filename="vnext_plus14_manifest_replay_provider_missing.json",
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["vnext_plus14_manifest_hash"] == ""
    assert any(
        issue.get("message") == "manifest fixture provider must be a frozen provider kind"
        and (issue.get("context") or {}).get("metric")
        == "provider_parity_replay_determinism_pct"
        and (issue.get("context") or {}).get("fixture_id") == fixture_id
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus14_replay_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    drift_payload = json.loads(
        _example_stop_gate_path("provider_parity_case_a_run_2.json").read_text(encoding="utf-8")
    )
    drift_payload["status"] = "FAIL"
    drift_path = tmp_path / "provider_parity_case_a_run_2_drift.json"
    _write_json(drift_path, drift_payload)

    manifest_payload = _vnext_plus14_manifest_payload()
    replay_fixtures = manifest_payload.get("provider_parity_replay_determinism_fixtures")
    assert isinstance(replay_fixtures, list) and replay_fixtures
    first_fixture = replay_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_runs = first_fixture.get("runs")
    assert isinstance(first_runs, list) and len(first_runs) == 3
    assert isinstance(first_runs[1], dict)
    first_runs[1]["artifact_ref"] = str(drift_path)
    manifest_path = _write_vnext_plus14_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=manifest_path,
    )

    assert report["valid"] is True
    assert report["metrics"]["provider_route_contract_parity_pct"] == 100.0
    assert report["metrics"]["codex_candidate_contract_valid_pct"] == 100.0
    assert report["metrics"]["provider_parity_replay_determinism_pct"] < 100.0
    assert report["gates"]["provider_route_contract_parity"] is True
    assert report["gates"]["codex_candidate_contract_valid"] is True
    assert report["gates"]["provider_parity_replay_determinism"] is False


def test_build_stop_gate_metrics_rejects_vnext_plus15_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    manifest_payload = _vnext_plus15_manifest_payload()
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus15_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["adeu_lane_report_replay_determinism_pct"] == 0.0
    assert report["metrics"]["adeu_projection_alignment_determinism_pct"] == 0.0
    assert report["metrics"]["adeu_depth_report_replay_determinism_pct"] == 0.0
    assert report["vnext_plus15_manifest_hash"] == ""
    assert any(
        issue.get("code") == "URM_ADEU_DEPTH_MANIFEST_HASH_MISMATCH"
        and issue.get("message") == "vnext+15 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus15_alignment_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    drift_payload = json.loads(
        _example_stop_gate_path("adeu_projection_alignment_case_a_2.json").read_text(
            encoding="utf-8"
        )
    )
    drift_issues = drift_payload.get("issues")
    assert isinstance(drift_issues, list) and drift_issues
    first_issue = drift_issues[0]
    assert isinstance(first_issue, dict)
    first_issue["subject_id"] = str(first_issue["subject_id"]) + ".drift"
    drift_path = tmp_path / "adeu_projection_alignment_case_a_2_drift.json"
    _write_json(drift_path, drift_payload)

    manifest_payload = _vnext_plus15_manifest_payload()
    alignment_fixtures = manifest_payload.get("projection_alignment_fixtures")
    assert isinstance(alignment_fixtures, list) and alignment_fixtures
    first_fixture = alignment_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_runs = first_fixture.get("runs")
    assert isinstance(first_runs, list) and len(first_runs) == 3
    assert isinstance(first_runs[1], dict)
    first_runs[1]["projection_alignment_path"] = str(drift_path)
    manifest_path = _write_vnext_plus15_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["adeu_lane_report_replay_determinism_pct"] == 100.0
    assert report["metrics"]["adeu_projection_alignment_determinism_pct"] < 100.0
    assert report["metrics"]["adeu_depth_report_replay_determinism_pct"] == 100.0
    assert report["gates"]["adeu_lane_report_replay_determinism"] is True
    assert report["gates"]["adeu_projection_alignment_determinism"] is False
    assert report["gates"]["adeu_depth_report_replay_determinism"] is True
    assert any(
        issue.get("code") == "URM_ADEU_DEPTH_ALIGNMENT_DIAGNOSTIC_DRIFT"
        and issue.get("message") == "vnext+15 projection alignment diagnostic drift"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus15_empty_lane_report_fixture(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    empty_lane_report_payload = {
        "schema": "adeu_lane_report@0.1",
        "source_text_hash": "hash-empty",
        "lane_nodes": {"O": [], "E": [], "D": [], "U": []},
        "lane_edge_counts": {"O": 0, "E": 0, "D": 0, "U": 0},
    }
    empty_lane_report_path = tmp_path / "adeu_lane_report_empty.json"
    _write_json(empty_lane_report_path, empty_lane_report_payload)

    manifest_payload = _vnext_plus15_manifest_payload()
    lane_fixtures = manifest_payload.get("lane_report_replay_fixtures")
    assert isinstance(lane_fixtures, list) and lane_fixtures
    first_fixture = lane_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_runs = first_fixture.get("runs")
    assert isinstance(first_runs, list) and len(first_runs) == 3
    for run in first_runs:
        assert isinstance(run, dict)
        run["lane_report_path"] = str(empty_lane_report_path)
    manifest_path = _write_vnext_plus15_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["adeu_lane_report_replay_determinism_pct"] == 0.0
    assert report["metrics"]["adeu_projection_alignment_determinism_pct"] == 100.0
    assert report["metrics"]["adeu_depth_report_replay_determinism_pct"] == 100.0
    assert any(
        issue.get("code") == "URM_ADEU_DEPTH_FIXTURE_INVALID"
        and issue.get("message") == "lane report fixture has empty lane-node evidence"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus16_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    manifest_payload = _vnext_plus16_manifest_payload()
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus16_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=_vnext_plus15_manifest_path(),
        vnext_plus16_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_dangling_reference_determinism_pct"] == 0.0
    assert report["metrics"]["artifact_cycle_policy_determinism_pct"] == 0.0
    assert report["metrics"]["artifact_deontic_conflict_determinism_pct"] == 0.0
    assert report["vnext_plus16_manifest_hash"] == ""
    assert any(
        issue.get("code") == "URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH"
        and issue.get("message") == "vnext+16 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus16_cycle_policy_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    drift_payload = json.loads(
        _example_stop_gate_path("adeu_integrity_cycle_policy_case_a_2.json").read_text(
            encoding="utf-8"
        )
    )
    drift_payload["source_text_hash"] = "hash-d2-case-a-drift"
    drift_path = tmp_path / "adeu_integrity_cycle_policy_case_a_2_drift.json"
    _write_json(drift_path, drift_payload)

    manifest_payload = _vnext_plus16_manifest_payload()
    cycle_fixtures = manifest_payload.get("cycle_policy_fixtures")
    assert isinstance(cycle_fixtures, list) and cycle_fixtures
    first_fixture = cycle_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_runs = first_fixture.get("runs")
    assert isinstance(first_runs, list) and len(first_runs) == 3
    assert isinstance(first_runs[1], dict)
    first_runs[1]["cycle_policy_path"] = str(drift_path)
    manifest_path = _write_vnext_plus16_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=_vnext_plus15_manifest_path(),
        vnext_plus16_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_dangling_reference_determinism_pct"] == 100.0
    assert report["metrics"]["artifact_cycle_policy_determinism_pct"] < 100.0
    assert report["metrics"]["artifact_deontic_conflict_determinism_pct"] == 100.0
    assert report["gates"]["artifact_dangling_reference_determinism"] is True
    assert report["gates"]["artifact_cycle_policy_determinism"] is False
    assert report["gates"]["artifact_deontic_conflict_determinism"] is True
    assert any(
        issue.get("code") == "URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT"
        and issue.get("message") == "vnext+16 cycle-policy diagnostic drift"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus16_all_zero_diagnostics(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    zero_dangling_payload = {
        "schema": "adeu_integrity_dangling_reference@0.1",
        "source_text_hash": "hash-d1-case-a",
        "summary": {
            "total_issues": 0,
            "missing_node_reference": 0,
            "missing_edge_endpoint": 0,
        },
        "issues": [],
    }
    zero_dangling_path = tmp_path / "adeu_integrity_dangling_reference_zero.json"
    _write_json(zero_dangling_path, zero_dangling_payload)

    manifest_payload = _vnext_plus16_manifest_payload()
    dangling_fixtures = manifest_payload.get("dangling_reference_fixtures")
    assert isinstance(dangling_fixtures, list) and dangling_fixtures
    first_fixture = dangling_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_runs = first_fixture.get("runs")
    assert isinstance(first_runs, list) and len(first_runs) == 3
    for run in first_runs:
        assert isinstance(run, dict)
        run["dangling_reference_path"] = str(zero_dangling_path)
    manifest_path = _write_vnext_plus16_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=_vnext_plus15_manifest_path(),
        vnext_plus16_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_dangling_reference_determinism_pct"] == 0.0
    assert report["metrics"]["artifact_cycle_policy_determinism_pct"] == 100.0
    assert report["metrics"]["artifact_deontic_conflict_determinism_pct"] == 100.0
    assert any(
        issue.get("code") == "URM_ADEU_INTEGRITY_FIXTURE_INVALID"
        and issue.get("message")
        == "vnext+16 dangling-reference fixtures must include non-zero diagnostics"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus17_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    manifest_payload = _vnext_plus17_manifest_payload()
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus17_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=_vnext_plus15_manifest_path(),
        vnext_plus16_manifest_path=_vnext_plus16_manifest_path(),
        vnext_plus17_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_reference_integrity_extended_determinism_pct"] == 0.0
    assert report["metrics"]["artifact_cycle_policy_extended_determinism_pct"] == 0.0
    assert report["metrics"]["artifact_deontic_conflict_extended_determinism_pct"] == 0.0
    assert report["vnext_plus17_manifest_hash"] == ""
    assert any(
        issue.get("code") == "URM_ADEU_INTEGRITY_MANIFEST_HASH_MISMATCH"
        and issue.get("message") == "vnext+17 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus17_cycle_policy_extended_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    drift_payload = json.loads(
        _example_stop_gate_path("adeu_integrity_cycle_policy_extended_case_a_2.json").read_text(
            encoding="utf-8"
        )
    )
    drift_payload["source_text_hash"] = "hash-e2-stop-gate-case-a-drift"
    drift_path = tmp_path / "adeu_integrity_cycle_policy_extended_case_a_2_drift.json"
    _write_json(drift_path, drift_payload)

    manifest_payload = _vnext_plus17_manifest_payload()
    cycle_fixtures = manifest_payload.get("cycle_policy_extended_fixtures")
    assert isinstance(cycle_fixtures, list) and cycle_fixtures
    first_fixture = cycle_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_runs = first_fixture.get("runs")
    assert isinstance(first_runs, list) and len(first_runs) == 3
    assert isinstance(first_runs[1], dict)
    first_runs[1]["cycle_policy_extended_path"] = str(drift_path)
    manifest_path = _write_vnext_plus17_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=_vnext_plus15_manifest_path(),
        vnext_plus16_manifest_path=_vnext_plus16_manifest_path(),
        vnext_plus17_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_reference_integrity_extended_determinism_pct"] == 100.0
    assert report["metrics"]["artifact_cycle_policy_extended_determinism_pct"] < 100.0
    assert report["metrics"]["artifact_deontic_conflict_extended_determinism_pct"] == 100.0
    assert report["gates"]["artifact_reference_integrity_extended_determinism"] is True
    assert report["gates"]["artifact_cycle_policy_extended_determinism"] is False
    assert report["gates"]["artifact_deontic_conflict_extended_determinism"] is True
    assert any(
        issue.get("code") == "URM_ADEU_INTEGRITY_DIAGNOSTIC_DRIFT"
        and issue.get("message") == "vnext+17 cycle-policy extended diagnostic drift"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus17_all_zero_reference_integrity(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    zero_reference_payload = {
        "schema": "adeu_integrity_reference_integrity_extended@0.1",
        "source_text_hash": "hash-e1-stop-gate-case-a",
        "summary": {
            "total_issues": 0,
            "edge_type_constraint_violation": 0,
            "duplicate_edge_identity": 0,
        },
        "issues": [],
    }
    zero_reference_path = tmp_path / "adeu_integrity_reference_integrity_extended_zero.json"
    _write_json(zero_reference_path, zero_reference_payload)

    manifest_payload = _vnext_plus17_manifest_payload()
    reference_fixtures = manifest_payload.get("reference_integrity_extended_fixtures")
    assert isinstance(reference_fixtures, list) and reference_fixtures
    first_fixture = reference_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_runs = first_fixture.get("runs")
    assert isinstance(first_runs, list) and len(first_runs) == 3
    for run in first_runs:
        assert isinstance(run, dict)
        run["reference_integrity_extended_path"] = str(zero_reference_path)
    manifest_path = _write_vnext_plus17_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        vnext_plus13_manifest_path=_vnext_plus13_manifest_path(),
        vnext_plus14_manifest_path=_vnext_plus14_manifest_path(),
        vnext_plus15_manifest_path=_vnext_plus15_manifest_path(),
        vnext_plus16_manifest_path=_vnext_plus16_manifest_path(),
        vnext_plus17_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_reference_integrity_extended_determinism_pct"] == 0.0
    assert report["metrics"]["artifact_cycle_policy_extended_determinism_pct"] == 100.0
    assert report["metrics"]["artifact_deontic_conflict_extended_determinism_pct"] == 100.0
    assert any(
        issue.get("code") == "URM_ADEU_INTEGRITY_FIXTURE_INVALID"
        and issue.get("message")
        == "vnext+17 reference-integrity extended fixtures must include non-zero diagnostics"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus18_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    manifest_payload = _vnext_plus18_manifest_payload()
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus18_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        **_vnext_plus13_to_17_manifest_kwargs(),
        vnext_plus18_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_validation_consolidation_parity_pct"] == 0.0
    assert report["metrics"]["artifact_transfer_report_consolidation_parity_pct"] == 0.0
    assert report["vnext_plus18_manifest_hash"] == ""
    assert any(
        issue.get("code") == "URM_ADEU_TOOLING_MANIFEST_HASH_MISMATCH"
        and issue.get("message") == "vnext+18 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_detects_vnext_plus18_validation_parity_drift(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    drift_payload = json.loads(
        _example_stop_gate_path("tooling_validation_parity_candidate_case_a_2.json").read_text(
            encoding="utf-8"
        )
    )
    payload = drift_payload.get("payload")
    assert isinstance(payload, dict)
    payload["status"] = "drift"
    drift_path = tmp_path / "tooling_validation_parity_candidate_case_a_2_drift.json"
    _write_json(drift_path, drift_payload)

    manifest_payload = _vnext_plus18_manifest_payload()
    validation_fixtures = manifest_payload.get("validation_parity_fixtures")
    assert isinstance(validation_fixtures, list) and validation_fixtures
    first_fixture = validation_fixtures[0]
    assert isinstance(first_fixture, dict)
    first_runs = first_fixture.get("runs")
    assert isinstance(first_runs, list) and len(first_runs) == 3
    assert isinstance(first_runs[1], dict)
    first_runs[1]["candidate_path"] = str(drift_path)
    manifest_path = _write_vnext_plus18_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        **_vnext_plus13_to_17_manifest_kwargs(),
        vnext_plus18_manifest_path=manifest_path,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_validation_consolidation_parity_pct"] < 100.0
    assert report["metrics"]["artifact_transfer_report_consolidation_parity_pct"] == 100.0
    assert report["gates"]["artifact_validation_consolidation_parity"] is False
    assert report["gates"]["artifact_transfer_report_consolidation_parity"] is True
    assert any(
        issue.get("code") == "URM_ADEU_TOOLING_PARITY_DRIFT"
        and issue.get("message") == "vnext+18 validation consolidation parity drift"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_rejects_vnext_plus19_manifest_hash_mismatch(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    manifest_payload = _vnext_plus19_manifest_payload()
    manifest_payload["manifest_hash"] = "0" * 64
    manifest_path = tmp_path / "vnext_plus19_manifest_bad_hash.json"
    _write_json(manifest_path, manifest_payload)

    manifest_kwargs = _vnext_plus13_to_19_manifest_kwargs()
    manifest_kwargs["vnext_plus19_manifest_path"] = manifest_path
    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        **manifest_kwargs,
    )

    assert report["valid"] is False
    assert report["metrics"]["artifact_core_ir_read_surface_determinism_pct"] == 0.0
    assert report["metrics"]["artifact_lane_read_surface_determinism_pct"] == 0.0
    assert report["metrics"]["artifact_integrity_read_surface_determinism_pct"] == 0.0
    assert report["vnext_plus19_manifest_hash"] == ""
    assert any(
        issue.get("code") == "URM_ADEU_READ_SURFACE_MANIFEST_HASH_MISMATCH"
        and issue.get("message") == "vnext+19 manifest_hash mismatch"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_build_stop_gate_metrics_excludes_created_at_recursively_for_vnext_plus19(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = _legacy_quality_payload()
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

    lane_capture_payload = json.loads(
        (
            _vnext_plus19_manifest_path().parent
            / "vnext_plus19"
            / "lane_read_surface_capture_case_a_2.json"
        ).read_text(encoding="utf-8")
    )
    captures = lane_capture_payload.get("captures")
    assert isinstance(captures, list) and len(captures) == 2
    for idx, capture in enumerate(captures, start=1):
        assert isinstance(capture, dict)
        response_payload = capture.get("response")
        assert isinstance(response_payload, dict)
        response_payload["created_at"] = f"2099-01-0{idx}T00:00:00Z"
    lane_capture_path = tmp_path / "lane_read_surface_capture_case_a_2_created_at_drift.json"
    _write_json(lane_capture_path, lane_capture_payload)

    manifest_payload = _vnext_plus19_manifest_payload()
    lane_fixtures = manifest_payload.get("lane_read_surface_fixtures")
    assert isinstance(lane_fixtures, list) and lane_fixtures
    lane_fixture = lane_fixtures[0]
    assert isinstance(lane_fixture, dict)
    lane_runs = lane_fixture.get("runs")
    assert isinstance(lane_runs, list) and len(lane_runs) == 3
    assert isinstance(lane_runs[1], dict)
    lane_runs[1]["lane_read_surface_path"] = str(lane_capture_path)
    manifest_path = _write_vnext_plus19_manifest_payload(
        tmp_path=tmp_path,
        payload=manifest_payload,
    )

    manifest_kwargs = _vnext_plus13_to_19_manifest_kwargs()
    manifest_kwargs["vnext_plus19_manifest_path"] = manifest_path
    report = build_stop_gate_metrics(
        **_base_stop_gate_kwargs(
            quality_current=quality_current,
            quality_baseline=quality_baseline,
        ),
        **manifest_kwargs,
    )

    assert report["valid"] is True
    assert report["all_passed"] is True
    assert report["metrics"]["artifact_core_ir_read_surface_determinism_pct"] == 100.0
    assert report["metrics"]["artifact_lane_read_surface_determinism_pct"] == 100.0
    assert report["metrics"]["artifact_integrity_read_surface_determinism_pct"] == 100.0
    assert not any(
        issue.get("code") == "URM_ADEU_READ_SURFACE_DIAGNOSTIC_DRIFT"
        for issue in report["issues"]
        if isinstance(issue, dict)
    )


def test_stop_gate_tools_uses_shared_integrity_manifest_loader() -> None:
    source = Path(stop_gate_tools_module.__file__).read_text(encoding="utf-8")
    assert "def _load_integrity_manifest_payload(" in source
    assert "def _validate_integrity_surface_fixtures(" in source
    assert "def _validate_vnext_plus16_surface_fixtures(" not in source
    assert "def _validate_vnext_plus17_surface_fixtures(" not in source


def test_stop_gate_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_current.write_text(
        json.dumps(
            {
                "dashboard_version": "quality.dashboard.v1",
                "metrics": {"question_stability_pct": 100.0},
            }
        ),
        encoding="utf-8",
    )
    out_json = tmp_path / "stop_gate_metrics.json"
    out_md = tmp_path / "stop_gate_metrics.md"
    exit_code = main(
        [
            "--incident-packet",
            str(_example_stop_gate_path("incident_packet_case_a_1.json")),
            "--incident-packet",
            str(_example_stop_gate_path("incident_packet_case_a_2.json")),
            "--event-stream",
            str(_event_fixture_path("sample_valid.ndjson")),
            "--connector-snapshot",
            str(_example_stop_gate_path("connector_snapshot_case_a_1.json")),
            "--connector-snapshot",
            str(_example_stop_gate_path("connector_snapshot_case_a_2.json")),
            "--validator-evidence-packet",
            str(_validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json")),
            "--validator-evidence-packet",
            str(_validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json")),
            "--validator-evidence-packet",
            str(_validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json")),
            "--semantics-diagnostics",
            str(_semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json")),
            "--semantics-diagnostics",
            str(_semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json")),
            "--semantics-diagnostics",
            str(_semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json")),
            "--quality-current",
            str(quality_current),
            "--vnext-plus7-manifest",
            str(_vnext_plus7_manifest_path()),
            "--vnext-plus8-manifest",
            str(_vnext_plus8_manifest_path()),
            "--vnext-plus9-manifest",
            str(_vnext_plus9_manifest_path()),
            "--vnext-plus10-manifest",
            str(_vnext_plus10_manifest_path()),
            "--vnext-plus11-manifest",
            str(_vnext_plus11_manifest_path()),
            "--vnext-plus13-manifest",
            str(_vnext_plus13_manifest_path()),
            "--vnext-plus14-manifest",
            str(_vnext_plus14_manifest_path()),
            "--vnext-plus15-manifest",
            str(_vnext_plus15_manifest_path()),
            "--vnext-plus16-manifest",
            str(_vnext_plus16_manifest_path()),
            "--vnext-plus17-manifest",
            str(_vnext_plus17_manifest_path()),
            "--vnext-plus18-manifest",
            str(_vnext_plus18_manifest_path()),
            "--vnext-plus19-manifest",
            str(_vnext_plus19_manifest_path()),
            "--out-json",
            str(out_json),
            "--out-md",
            str(out_md),
        ]
    )
    assert exit_code == 0
    payload = json.loads(out_json.read_text(encoding="utf-8"))
    assert payload["schema"] == "stop_gate_metrics@1"
    assert payload["valid"] is True
    assert out_md.is_file()
    assert "Stop-Gate Metrics" in out_md.read_text(encoding="utf-8")


def test_build_stop_gate_metrics_applies_frozen_v3_quality_rules(tmp_path: Path) -> None:
    quality_current = tmp_path / "quality_current_v3.json"
    quality_baseline = tmp_path / "quality_baseline_v3.json"
    quality_current.write_text(
        json.dumps(
            {
                "dashboard_version": "quality.dashboard.v1",
                "metrics": _quality_metrics_v3(),
            }
        ),
        encoding="utf-8",
    )
    quality_baseline.write_text(
        json.dumps(
            {
                "dashboard_version": "quality.dashboard.v1",
                "metrics": _quality_metrics_v3(
                    overrides={
                        "redundancy_rate": 0.1,
                        "top_k_stability@10": 1.0,
                        "evidence_coverage_rate": 1.0,
                        "bridge_loss_utilization_rate": 0.0,
                        "coherence_alert_count": 0.0,
                    }
                ),
            }
        ),
        encoding="utf-8",
    )

    report = build_stop_gate_metrics(
        incident_packet_paths=[
            _example_stop_gate_path("incident_packet_case_a_1.json"),
            _example_stop_gate_path("incident_packet_case_a_2.json"),
        ],
        event_stream_paths=[_event_fixture_path("sample_valid.ndjson")],
        connector_snapshot_paths=[
            _example_stop_gate_path("connector_snapshot_case_a_1.json"),
            _example_stop_gate_path("connector_snapshot_case_a_2.json"),
        ],
        validator_evidence_packet_paths=[
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_1.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_2.json"),
            _validator_evidence_fixture_path("validator_evidence_packet_case_a_3.json"),
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_3.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
        vnext_plus7_manifest_path=_vnext_plus7_manifest_path(),
        vnext_plus8_manifest_path=_vnext_plus8_manifest_path(),
        vnext_plus9_manifest_path=_vnext_plus9_manifest_path(),
        vnext_plus10_manifest_path=_vnext_plus10_manifest_path(),
    )

    assert report["valid"] is True
    assert report["metrics"]["quality_metric_ruleset"] == "frozen_v3"
    assert report["metrics"]["quality_deltas"]["redundancy_rate"] > 0.0
    assert report["metrics"]["quality_delta_non_negative"] is False
