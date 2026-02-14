from __future__ import annotations

import json
from pathlib import Path

from adeu_kernel import (
    build_proof_evidence_packet,
    build_semantics_diagnostics,
    build_validator_evidence_packet,
)
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
    }
    first = build_stop_gate_metrics(**kwargs)
    second = build_stop_gate_metrics(**kwargs)
    assert first == second
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
    assert first["metrics"]["quality_delta_non_negative"] is True


def test_build_stop_gate_metrics_detects_replay_hash_drift_for_semantics_metrics(
    tmp_path: Path,
) -> None:
    quality_current = tmp_path / "quality_current.json"
    quality_baseline = tmp_path / "quality_baseline.json"
    quality_payload = {
        "dashboard_version": "quality.dashboard.v1",
        "metrics": {"question_stability_pct": 100.0},
    }
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
    quality_payload = {
        "dashboard_version": "quality.dashboard.v1",
        "metrics": {"question_stability_pct": 100.0},
    }
    _write_json(quality_current, quality_payload)
    _write_json(quality_baseline, quality_payload)

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

    lint_event_paths = [
        _example_stop_gate_path("policy_lint_events_case_a_1.ndjson"),
        _example_stop_gate_path("policy_lint_events_case_a_2.ndjson"),
        _example_stop_gate_path("policy_lint_events_case_a_3.ndjson"),
    ]
    manifest_path = tmp_path / "vnext_plus7_manifest.json"
    _write_json(
        manifest_path,
        {
            "schema": "stop_gate.vnext_plus7_manifest@1",
            "replay_count": 3,
            "metrics": {
                "policy_lint_determinism_pct": [
                    {
                        "fixture_id": "policy_lint_case_a",
                        "runs": [
                            {"policy_lint_event_path": str(lint_event_paths[0])},
                            {"policy_lint_event_path": str(lint_event_paths[1])},
                            {"policy_lint_event_path": str(lint_event_paths[2])},
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
        },
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
    )

    assert report["valid"] is True
    assert report["metrics"]["policy_lint_determinism_pct"] == 100.0
    assert report["metrics"]["proof_replay_determinism_pct"] == 0.0
    assert report["metrics"]["policy_proof_packet_hash_stability_pct"] == 0.0
    assert report["gates"]["policy_lint_determinism"] is True
    assert report["gates"]["proof_replay_determinism"] is False
    assert report["gates"]["policy_proof_packet_hash_stability"] is False


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
    )

    assert report["valid"] is True
    assert report["metrics"]["quality_metric_ruleset"] == "frozen_v3"
    assert report["metrics"]["quality_deltas"]["redundancy_rate"] > 0.0
    assert report["metrics"]["quality_delta_non_negative"] is False
