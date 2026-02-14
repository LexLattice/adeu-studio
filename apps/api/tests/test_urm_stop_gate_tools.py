from __future__ import annotations

import json
from pathlib import Path

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
        ],
        "semantics_diagnostics_paths": [
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
        ],
        "quality_current_path": quality_current,
        "quality_baseline_path": quality_baseline,
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
    assert first["metrics"]["quality_delta_non_negative"] is True


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
            "--semantics-diagnostics",
            str(_semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json")),
            "--semantics-diagnostics",
            str(_semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json")),
            "--quality-current",
            str(quality_current),
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
        ],
        semantics_diagnostics_paths=[
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_1.json"),
            _semantics_diagnostics_fixture_path("semantics_diagnostics_case_a_2.json"),
        ],
        quality_current_path=quality_current,
        quality_baseline_path=quality_baseline,
    )

    assert report["valid"] is True
    assert report["metrics"]["quality_metric_ruleset"] == "frozen_v3"
    assert report["metrics"]["quality_deltas"]["redundancy_rate"] > 0.0
    assert report["metrics"]["quality_delta_non_negative"] is False
