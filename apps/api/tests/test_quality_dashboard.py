from __future__ import annotations

from pathlib import Path

from adeu_api.quality_dashboard import build_quality_dashboard, write_quality_dashboard


def test_build_quality_dashboard_contains_locked_metrics() -> None:
    dashboard = build_quality_dashboard(question_repeats=2, session_steps=2)

    metrics = dashboard["metrics"]
    assert "question_stability_pct" in metrics
    assert "avg_questions_per_ir" in metrics
    assert "avg_resolved_per_session" in metrics
    assert "avg_solver_calls_per_action" in metrics
    assert "p95_latency_ms" in metrics

    assert dashboard["fixture_counts"]["questions"] > 0
    assert dashboard["fixture_counts"]["tournament"] > 0
    assert "concepts.questions" in metrics["p95_latency_ms"]


def test_write_quality_dashboard_persists_json(tmp_path: Path) -> None:
    output = tmp_path / "quality_dashboard.json"

    dashboard = write_quality_dashboard(
        output,
        question_repeats=1,
        session_steps=1,
    )

    assert output.is_file()
    payload = output.read_text(encoding="utf-8")
    assert '"metrics"' in payload
    assert dashboard["dashboard_version"] == "quality.dashboard.v1"
