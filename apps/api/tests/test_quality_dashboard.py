from __future__ import annotations

import json
from pathlib import Path

from adeu_api.hashing import canonical_json
from adeu_api.quality_dashboard import (
    DETERMINISTIC_EVALUATION_TS,
    FROZEN_QUALITY_METRIC_RULES,
    build_quality_dashboard,
    write_quality_dashboard,
)


def test_build_quality_dashboard_contains_locked_metrics() -> None:
    left = build_quality_dashboard(question_repeats=2, session_steps=2)
    right = build_quality_dashboard(question_repeats=2, session_steps=2)
    assert left == right
    dashboard = left

    metrics = dashboard["metrics"]
    for metric_name in sorted(FROZEN_QUALITY_METRIC_RULES):
        assert metric_name in metrics

    assert dashboard["fixture_counts"]["questions"] > 0
    assert dashboard["fixture_counts"]["tournament"] > 0
    assert dashboard["generated_at"] == DETERMINISTIC_EVALUATION_TS
    assert dashboard["config"]["question_rank_version"] == "concepts.qrank.v3"
    assert dashboard["config"]["tournament_score_version"] == "concepts.tscore.v3"


def test_write_quality_dashboard_persists_json(tmp_path: Path) -> None:
    baseline = build_quality_dashboard(question_repeats=1, session_steps=1)
    baseline["metrics"]["redundancy_rate"] = -1.0
    baseline_path = tmp_path / "quality_dashboard_baseline.json"
    baseline_path.write_text(
        json.dumps(baseline, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    output = tmp_path / "quality_dashboard.json"

    dashboard = write_quality_dashboard(
        output,
        question_repeats=1,
        session_steps=1,
        baseline_path=baseline_path,
    )

    assert output.is_file()
    payload = output.read_text(encoding="utf-8")
    assert '"metrics"' in payload
    assert dashboard["dashboard_version"] == "quality.dashboard.v1"
    assert dashboard["input_manifest"]["schema"] == "quality.dashboard.inputs.v1"
    assert dashboard["delta_report"]["schema"] == "quality.dashboard.delta.v1"
    assert dashboard["delta_report"]["non_negative_quality"] is False
    assert dashboard["delta_report"]["metric_deltas"]["redundancy_rate"] > 0.0
    expected_keys = sorted(FROZEN_QUALITY_METRIC_RULES)
    assert sorted(dashboard["delta_report"]["metric_deltas"]) == expected_keys
    assert canonical_json(dashboard["quality_metric_rules"]) == canonical_json(
        FROZEN_QUALITY_METRIC_RULES
    )
