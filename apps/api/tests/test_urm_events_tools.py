from __future__ import annotations

import json
from pathlib import Path

from urm_runtime.events_tools import main, replay_events, summarize_events, validate_events


def _fixture_path(name: str) -> Path:
    return Path(__file__).resolve().parent / "fixtures" / "urm_events" / name


def test_validate_events_strict_passes_for_valid_fixture() -> None:
    path = _fixture_path("sample_valid.ndjson")
    result = validate_events(path, strict=True)
    assert result["schema"] == "urm-events-validate@1"
    assert result["valid"] is True
    assert result["event_count"] == 6
    assert result["issues"] == []


def test_validate_events_detects_seq_monotonic_violation(tmp_path: Path) -> None:
    path = tmp_path / "invalid_seq.ndjson"
    path.write_text(
        "\n".join(
            [
                '{"schema":"urm-events@1","event":"SESSION_START","stream_id":"copilot:s","seq":1,"ts":"2026-02-11T10:00:00+00:00","source":{"component":"urm_copilot_manager","version":"0.0.0","provider":"codex"},"context":{"session_id":"s","role":"copilot","endpoint":"urm.copilot.events"},"detail":{"status":"running"}}',
                '{"schema":"urm-events@1","event":"SESSION_READY","stream_id":"copilot:s","seq":1,"ts":"2026-02-11T10:00:01+00:00","source":{"component":"urm_copilot_manager","version":"0.0.0","provider":"codex"},"context":{"session_id":"s","role":"copilot","endpoint":"urm.copilot.events"},"detail":{"status":"running"}}',
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    result = validate_events(path, strict=True)
    assert result["valid"] is False
    assert any(issue["code"] == "SEQ_NOT_MONOTONIC" for issue in result["issues"])


def test_validate_events_accepts_proof_run_events_with_required_linkage_fields(
    tmp_path: Path,
) -> None:
    path = tmp_path / "proof_events.ndjson"
    events = [
        {
            "schema": "urm-events@1",
            "event": "POLICY_EVAL_START",
            "stream_id": "copilot:s",
            "seq": 1,
            "ts": "2026-02-11T10:00:00+00:00",
            "source": {"component": "urm_copilot_manager", "version": "0.0.0", "provider": "codex"},
            "context": {"session_id": "s", "role": "copilot", "endpoint": "urm.tools.call"},
            "detail": {"policy_hash": "a", "decision_code": "PENDING", "matched_rule_ids": []},
        },
        {
            "schema": "urm-events@1",
            "event": "PROOF_RUN_PASS",
            "stream_id": "copilot:s",
            "seq": 2,
            "ts": "2026-02-11T10:00:01+00:00",
            "source": {"component": "urm_copilot_manager", "version": "0.0.0", "provider": "codex"},
            "context": {"session_id": "s", "role": "copilot", "endpoint": "urm.tools.call"},
            "detail": {
                "proof_id": "proof_a",
                "artifact_ref": "proof:proof_a",
                "parent_stream_id": "copilot:s",
                "parent_seq": 1,
            },
        },
        {
            "schema": "urm-events@1",
            "event": "PROOF_RUN_FAIL",
            "stream_id": "copilot:s",
            "seq": 3,
            "ts": "2026-02-11T10:00:02+00:00",
            "source": {"component": "urm_copilot_manager", "version": "0.0.0", "provider": "codex"},
            "context": {"session_id": "s", "role": "copilot", "endpoint": "urm.tools.call"},
            "detail": {
                "proof_id": "proof_b",
                "artifact_ref": "proof:proof_b",
                "parent_stream_id": "copilot:s",
                "parent_seq": 2,
                "code": "URM_PROOF_BACKEND_UNAVAILABLE",
            },
        },
        {
            "schema": "urm-events@1",
            "event": "POLICY_EVAL_PASS",
            "stream_id": "copilot:s",
            "seq": 4,
            "ts": "2026-02-11T10:00:03+00:00",
            "source": {"component": "urm_copilot_manager", "version": "0.0.0", "provider": "codex"},
            "context": {"session_id": "s", "role": "copilot", "endpoint": "urm.tools.call"},
            "detail": {"policy_hash": "a", "decision_code": "ALLOW", "matched_rule_ids": []},
        },
    ]
    path.write_text(
        "\n".join(json.dumps(item, separators=(",", ":")) for item in events)
        + "\n",
        encoding="utf-8",
    )
    result = validate_events(path, strict=True)
    assert result["valid"] is True


def test_validate_events_rejects_proof_fail_without_code(tmp_path: Path) -> None:
    path = tmp_path / "proof_events_invalid.ndjson"
    path.write_text(
        "\n".join(
            json.dumps(item, separators=(",", ":"))
            for item in [
                {
                    "schema": "urm-events@1",
                    "event": "PROOF_RUN_FAIL",
                    "stream_id": "copilot:s",
                    "seq": 1,
                    "ts": "2026-02-11T10:00:02+00:00",
                    "source": {
                        "component": "urm_copilot_manager",
                        "version": "0.0.0",
                        "provider": "codex",
                    },
                    "context": {"session_id": "s", "role": "copilot", "endpoint": "urm.tools.call"},
                    "detail": {
                        "proof_id": "proof_b",
                        "artifact_ref": "proof:proof_b",
                        "parent_stream_id": "copilot:s",
                        "parent_seq": 0,
                    },
                }
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    result = validate_events(path, strict=True)
    assert result["valid"] is False
    assert any(issue["code"] == "DETAIL_MINIMUM_MISSING" for issue in result["issues"])


def test_replay_events_is_stable_for_same_input() -> None:
    path = _fixture_path("sample_valid.ndjson")
    first = replay_events(path)
    second = replay_events(path)
    assert first == second
    assert len(first) == 6


def test_replay_events_preserves_original_line_literal() -> None:
    path = _fixture_path("sample_valid.ndjson")
    original_lines = path.read_text(encoding="utf-8").splitlines()
    replay_lines = replay_events(path)
    assert replay_lines == original_lines


def test_summarize_events_has_stable_schema_and_fields() -> None:
    path = _fixture_path("sample_valid.ndjson")
    summary = summarize_events(path)
    assert summary["schema"] == "urm-events-summary@1"
    assert summary["event_count"] == 6
    assert summary["event_counts_by_type"]["SESSION_START"] == 1
    assert summary["tool_call_counts"] == {"start": 1, "pass": 0, "fail": 1}
    assert summary["error_counts"]["by_code"]["URM_POLICY_DENIED"] == 2
    assert summary["first_failure"]["event"] == "TOOL_CALL_FAIL"
    assert summary["durations_by_stream"]["copilot:sess-1"]["duration_secs"] == 5.0


def test_cli_main_validate_replay_and_summary(tmp_path: Path) -> None:
    in_path = _fixture_path("sample_valid.ndjson")
    replay_out = tmp_path / "replay.ndjson"
    summary_out = tmp_path / "summary.json"
    summary_md = tmp_path / "summary.md"

    assert main(["validate", "--in", str(in_path), "--strict"]) == 0
    assert main(["replay", "--in", str(in_path), "--out", str(replay_out)]) == 0
    assert replay_out.exists()
    assert main(
        [
            "summary",
            "--in",
            str(in_path),
            "--out-json",
            str(summary_out),
            "--out-md",
            str(summary_md),
        ]
    ) == 0
    assert summary_out.exists()
    assert summary_md.exists()
