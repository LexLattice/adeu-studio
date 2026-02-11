from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

from .hashing import canonical_json
from .models import NormalizedEvent

SESSION_EVENTS = {"SESSION_START", "SESSION_READY", "SESSION_STOP", "SESSION_FAIL"}
WORKER_EVENTS = {"WORKER_START", "WORKER_PASS", "WORKER_FAIL", "WORKER_CANCEL"}
APPROVAL_EVENTS = {
    "MODE_CHANGED",
    "APPROVAL_ISSUED",
    "APPROVAL_CONSUMED",
    "APPROVAL_REVOKED",
    "POLICY_DENIED",
}
TOOL_EVENTS = {"TOOL_CALL_START", "TOOL_CALL_PASS", "TOOL_CALL_FAIL"}
EVIDENCE_EVENTS = {"EVIDENCE_WRITTEN"}


@dataclass(frozen=True)
class ValidationIssue:
    line: int
    code: str
    message: str

    def as_json(self) -> dict[str, Any]:
        return {
            "line": self.line,
            "code": self.code,
            "message": self.message,
        }


@dataclass(frozen=True)
class ParsedEvent:
    line: int
    event: NormalizedEvent


def _read_ndjson_lines(path: Path) -> list[str]:
    return path.read_text(encoding="utf-8", errors="replace").splitlines()


def _parse_events(path: Path) -> tuple[list[ParsedEvent], list[ValidationIssue]]:
    events: list[ParsedEvent] = []
    issues: list[ValidationIssue] = []
    for line_no, line in enumerate(_read_ndjson_lines(path), start=1):
        if not line.strip():
            continue
        try:
            payload = json.loads(line)
        except json.JSONDecodeError as exc:
            issues.append(
                ValidationIssue(
                    line=line_no,
                    code="INVALID_JSON",
                    message=f"invalid JSON: {exc}",
                )
            )
            continue
        try:
            event = NormalizedEvent.model_validate(payload)
        except Exception as exc:  # noqa: BLE001
            issues.append(
                ValidationIssue(
                    line=line_no,
                    code="INVALID_EVENT",
                    message=f"invalid urm event envelope: {exc}",
                )
            )
            continue
        events.append(ParsedEvent(line=line_no, event=event))
    return events, issues


def _validate_seq_monotonicity(events: list[ParsedEvent]) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    last_seq_by_stream: dict[str, int] = {}
    for parsed in events:
        stream_id = parsed.event.stream_id
        prev = last_seq_by_stream.get(stream_id)
        if prev is not None and parsed.event.seq <= prev:
            issues.append(
                ValidationIssue(
                    line=parsed.line,
                    code="SEQ_NOT_MONOTONIC",
                    message=(
                        f"stream '{stream_id}' sequence must increase strictly; "
                        f"previous={prev}, current={parsed.event.seq}"
                    ),
                )
            )
        last_seq_by_stream[stream_id] = parsed.event.seq
    return issues


def _has_keys(obj: dict[str, Any], keys: tuple[str, ...]) -> bool:
    return all(key in obj for key in keys)


def _validate_detail_minima(events: list[ParsedEvent]) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    for parsed in events:
        event = parsed.event
        detail = event.detail
        if event.event in SESSION_EVENTS:
            if not _has_keys(detail, ("status",)):
                issues.append(
                    ValidationIssue(
                        line=parsed.line,
                        code="DETAIL_MINIMUM_MISSING",
                        message=f"{event.event} detail must include status",
                    )
                )
        elif event.event in WORKER_EVENTS:
            if not _has_keys(detail, ("worker_id", "status")):
                issues.append(
                    ValidationIssue(
                        line=parsed.line,
                        code="DETAIL_MINIMUM_MISSING",
                        message=f"{event.event} detail must include worker_id and status",
                    )
                )
        elif event.event == "MODE_CHANGED":
            if not _has_keys(detail, ("writes_allowed",)):
                issues.append(
                    ValidationIssue(
                        line=parsed.line,
                        code="DETAIL_MINIMUM_MISSING",
                        message="MODE_CHANGED detail must include writes_allowed",
                    )
                )
        elif event.event in {"APPROVAL_ISSUED", "APPROVAL_CONSUMED", "APPROVAL_REVOKED"}:
            if not _has_keys(detail, ("approval_id", "action_kind")):
                issues.append(
                    ValidationIssue(
                        line=parsed.line,
                        code="DETAIL_MINIMUM_MISSING",
                        message=f"{event.event} detail must include approval_id and action_kind",
                    )
                )
        elif event.event in TOOL_EVENTS:
            if not _has_keys(detail, ("tool_name",)):
                issues.append(
                    ValidationIssue(
                        line=parsed.line,
                        code="DETAIL_MINIMUM_MISSING",
                        message=f"{event.event} detail must include tool_name",
                    )
                )
        elif event.event in EVIDENCE_EVENTS:
            if not _has_keys(detail, ("evidence_id", "path")):
                issues.append(
                    ValidationIssue(
                        line=parsed.line,
                        code="DETAIL_MINIMUM_MISSING",
                        message=f"{event.event} detail must include evidence_id and path",
                    )
                )
    return issues


def validate_events(path: Path, *, strict: bool) -> dict[str, Any]:
    parsed, issues = _parse_events(path)
    issues.extend(_validate_seq_monotonicity(parsed))
    if strict:
        issues.extend(_validate_detail_minima(parsed))
    issues_sorted = sorted(issues, key=lambda item: (item.line, item.code, item.message))
    event_count = len(parsed)
    stream_count = len({item.event.stream_id for item in parsed})
    return {
        "schema": "urm-events-validate@1",
        "input": str(path),
        "strict": strict,
        "valid": len(issues_sorted) == 0,
        "event_count": event_count,
        "stream_count": stream_count,
        "issues": [issue.as_json() for issue in issues_sorted],
    }


def replay_events(path: Path) -> list[str]:
    parsed, issues = _parse_events(path)
    issues.extend(_validate_seq_monotonicity(parsed))
    if issues:
        first = sorted(issues, key=lambda item: (item.line, item.code, item.message))[0]
        raise ValueError(f"{first.code} at line {first.line}: {first.message}")
    return [
        canonical_json(item.event.model_dump(mode="json", by_alias=True))
        for item in parsed
    ]


def _first_failure(events: list[ParsedEvent]) -> dict[str, Any] | None:
    for parsed in events:
        event = parsed.event
        category: str | None = None
        if event.event == "SESSION_FAIL":
            category = "session"
        elif event.event == "WORKER_FAIL":
            category = "worker"
        elif event.event == "TOOL_CALL_FAIL":
            category = "tool"
        elif event.event == "POLICY_DENIED":
            category = "policy"
        elif event.event == "PROVIDER_PARSE_ERROR":
            category = "provider"
        if category is None:
            continue
        return {
            "category": category,
            "event": event.event,
            "stream_id": event.stream_id,
            "seq": event.seq,
            "ts": event.ts.isoformat(),
            "line": parsed.line,
        }
    return None


def _duration_by_stream(events: list[ParsedEvent]) -> dict[str, dict[str, Any]]:
    bounds: dict[str, tuple[datetime, datetime]] = {}
    for parsed in events:
        stream_id = parsed.event.stream_id
        ts = parsed.event.ts
        if stream_id not in bounds:
            bounds[stream_id] = (ts, ts)
            continue
        start, end = bounds[stream_id]
        if ts < start:
            start = ts
        if ts > end:
            end = ts
        bounds[stream_id] = (start, end)
    out: dict[str, dict[str, Any]] = {}
    for stream_id in sorted(bounds):
        start, end = bounds[stream_id]
        out[stream_id] = {
            "started_at": start.isoformat(),
            "ended_at": end.isoformat(),
            "duration_secs": round((end - start).total_seconds(), 6),
        }
    return out


def summarize_events(path: Path) -> dict[str, Any]:
    parsed, issues = _parse_events(path)
    issues.extend(_validate_seq_monotonicity(parsed))
    if issues:
        first = sorted(issues, key=lambda item: (item.line, item.code, item.message))[0]
        raise ValueError(f"{first.code} at line {first.line}: {first.message}")

    event_counts: dict[str, int] = {}
    tool_call_counts = {"start": 0, "pass": 0, "fail": 0}
    error_codes: dict[str, int] = {}
    error_count = 0
    for parsed_event in parsed:
        event = parsed_event.event
        event_counts[event.event] = event_counts.get(event.event, 0) + 1
        if event.event == "TOOL_CALL_START":
            tool_call_counts["start"] += 1
        elif event.event == "TOOL_CALL_PASS":
            tool_call_counts["pass"] += 1
        elif event.event == "TOOL_CALL_FAIL":
            tool_call_counts["fail"] += 1
        error_code = event.detail.get("error_code")
        if not isinstance(error_code, str):
            error_code = event.detail.get("code")
        if isinstance(error_code, str):
            error_count += 1
            error_codes[error_code] = error_codes.get(error_code, 0) + 1

    ordered_counts = {key: event_counts[key] for key in sorted(event_counts)}
    ordered_error_codes = {key: error_codes[key] for key in sorted(error_codes)}
    return {
        "schema": "urm-events-summary@1",
        "input": str(path),
        "event_count": len(parsed),
        "stream_count": len({item.event.stream_id for item in parsed}),
        "event_counts_by_type": ordered_counts,
        "first_failure": _first_failure(parsed),
        "durations_by_stream": _duration_by_stream(parsed),
        "tool_call_counts": tool_call_counts,
        "error_counts": {
            "total": error_count,
            "by_code": ordered_error_codes,
        },
    }


def summary_markdown(summary: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# URM Events Summary")
    lines.append("")
    lines.append(f"- Input: `{summary['input']}`")
    lines.append(f"- Event count: `{summary['event_count']}`")
    lines.append(f"- Stream count: `{summary['stream_count']}`")
    first_failure = summary["first_failure"]
    if first_failure is None:
        lines.append("- First failure: `none`")
    else:
        lines.append(
            "- First failure: "
            f"`{first_failure['category']}` event `{first_failure['event']}` "
            f"at seq `{first_failure['seq']}` (stream `{first_failure['stream_id']}`)"
        )
    lines.append("")
    lines.append("## Event Counts")
    lines.append("")
    for event_name, count in summary["event_counts_by_type"].items():
        lines.append(f"- `{event_name}`: `{count}`")
    lines.append("")
    lines.append("## Tool Calls")
    lines.append("")
    tool_counts = summary["tool_call_counts"]
    lines.append(f"- start: `{tool_counts['start']}`")
    lines.append(f"- pass: `{tool_counts['pass']}`")
    lines.append(f"- fail: `{tool_counts['fail']}`")
    lines.append("")
    lines.append("## Error Codes")
    lines.append("")
    lines.append(f"- total: `{summary['error_counts']['total']}`")
    for code, count in summary["error_counts"]["by_code"].items():
        lines.append(f"- `{code}`: `{count}`")
    lines.append("")
    lines.append("## Durations")
    lines.append("")
    for stream_id, duration in summary["durations_by_stream"].items():
        lines.append(
            f"- `{stream_id}`: `{duration['duration_secs']}`s "
            f"({duration['started_at']} -> {duration['ended_at']})"
        )
    lines.append("")
    return "\n".join(lines)


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="events",
        description="URM events tooling: validate, replay, and summarize NDJSON streams.",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate_parser = subparsers.add_parser("validate", help="Validate URM NDJSON event stream.")
    validate_parser.add_argument("--in", dest="input_path", type=Path, required=True)
    validate_parser.add_argument("--strict", action="store_true")

    replay_parser = subparsers.add_parser("replay", help="Replay normalized URM event stream.")
    replay_parser.add_argument("--in", dest="input_path", type=Path, required=True)
    replay_parser.add_argument("--out", dest="out_path", type=Path, required=False)

    summary_parser = subparsers.add_parser("summary", help="Summarize URM event stream.")
    summary_parser.add_argument("--in", dest="input_path", type=Path, required=True)
    summary_parser.add_argument("--out-json", dest="out_json_path", type=Path, required=False)
    summary_parser.add_argument("--out-md", dest="out_md_path", type=Path, required=False)

    return parser.parse_args(argv)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        if args.command == "validate":
            report = validate_events(args.input_path, strict=bool(args.strict))
            out = canonical_json(report)
            print(out)
            return 0 if report["valid"] else 1

        if args.command == "replay":
            lines = replay_events(args.input_path)
            payload = "\n".join(lines) + ("\n" if lines else "")
            if args.out_path is not None:
                _write_text(args.out_path, payload)
            else:
                sys.stdout.write(payload)
            return 0

        if args.command == "summary":
            summary = summarize_events(args.input_path)
            summary_json = canonical_json(summary)
            summary_md = summary_markdown(summary)
            if args.out_json_path is not None:
                _write_text(args.out_json_path, summary_json + "\n")
            else:
                print(summary_json)
            if args.out_md_path is not None:
                _write_text(args.out_md_path, summary_md)
            return 0
    except Exception as exc:  # noqa: BLE001
        print(str(exc), file=sys.stderr)
        return 1

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
