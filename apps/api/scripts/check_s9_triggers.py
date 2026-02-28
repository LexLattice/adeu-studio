from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json

S9_TRIGGER_CHECK_SCHEMA = "s9_trigger_check@1"
DEFAULT_REQUIRED_THRESHOLD = 100.0
REQUIRED_METRIC_KEYS: tuple[str, ...] = (
    "provider_route_contract_parity_pct",
    "codex_candidate_contract_valid_pct",
    "provider_parity_replay_determinism_pct",
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Deterministically check S9 trigger preconditions from stop-gate metrics.",
    )
    parser.add_argument(
        "--metrics-path",
        type=Path,
        default=None,
        help=(
            "Path to stop-gate metrics JSON. If omitted, resolves the v25 closeout "
            "artifact path relative to repository root."
        ),
    )
    parser.add_argument(
        "--required-threshold",
        type=float,
        default=DEFAULT_REQUIRED_THRESHOLD,
        help="Minimum required value for each S9 trigger metric.",
    )
    return parser.parse_args(argv)


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found from script location")


def _default_metrics_path(repo_root: Path) -> Path:
    return repo_root / "artifacts" / "stop_gate" / "metrics_v25_closeout.json"


def _display_path(path: Path, *, repo_root: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()


def _summary_template(*, metrics_path: str, threshold: float) -> dict[str, Any]:
    return {
        "schema": S9_TRIGGER_CHECK_SCHEMA,
        "metrics_path": metrics_path,
        "threshold": float(threshold),
        "required_keys": list(REQUIRED_METRIC_KEYS),
        "missing": [],
        "below": [],
        "pass": False,
    }


def _error_payload(*, code: str, message: str) -> dict[str, str]:
    return {"code": code, "message": message}


def _load_metrics_payload(metrics_path: Path) -> dict[str, Any]:
    payload = json.loads(metrics_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("metrics payload must be a JSON object")
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict):
        raise ValueError("metrics payload must include object field 'metrics'")
    return metrics


def _numeric_metric_value(*, metric_key: str, value: Any) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"metric '{metric_key}' must be numeric")
    return float(value)


def _evaluate(
    *,
    metrics: dict[str, Any],
    metrics_path_display: str,
    threshold: float,
) -> tuple[dict[str, Any], dict[str, str] | None]:
    summary = _summary_template(metrics_path=metrics_path_display, threshold=threshold)

    missing = sorted(key for key in REQUIRED_METRIC_KEYS if key not in metrics)
    below: list[dict[str, Any]] = []
    for key in REQUIRED_METRIC_KEYS:
        if key not in metrics:
            continue
        numeric_value = _numeric_metric_value(metric_key=key, value=metrics[key])
        if numeric_value < threshold:
            below.append({"key": key, "value": numeric_value})
    below.sort(key=lambda item: str(item["key"]))

    summary["missing"] = missing
    summary["below"] = below
    summary["pass"] = not missing and not below

    if missing:
        return summary, _error_payload(
            code="S9_TRIGGER_REQUIRED_METRIC_MISSING",
            message="required trigger metrics missing from payload",
        )
    if below:
        return summary, _error_payload(
            code="S9_TRIGGER_REQUIRED_THRESHOLD_FAILED",
            message="one or more trigger metrics below required threshold",
        )
    return summary, None


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = _repo_root()
    metrics_path = args.metrics_path or _default_metrics_path(repo_root)
    metrics_display = _display_path(metrics_path, repo_root=repo_root)
    summary = _summary_template(metrics_path=metrics_display, threshold=args.required_threshold)

    error: dict[str, str] | None = None
    if not metrics_path.exists():
        error = _error_payload(
            code="S9_TRIGGER_METRICS_PATH_MISSING",
            message="metrics path does not exist",
        )
    else:
        try:
            metrics = _load_metrics_payload(metrics_path)
            summary, error = _evaluate(
                metrics=metrics,
                metrics_path_display=metrics_display,
                threshold=args.required_threshold,
            )
        except json.JSONDecodeError:
            error = _error_payload(
                code="S9_TRIGGER_PAYLOAD_PARSE_ERROR",
                message="metrics payload is not valid JSON",
            )
        except ValueError as exc:
            error = _error_payload(
                code="S9_TRIGGER_PAYLOAD_INVALID",
                message=str(exc),
            )

    sys.stdout.write(canonical_json(summary) + "\n")
    if error is not None:
        sys.stderr.write(canonical_json(error) + "\n")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
