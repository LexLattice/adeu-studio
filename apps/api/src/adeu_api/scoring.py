from __future__ import annotations

from typing import TypeAlias

from adeu_ir import CheckReport, ReasonSeverity
from adeu_ir.models import CheckStatus

ScoreKey: TypeAlias = tuple[int, int, int, int]

_STATUS_RANK: dict[CheckStatus, int] = {"PASS": 2, "WARN": 1, "REFUSE": 0}


def status_rank(status: CheckStatus) -> int:
    return _STATUS_RANK[status]


def score_key(report: CheckReport) -> ScoreKey:
    """
    Canonical score key where higher is better:
    (status_rank, -num_errors, -num_warns, -total_reasons)
    """
    num_errors = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.ERROR)
    num_warns = sum(1 for r in report.reason_codes if r.severity == ReasonSeverity.WARN)
    return (
        status_rank(report.status),
        -num_errors,
        -num_warns,
        -len(report.reason_codes),
    )


def is_strict_improvement(
    candidate: ScoreKey,
    baseline: ScoreKey | None,
) -> bool:
    if baseline is None:
        return True
    return candidate > baseline


def ranking_sort_key(
    key: ScoreKey,
    ir_id: str,
) -> tuple[int, int, int, int, str]:
    # Ascending sort key that yields best candidates first.
    return (-key[0], -key[1], -key[2], -key[3], ir_id)
