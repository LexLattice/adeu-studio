from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Literal

from .errors import URMError
from .storage import apply_parent_budget_debit, transaction


def remaining_parent_duration_secs(
    *,
    session_started_at: str,
    max_session_duration_secs: int,
) -> int:
    started = datetime.fromisoformat(session_started_at)
    elapsed = datetime.now(tz=timezone.utc) - started
    remaining = max_session_duration_secs - int(elapsed.total_seconds())
    return max(0, remaining)


def child_budget_snapshot(
    *,
    session_started_at: str,
    max_session_duration_secs: int,
    budget_version: str,
    accounting_model: str,
    max_solver_calls: int,
    max_duration_secs: int,
    max_token_budget: int,
) -> dict[str, Any]:
    remaining_parent = remaining_parent_duration_secs(
        session_started_at=session_started_at,
        max_session_duration_secs=max_session_duration_secs,
    )
    return {
        "budget_version": budget_version,
        "accounting_model": accounting_model,
        "max_solver_calls": max_solver_calls,
        "max_duration_secs": min(max_duration_secs, remaining_parent),
        "max_token_budget": max_token_budget,
        "remaining_parent_duration_secs": remaining_parent,
        # Codex app-server does not currently provide stable token usage in this runtime path.
        "token_usage_unobserved": True,
    }


def budget_snapshot_int_value(
    *,
    budget_snapshot: dict[str, Any],
    key: str,
    default: int,
) -> int:
    raw_value = budget_snapshot.get(key)
    if isinstance(raw_value, bool):
        return default
    if isinstance(raw_value, int):
        return max(0, raw_value)
    return default


def extract_authoritative_token_usage(*, response: dict[str, Any]) -> int | None:
    result = response.get("result")
    if not isinstance(result, dict):
        return None
    usage = result.get("usage")
    if isinstance(usage, dict):
        for key in ("total_tokens", "totalTokens"):
            value = usage.get(key)
            if isinstance(value, int) and value >= 0:
                return value
    for key in ("total_tokens", "totalTokens"):
        value = result.get(key)
        if isinstance(value, int) and value >= 0:
            return value
    return None


def observe_child_budget_unlocked(*, child: Any) -> None:
    now = datetime.now(tz=timezone.utc)
    started_at = datetime.fromisoformat(child.started_at)
    child.last_budget_check_ts = now.isoformat()
    child.duration_secs_observed = max(0, int((now - started_at).total_seconds()))
    if child.token_usage_observed is None:
        child.token_usage_unobserved = bool(
            child.budget_snapshot.get("token_usage_unobserved", child.token_usage_unobserved)
        )
    else:
        child.token_usage_unobserved = False


def raise_child_budget_exceeded(
    *,
    child: Any,
    dimension: Literal["duration", "tokens", "solver_calls"],
    limit: int,
    observed: int,
) -> None:
    raise URMError(
        code="URM_CHILD_BUDGET_EXCEEDED",
        message=f"child budget exceeded for {dimension}",
        context={
            "child_id": child.child_id,
            "session_id": child.parent_session_id,
            "dimension": dimension,
            "limit": limit,
            "observed": observed,
            "token_usage_unobserved": child.token_usage_unobserved,
        },
    )


def enforce_child_budget_unlocked(
    *,
    child: Any,
    db_path: Path,
    accounting_model: str,
    max_duration_default: int,
    max_solver_calls_default: int,
    max_token_budget_default: int,
) -> None:
    observe_child_budget_unlocked(child=child)
    observed_accounting_model = child.budget_snapshot.get("accounting_model")
    if observed_accounting_model is None:
        observed_accounting_model = accounting_model
    if observed_accounting_model != accounting_model:
        raise URMError(
            code="URM_DISPATCH_ACCOUNTING_MODE_INVALID",
            message="unsupported child budget accounting model",
            context={
                "child_id": child.child_id,
                "session_id": child.parent_session_id,
                "accounting_model": observed_accounting_model,
                "expected_model": accounting_model,
            },
        )

    max_duration_secs = budget_snapshot_int_value(
        budget_snapshot=child.budget_snapshot,
        key="max_duration_secs",
        default=max_duration_default,
    )
    max_solver_calls = budget_snapshot_int_value(
        budget_snapshot=child.budget_snapshot,
        key="max_solver_calls",
        default=max_solver_calls_default,
    )
    max_token_budget = budget_snapshot_int_value(
        budget_snapshot=child.budget_snapshot,
        key="max_token_budget",
        default=max_token_budget_default,
    )

    solver_debit = max(0, child.solver_calls_observed - child.solver_calls_accounted_total)
    if solver_debit > 0:
        with transaction(db_path=db_path) as con:
            debit_result = apply_parent_budget_debit(
                con=con,
                parent_session_id=child.parent_session_id,
                budget_lane="solver_calls",
                debit=solver_debit,
                max_total=max_solver_calls,
            )
        if not debit_result.accepted:
            raise_child_budget_exceeded(
                child=child,
                dimension="solver_calls",
                limit=debit_result.row.max_total,
                observed=debit_result.row.current_total + debit_result.attempted_debit,
            )
        child.solver_calls_accounted_total = child.solver_calls_observed

    duration_debit = max(0, child.duration_secs_observed - child.duration_secs_accounted_total)
    if duration_debit > 0:
        with transaction(db_path=db_path) as con:
            debit_result = apply_parent_budget_debit(
                con=con,
                parent_session_id=child.parent_session_id,
                budget_lane="duration_secs",
                debit=duration_debit,
                max_total=max_duration_secs,
            )
        if not debit_result.accepted:
            raise_child_budget_exceeded(
                child=child,
                dimension="duration",
                limit=debit_result.row.max_total,
                observed=debit_result.row.current_total + debit_result.attempted_debit,
            )
        child.duration_secs_accounted_total = child.duration_secs_observed

    if not child.token_usage_unobserved and child.token_usage_observed is not None:
        token_debit = max(0, child.token_usage_observed - child.token_usage_accounted_total)
        if token_debit > 0:
            with transaction(db_path=db_path) as con:
                debit_result = apply_parent_budget_debit(
                    con=con,
                    parent_session_id=child.parent_session_id,
                    budget_lane="tokens",
                    debit=token_debit,
                    max_total=max_token_budget,
                )
            if not debit_result.accepted:
                raise_child_budget_exceeded(
                    child=child,
                    dimension="tokens",
                    limit=debit_result.row.max_total,
                    observed=debit_result.row.current_total + debit_result.attempted_debit,
                )
            child.token_usage_accounted_total = child.token_usage_observed
