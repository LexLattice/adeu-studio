from __future__ import annotations

from typing import Any

from pydantic import BaseModel, ConfigDict, Field


class URMErrorDetail(BaseModel):
    model_config = ConfigDict(extra="forbid")

    code: str
    message: str
    context: dict[str, Any] = Field(default_factory=dict)


class URMError(Exception):
    def __init__(
        self,
        *,
        code: str,
        message: str,
        status_code: int = 400,
        context: dict[str, Any] | None = None,
    ) -> None:
        super().__init__(message)
        self.status_code = status_code
        self.detail = URMErrorDetail(
            code=code,
            message=message,
            context=context or {},
        )


class ApprovalError(ValueError):
    """Base class for approval domain errors."""


class ApprovalNotFoundError(ApprovalError, KeyError):
    """Approval does not exist."""


class ApprovalMismatchError(ApprovalError):
    """Approval action kind/hash does not match expected payload."""


class ApprovalInvalidStateError(ApprovalError):
    """Approval was already revoked or consumed."""


class ApprovalExpiredError(ApprovalError):
    """Approval has expired."""


def error_envelope(
    *,
    code: str,
    message: str,
    context: dict[str, Any] | None = None,
) -> dict[str, URMErrorDetail]:
    return {"detail": URMErrorDetail(code=code, message=message, context=context or {})}
