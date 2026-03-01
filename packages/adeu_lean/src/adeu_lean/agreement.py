from __future__ import annotations

import json
import re
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any, Literal

from adeu_ir import ProofInput
from pydantic import BaseModel, ConfigDict, Field, ValidationError, model_validator

from .models import OBLIGATION_KINDS, LeanRequest, LeanResult, LeanResultStatus
from .runner import build_obligation_requests, build_proof_mapping_id, run_lean_request

AGREEMENT_FIXTURE_SCHEMA = "odeu_agreement.fixtures@0.1"
AGREEMENT_REPORT_SCHEMA = "odeu_agreement.report@0.1"
_HEX_64_RE = re.compile(r"^[a-f0-9]{64}$")
_STATUS_VALUES = frozenset({"proved", "failed"})


class AgreementHarnessError(ValueError):
    """Raised when agreement fixture loading/report generation fails closed."""


class AgreementFixture(BaseModel):
    model_config = ConfigDict(extra="forbid")

    fixture_id: str = Field(min_length=1)
    theorem_prefix: str = Field(min_length=1)
    inputs: list[ProofInput] = Field(default_factory=list)
    python_expected_status: dict[str, LeanResultStatus]

    @model_validator(mode="after")
    def _validate_expected_status(self) -> "AgreementFixture":
        expected_kinds = set(self.python_expected_status.keys())
        required_kinds = set(OBLIGATION_KINDS)
        if expected_kinds != required_kinds:
            missing = sorted(required_kinds - expected_kinds)
            extra = sorted(expected_kinds - required_kinds)
            raise ValueError(
                (
                    "python_expected_status must match frozen obligations exactly; "
                    f"missing={missing}, extra={extra}"
                )
            )
        return self


class AgreementFixtureBundle(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_name: Literal[AGREEMENT_FIXTURE_SCHEMA] = Field(alias="schema")
    proof_semantics_version: str = Field(min_length=1)
    fixtures: list[AgreementFixture] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_unique_fixture_ids(self) -> "AgreementFixtureBundle":
        seen: set[str] = set()
        for fixture in self.fixtures:
            if fixture.fixture_id in seen:
                raise ValueError(f"duplicate fixture_id: {fixture.fixture_id!r}")
            seen.add(fixture.fixture_id)
        return self


class AgreementReportRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    fixture_id: str = Field(min_length=1)
    theorem_prefix: str = Field(min_length=1)
    obligation_kind: str = Field(min_length=1)
    inputs_hash: str = Field(min_length=1)
    mapping_id: str = Field(min_length=1)
    python_expected_status: LeanResultStatus
    lean_observed_status: LeanResultStatus
    agreement: bool
    proof_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_row_contract(self) -> "AgreementReportRow":
        if self.obligation_kind not in OBLIGATION_KINDS:
            raise ValueError(f"unsupported obligation_kind: {self.obligation_kind!r}")
        for key, value in (("mapping_id", self.mapping_id), ("proof_hash", self.proof_hash)):
            if _HEX_64_RE.match(value) is None:
                raise ValueError(f"{key} must be 64-char lowercase SHA-256 hex")
        return self


class AgreementReportSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_rows: int = Field(ge=0)
    agree_rows: int = Field(ge=0)
    disagree_rows: int = Field(ge=0)
    all_agree: bool
    fail_closed: bool


class AgreementReport(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_name: Literal[AGREEMENT_REPORT_SCHEMA] = Field(alias="schema")
    proof_semantics_version: str = Field(min_length=1)
    fixtures: list[AgreementReportRow]
    summary: AgreementReportSummary

    @model_validator(mode="after")
    def _validate_report_contract(self) -> "AgreementReport":
        expected_order = sorted(
            self.fixtures,
            key=lambda row: (row.fixture_id, row.obligation_kind),
        )
        if self.fixtures != expected_order:
            raise ValueError("fixtures rows must be sorted by fixture_id, obligation_kind")

        total_rows = len(self.fixtures)
        disagree_rows = sum(1 for row in self.fixtures if not row.agreement)
        agree_rows = total_rows - disagree_rows
        all_agree = disagree_rows == 0
        fail_closed = disagree_rows > 0
        expected = {
            "total_rows": total_rows,
            "agree_rows": agree_rows,
            "disagree_rows": disagree_rows,
            "all_agree": all_agree,
            "fail_closed": fail_closed,
        }
        observed = self.summary.model_dump(mode="json")
        if observed != expected:
            raise ValueError(
                "summary mismatch: expected deterministic counts/flags "
                f"{expected}, got {observed}"
            )
        return self


def _require_hex64(value: str, *, field_name: str) -> str:
    if _HEX_64_RE.match(value) is None:
        raise AgreementHarnessError(f"{field_name} must be 64-char lowercase SHA-256 hex")
    return value


def _require_request_metadata_hash(
    *,
    request: LeanRequest,
    key: str,
    fixture_id: str,
    obligation_kind: str,
) -> str:
    if key not in request.metadata:
        raise AgreementHarnessError(
            "missing deterministic metadata key "
            f"{key!r} for {fixture_id}:{obligation_kind}"
        )
    value = request.metadata[key]
    if not isinstance(value, str) or not value:
        raise AgreementHarnessError(
            "invalid deterministic metadata key "
            f"{key!r} for {fixture_id}:{obligation_kind}: expected non-empty string"
        )
    return _require_hex64(value, field_name=key)


def _coerce_fixture_inputs(raw_inputs: list[Any], *, fixture_id: str) -> list[ProofInput]:
    normalized_inputs: list[ProofInput] = []
    for idx, entry in enumerate(raw_inputs):
        if isinstance(entry, ProofInput):
            normalized_inputs.append(entry)
            continue
        if not isinstance(entry, Mapping):
            raise AgreementHarnessError(
                f"fixture {fixture_id!r} input at index {idx} must be an object"
            )
        try:
            normalized_inputs.append(ProofInput.model_validate(entry))
        except ValidationError as exc:
            raise AgreementHarnessError(
                f"fixture {fixture_id!r} input at index {idx} is invalid: {exc}"
            ) from exc
    return normalized_inputs


def _parse_fixture_bundle(payload: Any) -> AgreementFixtureBundle:
    try:
        return AgreementFixtureBundle.model_validate(payload)
    except ValidationError as exc:
        raise AgreementHarnessError(f"schema-invalid agreement fixtures: {exc}") from exc


def load_agreement_fixture_bundle(path: Path | str) -> AgreementFixtureBundle:
    fixture_path = Path(path).resolve()
    if not fixture_path.exists():
        raise AgreementHarnessError(f"missing fixture bundle: {fixture_path}")
    try:
        payload = json.loads(fixture_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise AgreementHarnessError(f"invalid fixture bundle JSON: {fixture_path}") from exc
    return _parse_fixture_bundle(payload)


def _validate_result_status(result: LeanResult) -> LeanResultStatus:
    if result.status not in _STATUS_VALUES:
        raise AgreementHarnessError(f"unsupported lean_observed_status: {result.status!r}")
    return result.status


def _build_rows_for_fixture(
    *,
    fixture: AgreementFixture,
    proof_semantics_version: str,
    run_request: Callable[[LeanRequest], LeanResult],
) -> list[AgreementReportRow]:
    requests = build_obligation_requests(
        theorem_prefix=fixture.theorem_prefix,
        inputs=_coerce_fixture_inputs(fixture.inputs, fixture_id=fixture.fixture_id),
        semantics_version=proof_semantics_version,
    )
    requests_by_kind = {str(req.obligation_kind): req for req in requests}
    if set(requests_by_kind.keys()) != set(OBLIGATION_KINDS):
        raise AgreementHarnessError(
            "obligation-kind drift in request generation: "
            f"expected={sorted(OBLIGATION_KINDS)} observed={sorted(requests_by_kind.keys())}"
        )

    rows: list[AgreementReportRow] = []
    for obligation_kind in sorted(OBLIGATION_KINDS):
        request = requests_by_kind[obligation_kind]
        theorem_id_expected = f"{fixture.theorem_prefix}_{obligation_kind}"
        if request.theorem_id != theorem_id_expected:
            raise AgreementHarnessError(
                f"theorem_id drift for {fixture.fixture_id}:{obligation_kind}: "
                f"{request.theorem_id!r} != {theorem_id_expected!r}"
            )
        inputs_hash = _require_request_metadata_hash(
            request=request,
            key="inputs_hash",
            fixture_id=fixture.fixture_id,
            obligation_kind=obligation_kind,
        )
        theorem_src_hash = _require_request_metadata_hash(
            request=request,
            key="theorem_src_hash",
            fixture_id=fixture.fixture_id,
            obligation_kind=obligation_kind,
        )

        result = run_request(request)
        observed_status = _validate_result_status(result)
        proof_hash = _require_hex64(result.proof_hash, field_name="proof_hash")
        mapping_id = build_proof_mapping_id(
            theorem_id=request.theorem_id,
            obligation_kind=obligation_kind,
            inputs_hash=inputs_hash,
            proof_semantics_version=proof_semantics_version,
            theorem_src_hash=theorem_src_hash,
        )

        python_expected = fixture.python_expected_status[obligation_kind]
        identity_consistent = (
            request.obligation_kind == obligation_kind
            and result.theorem_id == request.theorem_id
            and request.semantics_version == proof_semantics_version
        )
        agreement = python_expected == observed_status and identity_consistent
        rows.append(
            AgreementReportRow(
                fixture_id=fixture.fixture_id,
                theorem_prefix=fixture.theorem_prefix,
                obligation_kind=obligation_kind,
                inputs_hash=inputs_hash,
                mapping_id=mapping_id,
                python_expected_status=python_expected,
                lean_observed_status=observed_status,
                agreement=agreement,
                proof_hash=proof_hash,
            )
        )
    return rows


def build_agreement_report(
    *,
    fixture_bundle: AgreementFixtureBundle,
    timeout_ms: int,
    lean_bin: str,
    lake_bin: str = "lake",
    project_root: Path | None = None,
    run_request: Callable[[LeanRequest], LeanResult] | None = None,
) -> dict[str, Any]:
    if timeout_ms <= 0:
        raise AgreementHarnessError("timeout_ms must be positive")

    if run_request is None:
        def run_request_fn(request: LeanRequest) -> LeanResult:
            return run_lean_request(
                request=request,
                timeout_ms=timeout_ms,
                lean_bin=lean_bin,
                lake_bin=lake_bin,
                project_root=project_root,
            )
    else:
        run_request_fn = run_request

    rows: list[AgreementReportRow] = []
    for fixture in sorted(fixture_bundle.fixtures, key=lambda item: item.fixture_id):
        rows.extend(
            _build_rows_for_fixture(
                fixture=fixture,
                proof_semantics_version=fixture_bundle.proof_semantics_version,
                run_request=run_request_fn,
            )
        )

    sorted_rows = sorted(rows, key=lambda row: (row.fixture_id, row.obligation_kind))
    disagree_rows = sum(1 for row in sorted_rows if not row.agreement)
    total_rows = len(sorted_rows)
    summary = AgreementReportSummary(
        total_rows=total_rows,
        agree_rows=total_rows - disagree_rows,
        disagree_rows=disagree_rows,
        all_agree=disagree_rows == 0,
        fail_closed=disagree_rows > 0,
    )
    report = AgreementReport(
        schema=AGREEMENT_REPORT_SCHEMA,
        proof_semantics_version=fixture_bundle.proof_semantics_version,
        fixtures=sorted_rows,
        summary=summary,
    )
    return report.model_dump(mode="json", by_alias=True)


def build_agreement_report_from_fixture_path(
    *,
    fixture_path: Path | str,
    timeout_ms: int,
    lean_bin: str,
    lake_bin: str = "lake",
    project_root: Path | None = None,
    run_request: Callable[[LeanRequest], LeanResult] | None = None,
) -> dict[str, Any]:
    fixture_bundle = load_agreement_fixture_bundle(fixture_path)
    return build_agreement_report(
        fixture_bundle=fixture_bundle,
        timeout_ms=timeout_ms,
        lean_bin=lean_bin,
        lake_bin=lake_bin,
        project_root=project_root,
        run_request=run_request,
    )


def validate_agreement_report(payload: Any) -> dict[str, Any]:
    try:
        report = AgreementReport.model_validate(payload)
    except ValidationError as exc:
        raise AgreementHarnessError(f"schema-invalid agreement report: {exc}") from exc
    return report.model_dump(mode="json", by_alias=True)
