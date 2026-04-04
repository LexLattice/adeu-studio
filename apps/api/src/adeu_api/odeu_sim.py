from __future__ import annotations

from typing import Any, Literal

from adeu_odeu_sim import (
    ADEU_ODEU_METRIC_POINT_SCHEMA,
    CANONICAL_REPLAY_HORIZON,
    MetricPoint,
    ScenarioConfig,
    run_canonical_scenario,
    summarize_action_counts,
    summarize_lane_state,
)
from fastapi import APIRouter, Body
from pydantic import BaseModel, ConfigDict, Field, model_validator

from .hashing import sha256_canonical_json

ODEU_RUN_REQUEST_SCHEMA = "adeu_odeu_run_request@1"
ODEU_RUN_SUMMARY_SCHEMA = "adeu_odeu_run_summary@1"
ODEU_RUN_RESPONSE_SCHEMA = "adeu_odeu_run_response@1"
ODEU_RUN_PATH = "/odeu-sim/run"
V51A_KERNEL_CONTRACT_REF = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS124.md#v124-continuation-contract-machine-checkable"
)
INVALID_REQUEST_REF = "artifact:odeu_run_request:invalid_request"
FAILURE_CODE_INVALID_REQUEST = "ODEU_SIM_INVALID_REQUEST"
FAILURE_CODE_KERNEL_MISMATCH = "ODEU_SIM_KERNEL_MISMATCH"
RELEASED_SCENARIO_NAMES: tuple[str, ...] = ("healthy_baseline", "weak_d")
OUTPUT_MODE_SUMMARY_ONLY_JSON = "summary_only_json"
REQUEST_STATUS_COMPLETED = "completed_clean"
REQUEST_STATUS_INVALID = "fail_closed_invalid_request"
REQUEST_STATUS_KERNEL_MISMATCH = "fail_closed_kernel_mismatch"
LANE_SUMMARY_KEYS: tuple[str, ...] = (
    "mean_legitimacy_belief",
    "mean_uncertainty",
    "mean_resources",
)

router = APIRouter(tags=["odeu-sim"])


class OdeuRunRouteError(Exception):
    def __init__(self, *, failure_code: str, request_ref: str = INVALID_REQUEST_REF) -> None:
        super().__init__(failure_code)
        self.failure_code = failure_code
        self.request_ref = request_ref


class OdeuRunMeta(BaseModel):
    model_config = ConfigDict(extra="forbid")

    scenario: str
    seed: int
    turn: int
    regime_label: str


class OdeuRunLaneSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    mean_legitimacy_belief: float
    mean_uncertainty: float
    mean_resources: float


class OdeuRunRequestArtifact(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal[ODEU_RUN_REQUEST_SCHEMA] = ODEU_RUN_REQUEST_SCHEMA
    scenario_name: Literal["healthy_baseline", "weak_d"]
    seed: int
    steps: int
    output_mode: Literal["summary_only_json"]
    request_hash: str = Field(
        default="",
        min_length=64,
        max_length=64,
        pattern=r"^[a-f0-9]{64}$",
    )

    @model_validator(mode="after")
    def _validate_and_hash(self) -> OdeuRunRequestArtifact:
        if self.seed < 0:
            raise ValueError("seed must be non-negative")
        if self.steps < 1 or self.steps > CANONICAL_REPLAY_HORIZON:
            raise ValueError(f"steps must be between 1 and {CANONICAL_REPLAY_HORIZON}")
        expected_hash = compute_odeu_run_request_hash(
            scenario_name=self.scenario_name,
            seed=self.seed,
            steps=self.steps,
            output_mode=self.output_mode,
        )
        if self.request_hash and self.request_hash != expected_hash:
            raise ValueError("request_hash does not match the frozen request hash subject")
        self.request_hash = expected_hash
        return self


class OdeuRunSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal[ODEU_RUN_SUMMARY_SCHEMA] = ODEU_RUN_SUMMARY_SCHEMA
    meta: OdeuRunMeta
    config_snapshot: ScenarioConfig
    scenario: str
    seed: int
    turn: int
    current_metric: MetricPoint
    lane_summary: OdeuRunLaneSummary
    action_counts: dict[str, int]
    event_record_count: int
    evidence_record_count: int
    sanction_event_count: int

    @model_validator(mode="after")
    def _validate_projection(self) -> OdeuRunSummary:
        if self.meta.scenario != self.scenario:
            raise ValueError("meta.scenario must match scenario")
        if self.meta.seed != self.seed:
            raise ValueError("meta.seed must match seed")
        if self.meta.turn != self.turn:
            raise ValueError("meta.turn must match turn")
        if self.meta.regime_label != self.current_metric.regime_label:
            raise ValueError("meta.regime_label must match current_metric.regime_label")
        if self.config_snapshot.name != self.scenario:
            raise ValueError("config_snapshot.name must match scenario")
        if tuple(self.lane_summary.model_dump(mode="json").keys()) != LANE_SUMMARY_KEYS:
            raise ValueError("lane_summary must preserve the frozen key order")
        if list(self.action_counts.keys()) != sorted(self.action_counts):
            raise ValueError("action_counts must be sorted by action name")
        if any(count <= 0 for count in self.action_counts.values()):
            raise ValueError("action_counts must omit zero-count action types")
        return self


class OdeuRunResponse(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal[ODEU_RUN_RESPONSE_SCHEMA] = ODEU_RUN_RESPONSE_SCHEMA
    request_status: Literal[
        "completed_clean",
        "fail_closed_invalid_request",
        "fail_closed_kernel_mismatch",
    ]
    request_ref: str
    kernel_contract_ref: str = V51A_KERNEL_CONTRACT_REF
    run_summary: OdeuRunSummary | None = None
    failure_code: str | None = None
    response_hash: str = Field(
        default="",
        min_length=64,
        max_length=64,
        pattern=r"^[a-f0-9]{64}$",
    )

    @model_validator(mode="after")
    def _validate_and_hash(self) -> OdeuRunResponse:
        if self.request_status == REQUEST_STATUS_COMPLETED:
            if self.run_summary is None or self.failure_code is not None:
                raise ValueError("completed_clean responses require run_summary only")
        else:
            if self.run_summary is not None or not self.failure_code:
                raise ValueError("fail-closed responses require failure_code only")
        expected_hash = compute_odeu_run_response_hash(
            request_status=self.request_status,
            request_ref=self.request_ref,
            kernel_contract_ref=self.kernel_contract_ref,
            run_summary=self.run_summary,
            failure_code=self.failure_code,
        )
        if self.response_hash and self.response_hash != expected_hash:
            raise ValueError("response_hash does not match the frozen response hash subject")
        self.response_hash = expected_hash
        return self


def compute_odeu_run_request_hash(
    *,
    scenario_name: str,
    seed: int,
    steps: int,
    output_mode: str,
) -> str:
    return sha256_canonical_json(
        {
            "scenario_name": scenario_name,
            "seed": seed,
            "steps": steps,
            "output_mode": output_mode,
        }
    )


def compute_odeu_run_response_hash(
    *,
    request_status: str,
    request_ref: str,
    kernel_contract_ref: str,
    run_summary: OdeuRunSummary | None,
    failure_code: str | None,
) -> str:
    return sha256_canonical_json(
        {
            "request_status": request_status,
            "request_ref": request_ref,
            "kernel_contract_ref": kernel_contract_ref,
            "run_summary": (
                run_summary.model_dump(mode="json", by_alias=True)
                if run_summary is not None
                else None
            ),
            "failure_code": failure_code,
        }
    )


def _request_ref(request_hash: str) -> str:
    return f"artifact:odeu_run_request:{request_hash}"


def _build_request_artifact(raw_request: Any) -> OdeuRunRequestArtifact:
    if not isinstance(raw_request, dict):
        raise OdeuRunRouteError(failure_code=FAILURE_CODE_INVALID_REQUEST)
    if set(raw_request) != {"scenario_name", "seed", "steps", "output_mode"}:
        raise OdeuRunRouteError(failure_code=FAILURE_CODE_INVALID_REQUEST)

    scenario_name = raw_request["scenario_name"]
    seed = raw_request["seed"]
    steps = raw_request["steps"]
    output_mode = raw_request["output_mode"]

    if not isinstance(scenario_name, str) or scenario_name not in RELEASED_SCENARIO_NAMES:
        raise OdeuRunRouteError(failure_code=FAILURE_CODE_INVALID_REQUEST)
    if not isinstance(seed, int) or isinstance(seed, bool) or seed < 0:
        raise OdeuRunRouteError(failure_code=FAILURE_CODE_INVALID_REQUEST)
    if (
        not isinstance(steps, int)
        or isinstance(steps, bool)
        or steps < 1
        or steps > CANONICAL_REPLAY_HORIZON
    ):
        raise OdeuRunRouteError(failure_code=FAILURE_CODE_INVALID_REQUEST)
    if output_mode != OUTPUT_MODE_SUMMARY_ONLY_JSON:
        raise OdeuRunRouteError(failure_code=FAILURE_CODE_INVALID_REQUEST)

    return OdeuRunRequestArtifact(
        scenario_name=scenario_name,
        seed=seed,
        steps=steps,
        output_mode=output_mode,
    )


def _build_run_summary(*, request: OdeuRunRequestArtifact) -> OdeuRunSummary:
    world = run_canonical_scenario(
        request.scenario_name,
        seed=request.seed,
        steps=request.steps,
    )
    current_metric = world.metrics_history[-1]
    lane_summary = summarize_lane_state(world)
    action_counts = summarize_action_counts(world)

    if world.scenario != request.scenario_name:
        raise OdeuRunRouteError(
            failure_code=FAILURE_CODE_KERNEL_MISMATCH,
            request_ref=_request_ref(request.request_hash),
        )
    if world.seed != request.seed or world.turn != request.steps:
        raise OdeuRunRouteError(
            failure_code=FAILURE_CODE_KERNEL_MISMATCH,
            request_ref=_request_ref(request.request_hash),
        )
    if current_metric.schema != ADEU_ODEU_METRIC_POINT_SCHEMA:
        raise OdeuRunRouteError(
            failure_code=FAILURE_CODE_KERNEL_MISMATCH,
            request_ref=_request_ref(request.request_hash),
        )
    if tuple(lane_summary.keys()) != LANE_SUMMARY_KEYS:
        raise OdeuRunRouteError(
            failure_code=FAILURE_CODE_KERNEL_MISMATCH,
            request_ref=_request_ref(request.request_hash),
        )
    if list(action_counts.keys()) != sorted(action_counts):
        raise OdeuRunRouteError(
            failure_code=FAILURE_CODE_KERNEL_MISMATCH,
            request_ref=_request_ref(request.request_hash),
        )
    if any(count <= 0 for count in action_counts.values()):
        raise OdeuRunRouteError(
            failure_code=FAILURE_CODE_KERNEL_MISMATCH,
            request_ref=_request_ref(request.request_hash),
        )

    return OdeuRunSummary(
        meta=OdeuRunMeta(
            scenario=world.scenario,
            seed=world.seed,
            turn=world.turn,
            regime_label=current_metric.regime_label,
        ),
        config_snapshot=world.config,
        scenario=world.scenario,
        seed=world.seed,
        turn=world.turn,
        current_metric=current_metric,
        lane_summary=OdeuRunLaneSummary.model_validate(lane_summary),
        action_counts=action_counts,
        event_record_count=len(world.event_records),
        evidence_record_count=len(world.evidence_records),
        sanction_event_count=len(world.sanction_events),
    )


def build_odeu_run_response(raw_request: Any) -> OdeuRunResponse:
    try:
        request = _build_request_artifact(raw_request)
        summary = _build_run_summary(request=request)
    except OdeuRunRouteError as exc:
        return OdeuRunResponse(
            request_status=(
                REQUEST_STATUS_INVALID
                if exc.failure_code == FAILURE_CODE_INVALID_REQUEST
                else REQUEST_STATUS_KERNEL_MISMATCH
            ),
            request_ref=exc.request_ref,
            failure_code=exc.failure_code,
        )

    return OdeuRunResponse(
        request_status=REQUEST_STATUS_COMPLETED,
        request_ref=_request_ref(request.request_hash),
        run_summary=summary,
    )


@router.post(ODEU_RUN_PATH, response_model=OdeuRunResponse)
def odeu_run_route(raw_request: Any = Body(...)) -> OdeuRunResponse:
    return build_odeu_run_response(raw_request)
