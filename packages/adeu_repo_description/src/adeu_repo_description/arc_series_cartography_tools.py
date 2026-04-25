from __future__ import annotations

import re
from copy import deepcopy
from pathlib import Path
from typing import Literal

from pydantic import Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .arc_series_cartography import (
    ClaimHorizon,
    CoordinatePosture,
    NamespaceKind,
    RepoRecursiveCoordinatePlanRow,
    ToolApplicabilityPosture,
    _CartographyBase,
    _non_empty,
    _reject_authority_laundering,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)

REPO_ARC_CARTOGRAPHY_TOOL_RUN_EVIDENCE_SCHEMA = (
    "repo_arc_cartography_tool_run_evidence@1"
)

CwdPosture = Literal["repo_root", "repo_subdir", "not_run_no_cwd"]
GapResolutionPosture = Literal[
    "open_carried_forward",
    "lawfully_resolved",
    "deferred_to_family_closeout",
]

_GLOBAL_PROOF_RE = re.compile(r"(?<![-\w])global(?:ly)?\b", re.IGNORECASE)
_FUTURE_V_FAMILY_RE = re.compile(
    r"(^|[:/])V(?:69|[7-9][0-9]|[1-9][0-9]{2,})(?:$|[^0-9])"
)
_V67_FAMILY_RE = re.compile(r"(^|[:/])V67(?:$|[^0-9])")


def _contains_arc_argument(command: list[str], arc: str) -> bool:
    return any(part == f"ARC={arc}" or part == arc for part in command)


def _is_v67_family_target(*, target_claim_id: str, target_namespace_kind: NamespaceKind) -> bool:
    return (
        target_namespace_kind in {"family_id", "family_slice_id"}
        and _V67_FAMILY_RE.search(target_claim_id) is not None
    )


def _is_future_lifecycle_target(value: str) -> bool:
    return _FUTURE_V_FAMILY_RE.search(value) is not None


class RepoArcCartographyToolRunRow(_CartographyBase):
    tool_invocation_ref: str
    tool_id: str
    command: list[str] = Field(min_length=1)
    cwd_posture: CwdPosture
    target_claim_id: str
    target_namespace_kind: NamespaceKind
    claim_horizon: ClaimHorizon
    observed_output_ref: str | None = None
    exit_status: int | None = None
    applicability_posture: ToolApplicabilityPosture
    limitation_note: str
    recommended_followup: str

    @model_validator(mode="after")
    def _validate_tool_run(self) -> RepoArcCartographyToolRunRow:
        object.__setattr__(
            self,
            "tool_invocation_ref",
            _non_empty(self.tool_invocation_ref, field_name="tool_invocation_ref"),
        )
        object.__setattr__(self, "tool_id", _non_empty(self.tool_id, field_name="tool_id"))
        object.__setattr__(
            self,
            "command",
            [_non_empty(part, field_name="command") for part in self.command],
        )
        object.__setattr__(
            self,
            "target_claim_id",
            _non_empty(self.target_claim_id, field_name="target_claim_id"),
        )
        if self.observed_output_ref is not None:
            object.__setattr__(
                self,
                "observed_output_ref",
                _repo_ref(self.observed_output_ref, field_name="observed_output_ref"),
            )
        object.__setattr__(
            self,
            "limitation_note",
            _non_empty(self.limitation_note, field_name="limitation_note"),
        )
        object.__setattr__(
            self,
            "recommended_followup",
            _reject_authority_laundering(
                self.recommended_followup, field_name="recommended_followup"
            ),
        )

        if self.applicability_posture == "not_run":
            if self.exit_status is not None or self.observed_output_ref is not None:
                raise ValueError("not_run tool rows cannot carry exit_status or output refs")
            if self.cwd_posture != "not_run_no_cwd":
                raise ValueError("not_run tool rows require cwd_posture = not_run_no_cwd")
            return self

        if self.exit_status is None or self.observed_output_ref is None:
            raise ValueError("run-bearing tool rows require exit_status and observed_output_ref")
        if self.cwd_posture == "not_run_no_cwd":
            raise ValueError("run-bearing tool rows cannot use not_run_no_cwd")
        if self.applicability_posture in {
            "applicable_and_supporting",
            "applicable_with_warnings",
            "namespace_limited",
        } and self.exit_status != 0:
            raise ValueError("supporting or namespace-limited tool rows require exit_status 0")
        if self.applicability_posture == "failed_or_inconclusive" and self.exit_status == 0:
            raise ValueError("failed_or_inconclusive tool rows require non-zero exit_status")
        if (
            self.applicability_posture == "applicable_and_supporting"
            and (
                _GLOBAL_PROOF_RE.search(self.target_claim_id)
                or _GLOBAL_PROOF_RE.search(self.limitation_note)
            )
        ):
            raise ValueError("passing tool result cannot be used as global proof")
        if _contains_arc_argument(self.command, "67") and _is_v67_family_target(
            target_claim_id=self.target_claim_id,
            target_namespace_kind=self.target_namespace_kind,
        ):
            raise ValueError("ARC=67 tool results cannot prove family V67 claims")
        if (
            self.claim_horizon in {"lock_authorized", "closeout_evidence"}
            and self.observed_output_ref.startswith("docs/support/")
        ):
            raise ValueError("support docs cannot become closeout evidence through tool results")
        return self


class RepoArcCartographyGapResolutionRow(_CartographyBase):
    gap_id: str
    resolution_posture: GapResolutionPosture
    source_tool_invocation_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_gap_resolution(self) -> RepoArcCartographyGapResolutionRow:
        object.__setattr__(self, "gap_id", _non_empty(self.gap_id, field_name="gap_id"))
        object.__setattr__(
            self,
            "source_tool_invocation_refs",
            _sorted_unique(
                self.source_tool_invocation_refs, field_name="source_tool_invocation_refs"
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _non_empty(self.limitation_note, field_name="limitation_note"),
        )
        if self.resolution_posture == "lawfully_resolved" and not self.source_tool_invocation_refs:
            raise ValueError("lawfully_resolved gap rows require source tool refs")
        return self


class RepoArcCartographyToolRunEvidence(_CartographyBase):
    schema: Literal["repo_arc_cartography_tool_run_evidence@1"] = (
        REPO_ARC_CARTOGRAPHY_TOOL_RUN_EVIDENCE_SCHEMA
    )
    tool_run_evidence_id: str
    cartography_id: str
    snapshot_id: str
    coverage_horizon: str
    expected_tool_invocation_refs: list[str] = Field(min_length=1)
    known_cartography_refs: list[str] = Field(min_length=1)
    v68b_gap_refs: list[str] = Field(min_length=1)
    coordinate_posture: CoordinatePosture
    tool_run_rows: list[RepoArcCartographyToolRunRow] = Field(min_length=1)
    coordinate_plan_rows: list[RepoRecursiveCoordinatePlanRow] = Field(default_factory=list)
    gap_resolution_rows: list[RepoArcCartographyGapResolutionRow] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_tool_run_evidence(self) -> RepoArcCartographyToolRunEvidence:
        object.__setattr__(
            self,
            "tool_run_evidence_id",
            _non_empty(self.tool_run_evidence_id, field_name="tool_run_evidence_id"),
        )
        object.__setattr__(
            self, "cartography_id", _non_empty(self.cartography_id, field_name="cartography_id")
        )
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self,
            "coverage_horizon",
            _non_empty(self.coverage_horizon, field_name="coverage_horizon"),
        )
        object.__setattr__(
            self,
            "expected_tool_invocation_refs",
            _sorted_unique(
                self.expected_tool_invocation_refs, field_name="expected_tool_invocation_refs"
            ),
        )
        object.__setattr__(
            self,
            "known_cartography_refs",
            _sorted_unique(self.known_cartography_refs, field_name="known_cartography_refs"),
        )
        object.__setattr__(
            self,
            "v68b_gap_refs",
            _sorted_unique(self.v68b_gap_refs, field_name="v68b_gap_refs"),
        )
        object.__setattr__(
            self,
            "tool_run_rows",
            _sorted_unique_by_ref(
                self.tool_run_rows, attr="tool_invocation_ref", field_name="tool_run_rows"
            ),
        )
        object.__setattr__(
            self,
            "coordinate_plan_rows",
            _sorted_unique_by_ref(
                self.coordinate_plan_rows,
                attr="coordinate_ref",
                field_name="coordinate_plan_rows",
            ),
        )
        object.__setattr__(
            self,
            "gap_resolution_rows",
            _sorted_unique_by_ref(
                self.gap_resolution_rows,
                attr="gap_id",
                field_name="gap_resolution_rows",
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _reject_authority_laundering(self.limitation_note, field_name="limitation_note"),
        )

        tool_refs = {row.tool_invocation_ref for row in self.tool_run_rows}
        missing_tools = sorted(set(self.expected_tool_invocation_refs) - tool_refs)
        if missing_tools:
            raise ValueError(f"expected tool invocations must be explicit: {missing_tools}")

        gap_rows_by_id = {row.gap_id: row for row in self.gap_resolution_rows}
        missing_gap_rows = sorted(set(self.v68b_gap_refs) - set(gap_rows_by_id))
        if missing_gap_rows:
            raise ValueError(
                "V68-B gap refs require resolution or carry-forward rows: "
                f"{missing_gap_rows}"
            )

        for row in self.gap_resolution_rows:
            unknown_tool_refs = sorted(set(row.source_tool_invocation_refs) - tool_refs)
            if unknown_tool_refs:
                raise ValueError(
                    "gap resolution source tool refs must reference known tool rows: "
                    f"{unknown_tool_refs}"
                )

        if self.coordinate_posture == "coordinate_emitted":
            if not self.coordinate_plan_rows:
                raise ValueError("coordinate emitted posture requires coordinate plan rows")
            for row in self.coordinate_plan_rows:
                if row.coordinate_posture != "coordinate_emitted":
                    raise ValueError(
                        "coordinate emitted posture cannot include coordinate absence rows"
                    )
                if not row.target_refs:
                    raise ValueError("emitted coordinate rows require target_refs")
        else:
            if not self.coordinate_plan_rows:
                raise ValueError("coordinate absence must be represented by coordinate plan rows")
            for row in self.coordinate_plan_rows:
                if row.coordinate_posture == "coordinate_emitted":
                    raise ValueError(
                        f"{self.coordinate_posture} posture cannot include "
                        "coordinate emitted rows"
                    )

        known_refs = set(self.known_cartography_refs) | tool_refs | set(self.v68b_gap_refs)
        for row in self.coordinate_plan_rows:
            if "odeu_conceptual_diff_report@1" in row.target_refs:
                raise ValueError("coordinate rows cannot admit odeu_conceptual_diff_report@1")
            future_targets = sorted(
                ref for ref in row.target_refs if _is_future_lifecycle_target(ref)
            )
            if future_targets:
                raise ValueError(
                    "coordinate rows cannot authorize future V-family targets beyond V68: "
                    f"{future_targets}"
                )
            unknown_targets = sorted(set(row.target_refs) - known_refs)
            if unknown_targets:
                raise ValueError(
                    "coordinate target_refs must reference known cartography rows: "
                    f"{unknown_targets}"
                )
        return self


V68C_DEFAULT_EXPECTED_TOOL_INVOCATION_REFS: tuple[str, ...] = (
    "tool-run:arc-closeout-check:ARC=67",
    "tool-run:coordinate-emission-probe",
    "tool-run:make-check:v68b",
    "tool-run:recursive-coordinate-lint:not-run",
)

V68C_DEFAULT_GAP_REFS: tuple[str, ...] = (
    "gap:coordinate_posture_absent:V68-B",
    "gap:review_required_ambiguous_derivation:historical_fullness",
    "gap:tool_applicability_unassessed:V68-C",
)


def _tool_run_evidence_id(payload_without_id: dict[str, object]) -> str:
    payload = deepcopy(payload_without_id)
    payload.setdefault("schema", REPO_ARC_CARTOGRAPHY_TOOL_RUN_EVIDENCE_SCHEMA)
    payload.pop("tool_run_evidence_id", None)
    digest = sha256_canonical_json(payload)
    return f"repo_arc_cartography_tool_run_evidence_{digest[:24]}"


def _require_existing_repo_refs(*, repo_root: Path, refs: list[str]) -> None:
    missing = sorted(ref for ref in refs if not (repo_root / ref).is_file())
    if missing:
        raise ValueError(f"expected V68-C observed output refs are missing: {missing}")


def derive_v68c_repo_arc_cartography_tool_run_evidence(
    *,
    repo_root: Path,
) -> RepoArcCartographyToolRunEvidence:
    observed_output_refs = [
        "apps/api/fixtures/repo_description/vnext_plus189/repo_arc_cartography_gap_scan_report_v189_reference.json",
        "artifacts/agent_harness/v189/evidence_inputs/v68b_arc_series_cartography_derivation_evidence_v189.json",
        "artifacts/stop_gate/metrics_v189_closeout.json",
    ]
    _require_existing_repo_refs(repo_root=repo_root, refs=observed_output_refs)

    tool_run_rows = [
        RepoArcCartographyToolRunRow(
            tool_invocation_ref="tool-run:arc-closeout-check:ARC=67",
            tool_id="tool:arc-closeout-check",
            command=["make", "arc-closeout-check", "ARC=67"],
            cwd_posture="repo_root",
            target_claim_id="implementation_arc:vNext+67",
            target_namespace_kind="implementation_arc_id",
            claim_horizon="descriptive_support",
            observed_output_ref="artifacts/stop_gate/metrics_v189_closeout.json",
            exit_status=0,
            applicability_posture="namespace_limited",
            limitation_note=(
                "ARC=67 checks the global implementation arc namespace only; "
                "it is not evidence for family V67."
            ),
            recommended_followup="Keep family and implementation arc namespaces separate.",
        ),
        RepoArcCartographyToolRunRow(
            tool_invocation_ref="tool-run:coordinate-emission-probe",
            tool_id="tool:recursive-coordinate-lint",
            command=["make", "recursive-coordinate-lint", "ARC=190"],
            cwd_posture="repo_root",
            target_claim_id="coordinate:V68-C",
            target_namespace_kind="evidence_arc_id",
            claim_horizon="review_pending",
            observed_output_ref=(
                "apps/api/fixtures/repo_description/vnext_plus189/"
                "repo_arc_cartography_gap_scan_report_v189_reference.json"
            ),
            exit_status=1,
            applicability_posture="failed_or_inconclusive",
            limitation_note="No released recursive-coordinate lint exists for V68-C yet.",
            recommended_followup="Carry deliberate coordinate absence into the V68-C output.",
        ),
        RepoArcCartographyToolRunRow(
            tool_invocation_ref="tool-run:make-check:v68b",
            tool_id="tool:make-check",
            command=["make", "check"],
            cwd_posture="repo_root",
            target_claim_id="slice:V68-B",
            target_namespace_kind="family_slice_id",
            claim_horizon="closeout_evidence",
            observed_output_ref=(
                "artifacts/agent_harness/v189/evidence_inputs/"
                "v68b_arc_series_cartography_derivation_evidence_v189.json"
            ),
            exit_status=0,
            applicability_posture="applicable_and_supporting",
            limitation_note="Supports the bounded V68-B implementation slice only.",
            recommended_followup="Use V68-B as released basis for V68-C hardening.",
        ),
        RepoArcCartographyToolRunRow(
            tool_invocation_ref="tool-run:recursive-coordinate-lint:not-run",
            tool_id="tool:recursive-coordinate-lint",
            command=["make", "recursive-coordinate-lint", "ARC=190"],
            cwd_posture="not_run_no_cwd",
            target_claim_id="coordinate:V68-C",
            target_namespace_kind="evidence_arc_id",
            claim_horizon="review_pending",
            observed_output_ref=None,
            exit_status=None,
            applicability_posture="not_run",
            limitation_note="No released V68-C recursive-coordinate lint entrypoint is available.",
            recommended_followup="Represent coordinate absence deliberately.",
        ),
    ]
    coordinate_plan_rows = [
        RepoRecursiveCoordinatePlanRow(
            coordinate_ref="coordinate:V68-C-deliberate-absence",
            coordinate_posture="coordinate_absent_deliberate",
            target_refs=[],
            non_authority_guardrail=(
                "Records deliberate coordinate absence only; later coordinate emission "
                "needs its own selected lock surface."
            ),
        )
    ]
    gap_resolution_rows = [
        RepoArcCartographyGapResolutionRow(
            gap_id="gap:coordinate_posture_absent:V68-B",
            resolution_posture="open_carried_forward",
            source_tool_invocation_refs=[
                "tool-run:coordinate-emission-probe",
                "tool-run:recursive-coordinate-lint:not-run",
            ],
            limitation_note="Coordinate absence remains deliberate until V68-C closeout.",
        ),
        RepoArcCartographyGapResolutionRow(
            gap_id="gap:review_required_ambiguous_derivation:historical_fullness",
            resolution_posture="open_carried_forward",
            source_tool_invocation_refs=["tool-run:make-check:v68b"],
            limitation_note="Historical fullness remains review-required for family closeout.",
        ),
        RepoArcCartographyGapResolutionRow(
            gap_id="gap:tool_applicability_unassessed:V68-C",
            resolution_posture="lawfully_resolved",
            source_tool_invocation_refs=[
                "tool-run:arc-closeout-check:ARC=67",
                "tool-run:coordinate-emission-probe",
                "tool-run:make-check:v68b",
                "tool-run:recursive-coordinate-lint:not-run",
            ],
            limitation_note="V68-C tool applicability is represented as scoped evidence rows.",
        ),
    ]
    payload = {
        "schema": REPO_ARC_CARTOGRAPHY_TOOL_RUN_EVIDENCE_SCHEMA,
        "cartography_id": "repo_arc_series_cartography_v68c_tool_run_seed",
        "snapshot_id": "vNext+190-prestart-on-main",
        "coverage_horizon": "V68-C starter tool-run evidence and coordinate posture seed",
        "expected_tool_invocation_refs": sorted(V68C_DEFAULT_EXPECTED_TOOL_INVOCATION_REFS),
        "known_cartography_refs": [
            "coordinate:V68-C",
            "family:V68",
            "family:V68-C",
            "implementation_arc:vNext+67",
            "slice:V68-B",
        ],
        "v68b_gap_refs": sorted(V68C_DEFAULT_GAP_REFS),
        "coordinate_posture": "coordinate_absent_deliberate",
        "tool_run_rows": [
            row.model_dump(mode="json")
            for row in sorted(tool_run_rows, key=lambda row: row.tool_invocation_ref)
        ],
        "coordinate_plan_rows": [row.model_dump(mode="json") for row in coordinate_plan_rows],
        "gap_resolution_rows": [
            row.model_dump(mode="json")
            for row in sorted(gap_resolution_rows, key=lambda row: row.gap_id)
        ],
        "limitation_note": (
            "Descriptive V68-C tool-run evidence only; later action requires separate planning."
        ),
    }
    payload["tool_run_evidence_id"] = _tool_run_evidence_id(payload)
    return RepoArcCartographyToolRunEvidence.model_validate(payload)
