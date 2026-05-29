from __future__ import annotations

import os
import subprocess
from hashlib import sha256
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, Field, model_validator

from .brl_0a import (
    MODEL_CONFIG,
    ObservationSurfaceKind,
    ProtectedSurfaceKind,
    RepoBehavioralCanonicalizationProfile,
    RepoBehavioralObservationHash,
    RepoBehavioralProbeContract,
    RepoBehavioralReplayManifest,
    RepoBehavioralReplayManifestValidationReport,
    _assert_non_empty_text,
    _assert_sha256,
    _assert_sorted_unique,
    _assert_unique_rows,
    canonical_hash,
    suite_root_hash_for,
)

REPO_BEHAVIORAL_REPLAY_EXECUTION_REPORT_SCHEMA = (
    "repo_behavioral_replay_execution_report@1"
)
REPO_BEHAVIORAL_OBSERVATION_RECORD_SCHEMA = "repo_behavioral_observation_record@1"
REPO_BEHAVIORAL_REGRESSION_DIFF_SCHEMA = "repo_behavioral_regression_diff@1"
REPO_BEHAVIORAL_SUITE_ROOT_HASH_REPORT_SCHEMA = (
    "repo_behavioral_suite_root_hash_report@1"
)

ReplayExecutionStatus = Literal[
    "completed",
    "completed_with_diffs",
    "blocked_by_manifest_validation",
    "capture_failed",
]
ProbeExecutionStatus = Literal[
    "completed",
    "timeout",
    "capture_failed",
    "not_run",
    "blocked_by_manifest_validation",
    "fixture_mutation_forbidden",
]
TimeoutStatus = Literal["completed", "timed_out", "not_run"]
RegressionDiffStatus = Literal[
    "match",
    "diff",
    "missing_expected",
    "missing_actual",
    "capture_failed",
    "not_run",
    "blocked_by_manifest_validation",
]
ChangedSurfaceKind = Literal[
    "exit_code",
    "stdout",
    "stderr",
    "output_files",
    "fixture_tree",
    "process_state",
    "timeout",
]
DiffAuthorityPosture = Literal["diff_report_only_not_patch_authority"]
ReplayExecutionAuthorityPosture = Literal["replay_report_only_not_product_authority"]
SuiteRootAuthorityPosture = Literal["suite_hash_report_only_not_certificate"]
SuiteRootStatus = Literal["match", "diff", "blocked_by_manifest_validation", "capture_failed"]

_SURFACE_TO_DIFF_KIND: dict[str, ChangedSurfaceKind] = {
    "exit_code": "exit_code",
    "stdout": "stdout",
    "stderr": "stderr",
    "output_file_tree": "output_files",
    "process_state": "process_state",
    "timeout_status": "timeout",
}
_OBSERVATION_REQUIRED_RAW_SURFACES: dict[str, ObservationSurfaceKind] = {
    "stdout": "stdout",
    "stderr": "stderr",
    "output_file_tree": "output_file_tree",
    "process_state": "process_state",
    "timeout_status": "timeout_status",
}


class _BrlBBase(BaseModel):
    model_config = MODEL_CONFIG


def hash_bytes(payload: bytes, *, domain: str) -> str:
    domain_prefix = _assert_non_empty_text(domain, field_name="domain").encode("utf-8")
    digest = sha256(domain_prefix + b"\0" + payload).hexdigest()
    return f"sha256:{digest}"


def hash_text(payload: str, *, domain: str) -> str:
    return hash_bytes(payload.encode("utf-8"), domain=domain)


def _file_tree_snapshot(root: Path) -> tuple[str, dict[str, str]]:
    if not root.is_dir():
        raise ValueError(f"file tree root is not a directory: {root}")
    rows: list[dict[str, str]] = []
    for path in sorted(candidate for candidate in root.rglob("*") if candidate.is_file()):
        relative = path.relative_to(root).as_posix()
        rows.append(
            {
                "path": relative,
                "sha256": hash_bytes(path.read_bytes(), domain="file_tree:file"),
            }
        )
    tree_hash = canonical_hash(
        {"schema": "repo_behavioral_file_tree_hash@1", "rows": rows},
        object_kind="repo_behavioral_file_tree_hash",
    )
    return tree_hash, {row["path"]: row["sha256"] for row in rows}


def hash_file_tree(root: Path) -> str:
    tree_hash, _snapshot = _file_tree_snapshot(root)
    return tree_hash


class ProbeExecutionRow(_BrlBBase):
    probe_id: str
    probe_contract_hash: str | None = None
    execution_status: ProbeExecutionStatus
    argv: list[str] = Field(default_factory=list)
    cwd_ref: str
    env_delta_hash: str | None = None
    timeout_policy_ref: str
    fixture_tree_hash_before: str | None = None
    fixture_tree_hash_after_actual: str | None = None
    observation_record_ref: str | None = None
    diff_ref: str | None = None

    @model_validator(mode="after")
    def _validate_row(self) -> ProbeExecutionRow:
        for field_name in ("probe_id", "cwd_ref", "timeout_policy_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "argv",
            [_assert_non_empty_text(value, field_name="argv") for value in self.argv],
        )
        for field_name in (
            "probe_contract_hash",
            "env_delta_hash",
            "fixture_tree_hash_before",
            "fixture_tree_hash_after_actual",
        ):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(self, field_name, _assert_sha256(value, field_name=field_name))
        for field_name in ("observation_record_ref", "diff_ref"):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(
                    self,
                    field_name,
                    _assert_non_empty_text(value, field_name=field_name),
                )
        return self


class RepoBehavioralObservationRecord(_BrlBBase):
    schema: Literal[REPO_BEHAVIORAL_OBSERVATION_RECORD_SCHEMA]
    observation_record_ref: str
    probe_id: str
    probe_contract_hash: str
    raw_exit_code: int | None = None
    raw_stdout_ref: str | None = None
    raw_stderr_ref: str | None = None
    raw_file_tree_hash_after: str | None = None
    raw_process_state_ref: str | None = None
    timeout_status: TimeoutStatus
    canonicalization_profile_ref: str
    canonicalization_profile_hash: str
    canonical_stdout_hash: str | None = None
    canonical_stderr_hash: str | None = None
    canonical_file_tree_hash_after: str | None = None
    canonical_process_state_hash: str | None = None
    canonical_observation_hash: str | None = None

    @model_validator(mode="after")
    def _validate_record(self) -> RepoBehavioralObservationRecord:
        for field_name in (
            "observation_record_ref",
            "probe_id",
            "canonicalization_profile_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "probe_contract_hash",
            "canonicalization_profile_hash",
            "canonical_stdout_hash",
            "canonical_stderr_hash",
            "canonical_file_tree_hash_after",
            "canonical_process_state_hash",
            "canonical_observation_hash",
            "raw_file_tree_hash_after",
        ):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(self, field_name, _assert_sha256(value, field_name=field_name))
        for field_name in ("raw_stdout_ref", "raw_stderr_ref", "raw_process_state_ref"):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(
                    self,
                    field_name,
                    _assert_non_empty_text(value, field_name=field_name),
                )
        if self.canonical_observation_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_observation_record",
                canonicalization_profile_hash=self.canonicalization_profile_hash,
                drop_keys={"canonical_observation_hash"},
            )
            if self.canonical_observation_hash != expected:
                raise ValueError("canonical_observation_hash must match observation record")
        return self


class StructuredDiffRow(_BrlBBase):
    surface: ChangedSurfaceKind
    expected_value: str | int | None = None
    actual_value: str | int | None = None
    summary: str

    @model_validator(mode="after")
    def _validate_row(self) -> StructuredDiffRow:
        object.__setattr__(
            self,
            "summary",
            _assert_non_empty_text(self.summary, field_name="summary"),
        )
        return self


class RepoBehavioralRegressionDiff(_BrlBBase):
    schema: Literal[REPO_BEHAVIORAL_REGRESSION_DIFF_SCHEMA]
    diff_ref: str
    probe_id: str
    expected_observation_hash_ref: str
    expected_canonical_observation_hash: str | None = None
    actual_observation_record_ref: str | None = None
    actual_canonical_observation_hash: str | None = None
    diff_status: RegressionDiffStatus
    changed_surfaces: list[ChangedSurfaceKind] = Field(default_factory=list)
    structured_diff_rows: list[StructuredDiffRow] = Field(default_factory=list)
    authority_posture: DiffAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_diff(self) -> RepoBehavioralRegressionDiff:
        for field_name in ("diff_ref", "probe_id", "expected_observation_hash_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "expected_canonical_observation_hash",
            "actual_canonical_observation_hash",
        ):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(self, field_name, _assert_sha256(value, field_name=field_name))
        if self.actual_observation_record_ref is not None:
            object.__setattr__(
                self,
                "actual_observation_record_ref",
                _assert_non_empty_text(
                    self.actual_observation_record_ref,
                    field_name="actual_observation_record_ref",
                ),
            )
        object.__setattr__(
            self,
            "changed_surfaces",
            _assert_sorted_unique(self.changed_surfaces, field_name="changed_surfaces"),
        )
        if self.diff_status == "match" and (self.changed_surfaces or self.structured_diff_rows):
            raise ValueError("match diffs cannot declare changed surfaces")
        if self.diff_status == "diff" and not self.changed_surfaces:
            raise ValueError("diff status requires changed surfaces")
        if self.diff_status == "diff":
            diff_row_surfaces = {row.surface for row in self.structured_diff_rows}
            missing_rows = sorted(set(self.changed_surfaces) - diff_row_surfaces)
            if missing_rows:
                raise ValueError(f"changed surfaces missing structured diff rows: {missing_rows}")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_regression_diff",
                drop_keys={"canonical_output_hash"},
            )
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match regression diff payload")
        return self


class SuiteRootPerProbeHashRow(_BrlBBase):
    probe_id: str
    expected_observation_hash_ref: str
    expected_canonical_observation_hash: str | None = None
    actual_canonical_observation_hash: str | None = None
    diff_status: RegressionDiffStatus

    @model_validator(mode="after")
    def _validate_row(self) -> SuiteRootPerProbeHashRow:
        for field_name in ("probe_id", "expected_observation_hash_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "expected_canonical_observation_hash",
            "actual_canonical_observation_hash",
        ):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(self, field_name, _assert_sha256(value, field_name=field_name))
        return self


class RepoBehavioralSuiteRootHashReport(_BrlBBase):
    schema: Literal[REPO_BEHAVIORAL_SUITE_ROOT_HASH_REPORT_SCHEMA]
    suite_root_hash_report_ref: str
    manifest_id: str
    manifest_hash: str
    expected_suite_root_hash: str
    actual_suite_root_hash: str | None = None
    per_probe_hash_rows: list[SuiteRootPerProbeHashRow]
    suite_root_status: SuiteRootStatus
    authority_posture: SuiteRootAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoBehavioralSuiteRootHashReport:
        for field_name in ("suite_root_hash_report_ref", "manifest_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("manifest_hash", "expected_suite_root_hash", "actual_suite_root_hash"):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(self, field_name, _assert_sha256(value, field_name=field_name))
        _assert_unique_rows(
            self.per_probe_hash_rows,
            attr_name="probe_id",
            field_name="per_probe_hash_rows",
        )
        object.__setattr__(
            self,
            "per_probe_hash_rows",
            sorted(self.per_probe_hash_rows, key=lambda row: row.probe_id),
        )
        if self.authority_posture != "suite_hash_report_only_not_certificate":
            raise ValueError("suite-root report cannot claim certificate authority")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_suite_root_hash_report",
                drop_keys={"canonical_output_hash"},
            )
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match suite-root report payload")
        return self


class RepoBehavioralReplayExecutionReport(_BrlBBase):
    schema: Literal[REPO_BEHAVIORAL_REPLAY_EXECUTION_REPORT_SCHEMA]
    execution_report_ref: str
    manifest_id: str
    manifest_hash: str
    manifest_validation_report_ref: str
    candidate_artifact_ref: str
    candidate_artifact_hash: str
    execution_environment_ref: str
    execution_environment_hash: str
    probe_execution_rows: list[ProbeExecutionRow]
    observation_record_refs: list[str] = Field(default_factory=list)
    diff_refs: list[str] = Field(default_factory=list)
    suite_root_hash_report_ref: str
    execution_status: ReplayExecutionStatus
    authority_posture: ReplayExecutionAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoBehavioralReplayExecutionReport:
        for field_name in (
            "execution_report_ref",
            "manifest_id",
            "manifest_validation_report_ref",
            "candidate_artifact_ref",
            "execution_environment_ref",
            "suite_root_hash_report_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "manifest_hash",
            "candidate_artifact_hash",
            "execution_environment_hash",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sha256(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(
            self.probe_execution_rows,
            attr_name="probe_id",
            field_name="probe_execution_rows",
        )
        object.__setattr__(
            self,
            "probe_execution_rows",
            sorted(self.probe_execution_rows, key=lambda row: row.probe_id),
        )
        for field_name in ("observation_record_refs", "diff_refs"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.authority_posture != "replay_report_only_not_product_authority":
            raise ValueError("replay report cannot claim product authority")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_replay_execution_report",
                drop_keys={"canonical_output_hash"},
            )
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match execution report payload")
        return self


def _with_hash(model: BaseModel, *, object_kind: str, hash_field: str) -> Any:
    payload = model.model_dump(mode="json", exclude_none=True)
    canonicalization_profile_hash = getattr(model, "canonicalization_profile_hash", None)
    payload[hash_field] = canonical_hash(
        model,
        object_kind=object_kind,
        canonicalization_profile_hash=(
            canonicalization_profile_hash
            if isinstance(canonicalization_profile_hash, str)
            else None
        ),
        drop_keys={hash_field},
    )
    return type(model).model_validate(payload)


def _hash_env_delta(env_delta: dict[str, str]) -> str:
    return canonical_hash(
        {
            "schema": "repo_behavioral_env_delta_hash@1",
            "env_delta": dict(sorted(env_delta.items())),
        },
        object_kind="repo_behavioral_env_delta_hash",
    )


def _actual_observation_hash_for_suite(
    *,
    diff_status: RegressionDiffStatus,
    expected_hash: str | None,
    actual_hash: str | None,
) -> str | None:
    if diff_status == "match":
        return expected_hash
    return actual_hash


def _build_diff(
    *,
    probe: RepoBehavioralProbeContract,
    expected: RepoBehavioralObservationHash | None,
    actual: RepoBehavioralObservationRecord | None,
    diff_status_override: RegressionDiffStatus | None = None,
) -> RepoBehavioralRegressionDiff:
    expected_ref = probe.expected_observation_hash_ref
    expected_hash = expected.canonical_observation_hash if expected is not None else None
    actual_hash = actual.canonical_observation_hash if actual is not None else None
    rows: list[StructuredDiffRow] = []
    changed_surfaces: list[ChangedSurfaceKind] = []
    status: RegressionDiffStatus

    if diff_status_override is not None:
        status = diff_status_override
    elif expected is None:
        status = "missing_expected"
    elif actual is None:
        status = "missing_actual"
    else:
        comparisons: list[tuple[ProtectedSurfaceKind, Any, Any]] = [
            ("exit_code", expected.exit_code, actual.raw_exit_code),
            ("stdout", expected.stdout_hash, actual.canonical_stdout_hash),
            ("stderr", expected.stderr_hash, actual.canonical_stderr_hash),
            (
                "output_file_tree",
                expected.output_file_tree_hash,
                actual.canonical_file_tree_hash_after,
            ),
            ("process_state", expected.process_state_hash, actual.canonical_process_state_hash),
            ("timeout_status", expected.timeout_status, actual.timeout_status),
        ]
        for surface, expected_value, actual_value in comparisons:
            if surface not in probe.protected_surfaces:
                continue
            if expected_value != actual_value:
                diff_surface = _SURFACE_TO_DIFF_KIND[surface]
                changed_surfaces.append(diff_surface)
                rows.append(
                    StructuredDiffRow(
                        surface=diff_surface,
                        expected_value=expected_value,
                        actual_value=actual_value,
                        summary=f"{surface} changed for {probe.probe_id}",
                    )
                )
        status = "diff" if changed_surfaces else "match"

    diff_without_hash = RepoBehavioralRegressionDiff(
        schema=REPO_BEHAVIORAL_REGRESSION_DIFF_SCHEMA,
        diff_ref=f"diff:{probe.probe_id}",
        probe_id=probe.probe_id,
        expected_observation_hash_ref=expected_ref,
        expected_canonical_observation_hash=expected_hash,
        actual_observation_record_ref=actual.observation_record_ref if actual is not None else None,
        actual_canonical_observation_hash=actual_hash,
        diff_status=status,
        changed_surfaces=changed_surfaces,
        structured_diff_rows=rows,
        authority_posture="diff_report_only_not_patch_authority",
    )
    return _with_hash(
        diff_without_hash,
        object_kind="repo_behavioral_regression_diff",
        hash_field="canonical_output_hash",
    )


def _capture_failure_record(
    *,
    probe: RepoBehavioralProbeContract,
    profile: RepoBehavioralCanonicalizationProfile,
    timeout_status: TimeoutStatus = "not_run",
) -> RepoBehavioralObservationRecord:
    record_without_hash = RepoBehavioralObservationRecord(
        schema=REPO_BEHAVIORAL_OBSERVATION_RECORD_SCHEMA,
        observation_record_ref=f"observation:{probe.probe_id}",
        probe_id=probe.probe_id,
        probe_contract_hash=probe.probe_contract_hash
        or canonical_hash(
            probe,
            object_kind="repo_behavioral_probe_contract",
            canonicalization_profile_hash=probe.canonicalization_profile_hash,
            drop_keys={"probe_contract_hash"},
        ),
        raw_exit_code=None,
        raw_stdout_ref=None,
        raw_stderr_ref=None,
        raw_file_tree_hash_after=None,
        raw_process_state_ref=None,
        timeout_status=timeout_status,
        canonicalization_profile_ref=profile.canonicalization_profile_ref,
        canonicalization_profile_hash=profile.profile_hash or "",
    )
    return _with_hash(
        record_without_hash,
        object_kind="repo_behavioral_observation_record",
        hash_field="canonical_observation_hash",
    )


def _capture_failed_probe_row(
    *,
    probe: RepoBehavioralProbeContract,
    profile: RepoBehavioralCanonicalizationProfile,
    fixture_tree_hash_before: str | None = None,
    timeout_status: TimeoutStatus = "not_run",
) -> tuple[ProbeExecutionRow, RepoBehavioralObservationRecord]:
    record = _capture_failure_record(
        probe=probe,
        profile=profile,
        timeout_status=timeout_status,
    )
    return (
        ProbeExecutionRow(
            probe_id=probe.probe_id,
            probe_contract_hash=probe.probe_contract_hash,
            execution_status="capture_failed",
            argv=probe.argv,
            cwd_ref=probe.cwd_ref,
            env_delta_hash=_hash_env_delta(probe.env_delta),
            timeout_policy_ref=probe.timeout_policy_ref,
            fixture_tree_hash_before=fixture_tree_hash_before,
            fixture_tree_hash_after_actual=None,
            observation_record_ref=record.observation_record_ref,
            diff_ref=f"diff:{probe.probe_id}",
        ),
        record,
    )


def _changed_file_tree_paths(
    before_snapshot: dict[str, str],
    after_snapshot: dict[str, str],
) -> list[str]:
    return sorted(
        path
        for path in set(before_snapshot) | set(after_snapshot)
        if before_snapshot.get(path) != after_snapshot.get(path)
    )


def _is_workspace_path_allowlisted(path: str, allowlist: list[str]) -> bool:
    for allowed in allowlist:
        normalized_allowed = allowed.strip("/")
        if not normalized_allowed or normalized_allowed.startswith("../"):
            continue
        if path == normalized_allowed or path.startswith(f"{normalized_allowed}/"):
            return True
    return False


def _capture_probe(
    *,
    probe: RepoBehavioralProbeContract,
    profile: RepoBehavioralCanonicalizationProfile,
    cwd_map: dict[str, Path],
    stdin_map: dict[str, bytes],
    timeout_seconds_by_ref: dict[str, float],
    env_base: dict[str, str],
) -> tuple[ProbeExecutionRow, RepoBehavioralObservationRecord]:
    missing_raw_surfaces = [
        surface
        for surface in probe.protected_surfaces
        if surface in _OBSERVATION_REQUIRED_RAW_SURFACES
        and _OBSERVATION_REQUIRED_RAW_SURFACES[surface]
        not in probe.surface_policy.raw_observed_surfaces
    ]
    if missing_raw_surfaces or not probe.argv:
        return _capture_failed_probe_row(
            probe=probe,
            profile=profile,
            fixture_tree_hash_before=probe.fixture_tree_hash_before,
        )

    cwd = cwd_map.get(probe.cwd_ref)
    timeout_seconds = timeout_seconds_by_ref.get(probe.timeout_policy_ref)
    stdin_bytes = b""
    if probe.stdin_ref is not None:
        stdin_bytes = stdin_map.get(probe.stdin_ref, b"")
    stdin_missing = probe.stdin_ref is not None and probe.stdin_ref not in stdin_map
    if cwd is None or not cwd.is_dir() or timeout_seconds is None or stdin_missing:
        return _capture_failed_probe_row(
            probe=probe,
            profile=profile,
            fixture_tree_hash_before=probe.fixture_tree_hash_before,
        )

    try:
        before_tree_hash, before_snapshot = _file_tree_snapshot(cwd)
    except (OSError, ValueError):
        return _capture_failed_probe_row(
            probe=probe,
            profile=profile,
            fixture_tree_hash_before=probe.fixture_tree_hash_before,
        )
    if (
        probe.fixture_tree_hash_before is not None
        and before_tree_hash != probe.fixture_tree_hash_before
    ):
        return _capture_failed_probe_row(
            probe=probe,
            profile=profile,
            fixture_tree_hash_before=before_tree_hash,
        )

    env = dict(env_base)
    env.update(probe.env_delta)
    timeout_status: TimeoutStatus = "completed"
    execution_status: ProbeExecutionStatus = "completed"
    try:
        completed = subprocess.run(
            probe.argv,
            input=stdin_bytes,
            cwd=cwd,
            env=env,
            capture_output=True,
            timeout=timeout_seconds,
            check=False,
        )
        stdout = completed.stdout
        stderr = completed.stderr
        exit_code: int | None = completed.returncode
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or b""
        stderr = exc.stderr or b""
        exit_code = None
        timeout_status = "timed_out"
        execution_status = "timeout"
    except OSError:
        return _capture_failed_probe_row(
            probe=probe,
            profile=profile,
            fixture_tree_hash_before=before_tree_hash,
        )
    try:
        after_tree_hash, after_snapshot = _file_tree_snapshot(cwd)
    except (OSError, ValueError):
        return _capture_failed_probe_row(
            probe=probe,
            profile=profile,
            fixture_tree_hash_before=before_tree_hash,
            timeout_status=timeout_status,
        )

    changed_paths = _changed_file_tree_paths(before_snapshot, after_snapshot)
    if (
        probe.fixture_tree_protection_kind == "read_only"
        and probe.fixture_tree_hash_before is not None
        and after_tree_hash != before_tree_hash
    ):
        execution_status = "fixture_mutation_forbidden"
    elif (
        probe.fixture_tree_hash_after_expected is not None
        and after_tree_hash != probe.fixture_tree_hash_after_expected
    ):
        execution_status = "fixture_mutation_forbidden"
    elif (
        probe.fixture_tree_protection_kind == "workspace_mutation_allowed"
        and probe.workspace_write_allowlist
        and any(
            not _is_workspace_path_allowlisted(path, probe.workspace_write_allowlist)
            for path in changed_paths
        )
    ):
        execution_status = "fixture_mutation_forbidden"

    stdout_hash = hash_bytes(stdout, domain="stdout")
    stderr_hash = hash_bytes(stderr, domain="stderr")
    record_without_hash = RepoBehavioralObservationRecord(
        schema=REPO_BEHAVIORAL_OBSERVATION_RECORD_SCHEMA,
        observation_record_ref=f"observation:{probe.probe_id}",
        probe_id=probe.probe_id,
        probe_contract_hash=probe.probe_contract_hash
        or canonical_hash(
            probe,
            object_kind="repo_behavioral_probe_contract",
            canonicalization_profile_hash=probe.canonicalization_profile_hash,
            drop_keys={"probe_contract_hash"},
        ),
        raw_exit_code=exit_code,
        raw_stdout_ref=f"raw:stdout:{stdout_hash}",
        raw_stderr_ref=f"raw:stderr:{stderr_hash}",
        raw_file_tree_hash_after=after_tree_hash,
        raw_process_state_ref=None,
        timeout_status=timeout_status,
        canonicalization_profile_ref=profile.canonicalization_profile_ref,
        canonicalization_profile_hash=profile.profile_hash or "",
        canonical_stdout_hash=stdout_hash,
        canonical_stderr_hash=stderr_hash,
        canonical_file_tree_hash_after=after_tree_hash,
        canonical_process_state_hash=None,
    )
    record = _with_hash(
        record_without_hash,
        object_kind="repo_behavioral_observation_record",
        hash_field="canonical_observation_hash",
    )
    row = ProbeExecutionRow(
        probe_id=probe.probe_id,
        probe_contract_hash=probe.probe_contract_hash,
        execution_status=execution_status,
        argv=probe.argv,
        cwd_ref=probe.cwd_ref,
        env_delta_hash=_hash_env_delta(probe.env_delta),
        timeout_policy_ref=probe.timeout_policy_ref,
        fixture_tree_hash_before=before_tree_hash,
        fixture_tree_hash_after_actual=after_tree_hash,
        observation_record_ref=record.observation_record_ref,
        diff_ref=f"diff:{probe.probe_id}",
    )
    return row, record


def _blocked_outputs(
    *,
    manifest: RepoBehavioralReplayManifest,
    manifest_validation_report: RepoBehavioralReplayManifestValidationReport,
    candidate_artifact_ref: str,
    candidate_artifact_hash: str,
    execution_environment_ref: str,
    execution_environment_hash: str,
    probes: list[RepoBehavioralProbeContract],
) -> tuple[
    RepoBehavioralReplayExecutionReport,
    list[RepoBehavioralObservationRecord],
    list[RepoBehavioralRegressionDiff],
    RepoBehavioralSuiteRootHashReport,
]:
    diffs = [
        _build_diff(
            probe=probe,
            expected=None,
            actual=None,
            diff_status_override="blocked_by_manifest_validation",
        )
        for probe in sorted(probes, key=lambda row: row.probe_id)
    ]
    probe_rows = [
        ProbeExecutionRow(
            probe_id=probe.probe_id,
            probe_contract_hash=probe.probe_contract_hash,
            execution_status="blocked_by_manifest_validation",
            argv=probe.argv,
            cwd_ref=probe.cwd_ref,
            env_delta_hash=_hash_env_delta(probe.env_delta),
            timeout_policy_ref=probe.timeout_policy_ref,
            fixture_tree_hash_before=probe.fixture_tree_hash_before,
            fixture_tree_hash_after_actual=None,
            observation_record_ref=None,
            diff_ref=f"diff:{probe.probe_id}",
        )
        for probe in sorted(probes, key=lambda row: row.probe_id)
    ]
    suite_without_hash = RepoBehavioralSuiteRootHashReport(
        schema=REPO_BEHAVIORAL_SUITE_ROOT_HASH_REPORT_SCHEMA,
        suite_root_hash_report_ref=f"suite-root:{manifest.manifest_id}",
        manifest_id=manifest.manifest_id,
        manifest_hash=manifest.manifest_hash or manifest_validation_report.manifest_hash,
        expected_suite_root_hash=manifest.suite_root_hash
        or suite_root_hash_for(
            probe_contract_refs=manifest.probe_contract_refs,
            probe_contract_hashes=manifest.probe_contract_hashes,
            expected_observation_hash_refs=manifest.expected_observation_hash_refs,
            expected_observation_hashes=manifest.expected_observation_hashes,
            canonicalization_profile_ref=manifest.canonicalization_profile_ref,
            canonicalization_profile_hash=manifest.canonicalization_profile_hash,
        ),
        actual_suite_root_hash=None,
        per_probe_hash_rows=[
            SuiteRootPerProbeHashRow(
                probe_id=probe.probe_id,
                expected_observation_hash_ref=probe.expected_observation_hash_ref,
                expected_canonical_observation_hash=None,
                actual_canonical_observation_hash=None,
                diff_status="blocked_by_manifest_validation",
            )
            for probe in sorted(probes, key=lambda row: row.probe_id)
        ],
        suite_root_status="blocked_by_manifest_validation",
        authority_posture="suite_hash_report_only_not_certificate",
    )
    suite_report = _with_hash(
        suite_without_hash,
        object_kind="repo_behavioral_suite_root_hash_report",
        hash_field="canonical_output_hash",
    )
    report_without_hash = RepoBehavioralReplayExecutionReport(
        schema=REPO_BEHAVIORAL_REPLAY_EXECUTION_REPORT_SCHEMA,
        execution_report_ref=f"execution:{manifest.manifest_id}",
        manifest_id=manifest.manifest_id,
        manifest_hash=manifest.manifest_hash or manifest_validation_report.manifest_hash,
        manifest_validation_report_ref=manifest_validation_report.validation_report_ref,
        candidate_artifact_ref=candidate_artifact_ref,
        candidate_artifact_hash=candidate_artifact_hash,
        execution_environment_ref=execution_environment_ref,
        execution_environment_hash=execution_environment_hash,
        probe_execution_rows=probe_rows,
        observation_record_refs=[],
        diff_refs=[diff.diff_ref for diff in diffs],
        suite_root_hash_report_ref=suite_report.suite_root_hash_report_ref,
        execution_status="blocked_by_manifest_validation",
        authority_posture="replay_report_only_not_product_authority",
    )
    execution_report = _with_hash(
        report_without_hash,
        object_kind="repo_behavioral_replay_execution_report",
        hash_field="canonical_output_hash",
    )
    return execution_report, [], diffs, suite_report


def _manifest_inputs_match(
    *,
    manifest: RepoBehavioralReplayManifest,
    probe_by_ref: dict[str, RepoBehavioralProbeContract],
    expected_by_ref: dict[str, RepoBehavioralObservationHash],
) -> bool:
    if set(probe_by_ref) != set(manifest.probe_contract_refs):
        return False
    if {
        probe.probe_contract_hash
        for probe in probe_by_ref.values()
        if probe.probe_contract_hash is not None
    } != set(manifest.probe_contract_hashes):
        return False
    if set(expected_by_ref) != set(manifest.expected_observation_hash_refs):
        return False
    if {
        expected.canonical_observation_hash
        for expected in expected_by_ref.values()
        if expected.canonical_observation_hash is not None
    } != set(manifest.expected_observation_hashes):
        return False
    for probe in probe_by_ref.values():
        expected = expected_by_ref.get(probe.expected_observation_hash_ref)
        if expected is None or expected.probe_id != probe.probe_id:
            return False
    return True


def replay_manifest(
    *,
    manifest: RepoBehavioralReplayManifest | dict[str, Any],
    manifest_validation_report: RepoBehavioralReplayManifestValidationReport | dict[str, Any],
    probe_contracts: list[RepoBehavioralProbeContract | dict[str, Any]],
    canonicalization_profile: RepoBehavioralCanonicalizationProfile | dict[str, Any],
    expected_observation_hashes: list[RepoBehavioralObservationHash | dict[str, Any]],
    candidate_artifact_ref: str,
    candidate_artifact_hash: str,
    cwd_map: dict[str, Path],
    timeout_seconds_by_ref: dict[str, float],
    stdin_map: dict[str, bytes] | None = None,
    env_base: dict[str, str] | None = None,
) -> tuple[
    RepoBehavioralReplayExecutionReport,
    list[RepoBehavioralObservationRecord],
    list[RepoBehavioralRegressionDiff],
    RepoBehavioralSuiteRootHashReport,
]:
    loaded_manifest = (
        manifest
        if isinstance(manifest, RepoBehavioralReplayManifest)
        else RepoBehavioralReplayManifest.model_validate(manifest)
    )
    loaded_validation_report = (
        manifest_validation_report
        if isinstance(manifest_validation_report, RepoBehavioralReplayManifestValidationReport)
        else RepoBehavioralReplayManifestValidationReport.model_validate(manifest_validation_report)
    )
    loaded_probes = [
        probe
        if isinstance(probe, RepoBehavioralProbeContract)
        else RepoBehavioralProbeContract.model_validate(probe)
        for probe in probe_contracts
    ]
    loaded_profile = (
        canonicalization_profile
        if isinstance(canonicalization_profile, RepoBehavioralCanonicalizationProfile)
        else RepoBehavioralCanonicalizationProfile.model_validate(canonicalization_profile)
    )
    loaded_expected = [
        expected
        if isinstance(expected, RepoBehavioralObservationHash)
        else RepoBehavioralObservationHash.model_validate(expected)
        for expected in expected_observation_hashes
    ]
    candidate_artifact_ref = _assert_non_empty_text(
        candidate_artifact_ref,
        field_name="candidate_artifact_ref",
    )
    candidate_artifact_hash = _assert_sha256(
        candidate_artifact_hash,
        field_name="candidate_artifact_hash",
    )
    execution_environment_ref = loaded_manifest.execution_environment_ref
    execution_environment_hash = loaded_manifest.execution_environment_hash
    probe_by_ref = {probe.probe_id: probe for probe in loaded_probes}
    expected_by_ref = {expected.observation_hash_ref: expected for expected in loaded_expected}
    if (
        loaded_validation_report.validation_status != "valid_for_manifest_lock"
        or loaded_validation_report.manifest_hash != loaded_manifest.manifest_hash
        or loaded_profile.canonicalization_profile_ref
        != loaded_manifest.canonicalization_profile_ref
        or loaded_profile.profile_hash != loaded_manifest.canonicalization_profile_hash
        or not _manifest_inputs_match(
            manifest=loaded_manifest,
            probe_by_ref=probe_by_ref,
            expected_by_ref=expected_by_ref,
        )
    ):
        return _blocked_outputs(
            manifest=loaded_manifest,
            manifest_validation_report=loaded_validation_report,
            candidate_artifact_ref=candidate_artifact_ref,
            candidate_artifact_hash=candidate_artifact_hash,
            execution_environment_ref=execution_environment_ref,
            execution_environment_hash=execution_environment_hash,
            probes=loaded_probes,
        )

    stdin_map = stdin_map or {}
    env_base = dict(os.environ if env_base is None else env_base)
    observation_records: list[RepoBehavioralObservationRecord] = []
    diffs: list[RepoBehavioralRegressionDiff] = []
    probe_rows: list[ProbeExecutionRow] = []
    per_probe_hash_rows: list[SuiteRootPerProbeHashRow] = []
    actual_suite_hashes: list[str] = []

    for probe in sorted(loaded_probes, key=lambda row: row.probe_id):
        probe_row, observation_record = _capture_probe(
            probe=probe,
            profile=loaded_profile,
            cwd_map=cwd_map,
            stdin_map=stdin_map,
            timeout_seconds_by_ref=timeout_seconds_by_ref,
            env_base=env_base,
        )
        observation_records.append(observation_record)
        expected = expected_by_ref.get(probe.expected_observation_hash_ref)
        diff_status_override: RegressionDiffStatus | None = None
        if probe_row.execution_status in {"capture_failed", "fixture_mutation_forbidden"}:
            diff_status_override = "capture_failed"
        diff = _build_diff(
            probe=probe,
            expected=expected,
            actual=observation_record,
            diff_status_override=diff_status_override,
        )
        diffs.append(diff)
        probe_rows.append(probe_row)
        actual_hash_for_suite = _actual_observation_hash_for_suite(
            diff_status=diff.diff_status,
            expected_hash=expected.canonical_observation_hash if expected is not None else None,
            actual_hash=observation_record.canonical_observation_hash,
        )
        if actual_hash_for_suite is not None:
            actual_suite_hashes.append(actual_hash_for_suite)
        per_probe_hash_rows.append(
            SuiteRootPerProbeHashRow(
                probe_id=probe.probe_id,
                expected_observation_hash_ref=probe.expected_observation_hash_ref,
                expected_canonical_observation_hash=(
                    expected.canonical_observation_hash if expected is not None else None
                ),
                actual_canonical_observation_hash=actual_hash_for_suite,
                diff_status=diff.diff_status,
            )
        )

    actual_suite_root_hash = suite_root_hash_for(
        probe_contract_refs=loaded_manifest.probe_contract_refs,
        probe_contract_hashes=loaded_manifest.probe_contract_hashes,
        expected_observation_hash_refs=loaded_manifest.expected_observation_hash_refs,
        expected_observation_hashes=actual_suite_hashes,
        canonicalization_profile_ref=loaded_manifest.canonicalization_profile_ref,
        canonicalization_profile_hash=loaded_manifest.canonicalization_profile_hash,
    )
    suite_status: SuiteRootStatus = (
        "match"
        if actual_suite_root_hash == loaded_manifest.suite_root_hash
        else "capture_failed"
        if any(diff.diff_status == "capture_failed" for diff in diffs)
        else "diff"
    )
    suite_without_hash = RepoBehavioralSuiteRootHashReport(
        schema=REPO_BEHAVIORAL_SUITE_ROOT_HASH_REPORT_SCHEMA,
        suite_root_hash_report_ref=f"suite-root:{loaded_manifest.manifest_id}",
        manifest_id=loaded_manifest.manifest_id,
        manifest_hash=loaded_manifest.manifest_hash,
        expected_suite_root_hash=loaded_manifest.suite_root_hash,
        actual_suite_root_hash=actual_suite_root_hash,
        per_probe_hash_rows=per_probe_hash_rows,
        suite_root_status=suite_status,
        authority_posture="suite_hash_report_only_not_certificate",
    )
    suite_report = _with_hash(
        suite_without_hash,
        object_kind="repo_behavioral_suite_root_hash_report",
        hash_field="canonical_output_hash",
    )
    execution_status: ReplayExecutionStatus = (
        "completed"
        if all(diff.diff_status == "match" for diff in diffs)
        else "capture_failed"
        if any(diff.diff_status == "capture_failed" for diff in diffs)
        else "completed_with_diffs"
    )
    report_without_hash = RepoBehavioralReplayExecutionReport(
        schema=REPO_BEHAVIORAL_REPLAY_EXECUTION_REPORT_SCHEMA,
        execution_report_ref=f"execution:{loaded_manifest.manifest_id}",
        manifest_id=loaded_manifest.manifest_id,
        manifest_hash=loaded_manifest.manifest_hash,
        manifest_validation_report_ref=loaded_validation_report.validation_report_ref,
        candidate_artifact_ref=candidate_artifact_ref,
        candidate_artifact_hash=candidate_artifact_hash,
        execution_environment_ref=execution_environment_ref,
        execution_environment_hash=execution_environment_hash,
        probe_execution_rows=probe_rows,
        observation_record_refs=[record.observation_record_ref for record in observation_records],
        diff_refs=[diff.diff_ref for diff in diffs],
        suite_root_hash_report_ref=suite_report.suite_root_hash_report_ref,
        execution_status=execution_status,
        authority_posture="replay_report_only_not_product_authority",
    )
    execution_report = _with_hash(
        report_without_hash,
        object_kind="repo_behavioral_replay_execution_report",
        hash_field="canonical_output_hash",
    )
    return execution_report, observation_records, diffs, suite_report
