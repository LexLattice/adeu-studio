from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

from adeu_ir.repo import repo_root

from .models import (
    CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA,
    ConstitutionalCoherenceFinding,
    ConstitutionalCoherenceLaneDriftRecord,
    ConstitutionalCoherencePredicateEvaluation,
    ConstitutionalCoherenceReport,
    ConstitutionalGovernanceCalibrationEntry,
    ConstitutionalGovernanceCalibrationRegister,
    ConstitutionalMigrationDecisionEntry,
    ConstitutionalMigrationDecisionRegister,
    ConstitutionalSupportAdmissionRecord,
    ConstitutionalUnresolvedSeamEntry,
    ConstitutionalUnresolvedSeamRegister,
    compute_constitutional_governance_calibration_entry_id,
    compute_constitutional_governance_calibration_register_id,
    compute_constitutional_migration_decision_entry_id,
    compute_constitutional_migration_decision_register_id,
    compute_constitutional_report_id,
    compute_constitutional_unresolved_seam_entry_id,
    compute_constitutional_unresolved_seam_register_id,
)

CHECKER_VERSION = "v55a_constitutional_coherence_checker@1"
TARGET_ARC = "vNext+149"
TARGET_PATH = "V55-A"
V55B_CHECKER_VERSION = "v55b_constitutional_coherence_checker@1"
V55B_TARGET_ARC = "vNext+150"
V55B_TARGET_PATH = "V55-B"
V55C_CHECKER_VERSION = "v55c_constitutional_governance_migration_checker@1"
V55C_TARGET_ARC = "vNext+151"
V55C_TARGET_PATH = "V55-C"
MAX_STRUCTURED_DOC_BYTES = 1_048_576
DEFAULT_ADMISSIONS_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55a/"
    "constitutional_support_admission_records_v55a.json"
)
DEFAULT_V55B_ADMISSIONS_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55b/"
    "constitutional_support_admission_records_v55b.json"
)
DEFAULT_V55B_DRIFT_RECORD_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55b/"
    "reference_constitutional_coherence_lane_drift_record.json"
)
DEFAULT_V55C_ADMISSIONS_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55c/"
    "constitutional_support_admission_records_v55c.json"
)
DEFAULT_V55C_DRIFT_RECORD_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55c/"
    "reference_constitutional_coherence_lane_drift_record.json"
)
DEFAULT_V55C_V55A_REPORT_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55a/"
    "reference_constitutional_coherence_report.json"
)
DEFAULT_V55C_V55A_UNRESOLVED_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55a/"
    "reference_constitutional_unresolved_seam_register.json"
)
DEFAULT_V55C_V55B_REPORT_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55b/"
    "reference_constitutional_coherence_report.json"
)
DEFAULT_V55C_V55B_UNRESOLVED_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55b/"
    "reference_constitutional_unresolved_seam_register.json"
)
DEFAULT_V55C_V55B_DRIFT_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55b/"
    "reference_constitutional_coherence_lane_drift_record.json"
)
DEFAULT_V55C_V55B_EVIDENCE_PATH = (
    "artifacts/agent_harness/v150/evidence_inputs/"
    "v55b_descendant_trial_hardening_evidence_v150.json"
)
EXPECTED_ADMITTED_SEED_ARTIFACTS = (
    "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md",
    "docs/support/ADEU_SCHEMA_META_GRAMMAR.md",
    "docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED.md",
    "docs/support/ODEU_MEMBRANE_ARCHITECTURE.md",
    "docs/support/crypto data spec2.md",
)
PREFERRED_DESCENDANT_ARTIFACT = "docs/support/crypto data spec2.md"
REQUIRED_V55B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "structured_input_only": "holds",
    "exact_admitted_seed_set": "holds",
    "warning_only_checker": "holds",
    "checker_report_surface_reuse_default": "holds",
    "descendant_trial_profile_hardening": "amended",
}
EXPECTED_V55B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS149.md"
REQUIRED_V55C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "structured_input_only": "holds",
    "exact_admitted_seed_set": "holds",
    "warning_only_checker": "holds",
    "checker_report_surface_reuse_default": "holds",
    "governance_migration_decision_surfaces": "amended",
}
EXPECTED_V55C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS150.md"
EXPECTED_V55C_V55B_EVIDENCE_SCHEMA = "v55b_descendant_trial_hardening_evidence@1"

_AUTHORITY_LINE_RE = re.compile(r"^Authority layer:\s*(.+)$", re.MULTILINE)
_STATUS_LINE_RE = re.compile(r"^Status:\s*(.+)$", re.MULTILINE)
_DESIGNATED_SUPPORT_BLOCK_RE = re.compile(
    rf'"schema"\s*:\s*"{re.escape(CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA)}"'
)


@dataclass(frozen=True)
class StructuredDocSurface:
    artifact_ref: str
    status_line: str | None
    authority_layer_line: str | None
    json_block_schemas: tuple[str, ...]
    json_block_count: int


def _resolve_path(*, repo_root_path: Path, value: str) -> Path:
    path = Path(value)
    return path if path.is_absolute() else repo_root_path / path


def _resolve_structured_doc_path(*, repo_root_path: Path, artifact_ref: str) -> Path:
    path = Path(artifact_ref)
    if path.is_absolute():
        raise ValueError(f"{artifact_ref}: artifact_ref must remain repo-relative in V55-A")

    root = repo_root_path.resolve()
    cursor = root
    for part in path.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise ValueError(f"{artifact_ref}: symlink component forbidden in V55-A")

    try:
        resolved = cursor.resolve(strict=True)
    except FileNotFoundError as exc:
        raise ValueError(f"{artifact_ref}: admitted seed artifact not found") from exc

    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ValueError(f"{artifact_ref}: resolved path escapes repository root") from exc

    if not resolved.is_file():
        raise ValueError(f"{artifact_ref}: admitted seed artifact must be a file")
    if resolved.stat().st_size > MAX_STRUCTURED_DOC_BYTES:
        raise ValueError(
            f"{artifact_ref}: admitted seed artifact exceeds {MAX_STRUCTURED_DOC_BYTES} bytes"
        )
    return resolved


def _extract_json_blocks(text: str) -> list[str]:
    lines = text.splitlines()
    blocks: list[str] = []
    index = 0
    while index < len(lines):
        if lines[index].strip() != "```json":
            index += 1
            continue
        index += 1
        block_lines: list[str] = []
        while index < len(lines) and lines[index].strip() != "```":
            block_lines.append(lines[index])
            index += 1
        blocks.append("\n".join(block_lines).strip())
        if index < len(lines):
            index += 1
    return blocks


def _looks_like_designated_support_block(block_text: str) -> bool:
    return _DESIGNATED_SUPPORT_BLOCK_RE.search(block_text) is not None


def _extract_structured_doc_surface(
    *,
    repo_root_path: Path,
    artifact_ref: str,
) -> StructuredDocSurface:
    doc_path = _resolve_structured_doc_path(
        repo_root_path=repo_root_path,
        artifact_ref=artifact_ref,
    )
    text = doc_path.read_text(encoding="utf-8")
    json_block_schemas: list[str] = []
    for block_text in _extract_json_blocks(text):
        try:
            payload = json.loads(block_text)
        except json.JSONDecodeError as exc:
            if _looks_like_designated_support_block(block_text):
                raise ValueError(
                    f"{artifact_ref}: invalid designated structured block: {exc}"
                ) from exc
            continue
        if not isinstance(payload, dict):
            continue
        schema = payload.get("schema")
        if isinstance(schema, str):
            json_block_schemas.append(schema)
    status_match = _STATUS_LINE_RE.search(text)
    authority_match = _AUTHORITY_LINE_RE.search(text)
    return StructuredDocSurface(
        artifact_ref=artifact_ref,
        status_line=status_match.group(1).strip() if status_match else None,
        authority_layer_line=authority_match.group(1).strip() if authority_match else None,
        json_block_schemas=tuple(json_block_schemas),
        json_block_count=len(json_block_schemas),
    )


def load_support_admission_records(*, path: Path) -> list[ConstitutionalSupportAdmissionRecord]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, list):
        raise ValueError("support admission payload must be a list of records")
    records = [ConstitutionalSupportAdmissionRecord.model_validate(item) for item in payload]
    seen: set[str] = set()
    for record in records:
        if record.artifact_ref in seen:
            raise ValueError(f"duplicate artifact_ref in admission records: {record.artifact_ref}")
        seen.add(record.artifact_ref)
    return records


def load_lane_drift_record(*, path: Path) -> ConstitutionalCoherenceLaneDriftRecord:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("lane drift payload must be an object")
    return ConstitutionalCoherenceLaneDriftRecord.model_validate(payload)


def load_coherence_report(*, path: Path) -> ConstitutionalCoherenceReport:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("coherence report payload must be an object")
    return ConstitutionalCoherenceReport.model_validate(payload)


def load_unresolved_seam_register(*, path: Path) -> ConstitutionalUnresolvedSeamRegister:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("unresolved seam register payload must be an object")
    return ConstitutionalUnresolvedSeamRegister.model_validate(payload)


def _canonicalize_admitted_seed_records(
    records: list[ConstitutionalSupportAdmissionRecord],
) -> list[ConstitutionalSupportAdmissionRecord]:
    records_by_ref = {record.artifact_ref: record for record in records}
    actual_refs = set(records_by_ref)
    expected_refs = set(EXPECTED_ADMITTED_SEED_ARTIFACTS)
    missing_refs = sorted(expected_refs - actual_refs)
    extra_refs = sorted(actual_refs - expected_refs)
    if missing_refs or extra_refs:
        detail_parts: list[str] = []
        if missing_refs:
            detail_parts.append(f"missing={missing_refs}")
        if extra_refs:
            detail_parts.append(f"extra={extra_refs}")
        raise ValueError(
            "admissions must match the exact admitted seed set; " + ", ".join(detail_parts)
        )
    return [records_by_ref[artifact_ref] for artifact_ref in EXPECTED_ADMITTED_SEED_ARTIFACTS]


def _evaluation(
    *,
    predicate_id: str,
    artifact_ref: str,
    status: str,
    evidence_source: str,
    detail_note: str,
) -> ConstitutionalCoherencePredicateEvaluation:
    return ConstitutionalCoherencePredicateEvaluation(
        predicate_id=predicate_id,
        artifact_ref=artifact_ref,
        status=status,
        evidence_source=evidence_source,
        detail_note=detail_note,
    )


def _resolve_repo_input_path(*, repo_root_path: Path, value: str) -> Path:
    return _resolve_path(repo_root_path=repo_root_path, value=value)


def _warning(
    *,
    code: str,
    artifact_ref: str,
    predicate_id: str,
    message: str,
) -> ConstitutionalCoherenceFinding:
    return ConstitutionalCoherenceFinding(
        code=code,
        artifact_ref=artifact_ref,
        predicate_id=predicate_id,
        message=message,
    )


def _validate_v55b_lane_drift_record(
    record: ConstitutionalCoherenceLaneDriftRecord,
) -> ConstitutionalCoherenceLaneDriftRecord:
    if record.target_arc != V55B_TARGET_ARC:
        raise ValueError(
            f"V55-B lane drift record must target {V55B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V55B_TARGET_PATH:
        raise ValueError(
            f"V55-B lane drift record must target {V55B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V55B_PRIOR_LANE_REF:
        raise ValueError(
            "V55-B lane drift record must point at "
            f"{EXPECTED_V55B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )

    seen_assumption_refs: set[str] = set()
    duplicate_assumption_refs: list[str] = []
    for entry in record.entries:
        if entry.assumption_ref in seen_assumption_refs:
            duplicate_assumption_refs.append(entry.assumption_ref)
            continue
        seen_assumption_refs.add(entry.assumption_ref)
    if duplicate_assumption_refs:
        raise ValueError(
            "V55-B lane drift record must not repeat assumption refs; "
            f"duplicates={sorted(set(duplicate_assumption_refs))}"
        )

    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V55B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    unexpected_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V55B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or unexpected_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if unexpected_statuses:
            detail_parts.append(f"status_mismatch={unexpected_statuses}")
        raise ValueError(
            "V55-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _reclassify_v55b_unresolved_entry(
    entry: ConstitutionalUnresolvedSeamEntry,
) -> ConstitutionalUnresolvedSeamEntry:
    if entry.predicate_id == "descendant_claim_within_parent_entitlement":
        reason_kind = "family_law_gap"
    elif entry.predicate_id == "support_surface_not_self_promoted":
        reason_kind = "admission_surface_gap"
    else:
        reason_kind = entry.reason_kind
    return entry.model_copy(update={"reason_kind": reason_kind})


def _v55b_descendant_record(
    records: list[ConstitutionalSupportAdmissionRecord],
) -> ConstitutionalSupportAdmissionRecord:
    descendant_records = [record for record in records if record.is_descendant_surface]
    if len(descendant_records) != 1:
        raise ValueError(
            "V55-B requires exactly one admitted descendant support surface in the seed set"
        )
    record = descendant_records[0]
    if record.artifact_ref != PREFERRED_DESCENDANT_ARTIFACT:
        raise ValueError(
            "V55-B requires the preferred descendant artifact "
            f"{PREFERRED_DESCENDANT_ARTIFACT!r}, got {record.artifact_ref!r}"
        )
    if record.authority_layer != "support":
        raise ValueError(
            "V55-B requires the preferred descendant to remain a support-surface admission"
        )
    if record.current_authority_relation != "support_descendant_exemplar":
        raise ValueError(
            "V55-B requires the preferred descendant to keep the "
            "'support_descendant_exemplar' relation"
        )
    return record


def _build_v55b_descendant_hardening(
    *,
    repo_root_path: Path,
    descendant_record: ConstitutionalSupportAdmissionRecord,
) -> tuple[list[ConstitutionalCoherenceFinding], list[ConstitutionalUnresolvedSeamEntry]]:
    surface = _extract_structured_doc_surface(
        repo_root_path=repo_root_path,
        artifact_ref=descendant_record.artifact_ref,
    )
    warnings: list[ConstitutionalCoherenceFinding] = []
    unresolved_entries: list[ConstitutionalUnresolvedSeamEntry] = []

    if surface.authority_layer_line is None:
        warnings.append(
            _warning(
                code="DESCENDANT_STRUCTURED_AUTHORITY_LAYER_MISSING",
                artifact_ref=descendant_record.artifact_ref,
                predicate_id="authority_layer_declared",
                message=(
                    "preferred descendant support surface lacks an explicit "
                    "'Authority layer:' line; V55-B keeps it support-surface only and "
                    "non-promoting until the local claim surface is tightened"
                ),
            )
        )
        unresolved_entries.append(
            _unresolved(
                artifact_ref=descendant_record.artifact_ref,
                predicate_id="authority_layer_declared",
                reason_kind="descendant_law_gap",
                required_follow_up=[
                    (
                        "declare explicit authority-layer posture inside the preferred "
                        "descendant support surface"
                    ),
                    (
                        "keep the descendant trial non-promoting and support-surface "
                        "only until the local claim surface is tightened"
                    ),
                ],
            )
        )

    return warnings, unresolved_entries


def _validate_v55c_lane_drift_record(
    record: ConstitutionalCoherenceLaneDriftRecord,
) -> ConstitutionalCoherenceLaneDriftRecord:
    if record.target_arc != V55C_TARGET_ARC:
        raise ValueError(
            f"V55-C lane drift record must target {V55C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V55C_TARGET_PATH:
        raise ValueError(
            f"V55-C lane drift record must target {V55C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V55C_PRIOR_LANE_REF:
        raise ValueError(
            "V55-C lane drift record must point at "
            f"{EXPECTED_V55C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )

    seen_assumption_refs: set[str] = set()
    duplicate_assumption_refs: list[str] = []
    for entry in record.entries:
        if entry.assumption_ref in seen_assumption_refs:
            duplicate_assumption_refs.append(entry.assumption_ref)
            continue
        seen_assumption_refs.add(entry.assumption_ref)
    if duplicate_assumption_refs:
        raise ValueError(
            "V55-C lane drift record must not repeat assumption refs; "
            f"duplicates={sorted(set(duplicate_assumption_refs))}"
        )

    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V55C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    unexpected_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V55C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or unexpected_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if unexpected_statuses:
            detail_parts.append(f"status_mismatch={unexpected_statuses}")
        raise ValueError(
            "V55-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_expected_report(
    *,
    report: ConstitutionalCoherenceReport,
    target_arc: str,
    target_path: str,
    checker_version: str,
) -> ConstitutionalCoherenceReport:
    if report.target_arc != target_arc:
        raise ValueError(f"expected report target_arc {target_arc!r}, got {report.target_arc!r}")
    if report.target_path != target_path:
        raise ValueError(f"expected report target_path {target_path!r}, got {report.target_path!r}")
    if report.checker_version != checker_version:
        raise ValueError(
            f"expected report checker_version {checker_version!r}, got {report.checker_version!r}"
        )
    expected_refs = list(EXPECTED_ADMITTED_SEED_ARTIFACTS)
    if report.checked_artifact_refs != expected_refs:
        raise ValueError("prior coherence report must retain the exact admitted seed set order")
    return report


def _validate_expected_unresolved_register(
    *,
    register: ConstitutionalUnresolvedSeamRegister,
    target_arc: str,
    target_path: str,
) -> ConstitutionalUnresolvedSeamRegister:
    if register.target_arc != target_arc:
        raise ValueError(
            f"expected unresolved register target_arc {target_arc!r}, got {register.target_arc!r}"
        )
    if register.target_path != target_path:
        raise ValueError(
            "expected unresolved register target_path "
            f"{target_path!r}, got {register.target_path!r}"
        )
    return register


def _load_json_object(*, path: Path, error_label: str) -> dict[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{error_label} payload must be an object")
    return payload


def _validate_v55b_evidence_payload(
    payload: dict[str, object],
    *,
    report: ConstitutionalCoherenceReport,
    unresolved: ConstitutionalUnresolvedSeamRegister,
    lane_drift: ConstitutionalCoherenceLaneDriftRecord,
) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V55C_V55B_EVIDENCE_SCHEMA:
        raise ValueError(
            "V55-C requires the shipped V55-B descendant-trial evidence payload on main"
        )
    if payload.get("warning_only_checker_preserved") is not True:
        raise ValueError("V55-B evidence must preserve the warning-only checker posture")
    if payload.get("support_surface_descendant_trial_only") is not True:
        raise ValueError("V55-B evidence must preserve support-surface-only descendant posture")
    if payload.get("reference_warning_count") != report.warning_count:
        raise ValueError("V55-B evidence warning count must match the shipped V55-B report")
    if payload.get("reference_unresolved_entry_count") != unresolved.entry_count:
        raise ValueError(
            "V55-B evidence unresolved entry count must match the shipped V55-B register"
        )
    if payload.get("reference_lane_drift_entry_count") != lane_drift.entry_count:
        raise ValueError("V55-B evidence lane-drift count must match the shipped V55-B handoff")
    return payload


def _governance_entry(
    *,
    predicate_id: str,
    surface_ref: str,
    current_posture: str,
    recommended_outcome: str,
    rationale: str,
    evidence_refs: list[str],
) -> ConstitutionalGovernanceCalibrationEntry:
    return ConstitutionalGovernanceCalibrationEntry(
        calibration_id=compute_constitutional_governance_calibration_entry_id(
            predicate_id=predicate_id,
            surface_ref=surface_ref,
        ),
        predicate_id=predicate_id,
        surface_ref=surface_ref,
        current_posture=current_posture,
        recommended_outcome=recommended_outcome,
        rationale=rationale,
        evidence_refs=evidence_refs,
    )


def _migration_entry(
    *,
    surface_id: str,
    current_posture: str,
    recommended_outcome: str,
    rationale: str,
    evidence_refs: list[str],
) -> ConstitutionalMigrationDecisionEntry:
    return ConstitutionalMigrationDecisionEntry(
        decision_id=compute_constitutional_migration_decision_entry_id(surface_id=surface_id),
        surface_id=surface_id,
        current_posture=current_posture,
        recommended_outcome=recommended_outcome,
        rationale=rationale,
        evidence_refs=evidence_refs,
    )


def _build_v55c_governance_calibration_register(
    *,
    v55a_unresolved_path: str,
    v55b_report_path: str,
    v55b_unresolved_path: str,
    v55b_evidence_path: str,
    v55b_report: ConstitutionalCoherenceReport,
    v55a_unresolved: ConstitutionalUnresolvedSeamRegister,
    v55b_unresolved: ConstitutionalUnresolvedSeamRegister,
) -> ConstitutionalGovernanceCalibrationRegister:
    descendant_warning = next(
        (
            warning
            for warning in v55b_report.warnings
            if warning.code == "DESCENDANT_STRUCTURED_AUTHORITY_LAYER_MISSING"
            and warning.artifact_ref == PREFERRED_DESCENDANT_ARTIFACT
        ),
        None,
    )
    if descendant_warning is None:
        raise ValueError("V55-C requires the shipped V55-B descendant authority-layer warning")

    descendant_gap = next(
        (
            entry
            for entry in v55b_unresolved.entries
            if entry.artifact_ref == PREFERRED_DESCENDANT_ARTIFACT
            and entry.predicate_id == "authority_layer_declared"
            and entry.reason_kind == "descendant_law_gap"
        ),
        None,
    )
    if descendant_gap is None:
        raise ValueError("V55-C requires the shipped V55-B descendant-law gap entry")

    family_gap_entries = [
        entry
        for entry in v55b_unresolved.entries
        if entry.reason_kind == "family_law_gap"
        and entry.predicate_id == "descendant_claim_within_parent_entitlement"
    ]
    if not family_gap_entries:
        raise ValueError("V55-C requires shipped V55-B family-law gap entries")

    admission_gap_entries = [
        entry
        for entry in v55b_unresolved.entries
        if entry.reason_kind == "admission_surface_gap"
        and entry.predicate_id == "support_surface_not_self_promoted"
    ]
    if not admission_gap_entries:
        raise ValueError("V55-C requires shipped V55-B admission-surface gap entries")

    entries = [
        _governance_entry(
            predicate_id="authority_layer_declared",
            surface_ref=PREFERRED_DESCENDANT_ARTIFACT,
            current_posture="v55b_warning_plus_descendant_law_gap",
            recommended_outcome="candidate_for_later_local_hardening",
            rationale=(
                "the preferred crypto descendant is the one concrete local claim surface "
                "with an explicit V55-B warning plus descendant-law gap, so it is the "
                "only predicate/surface pair currently worth carrying forward as a later "
                "local hardening candidate"
            ),
            evidence_refs=[
                v55b_report_path,
                v55b_unresolved_path,
                v55b_evidence_path,
            ],
        ),
        _governance_entry(
            predicate_id="descendant_claim_within_parent_entitlement",
            surface_ref="surface_family:non_descendant_seed_surfaces",
            current_posture=(
                f"{len(family_gap_entries)} v55b family_law_gap entries on "
                "non-descendant seed surfaces"
            ),
            recommended_outcome="not_selected_for_escalation",
            rationale=(
                "these unresolved entries reflect bounded non-descendant scope rather than "
                "a concrete escalation target, so the family-level posture should remain "
                "advisory-only and non-escalated in V55-C"
            ),
            evidence_refs=[
                v55a_unresolved_path,
                v55b_unresolved_path,
            ],
        ),
        _governance_entry(
            predicate_id="support_surface_not_self_promoted",
            surface_ref="surface_family:non_support_seed_surfaces",
            current_posture=(
                f"{len(admission_gap_entries)} v55b admission_surface_gap entries on "
                "non-support seed surfaces"
            ),
            recommended_outcome="not_selected_for_escalation",
            rationale=(
                "the admission-surface gaps still describe scope-bounded non-applicability "
                "rather than a predicate/surface pair ready for stronger local governance"
            ),
            evidence_refs=[
                v55a_unresolved_path,
                v55b_unresolved_path,
            ],
        ),
    ]
    return ConstitutionalGovernanceCalibrationRegister(
        register_id=compute_constitutional_governance_calibration_register_id(
            target_arc=V55C_TARGET_ARC,
            target_path=V55C_TARGET_PATH,
            calibration_ids=[entry.calibration_id for entry in entries],
        ),
        target_arc=V55C_TARGET_ARC,
        target_path=V55C_TARGET_PATH,
        baseline_checker_version=V55B_CHECKER_VERSION,
        entry_count=len(entries),
        entries=entries,
    )


def _build_v55c_migration_decision_register(
    *,
    v55a_report_path: str,
    v55b_report_path: str,
    v55b_unresolved_path: str,
    v55b_drift_path: str,
    v55b_evidence_path: str,
) -> ConstitutionalMigrationDecisionRegister:
    entries = [
        _migration_entry(
            surface_id="checker_exit_codes",
            current_posture="warning_only_exit_zero_in_v55a_and_v55b",
            recommended_outcome="keep_warning_only",
            rationale=(
                "V55-C is advisory-only, so checker exit codes must stay warning-only "
                "until a later explicit migration lane selects stronger local gating"
            ),
            evidence_refs=[v55b_evidence_path, v55b_drift_path],
        ),
        _migration_entry(
            surface_id="warning_behavior",
            current_posture="warnings_emitted_without_live_promotion",
            recommended_outcome="keep_warning_only",
            rationale=(
                "the inherited warning behavior remains the bounded live posture for the "
                "constitutional coherence checker family in V55-C"
            ),
            evidence_refs=[v55a_report_path, v55b_report_path, v55b_evidence_path],
        ),
        _migration_entry(
            surface_id="report_semantics",
            current_posture="report_provenance_is_multi_artifact_not_report_only",
            recommended_outcome="needs_more_evidence",
            rationale=(
                "the shipped report surface is not yet self-sufficient for audit without "
                "the paired unresolved register, lane-drift record, and evidence input, "
                "so report-semantics changes should stay deferred"
            ),
            evidence_refs=[
                v55a_report_path,
                v55b_report_path,
                v55b_drift_path,
                v55b_evidence_path,
            ],
        ),
        _migration_entry(
            surface_id="unresolved_seam_emission",
            current_posture="unresolved_seams_remain_visible_and_non_gating",
            recommended_outcome="keep_warning_only",
            rationale=(
                "V55-C should preserve unresolved-seam visibility while keeping those "
                "outputs advisory-only and non-live by default"
            ),
            evidence_refs=[v55b_unresolved_path, v55b_evidence_path],
        ),
        _migration_entry(
            surface_id="checker_global_escalation",
            current_posture="not_selected_in_v55c",
            recommended_outcome="not_selected_for_escalation",
            rationale=(
                "the lane is bounded to per-predicate/per-surface decisions only, so "
                "checker-global escalation stays outside the selected scope"
            ),
            evidence_refs=[v55b_drift_path, v55b_evidence_path],
        ),
        _migration_entry(
            surface_id="ci_branch_protection",
            current_posture="not_selected_in_v55c",
            recommended_outcome="not_selected_for_escalation",
            rationale=(
                "repo-wide CI or branch-protection gating remains explicitly deferred beyond V55-C"
            ),
            evidence_refs=[v55b_drift_path, v55b_evidence_path],
        ),
    ]
    return ConstitutionalMigrationDecisionRegister(
        register_id=compute_constitutional_migration_decision_register_id(
            target_arc=V55C_TARGET_ARC,
            target_path=V55C_TARGET_PATH,
            decision_ids=[entry.decision_id for entry in entries],
        ),
        target_arc=V55C_TARGET_ARC,
        target_path=V55C_TARGET_PATH,
        baseline_checker_version=V55B_CHECKER_VERSION,
        entry_count=len(entries),
        entries=entries,
    )


def _unresolved(
    *,
    artifact_ref: str,
    predicate_id: str,
    reason_kind: str,
    required_follow_up: list[str],
) -> ConstitutionalUnresolvedSeamEntry:
    return ConstitutionalUnresolvedSeamEntry(
        seam_id=compute_constitutional_unresolved_seam_entry_id(
            artifact_ref=artifact_ref,
            predicate_id=predicate_id,
        ),
        artifact_ref=artifact_ref,
        predicate_id=predicate_id,
        reason_kind=reason_kind,
        required_follow_up=required_follow_up,
    )


def run_constitutional_coherence_v55a(
    *,
    repo_root_path: Path | None = None,
    admissions_path: Path | None = None,
) -> tuple[ConstitutionalCoherenceReport, ConstitutionalUnresolvedSeamRegister]:
    root = repo_root_path or repo_root(anchor=Path(__file__))
    resolved_admissions = _resolve_path(
        repo_root_path=root,
        value=str(admissions_path or DEFAULT_ADMISSIONS_PATH),
    )
    records = _canonicalize_admitted_seed_records(
        load_support_admission_records(path=resolved_admissions)
    )
    evaluations: list[ConstitutionalCoherencePredicateEvaluation] = []
    warnings: list[ConstitutionalCoherenceFinding] = []
    unresolved_entries: list[ConstitutionalUnresolvedSeamEntry] = []

    for record in records:
        surface = _extract_structured_doc_surface(
            repo_root_path=root,
            artifact_ref=record.artifact_ref,
        )

        evaluations.append(
            _evaluation(
                predicate_id="authority_layer_declared",
                artifact_ref=record.artifact_ref,
                status="pass",
                evidence_source="support_admission_record",
                detail_note=f"authority layer declared as {record.authority_layer}",
            )
        )
        evaluations.append(
            _evaluation(
                predicate_id="authority_relation_legal",
                artifact_ref=record.artifact_ref,
                status="pass",
                evidence_source="support_admission_record",
                detail_note=(f"authority relation admitted as {record.current_authority_relation}"),
            )
        )
        evaluations.append(
            _evaluation(
                predicate_id="placement_basis_present_when_required",
                artifact_ref=record.artifact_ref,
                status="pass",
                evidence_source="support_admission_record",
                detail_note=f"placement basis declared as {record.placement_basis}",
            )
        )
        evaluations.append(
            _evaluation(
                predicate_id="coverage_scope_present_when_required",
                artifact_ref=record.artifact_ref,
                status="pass",
                evidence_source="support_admission_record",
                detail_note=(f"coverage scope declared as {record.coverage_scope.scope_kind}"),
            )
        )
        evaluations.append(
            _evaluation(
                predicate_id="dominant_force_band_resolved",
                artifact_ref=record.artifact_ref,
                status="pass",
                evidence_source="support_admission_record",
                detail_note=(f"dominant force band declared as {record.dominant_force_band}"),
            )
        )
        if record.promotion_claim:
            evaluations.append(
                _evaluation(
                    predicate_id="promotion_claim_has_witness",
                    artifact_ref=record.artifact_ref,
                    status="pass",
                    evidence_source="support_admission_record",
                    detail_note=(
                        "promotion witness refs declared: "
                        f"{', '.join(record.promotion_witness_refs)}"
                    ),
                )
            )
        else:
            evaluations.append(
                _evaluation(
                    predicate_id="promotion_claim_has_witness",
                    artifact_ref=record.artifact_ref,
                    status="pass",
                    evidence_source="support_admission_record",
                    detail_note="no promotion claim declared in starter posture",
                )
            )

        if record.is_descendant_surface:
            evaluations.append(
                _evaluation(
                    predicate_id="descendant_claim_within_parent_entitlement",
                    artifact_ref=record.artifact_ref,
                    status="pass",
                    evidence_source="support_admission_record",
                    detail_note=(
                        "descendant surface kept within parent entitlement under "
                        f"{record.parent_family_ref}"
                    ),
                )
            )
        else:
            evaluations.append(
                _evaluation(
                    predicate_id="descendant_claim_within_parent_entitlement",
                    artifact_ref=record.artifact_ref,
                    status="not_evaluable_yet",
                    evidence_source="support_admission_record",
                    detail_note="artifact is not declared as a descendant surface",
                )
            )
            unresolved_entries.append(
                _unresolved(
                    artifact_ref=record.artifact_ref,
                    predicate_id="descendant_claim_within_parent_entitlement",
                    reason_kind="not_evaluable_yet",
                    required_follow_up=[
                        (
                            "keep descendant-specific predicate evaluation limited to "
                            "declared descendants"
                        ),
                    ],
                )
            )

        evaluations.append(
            _evaluation(
                predicate_id="projection_does_not_mint_authority",
                artifact_ref=record.artifact_ref,
                status="pass" if not record.projection_mints_authority else "warn",
                evidence_source="support_admission_record",
                detail_note=(
                    "projection posture keeps authority minting disabled"
                    if not record.projection_mints_authority
                    else "projection posture appears to mint authority"
                ),
            )
        )
        if record.projection_mints_authority:
            warnings.append(
                _warning(
                    code="PROJECTION_MINTS_AUTHORITY",
                    artifact_ref=record.artifact_ref,
                    predicate_id="projection_does_not_mint_authority",
                    message="projection posture must not mint authority in V55-A",
                )
            )

        if record.authority_layer == "support":
            legal_support_relations = {
                "support_shaping_only",
                "support_descendant_exemplar",
                "coexisting_non_override",
            }
            is_legal = record.current_authority_relation in legal_support_relations
            evaluations.append(
                _evaluation(
                    predicate_id="support_surface_not_self_promoted",
                    artifact_ref=record.artifact_ref,
                    status="pass" if is_legal else "warn",
                    evidence_source="support_admission_record",
                    detail_note=(
                        "support surface remains non-promoted"
                        if is_legal
                        else "support surface looks self-promoted"
                    ),
                )
            )
            if not is_legal:
                warnings.append(
                    _warning(
                        code="SUPPORT_SURFACE_SELF_PROMOTED",
                        artifact_ref=record.artifact_ref,
                        predicate_id="support_surface_not_self_promoted",
                        message="support surface must not self-promote in V55-A",
                    )
                )
        else:
            evaluations.append(
                _evaluation(
                    predicate_id="support_surface_not_self_promoted",
                    artifact_ref=record.artifact_ref,
                    status="not_evaluable_yet",
                    evidence_source="support_admission_record",
                    detail_note="predicate applies only to support-layer surfaces",
                )
            )
            unresolved_entries.append(
                _unresolved(
                    artifact_ref=record.artifact_ref,
                    predicate_id="support_surface_not_self_promoted",
                    reason_kind="not_evaluable_yet",
                    required_follow_up=[
                        "keep support-self-promotion checks scoped to admitted support surfaces",
                    ],
                )
            )

        if surface.status_line is None and surface.json_block_count == 0:
            warnings.append(
                _warning(
                    code="NO_STRUCTURED_DOC_CLAIMS_VISIBLE",
                    artifact_ref=record.artifact_ref,
                    predicate_id="authority_layer_declared",
                    message=(
                        "seed artifact exposes no visible status line or json block; "
                        "starter evaluation depends entirely on the admission record"
                    ),
                )
            )

    checked_artifact_refs = [record.artifact_ref for record in records]
    report = ConstitutionalCoherenceReport(
        report_id=compute_constitutional_report_id(
            target_arc=TARGET_ARC,
            target_path=TARGET_PATH,
            checked_artifact_refs=checked_artifact_refs,
            checker_version=CHECKER_VERSION,
        ),
        target_arc=TARGET_ARC,
        target_path=TARGET_PATH,
        checker_version=CHECKER_VERSION,
        checked_artifact_refs=checked_artifact_refs,
        evaluations=evaluations,
        warning_count=len(warnings),
        warnings=warnings,
    )
    unresolved_register = ConstitutionalUnresolvedSeamRegister(
        register_id=compute_constitutional_unresolved_seam_register_id(
            target_arc=TARGET_ARC,
            target_path=TARGET_PATH,
            seam_ids=[entry.seam_id for entry in unresolved_entries],
        ),
        target_arc=TARGET_ARC,
        target_path=TARGET_PATH,
        entry_count=len(unresolved_entries),
        entries=unresolved_entries,
    )
    return report, unresolved_register


def run_constitutional_coherence_v55b(
    *,
    repo_root_path: Path | None = None,
    admissions_path: Path | None = None,
    lane_drift_path: Path | None = None,
) -> tuple[ConstitutionalCoherenceReport, ConstitutionalUnresolvedSeamRegister]:
    root = repo_root_path or repo_root(anchor=Path(__file__))
    resolved_admissions = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(admissions_path or DEFAULT_V55B_ADMISSIONS_PATH),
    )
    resolved_lane_drift = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(lane_drift_path or DEFAULT_V55B_DRIFT_RECORD_PATH),
    )
    _validate_v55b_lane_drift_record(load_lane_drift_record(path=resolved_lane_drift))

    records = _canonicalize_admitted_seed_records(
        load_support_admission_records(path=resolved_admissions)
    )
    descendant_record = _v55b_descendant_record(records)

    base_report, base_unresolved = run_constitutional_coherence_v55a(
        repo_root_path=root,
        admissions_path=resolved_admissions,
    )
    descendant_warnings, descendant_unresolved = _build_v55b_descendant_hardening(
        repo_root_path=root,
        descendant_record=descendant_record,
    )

    warnings = [*base_report.warnings, *descendant_warnings]
    unresolved_entries = [
        *(_reclassify_v55b_unresolved_entry(entry) for entry in base_unresolved.entries),
        *descendant_unresolved,
    ]
    checked_artifact_refs = list(base_report.checked_artifact_refs)
    report = ConstitutionalCoherenceReport(
        report_id=compute_constitutional_report_id(
            target_arc=V55B_TARGET_ARC,
            target_path=V55B_TARGET_PATH,
            checked_artifact_refs=checked_artifact_refs,
            checker_version=V55B_CHECKER_VERSION,
        ),
        target_arc=V55B_TARGET_ARC,
        target_path=V55B_TARGET_PATH,
        checker_version=V55B_CHECKER_VERSION,
        checked_artifact_refs=checked_artifact_refs,
        evaluations=list(base_report.evaluations),
        warning_count=len(warnings),
        warnings=warnings,
    )
    unresolved_register = ConstitutionalUnresolvedSeamRegister(
        register_id=compute_constitutional_unresolved_seam_register_id(
            target_arc=V55B_TARGET_ARC,
            target_path=V55B_TARGET_PATH,
            seam_ids=[entry.seam_id for entry in unresolved_entries],
        ),
        target_arc=V55B_TARGET_ARC,
        target_path=V55B_TARGET_PATH,
        entry_count=len(unresolved_entries),
        entries=unresolved_entries,
    )
    return report, unresolved_register


def run_constitutional_coherence_v55c(
    *,
    repo_root_path: Path | None = None,
    admissions_path: Path | None = None,
    lane_drift_path: Path | None = None,
    v55a_report_path: Path | None = None,
    v55a_unresolved_path: Path | None = None,
    v55b_report_path: Path | None = None,
    v55b_unresolved_path: Path | None = None,
    v55b_drift_path: Path | None = None,
    v55b_evidence_path: Path | None = None,
) -> tuple[
    ConstitutionalGovernanceCalibrationRegister,
    ConstitutionalMigrationDecisionRegister,
]:
    root = repo_root_path or repo_root(anchor=Path(__file__))
    resolved_admissions = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(admissions_path or DEFAULT_V55C_ADMISSIONS_PATH),
    )
    resolved_lane_drift = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(lane_drift_path or DEFAULT_V55C_DRIFT_RECORD_PATH),
    )
    resolved_v55a_report = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(v55a_report_path or DEFAULT_V55C_V55A_REPORT_PATH),
    )
    resolved_v55a_unresolved = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(v55a_unresolved_path or DEFAULT_V55C_V55A_UNRESOLVED_PATH),
    )
    resolved_v55b_report = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(v55b_report_path or DEFAULT_V55C_V55B_REPORT_PATH),
    )
    resolved_v55b_unresolved = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(v55b_unresolved_path or DEFAULT_V55C_V55B_UNRESOLVED_PATH),
    )
    resolved_v55b_drift = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(v55b_drift_path or DEFAULT_V55C_V55B_DRIFT_PATH),
    )
    resolved_v55b_evidence = _resolve_repo_input_path(
        repo_root_path=root,
        value=str(v55b_evidence_path or DEFAULT_V55C_V55B_EVIDENCE_PATH),
    )

    _validate_v55c_lane_drift_record(load_lane_drift_record(path=resolved_lane_drift))
    _canonicalize_admitted_seed_records(load_support_admission_records(path=resolved_admissions))

    _validate_expected_report(
        report=load_coherence_report(path=resolved_v55a_report),
        target_arc=TARGET_ARC,
        target_path=TARGET_PATH,
        checker_version=CHECKER_VERSION,
    )
    v55a_unresolved = _validate_expected_unresolved_register(
        register=load_unresolved_seam_register(path=resolved_v55a_unresolved),
        target_arc=TARGET_ARC,
        target_path=TARGET_PATH,
    )
    v55b_report = _validate_expected_report(
        report=load_coherence_report(path=resolved_v55b_report),
        target_arc=V55B_TARGET_ARC,
        target_path=V55B_TARGET_PATH,
        checker_version=V55B_CHECKER_VERSION,
    )
    v55b_unresolved = _validate_expected_unresolved_register(
        register=load_unresolved_seam_register(path=resolved_v55b_unresolved),
        target_arc=V55B_TARGET_ARC,
        target_path=V55B_TARGET_PATH,
    )
    v55b_drift = _validate_v55b_lane_drift_record(load_lane_drift_record(path=resolved_v55b_drift))
    _validate_v55b_evidence_payload(
        _load_json_object(path=resolved_v55b_evidence, error_label="V55-B evidence"),
        report=v55b_report,
        unresolved=v55b_unresolved,
        lane_drift=v55b_drift,
    )

    governance_register = _build_v55c_governance_calibration_register(
        v55a_unresolved_path=str(resolved_v55a_unresolved.relative_to(root)),
        v55b_report_path=str(resolved_v55b_report.relative_to(root)),
        v55b_unresolved_path=str(resolved_v55b_unresolved.relative_to(root)),
        v55b_evidence_path=str(resolved_v55b_evidence.relative_to(root)),
        v55b_report=v55b_report,
        v55a_unresolved=v55a_unresolved,
        v55b_unresolved=v55b_unresolved,
    )
    migration_register = _build_v55c_migration_decision_register(
        v55a_report_path=str(resolved_v55a_report.relative_to(root)),
        v55b_report_path=str(resolved_v55b_report.relative_to(root)),
        v55b_unresolved_path=str(resolved_v55b_unresolved.relative_to(root)),
        v55b_drift_path=str(resolved_v55b_drift.relative_to(root)),
        v55b_evidence_path=str(resolved_v55b_evidence.relative_to(root)),
    )
    return governance_register, migration_register


def render_report_payload(report: ConstitutionalCoherenceReport) -> str:
    return json.dumps(report.model_dump(by_alias=True), indent=2, sort_keys=True) + "\n"


def render_unresolved_register_payload(register: ConstitutionalUnresolvedSeamRegister) -> str:
    return json.dumps(register.model_dump(by_alias=True), indent=2, sort_keys=True) + "\n"


def render_governance_calibration_register_payload(
    register: ConstitutionalGovernanceCalibrationRegister,
) -> str:
    return json.dumps(register.model_dump(by_alias=True), indent=2, sort_keys=True) + "\n"


def render_migration_decision_register_payload(
    register: ConstitutionalMigrationDecisionRegister,
) -> str:
    return json.dumps(register.model_dump(by_alias=True), indent=2, sort_keys=True) + "\n"
