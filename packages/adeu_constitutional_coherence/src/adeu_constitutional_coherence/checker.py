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
    ConstitutionalSupportAdmissionRecord,
    ConstitutionalUnresolvedSeamEntry,
    ConstitutionalUnresolvedSeamRegister,
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
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
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


def render_report_payload(report: ConstitutionalCoherenceReport) -> str:
    return json.dumps(report.model_dump(by_alias=True), indent=2, sort_keys=True) + "\n"


def render_unresolved_register_payload(register: ConstitutionalUnresolvedSeamRegister) -> str:
    return json.dumps(register.model_dump(by_alias=True), indent=2, sort_keys=True) + "\n"
