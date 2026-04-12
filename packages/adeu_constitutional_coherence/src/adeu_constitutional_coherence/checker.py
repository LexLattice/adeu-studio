from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

from adeu_ir.repo import repo_root

from .models import (
    CONSTITUTIONAL_SUPPORT_ADMISSION_RECORD_SCHEMA,
    ConstitutionalCoherenceFinding,
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
DEFAULT_ADMISSIONS_PATH = (
    "packages/adeu_constitutional_coherence/tests/fixtures/v55a/"
    "constitutional_support_admission_records_v55a.json"
)

_JSON_BLOCK_SCHEMA_RE = re.compile(r'"schema"\s*:\s*"([^"]+)"')
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
    doc_path = _resolve_path(repo_root_path=repo_root_path, value=artifact_ref)
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
            continue
        match = _JSON_BLOCK_SCHEMA_RE.search(block_text)
        if match is not None:
            json_block_schemas.append(match.group(1))
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
    records = [
        ConstitutionalSupportAdmissionRecord.model_validate(item)
        for item in payload
    ]
    seen: set[str] = set()
    for record in records:
        if record.artifact_ref in seen:
            raise ValueError(f"duplicate artifact_ref in admission records: {record.artifact_ref}")
        seen.add(record.artifact_ref)
    return records


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
    records = load_support_admission_records(path=resolved_admissions)
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
                detail_note=(
                    "authority relation admitted as "
                    f"{record.current_authority_relation}"
                ),
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
                detail_note=(
                    "coverage scope declared as "
                    f"{record.coverage_scope.scope_kind}"
                ),
            )
        )
        evaluations.append(
            _evaluation(
                predicate_id="dominant_force_band_resolved",
                artifact_ref=record.artifact_ref,
                status="pass",
                evidence_source="support_admission_record",
                detail_note=(
                    "dominant force band declared as "
                    f"{record.dominant_force_band}"
                ),
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


def render_report_payload(report: ConstitutionalCoherenceReport) -> str:
    return json.dumps(report.model_dump(by_alias=True), indent=2, sort_keys=True) + "\n"


def render_unresolved_register_payload(register: ConstitutionalUnresolvedSeamRegister) -> str:
    return json.dumps(register.model_dump(by_alias=True), indent=2, sort_keys=True) + "\n"
