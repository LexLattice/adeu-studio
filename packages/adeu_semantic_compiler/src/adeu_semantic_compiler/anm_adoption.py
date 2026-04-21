from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Literal

from adeu_commitments_ir import (
    AnmCompileAdvisoryResult,
    AnmCompileDiagnosticRow,
    AnmCompileReport,
    AnmDocAuthorityProfile,
    AnmDocClassPolicy,
    AnmMigrationBindingProfile,
    AnmProseBoundaryNoticeRow,
    AnmProseBoundaryNoticeSet,
    AnmReaderProjectionManifest,
    AnmSemanticDiffReport,
    AnmSourceSetManifest,
    AnmV66CConsumedLineage,
    AnmV66CPolicyAnchor,
    canonicalize_anm_doc_authority_profile_payload,
    canonicalize_anm_doc_class_policy_payload,
    canonicalize_anm_migration_binding_profile_payload,
    canonicalize_anm_reader_projection_manifest_payload,
    canonicalize_anm_semantic_diff_report_payload,
    canonicalize_anm_source_set_manifest_payload,
    stable_payload_hash,
)
from adeu_semantic_source import AnmCompileError, inspect_v66a_source

_NORMATIVE_TONE_RE = re.compile(
    r"\b(must(?:\s+not)?|shall|required|forbidden|may\s+not)\b",
    re.IGNORECASE,
)
_FROZEN_POLICY_ANCHOR_SCHEMA_ID = "anm_v66c_frozen_policy_anchor@1"
_POLICY_ANCHOR_REF = "anm_v66c_policy_anchor:starter"
_ADVISORY_OUTCOME_REDUCER_REF = "anm_v66c_advisory_outcome_reducer:starter"
_NOTICE_DETECTION_POLICY_REF = "anm_v66c_notice_detection_policy:starter"
_REASON_CURRENT_GUARDRAILS = "ANM_V66C_CURRENT_GUARDRAILS_SUFFICIENT"
_REASON_NEEDS_MORE_REGISTRATION = "ANM_V66C_NEEDS_MORE_REGISTRATION"
_REASON_NEEDS_PROJECTION_REFRESH = "ANM_V66C_NEEDS_PROJECTION_REFRESH"
_REASON_NEEDS_TRANSITION_LAW_REVIEW = "ANM_V66C_NEEDS_TRANSITION_LAW_REVIEW"
_REASON_MARKDOWN_TRANSITION_CANDIDATE = (
    "ANM_V66C_CANDIDATE_FOR_LATER_MARKDOWN_TRANSITION_REVIEW"
)
_REASON_INVALID_PRIOR_BASIS = "ANM_V66C_INVALID_PRIOR_BASIS"
_REASON_INVALID_POLICY_ANCHOR = "ANM_V66C_INVALID_POLICY_ANCHOR"
_REASON_INVALID_NOTICE_EVIDENCE = "ANM_V66C_INVALID_NOTICE_EVIDENCE"
_REASON_INVALID_AUTHORITY_CLAIM = "ANM_V66C_INVALID_AUTHORITY_CLAIM"

_NOTICE_DETECTION_POLICY_PAYLOAD = {
    "schema_id": _FROZEN_POLICY_ANCHOR_SCHEMA_ID,
    "notice_kinds": [
        "class_policy_overpromotion_risk",
        "generated_projection_authority_overread_risk",
        "normative_tone_without_compiled_authority_block",
        "projection_staleness_visible",
        "transition_law_scope_ambiguity",
    ],
    "normative_tone_regex": _NORMATIVE_TONE_RE.pattern,
    "sample_kinds": ["example_block", "plain_prose", "quoted_text"],
}
_ADVISORY_OUTCOME_REDUCER_PAYLOAD = {
    "schema_id": _FROZEN_POLICY_ANCHOR_SCHEMA_ID,
    "valid_precedence": [
        "needs_projection_refresh",
        "needs_transition_law_review",
        "needs_more_registration",
        "candidate_for_later_markdown_transition_review",
        "current_guardrails_sufficient",
    ],
    "invalid_statuses": [
        "invalid_authority_claim_rejected",
        "invalid_missing_prior_basis",
        "invalid_notice_evidence",
        "invalid_policy_anchor",
        "invalid_prior_basis_hash_mismatch",
        "invalid_unsupported_schema",
    ],
}
_POLICY_ANCHOR_PAYLOAD = {
    "schema_id": _FROZEN_POLICY_ANCHOR_SCHEMA_ID,
    "policy_anchor_ref": _POLICY_ANCHOR_REF,
    "advisory_outcome_reducer_ref": _ADVISORY_OUTCOME_REDUCER_REF,
    "notice_detection_policy_ref": _NOTICE_DETECTION_POLICY_REF,
}

V66CProseBoundarySampleKind = Literal["plain_prose", "quoted_text", "example_block"]


@dataclass(frozen=True)
class V66CAdoptionHardeningResult:
    compile_report: AnmCompileReport
    prose_boundary_notice_set: AnmProseBoundaryNoticeSet


@dataclass(frozen=True)
class _ProseBoundarySample:
    sample_ref: str
    source_doc_ref: str
    sample_text: str
    sample_kind: V66CProseBoundarySampleKind


def _load_manifest(payload: AnmSourceSetManifest | dict[str, Any]) -> AnmSourceSetManifest:
    return (
        payload
        if isinstance(payload, AnmSourceSetManifest)
        else AnmSourceSetManifest.model_validate(payload)
    )


def _load_policy(payload: AnmDocClassPolicy | dict[str, Any]) -> AnmDocClassPolicy:
    return (
        payload
        if isinstance(payload, AnmDocClassPolicy)
        else AnmDocClassPolicy.model_validate(payload)
    )


def _load_profiles(
    payloads: list[AnmDocAuthorityProfile | dict[str, Any]],
) -> list[AnmDocAuthorityProfile]:
    profiles = [
        payload
        if isinstance(payload, AnmDocAuthorityProfile)
        else AnmDocAuthorityProfile.model_validate(payload)
        for payload in payloads
    ]
    doc_refs = [item.doc_ref for item in profiles]
    if doc_refs != sorted(doc_refs):
        raise AnmCompileError("authority profiles must be sorted by doc_ref for V66-C")
    if len(doc_refs) != len(set(doc_refs)):
        raise AnmCompileError("authority profiles must not contain duplicate doc_ref values")
    return profiles


def _load_migration(
    payload: AnmMigrationBindingProfile | dict[str, Any],
) -> AnmMigrationBindingProfile:
    return (
        payload
        if isinstance(payload, AnmMigrationBindingProfile)
        else AnmMigrationBindingProfile.model_validate(payload)
    )


def _load_projection(
    payload: AnmReaderProjectionManifest | dict[str, Any] | None,
) -> AnmReaderProjectionManifest | None:
    if payload is None:
        return None
    return (
        payload
        if isinstance(payload, AnmReaderProjectionManifest)
        else AnmReaderProjectionManifest.model_validate(payload)
    )


def _load_diff(
    payload: AnmSemanticDiffReport | dict[str, Any] | None,
) -> AnmSemanticDiffReport | None:
    if payload is None:
        return None
    return (
        payload
        if isinstance(payload, AnmSemanticDiffReport)
        else AnmSemanticDiffReport.model_validate(payload)
    )


def _load_samples(samples: list[dict[str, Any]] | None) -> list[_ProseBoundarySample]:
    loaded: list[_ProseBoundarySample] = []
    for raw_sample in samples or []:
        sample_ref = str(raw_sample["sample_ref"]).strip()
        source_doc_ref = str(raw_sample["source_doc_ref"]).strip()
        sample_text = str(raw_sample["sample_text"])
        sample_kind = raw_sample["sample_kind"]
        if not sample_ref:
            raise AnmCompileError("selected prose-boundary sample refs must not be empty")
        if not source_doc_ref:
            raise AnmCompileError("selected prose-boundary sample source_doc_ref must not be empty")
        if sample_kind not in {"plain_prose", "quoted_text", "example_block"}:
            raise AnmCompileError(f"unsupported V66-C prose sample kind: {sample_kind!r}")
        loaded.append(
            _ProseBoundarySample(
                sample_ref=sample_ref,
                source_doc_ref=source_doc_ref,
                sample_text=sample_text,
                sample_kind=sample_kind,
            )
        )
    sample_refs = [item.sample_ref for item in loaded]
    if sample_refs != sorted(sample_refs):
        raise AnmCompileError("selected prose-boundary sample refs must be sorted")
    if len(sample_refs) != len(set(sample_refs)):
        raise AnmCompileError("selected prose-boundary sample refs must be unique")
    return loaded


def _manifest_ref(manifest: AnmSourceSetManifest) -> str:
    return f"anm_source_set_manifest:{manifest.manifest_id}"


def _policy_ref(policy: AnmDocClassPolicy) -> str:
    return f"anm_doc_class_policy:{policy.policy_id}"


def _migration_ref(profile: AnmMigrationBindingProfile) -> str:
    return f"anm_migration_binding_profile:{profile.migration_binding_profile_id}"


def _projection_ref(manifest: AnmReaderProjectionManifest | None) -> str | None:
    if manifest is None:
        return None
    return f"anm_reader_projection_manifest:{manifest.projection_manifest_id}"


def _diff_ref(report: AnmSemanticDiffReport | None) -> str | None:
    if report is None:
        return None
    return f"anm_semantic_diff_report:{report.diff_report_id}"


def _profile_basis_hash(profiles: list[AnmDocAuthorityProfile]) -> str:
    return stable_payload_hash(
        [canonicalize_anm_doc_authority_profile_payload(item) for item in profiles]
    )


def _require_basis_alignment(
    *,
    manifest: AnmSourceSetManifest,
    authority_profiles: list[AnmDocAuthorityProfile],
    class_policy: AnmDocClassPolicy,
    migration_binding_profile: AnmMigrationBindingProfile,
    reader_projection_manifest: AnmReaderProjectionManifest | None,
    semantic_diff_report: AnmSemanticDiffReport | None,
) -> list[AnmCompileDiagnosticRow]:
    diagnostics: list[AnmCompileDiagnosticRow] = []
    manifest_ref = _manifest_ref(manifest)
    manifest_hash = stable_payload_hash(canonicalize_anm_source_set_manifest_payload(manifest))
    policy_ref = _policy_ref(class_policy)
    policy_hash = stable_payload_hash(canonicalize_anm_doc_class_policy_payload(class_policy))
    profiles_hash = _profile_basis_hash(authority_profiles)
    expected_profile_ref = f"sha256:{profiles_hash}"

    for profile in (migration_binding_profile, reader_projection_manifest, semantic_diff_report):
        if profile is None:
            continue
        subject_ref = getattr(
            profile,
            "migration_binding_profile_id",
            getattr(profile, "projection_manifest_id", getattr(profile, "diff_report_id", "v66c")),
        )
        profile_manifest_ref = profile.consumed_source_set_manifest_ref
        profile_manifest_hash = profile.consumed_source_set_manifest_hash
        profile_policy_ref = profile.consumed_doc_class_policy_ref
        profile_policy_hash = profile.consumed_doc_class_policy_hash
        profile_profiles_ref = profile.consumed_authority_profile_set_ref_or_hash
        if (
            profile_manifest_ref != manifest_ref
            or profile_manifest_hash != manifest_hash
            or profile_policy_ref != policy_ref
            or profile_policy_hash != policy_hash
            or profile_profiles_ref != expected_profile_ref
        ):
            diagnostics.append(
                AnmCompileDiagnosticRow(
                    diagnostic_id=f"diag:prior_basis_hash_mismatch:{subject_ref}",
                    diagnostic_kind="prior_basis_hash_mismatch",
                    severity="error",
                    source_surface={
                        "migration_binding_profile_id": "v66b_migration_binding_profile",
                        "projection_manifest_id": "v66b_reader_projection_manifest",
                        "diff_report_id": "v66b_semantic_diff_report",
                    }[
                        "migration_binding_profile_id"
                        if hasattr(profile, "migration_binding_profile_id")
                        else "projection_manifest_id"
                        if hasattr(profile, "projection_manifest_id")
                        else "diff_report_id"
                    ],
                    subject_ref=str(subject_ref),
                    evidence_refs=sorted(
                        {
                            manifest_ref,
                            policy_ref,
                            expected_profile_ref,
                        }
                    ),
                    advisory_effect="none",
                    authority_effect="current_markdown_remains_controlling",
                )
            )
    return diagnostics


def _require_selected_v66b_inputs(
    *,
    migration_binding_profile: AnmMigrationBindingProfile,
    reader_projection_manifest: AnmReaderProjectionManifest | None,
    semantic_diff_report: AnmSemanticDiffReport | None,
) -> list[AnmCompileDiagnosticRow]:
    diagnostics: list[AnmCompileDiagnosticRow] = []
    if any(row.generated_reader_projection_refs for row in migration_binding_profile.binding_rows):
        if reader_projection_manifest is None:
            diagnostics.append(
                AnmCompileDiagnosticRow(
                    diagnostic_id="diag:prior_basis_missing:reader_projection_manifest",
                    diagnostic_kind="prior_basis_missing",
                    severity="error",
                    source_surface="v66b_reader_projection_manifest",
                    subject_ref="anm_reader_projection_manifest",
                    evidence_refs=[_migration_ref(migration_binding_profile)],
                    advisory_effect="none",
                    authority_effect="current_markdown_remains_controlling",
                )
            )
    if any(row.semantic_diff_ref_or_none for row in migration_binding_profile.binding_rows):
        if semantic_diff_report is None:
            diagnostics.append(
                AnmCompileDiagnosticRow(
                    diagnostic_id="diag:prior_basis_missing:semantic_diff_report",
                    diagnostic_kind="prior_basis_missing",
                    severity="error",
                    source_surface="v66b_semantic_diff_report",
                    subject_ref="anm_semantic_diff_report",
                    evidence_refs=[_migration_ref(migration_binding_profile)],
                    advisory_effect="none",
                    authority_effect="current_markdown_remains_controlling",
                )
            )
    return diagnostics


def _policy_anchor() -> AnmV66CPolicyAnchor:
    return AnmV66CPolicyAnchor(
        policy_anchor_ref=_POLICY_ANCHOR_REF,
        policy_anchor_hash=stable_payload_hash(_POLICY_ANCHOR_PAYLOAD),
        policy_anchor_schema_id=_FROZEN_POLICY_ANCHOR_SCHEMA_ID,
        advisory_outcome_reducer_ref=_ADVISORY_OUTCOME_REDUCER_REF,
        advisory_outcome_reducer_hash=stable_payload_hash(_ADVISORY_OUTCOME_REDUCER_PAYLOAD),
        notice_detection_policy_ref=_NOTICE_DETECTION_POLICY_REF,
        notice_detection_policy_hash=stable_payload_hash(_NOTICE_DETECTION_POLICY_PAYLOAD),
    )


def _build_policy_anchor_or_diagnostic() -> tuple[
    AnmV66CPolicyAnchor, list[AnmCompileDiagnosticRow]
]:
    try:
        return _policy_anchor(), []
    except ValueError:
        fallback = AnmV66CPolicyAnchor(
            policy_anchor_ref=_POLICY_ANCHOR_REF,
            policy_anchor_hash=stable_payload_hash(_POLICY_ANCHOR_PAYLOAD),
            policy_anchor_schema_id=_FROZEN_POLICY_ANCHOR_SCHEMA_ID,
            advisory_outcome_reducer_ref=_ADVISORY_OUTCOME_REDUCER_REF,
            advisory_outcome_reducer_hash=stable_payload_hash(_ADVISORY_OUTCOME_REDUCER_PAYLOAD),
            notice_detection_policy_ref=_NOTICE_DETECTION_POLICY_REF,
            notice_detection_policy_hash=stable_payload_hash(_NOTICE_DETECTION_POLICY_PAYLOAD),
        )
        return (
            fallback,
            [
                AnmCompileDiagnosticRow(
                    diagnostic_id="diag:policy_anchor_invalid",
                    diagnostic_kind="policy_anchor_invalid",
                    severity="error",
                    source_surface="frozen_policy_anchor",
                    subject_ref=_POLICY_ANCHOR_REF,
                    evidence_refs=[_POLICY_ANCHOR_REF],
                    advisory_effect="none",
                    authority_effect="current_markdown_remains_controlling",
                )
            ],
        )


def _consumed_lineage(
    *,
    manifest: AnmSourceSetManifest,
    authority_profiles: list[AnmDocAuthorityProfile],
    class_policy: AnmDocClassPolicy,
    migration_binding_profile: AnmMigrationBindingProfile,
    reader_projection_manifest: AnmReaderProjectionManifest | None,
    semantic_diff_report: AnmSemanticDiffReport | None,
) -> AnmV66CConsumedLineage:
    return AnmV66CConsumedLineage(
        consumed_v66a_source_set_manifest_ref=_manifest_ref(manifest),
        consumed_v66a_source_set_manifest_hash=stable_payload_hash(
            canonicalize_anm_source_set_manifest_payload(manifest)
        ),
        consumed_v66a_authority_profile_set_ref_or_hash=f"sha256:{_profile_basis_hash(authority_profiles)}",
        consumed_v66a_doc_class_policy_ref=_policy_ref(class_policy),
        consumed_v66a_doc_class_policy_hash=stable_payload_hash(
            canonicalize_anm_doc_class_policy_payload(class_policy)
        ),
        consumed_v66b_migration_binding_profile_ref=_migration_ref(migration_binding_profile),
        consumed_v66b_migration_binding_profile_hash=stable_payload_hash(
            canonicalize_anm_migration_binding_profile_payload(migration_binding_profile)
        ),
        consumed_v66b_reader_projection_manifest_ref_or_none=_projection_ref(reader_projection_manifest),
        consumed_v66b_reader_projection_manifest_hash_or_none=(
            stable_payload_hash(
                canonicalize_anm_reader_projection_manifest_payload(reader_projection_manifest)
            )
            if reader_projection_manifest is not None
            else None
        ),
        consumed_v66b_semantic_diff_report_ref_or_none=_diff_ref(semantic_diff_report),
        consumed_v66b_semantic_diff_report_hash_or_none=(
            stable_payload_hash(canonicalize_anm_semantic_diff_report_payload(semantic_diff_report))
            if semantic_diff_report is not None
            else None
        ),
    )


def _normative_tone_notice_rows(
    *,
    samples: list[_ProseBoundarySample],
    governed_doc_refs: set[str],
) -> tuple[list[AnmProseBoundaryNoticeRow], list[AnmCompileDiagnosticRow]]:
    notices: list[AnmProseBoundaryNoticeRow] = []
    diagnostics: list[AnmCompileDiagnosticRow] = []
    for sample in samples:
        if sample.source_doc_ref not in governed_doc_refs:
            diagnostics.append(
                AnmCompileDiagnosticRow(
                    diagnostic_id=f"diag:notice_evidence_invalid:{sample.sample_ref}",
                    diagnostic_kind="notice_evidence_invalid",
                    severity="error",
                    source_surface="selected_prose_boundary_sample",
                    subject_ref=sample.sample_ref,
                    evidence_refs=[sample.sample_ref],
                    advisory_effect="none",
                    authority_effect="current_markdown_remains_controlling",
                )
            )
            continue
        if sample.sample_kind != "plain_prose":
            continue
        inspected = inspect_v66a_source(source_text=sample.sample_text)
        if inspected["explicit_profile"] is not None or inspected["has_recognized_d1_blocks"]:
            continue
        if _NORMATIVE_TONE_RE.search(sample.sample_text) is None:
            continue
        notices.append(
            AnmProseBoundaryNoticeRow(
                notice_id=f"notice:normative_tone:{sample.sample_ref}",
                notice_kind="normative_tone_without_compiled_authority_block",
                severity="warning",
                source_doc_ref=sample.source_doc_ref,
                subject_ref=sample.sample_ref,
                evidence_refs=[sample.sample_ref],
                compiled_authority_block_ref_or_none=None,
                advisory_effect="registration_review_needed",
                authority_effect="current_markdown_remains_controlling",
            )
        )
    return notices, diagnostics


def _projection_notice_rows(
    projection_manifest: AnmReaderProjectionManifest | None,
) -> tuple[list[AnmProseBoundaryNoticeRow], list[AnmCompileDiagnosticRow]]:
    if projection_manifest is None:
        return [], []
    notices: list[AnmProseBoundaryNoticeRow] = []
    diagnostics: list[AnmCompileDiagnosticRow] = []
    for row in projection_manifest.projection_rows:
        subject_ref = f"projection:{row.projection_doc_ref}"
        if row.projection_authority_posture == "invalid_claims_authority":
            notice = AnmProseBoundaryNoticeRow(
                notice_id=f"notice:projection_authority:{row.projection_doc_ref}",
                notice_kind="generated_projection_authority_overread_risk",
                severity="error",
                source_doc_ref=row.source_doc_ref,
                subject_ref=subject_ref,
                evidence_refs=[subject_ref],
                compiled_authority_block_ref_or_none=None,
                advisory_effect="review_visibility_only",
                authority_effect="invalid_authority_claim_rejected",
            )
            notices.append(notice)
            diagnostics.append(
                AnmCompileDiagnosticRow(
                    diagnostic_id=f"diag:projection_authority:{row.projection_doc_ref}",
                    diagnostic_kind="generated_projection_authority_overread_risk",
                    severity="error",
                    source_surface="v66b_reader_projection_manifest",
                    subject_ref=subject_ref,
                    evidence_refs=[subject_ref],
                    advisory_effect="review_visibility_only",
                    authority_effect="invalid_authority_claim_rejected",
                )
            )
        elif (
            row.projection_status == "stale"
            or row.drift_status == "source_changed_projection_stale"
        ):
            notices.append(
                AnmProseBoundaryNoticeRow(
                    notice_id=f"notice:projection_stale:{row.projection_doc_ref}",
                    notice_kind="projection_staleness_visible",
                    severity="warning",
                    source_doc_ref=row.source_doc_ref,
                    subject_ref=subject_ref,
                    evidence_refs=[subject_ref],
                    compiled_authority_block_ref_or_none=None,
                    advisory_effect="projection_refresh_needed",
                    authority_effect="current_markdown_remains_controlling",
                )
            )
    return notices, diagnostics


def _transition_and_policy_notices(
    *,
    migration_binding_profile: AnmMigrationBindingProfile,
    authority_profiles: list[AnmDocAuthorityProfile],
    class_policy: AnmDocClassPolicy,
) -> list[AnmProseBoundaryNoticeRow]:
    notices: list[AnmProseBoundaryNoticeRow] = []
    for row in migration_binding_profile.binding_rows:
        if row.supersession_claim_status == "claimed_without_transition_law_rejected":
            notices.append(
                AnmProseBoundaryNoticeRow(
                    notice_id=f"notice:transition_scope:{row.binding_id}",
                    notice_kind="transition_law_scope_ambiguity",
                    severity="warning",
                    source_doc_ref=row.host_doc_ref,
                    subject_ref=f"binding:{row.binding_id}",
                    evidence_refs=[f"binding:{row.binding_id}"],
                    compiled_authority_block_ref_or_none=None,
                    advisory_effect="transition_law_review_needed",
                    authority_effect="current_markdown_remains_controlling",
                )
            )
    policy_rows = {row.doc_class: row for row in class_policy.policy_rows}
    for profile in authority_profiles:
        policy_row = policy_rows.get(profile.doc_class)
        if policy_row is None:
            continue
        if set(profile.allowed_outputs) - set(policy_row.allowed_outputs):
            notices.append(
                AnmProseBoundaryNoticeRow(
                    notice_id=f"notice:class_policy_overpromotion:{profile.doc_ref}",
                    notice_kind="class_policy_overpromotion_risk",
                    severity="warning",
                    source_doc_ref=profile.doc_ref,
                    subject_ref=f"profile:{profile.doc_id}",
                    evidence_refs=[f"profile:{profile.doc_id}"],
                    compiled_authority_block_ref_or_none=None,
                    advisory_effect="registration_review_needed",
                    authority_effect="current_markdown_remains_controlling",
                )
            )
    return notices


def build_v66c_prose_boundary_notice_set(
    *,
    manifest: AnmSourceSetManifest | dict[str, Any],
    authority_profiles: list[AnmDocAuthorityProfile | dict[str, Any]],
    class_policy: AnmDocClassPolicy | dict[str, Any],
    migration_binding_profile: AnmMigrationBindingProfile | dict[str, Any],
    reader_projection_manifest: AnmReaderProjectionManifest | dict[str, Any] | None = None,
    semantic_diff_report: AnmSemanticDiffReport | dict[str, Any] | None = None,
    prose_boundary_samples: list[dict[str, Any]] | None = None,
    notice_set_id: str = "notice:v66c-starter",
) -> tuple[AnmProseBoundaryNoticeSet, list[AnmCompileDiagnosticRow]]:
    manifest_model = _load_manifest(manifest)
    profiles_model = _load_profiles(authority_profiles)
    class_policy_model = _load_policy(class_policy)
    migration_model = _load_migration(migration_binding_profile)
    projection_model = _load_projection(reader_projection_manifest)
    diff_model = _load_diff(semantic_diff_report)
    samples = _load_samples(prose_boundary_samples)

    diagnostics = _require_basis_alignment(
        manifest=manifest_model,
        authority_profiles=profiles_model,
        class_policy=class_policy_model,
        migration_binding_profile=migration_model,
        reader_projection_manifest=projection_model,
        semantic_diff_report=diff_model,
    )
    diagnostics.extend(
        _require_selected_v66b_inputs(
            migration_binding_profile=migration_model,
            reader_projection_manifest=projection_model,
            semantic_diff_report=diff_model,
        )
    )

    governed_doc_refs = {entry.doc_ref for entry in manifest_model.source_entries}
    sample_notices, sample_diagnostics = _normative_tone_notice_rows(
        samples=samples,
        governed_doc_refs=governed_doc_refs,
    )
    diagnostics.extend(sample_diagnostics)
    projection_notices, projection_diagnostics = _projection_notice_rows(projection_model)
    diagnostics.extend(projection_diagnostics)
    notice_rows = sample_notices + projection_notices + _transition_and_policy_notices(
        migration_binding_profile=migration_model,
        authority_profiles=profiles_model,
        class_policy=class_policy_model,
    )
    notice_rows.sort(key=lambda item: item.notice_id)
    policy_anchor, policy_anchor_diagnostics = _build_policy_anchor_or_diagnostic()
    diagnostics.extend(policy_anchor_diagnostics)

    report_status = "valid"
    if any(item.diagnostic_kind == "prior_basis_missing" for item in diagnostics):
        report_status = "invalid_missing_prior_basis"
    elif any(item.diagnostic_kind == "prior_basis_hash_mismatch" for item in diagnostics):
        report_status = "invalid_prior_basis_hash_mismatch"
    elif any(item.diagnostic_kind == "policy_anchor_invalid" for item in diagnostics):
        report_status = "invalid_policy_anchor"
    elif any(item.diagnostic_kind == "notice_evidence_invalid" for item in diagnostics):
        report_status = "invalid_notice_evidence"
    elif any(
        item.authority_effect == "invalid_authority_claim_rejected" for item in diagnostics
    ):
        report_status = "invalid_authority_claim_rejected"

    notice_set = AnmProseBoundaryNoticeSet(
        notice_set_id=notice_set_id,
        report_status=report_status,
        consumed_lineage=_consumed_lineage(
            manifest=manifest_model,
            authority_profiles=profiles_model,
            class_policy=class_policy_model,
            migration_binding_profile=migration_model,
            reader_projection_manifest=projection_model,
            semantic_diff_report=diff_model,
        ),
        policy_anchor=policy_anchor,
        notice_rows=notice_rows,
    )
    return notice_set, diagnostics


def _diagnostics_from_notices(
    notices: list[AnmProseBoundaryNoticeRow],
) -> list[AnmCompileDiagnosticRow]:
    return [
        AnmCompileDiagnosticRow(
            diagnostic_id=notice.notice_id.replace("notice:", "diag:"),
            diagnostic_kind=notice.notice_kind,
            severity=notice.severity,
            source_surface=(
                "selected_prose_boundary_sample"
                if notice.notice_kind == "normative_tone_without_compiled_authority_block"
                else "v66b_reader_projection_manifest"
                if notice.notice_kind
                in {
                    "generated_projection_authority_overread_risk",
                    "projection_staleness_visible",
                }
                else "v66b_migration_binding_profile"
                if notice.notice_kind == "transition_law_scope_ambiguity"
                else "v66a_doc_authority_profile"
            ),
            subject_ref=notice.subject_ref,
            evidence_refs=list(notice.evidence_refs),
            advisory_effect=notice.advisory_effect,
            authority_effect=notice.authority_effect,
        )
        for notice in notices
    ]


def _reduce_valid_advisory_result(
    *,
    notice_rows: list[AnmProseBoundaryNoticeRow],
    migration_binding_profile: AnmMigrationBindingProfile,
    policy_anchor: AnmV66CPolicyAnchor,
) -> AnmCompileAdvisoryResult:
    notice_kinds = {row.notice_kind for row in notice_rows}
    reason_codes: set[str] = set()
    if "projection_staleness_visible" in notice_kinds:
        reason_codes.add(_REASON_NEEDS_PROJECTION_REFRESH)
        posture = "needs_projection_refresh"
    elif "transition_law_scope_ambiguity" in notice_kinds:
        reason_codes.add(_REASON_NEEDS_TRANSITION_LAW_REVIEW)
        posture = "needs_transition_law_review"
    elif notice_kinds & {
        "class_policy_overpromotion_risk",
        "normative_tone_without_compiled_authority_block",
    }:
        reason_codes.add(_REASON_NEEDS_MORE_REGISTRATION)
        posture = "needs_more_registration"
    elif any(
        row.supersession_claim_status == "claimed_with_explicit_transition_law"
        for row in migration_binding_profile.binding_rows
    ):
        reason_codes.add(_REASON_MARKDOWN_TRANSITION_CANDIDATE)
        posture = "candidate_for_later_markdown_transition_review"
    else:
        reason_codes.add(_REASON_CURRENT_GUARDRAILS)
        posture = "current_guardrails_sufficient"
    return AnmCompileAdvisoryResult(
        recommended_adoption_posture_or_none=posture,
        reason_codes=sorted(reason_codes),
        reducer_policy_ref=policy_anchor.advisory_outcome_reducer_ref,
        reducer_policy_hash=policy_anchor.advisory_outcome_reducer_hash,
    )


def build_v66c_compile_report(
    *,
    manifest: AnmSourceSetManifest | dict[str, Any],
    authority_profiles: list[AnmDocAuthorityProfile | dict[str, Any]],
    class_policy: AnmDocClassPolicy | dict[str, Any],
    migration_binding_profile: AnmMigrationBindingProfile | dict[str, Any],
    reader_projection_manifest: AnmReaderProjectionManifest | dict[str, Any] | None = None,
    semantic_diff_report: AnmSemanticDiffReport | dict[str, Any] | None = None,
    prose_boundary_notice_set: AnmProseBoundaryNoticeSet | dict[str, Any],
    structural_diagnostics: list[AnmCompileDiagnosticRow] | None = None,
    compile_report_id: str = "compile:v66c-starter",
) -> AnmCompileReport:
    manifest_model = _load_manifest(manifest)
    profiles_model = _load_profiles(authority_profiles)
    class_policy_model = _load_policy(class_policy)
    migration_model = _load_migration(migration_binding_profile)
    projection_model = _load_projection(reader_projection_manifest)
    diff_model = _load_diff(semantic_diff_report)
    notice_set = (
        prose_boundary_notice_set
        if isinstance(prose_boundary_notice_set, AnmProseBoundaryNoticeSet)
        else AnmProseBoundaryNoticeSet.model_validate(prose_boundary_notice_set)
    )
    expected_lineage = _consumed_lineage(
        manifest=manifest_model,
        authority_profiles=profiles_model,
        class_policy=class_policy_model,
        migration_binding_profile=migration_model,
        reader_projection_manifest=projection_model,
        semantic_diff_report=diff_model,
    )

    diagnostics = list(structural_diagnostics or []) + _diagnostics_from_notices(
        notice_set.notice_rows
    )
    if notice_set.consumed_lineage != expected_lineage:
        diagnostics.append(
            AnmCompileDiagnosticRow(
                diagnostic_id="diag:prior_basis_hash_mismatch:notice_set_lineage",
                diagnostic_kind="prior_basis_hash_mismatch",
                severity="error",
                source_surface="v66b_migration_binding_profile",
                subject_ref=notice_set.notice_set_id,
                evidence_refs=[notice_set.notice_set_id],
                advisory_effect="none",
                authority_effect="current_markdown_remains_controlling",
            )
        )
    diagnostics = list({item.diagnostic_id: item for item in diagnostics}.values())
    diagnostics.sort(key=lambda item: item.diagnostic_id)
    report_status = notice_set.report_status
    if any(item.diagnostic_kind == "prior_basis_missing" for item in diagnostics):
        report_status = "invalid_missing_prior_basis"
    elif any(item.diagnostic_kind == "prior_basis_hash_mismatch" for item in diagnostics):
        report_status = "invalid_prior_basis_hash_mismatch"
    elif any(item.diagnostic_kind == "policy_anchor_invalid" for item in diagnostics):
        report_status = "invalid_policy_anchor"
    elif any(item.diagnostic_kind == "notice_evidence_invalid" for item in diagnostics):
        report_status = "invalid_notice_evidence"
    elif any(item.authority_effect == "invalid_authority_claim_rejected" for item in diagnostics):
        report_status = "invalid_authority_claim_rejected"

    if report_status == "valid":
        advisory_result = _reduce_valid_advisory_result(
            notice_rows=notice_set.notice_rows,
            migration_binding_profile=migration_model,
            policy_anchor=notice_set.policy_anchor,
        )
    else:
        reason_code = {
            "invalid_missing_prior_basis": _REASON_INVALID_PRIOR_BASIS,
            "invalid_prior_basis_hash_mismatch": _REASON_INVALID_PRIOR_BASIS,
            "invalid_policy_anchor": _REASON_INVALID_POLICY_ANCHOR,
            "invalid_notice_evidence": _REASON_INVALID_NOTICE_EVIDENCE,
            "invalid_authority_claim_rejected": _REASON_INVALID_AUTHORITY_CLAIM,
            "invalid_unsupported_schema": _REASON_INVALID_PRIOR_BASIS,
        }[notice_set.report_status]
        advisory_result = AnmCompileAdvisoryResult(
            recommended_adoption_posture_or_none=None,
            reason_codes=[reason_code],
            reducer_policy_ref=notice_set.policy_anchor.advisory_outcome_reducer_ref,
            reducer_policy_hash=notice_set.policy_anchor.advisory_outcome_reducer_hash,
        )

    return AnmCompileReport(
        compile_report_id=compile_report_id,
        report_status=report_status,
        consumed_lineage=expected_lineage,
        policy_anchor=notice_set.policy_anchor,
        diagnostic_rows=diagnostics,
        advisory_result=advisory_result,
    )


def check_v66c_anm_adoption_hardening(
    *,
    manifest: AnmSourceSetManifest | dict[str, Any],
    authority_profiles: list[AnmDocAuthorityProfile | dict[str, Any]],
    class_policy: AnmDocClassPolicy | dict[str, Any],
    migration_binding_profile: AnmMigrationBindingProfile | dict[str, Any],
    reader_projection_manifest: AnmReaderProjectionManifest | dict[str, Any] | None = None,
    semantic_diff_report: AnmSemanticDiffReport | dict[str, Any] | None = None,
    prose_boundary_samples: list[dict[str, Any]] | None = None,
    notice_set_id: str = "notice:v66c-starter",
    compile_report_id: str = "compile:v66c-starter",
) -> V66CAdoptionHardeningResult:
    notice_set, structural_diagnostics = build_v66c_prose_boundary_notice_set(
        manifest=manifest,
        authority_profiles=authority_profiles,
        class_policy=class_policy,
        migration_binding_profile=migration_binding_profile,
        reader_projection_manifest=reader_projection_manifest,
        semantic_diff_report=semantic_diff_report,
        prose_boundary_samples=prose_boundary_samples,
        notice_set_id=notice_set_id,
    )
    compile_report = build_v66c_compile_report(
        manifest=manifest,
        authority_profiles=authority_profiles,
        class_policy=class_policy,
        migration_binding_profile=migration_binding_profile,
        reader_projection_manifest=reader_projection_manifest,
        semantic_diff_report=semantic_diff_report,
        prose_boundary_notice_set=notice_set,
        structural_diagnostics=structural_diagnostics,
        compile_report_id=compile_report_id,
    )
    return V66CAdoptionHardeningResult(
        compile_report=compile_report,
        prose_boundary_notice_set=notice_set,
    )


__all__ = [
    "V66CAdoptionHardeningResult",
    "build_v66c_compile_report",
    "build_v66c_prose_boundary_notice_set",
    "check_v66c_anm_adoption_hardening",
]
