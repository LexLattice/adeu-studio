from __future__ import annotations

from collections import Counter
from typing import Any, Mapping

from .hashing import canonical_json

COHERENCE_SCHEMA_VERSION = "concepts.coherence.v1"
EXPECTED_QUESTION_RANK_VERSION = "concepts.qrank.v3"
EXPECTED_TOURNAMENT_SCORE_VERSION = "concepts.tscore.v3"
EXPECTED_OBJECTIVE_VECTOR_VERSION = "concepts.tobjective.v3"
EXPECTED_TIE_BREAK_VERSION = "concepts.ttiebreak.v1"


def _as_str(value: Any) -> str | None:
    if isinstance(value, str) and value:
        return value
    return None


def _sorted_unique(values: list[str]) -> list[str]:
    return sorted(set(values))


def _normalize_details(details: Mapping[str, Any]) -> dict[str, Any]:
    normalized: dict[str, Any] = {}
    for key in sorted(details.keys()):
        value = details[key]
        if isinstance(value, list):
            if all(isinstance(item, str) for item in value):
                normalized[key] = sorted(set(value))
            else:
                normalized[key] = value
        elif isinstance(value, dict):
            normalized[key] = _normalize_details(value)
        else:
            normalized[key] = value
    return normalized


def _alert(
    *,
    code: str,
    severity: str = "warn",
    message: str,
    details: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "code": code,
        "severity": severity,
        "message": message,
        "details": _normalize_details(details or {}),
    }


def _question_items(question_artifact: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    items = question_artifact.get("questions")
    if isinstance(items, list):
        return [item for item in items if isinstance(item, Mapping)]
    return []


def _tournament_candidates(tournament_artifact: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    items = tournament_artifact.get("candidates")
    if isinstance(items, list):
        return [item for item in items if isinstance(item, Mapping)]
    return []


def _question_ids(question_artifact: Mapping[str, Any]) -> list[str]:
    output: list[str] = []
    for question in _question_items(question_artifact):
        value = _as_str(question.get("question_id"))
        if value:
            output.append(value)
    return _sorted_unique(output)


def _candidate_question_ids(tournament_artifact: Mapping[str, Any]) -> list[str]:
    output: list[str] = []
    for candidate in _tournament_candidates(tournament_artifact):
        value = _as_str(candidate.get("question_id"))
        if value:
            output.append(value)
    return _sorted_unique(output)


def _question_anchor_object_ids(question_artifact: Mapping[str, Any]) -> list[str]:
    object_ids: list[str] = []
    for question in _question_items(question_artifact):
        anchors = question.get("anchors")
        if not isinstance(anchors, list):
            continue
        for anchor in anchors:
            if not isinstance(anchor, Mapping):
                continue
            object_id = _as_str(anchor.get("object_id"))
            if object_id:
                object_ids.append(object_id)
    return _sorted_unique(object_ids)


def _bridge_loss_has_non_preserved_entries(report: Mapping[str, Any] | None) -> bool:
    if report is None:
        return False
    entries = report.get("entries")
    if not isinstance(entries, list):
        return False
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        status = _as_str(entry.get("status"))
        if status and status != "preserved":
            return True
    return False


def _bridge_signal_count(payload: Mapping[str, Any]) -> int:
    signals = payload.get("bridge_loss_signals")
    if not isinstance(signals, list):
        return 0
    return len([item for item in signals if isinstance(item, Mapping)])


def _score_metadata(tournament_artifact: Mapping[str, Any]) -> Mapping[str, Any]:
    metadata = tournament_artifact.get("score_metadata")
    if isinstance(metadata, Mapping):
        return metadata
    return {}


def build_concepts_coherence_artifact(
    *,
    run_id: str,
    question_artifact: Mapping[str, Any],
    tournament_artifact: Mapping[str, Any],
    bridge_loss_report: Mapping[str, Any] | None = None,
    patch_apply_summary: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    alerts: list[dict[str, Any]] = []

    question_rank_version = _as_str(question_artifact.get("question_rank_version"))
    tournament_score_version = _as_str(tournament_artifact.get("tournament_score_version"))

    if question_rank_version and question_rank_version != EXPECTED_QUESTION_RANK_VERSION:
        alerts.append(
            _alert(
                code="question_rank_version_mismatch",
                message="question artifact rank version differs from expected v3",
                details={
                    "expected": EXPECTED_QUESTION_RANK_VERSION,
                    "actual": question_rank_version,
                },
            )
        )

    if tournament_score_version and tournament_score_version != EXPECTED_TOURNAMENT_SCORE_VERSION:
        alerts.append(
            _alert(
                code="tournament_score_version_mismatch",
                message="tournament artifact score version differs from expected v3",
                details={
                    "expected": EXPECTED_TOURNAMENT_SCORE_VERSION,
                    "actual": tournament_score_version,
                },
            )
        )

    evidence_refs = question_artifact.get("evidence_refs")
    if not isinstance(evidence_refs, list) or not evidence_refs:
        alerts.append(
            _alert(
                code="missing_required_cross_artifact_references",
                message="question artifact has no evidence_refs",
                details={"artifact": "question_ranking"},
            )
        )
    else:
        invalid_ref_count = 0
        for item in evidence_refs:
            if not isinstance(item, Mapping):
                invalid_ref_count += 1
                continue
            if _as_str(item.get("kind")) is None or _as_str(item.get("ref")) is None:
                invalid_ref_count += 1
        if invalid_ref_count:
            alerts.append(
                _alert(
                    code="missing_required_cross_artifact_references",
                    message="question artifact includes invalid evidence_refs entries",
                    details={
                        "artifact": "question_ranking",
                        "invalid_ref_count": invalid_ref_count,
                    },
                )
            )

    question_ids = _question_ids(question_artifact)
    candidate_question_ids = _candidate_question_ids(tournament_artifact)
    missing_candidate_question_ids = sorted(set(candidate_question_ids) - set(question_ids))
    if missing_candidate_question_ids:
        alerts.append(
            _alert(
                code="inconsistent_question_id_references",
                message="tournament candidates reference unknown question_ids",
                details={"unknown_question_ids": missing_candidate_question_ids},
            )
        )

    metadata = _score_metadata(tournament_artifact)
    metadata_score_version = _as_str(metadata.get("score_version"))
    if (
        tournament_score_version is not None
        and metadata_score_version is not None
        and metadata_score_version != tournament_score_version
    ):
        alerts.append(
            _alert(
                code="score_version_mismatch",
                message="score_metadata.score_version differs from tournament_score_version",
                details={
                    "tournament_score_version": tournament_score_version,
                    "metadata_score_version": metadata_score_version,
                },
            )
        )

    metadata_objective_version = _as_str(metadata.get("objective_vector_version"))
    metadata_tie_break_version = _as_str(metadata.get("tie_break_version"))
    if metadata_objective_version and metadata_objective_version != EXPECTED_OBJECTIVE_VECTOR_VERSION:
        alerts.append(
            _alert(
                code="objective_vector_version_mismatch",
                message="score metadata objective_vector_version differs from expected",
                details={
                    "expected": EXPECTED_OBJECTIVE_VECTOR_VERSION,
                    "actual": metadata_objective_version,
                },
            )
        )
    if metadata_tie_break_version and metadata_tie_break_version != EXPECTED_TIE_BREAK_VERSION:
        alerts.append(
            _alert(
                code="tie_break_version_mismatch",
                message="score metadata tie_break_version differs from expected",
                details={
                    "expected": EXPECTED_TIE_BREAK_VERSION,
                    "actual": metadata_tie_break_version,
                },
            )
        )

    candidate_score_versions = _sorted_unique(
        [
            value
            for value in (_as_str(item.get("score_version")) for item in _tournament_candidates(tournament_artifact))
            if value is not None
        ]
    )
    if tournament_score_version and candidate_score_versions and candidate_score_versions != [
        tournament_score_version
    ]:
        alerts.append(
            _alert(
                code="candidate_score_version_mismatch",
                message="candidate score_version values are inconsistent with tournament_score_version",
                details={
                    "tournament_score_version": tournament_score_version,
                    "candidate_score_versions": candidate_score_versions,
                },
            )
        )

    candidate_objective_versions = _sorted_unique(
        [
            value
            for candidate in _tournament_candidates(tournament_artifact)
            for value in (
                _as_str(
                    (candidate.get("tie_break_provenance") or {}).get("objective_vector_version")
                    if isinstance(candidate.get("tie_break_provenance"), Mapping)
                    else None
                ),
            )
            if value is not None
        ]
    )
    candidate_tie_break_versions = _sorted_unique(
        [
            value
            for candidate in _tournament_candidates(tournament_artifact)
            for value in (
                _as_str(
                    (candidate.get("tie_break_provenance") or {}).get("tie_break_version")
                    if isinstance(candidate.get("tie_break_provenance"), Mapping)
                    else None
                ),
            )
            if value is not None
        ]
    )
    if candidate_objective_versions and candidate_objective_versions != [EXPECTED_OBJECTIVE_VECTOR_VERSION]:
        alerts.append(
            _alert(
                code="candidate_objective_vector_version_mismatch",
                message="candidate tie-break provenance objective_vector_version differs from expected",
                details={
                    "expected": EXPECTED_OBJECTIVE_VECTOR_VERSION,
                    "candidate_objective_vector_versions": candidate_objective_versions,
                },
            )
        )
    if candidate_tie_break_versions and candidate_tie_break_versions != [EXPECTED_TIE_BREAK_VERSION]:
        alerts.append(
            _alert(
                code="candidate_tie_break_version_mismatch",
                message="candidate tie-break provenance tie_break_version differs from expected",
                details={
                    "expected": EXPECTED_TIE_BREAK_VERSION,
                    "candidate_tie_break_versions": candidate_tie_break_versions,
                },
            )
        )

    question_solver_trust = _as_str(question_artifact.get("solver_trust"))
    tournament_solver_trust = _as_str(tournament_artifact.get("solver_trust"))
    if (
        question_solver_trust is not None
        and tournament_solver_trust is not None
        and question_solver_trust != tournament_solver_trust
    ):
        alerts.append(
            _alert(
                code="contradictory_status_labels",
                message="question/tournament solver_trust labels contradict",
                details={
                    "question_solver_trust": question_solver_trust,
                    "tournament_solver_trust": tournament_solver_trust,
                },
            )
        )

    question_mapping_trust = _as_str(question_artifact.get("mapping_trust"))
    tournament_mapping_trust = _as_str(tournament_artifact.get("mapping_trust"))
    if (
        question_mapping_trust is not None
        and tournament_mapping_trust is not None
        and question_mapping_trust != tournament_mapping_trust
    ):
        alerts.append(
            _alert(
                code="contradictory_status_labels",
                message="question/tournament mapping_trust labels contradict",
                details={
                    "question_mapping_trust": question_mapping_trust,
                    "tournament_mapping_trust": tournament_mapping_trust,
                },
            )
        )

    if isinstance(patch_apply_summary, Mapping):
        declared_entity_ids = patch_apply_summary.get("entity_ids")
        if isinstance(declared_entity_ids, list):
            declared_ids = _sorted_unique(
                [value for value in (_as_str(item) for item in declared_entity_ids) if value is not None]
            )
            unknown_anchor_ids = sorted(
                set(_question_anchor_object_ids(question_artifact)) - set(declared_ids)
            )
            if unknown_anchor_ids:
                alerts.append(
                    _alert(
                        code="inconsistent_entity_id_references",
                        message="question anchor object_ids are missing from patch_apply_summary entity_ids",
                        details={"unknown_anchor_ids": unknown_anchor_ids},
                    )
                )

    if _bridge_loss_has_non_preserved_entries(bridge_loss_report):
        question_bridge_signal_count = _bridge_signal_count(question_artifact)
        tournament_bridge_signal_count = _bridge_signal_count(tournament_artifact)
        if question_bridge_signal_count + tournament_bridge_signal_count == 0:
            alerts.append(
                _alert(
                    code="missing_bridge_loss_references",
                    message="bridge loss report has non-preserved entries but no bridge_loss_signals are referenced",
                    details={},
                )
            )

    alerts = sorted(
        alerts,
        key=lambda item: (
            str(item.get("code", "")),
            str(item.get("severity", "")),
            canonical_json(item.get("details", {})),
            str(item.get("message", "")),
        ),
    )

    counter = Counter(item["code"] for item in alerts)
    artifact = {
        "schema_version": COHERENCE_SCHEMA_VERSION,
        "run_id": run_id,
        "question_rank_version": question_rank_version,
        "tournament_score_version": tournament_score_version,
        "artifact_presence": {
            "bridge_loss_report": bridge_loss_report is not None,
            "question_ranking": True,
            "tournament_ranking": True,
            "patch_apply_summary": patch_apply_summary is not None,
        },
        "coherence_alert_count": len(alerts),
        "coherence_alerts": alerts,
        "coherence_counts_by_code": {
            code: counter[code]
            for code in sorted(counter.keys())
        },
    }
    return artifact

