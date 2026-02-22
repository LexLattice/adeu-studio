from __future__ import annotations

from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, model_validator

from .models import _EDGE_TYPING_MATRIX, AdeuCoreIR

IntegrityReferenceIntegrityExtendedSchemaVersion = Literal[
    "adeu_integrity_reference_integrity_extended@0.1"
]
IntegrityReferenceIntegrityExtendedIssueKind = Literal[
    "edge_type_constraint_violation",
    "duplicate_edge_identity",
]

_MAX_EMITTED_ISSUES = 1000
_MISSING_COMPONENT = "_MISSING_"


def _is_present_component(value: Any) -> bool:
    return isinstance(value, str) and value != ""


def _edge_component(value: Any) -> str:
    if _is_present_component(value):
        return value
    return _MISSING_COMPONENT


def _issue_sort_key(
    issue: "AdeuIntegrityReferenceIntegrityExtendedIssue",
) -> tuple[IntegrityReferenceIntegrityExtendedIssueKind, str, str]:
    return (issue.kind, issue.subject_id, issue.related_id)


class AdeuIntegrityReferenceIntegrityExtendedSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_issues: int
    edge_type_constraint_violation: int
    duplicate_edge_identity: int

    @model_validator(mode="after")
    def _validate_total(self) -> "AdeuIntegrityReferenceIntegrityExtendedSummary":
        expected_total = self.edge_type_constraint_violation + self.duplicate_edge_identity
        if self.total_issues != expected_total:
            raise ValueError("summary.total_issues must equal the sum of issue counts")
        return self


class AdeuIntegrityReferenceIntegrityExtendedIssue(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: IntegrityReferenceIntegrityExtendedIssueKind
    subject_id: str
    related_id: str = ""
    details: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_ids(self) -> "AdeuIntegrityReferenceIntegrityExtendedIssue":
        if not self.subject_id:
            raise ValueError("issue.subject_id may not be empty")
        return self


class AdeuIntegrityReferenceIntegrityExtended(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: IntegrityReferenceIntegrityExtendedSchemaVersion = (
        "adeu_integrity_reference_integrity_extended@0.1"
    )
    source_text_hash: str
    summary: AdeuIntegrityReferenceIntegrityExtendedSummary
    issues: list[AdeuIntegrityReferenceIntegrityExtendedIssue]
    metadata: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuIntegrityReferenceIntegrityExtended":
        sorted_issues = sorted(self.issues, key=_issue_sort_key)
        if self.issues != sorted_issues:
            raise ValueError("issues must be sorted by (kind, subject_id, related_id)")

        counts: dict[IntegrityReferenceIntegrityExtendedIssueKind, int] = {
            "edge_type_constraint_violation": 0,
            "duplicate_edge_identity": 0,
        }
        for issue in self.issues:
            counts[issue.kind] += 1

        expected_summary = {
            "total_issues": len(self.issues),
            "edge_type_constraint_violation": counts["edge_type_constraint_violation"],
            "duplicate_edge_identity": counts["duplicate_edge_identity"],
        }
        actual_summary = self.summary.model_dump(mode="json")
        if actual_summary != expected_summary:
            raise ValueError("summary counts must match issues list counts exactly")
        return self


def _extract_source_text_hash(payload: Mapping[str, Any]) -> str:
    source_text_hash = payload.get("source_text_hash")
    if not _is_present_component(source_text_hash):
        raise ValueError("source_text_hash must be a non-empty string")
    return source_text_hash


def _collect_node_index(payload: Mapping[str, Any]) -> dict[str, tuple[str | None, str | None]]:
    raw_nodes = payload.get("nodes")
    if raw_nodes is None:
        return {}
    if not isinstance(raw_nodes, list):
        raise ValueError("nodes must be a list when present")

    node_index: dict[str, tuple[str | None, str | None]] = {}
    for node in raw_nodes:
        if not isinstance(node, Mapping):
            continue
        node_id = node.get("id")
        if not _is_present_component(node_id):
            continue
        if node_id in node_index:
            continue
        layer = node.get("layer")
        kind = node.get("kind")
        node_index[node_id] = (
            layer if _is_present_component(layer) else None,
            kind if _is_present_component(kind) else None,
        )
    return node_index


def _extract_edges(payload: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    raw_edges = payload.get("edges")
    if raw_edges is None:
        return []
    if not isinstance(raw_edges, list):
        raise ValueError("edges must be a list when present")
    return [edge for edge in raw_edges if isinstance(edge, Mapping)]


def _edge_refs(edge: Mapping[str, Any]) -> tuple[Any, Any, Any]:
    edge_type = edge.get("type")
    from_ref = edge.get("from", edge.get("from_ref"))
    to_ref = edge.get("to", edge.get("to_ref"))
    return edge_type, from_ref, to_ref


def _raise_issue_cap_error() -> None:
    raise ValueError(
        "URM_ADEU_INTEGRITY_FIXTURE_INVALID: "
        "reference-integrity extended diagnostics exceeded cap"
    )


def build_integrity_reference_integrity_extended_diagnostics(
    payload: AdeuCoreIR | Mapping[str, Any],
) -> AdeuIntegrityReferenceIntegrityExtended:
    raw_payload: Mapping[str, Any]
    if isinstance(payload, AdeuCoreIR):
        raw_payload = payload.model_dump(mode="json", by_alias=True, exclude_none=False)
    else:
        raw_payload = payload

    source_text_hash = _extract_source_text_hash(raw_payload)
    node_index = _collect_node_index(raw_payload)
    edges = _extract_edges(raw_payload)

    issue_map: dict[
        tuple[IntegrityReferenceIntegrityExtendedIssueKind, str, str],
        AdeuIntegrityReferenceIntegrityExtendedIssue,
    ] = {}
    duplicate_counts: dict[tuple[str, str, str], int] = {}

    for edge in edges:
        edge_type, from_ref, to_ref = _edge_refs(edge)
        normalized_edge_type = _edge_component(edge_type)
        normalized_from = _edge_component(from_ref)
        normalized_to = _edge_component(to_ref)
        subject_id = f"edge:{normalized_edge_type}:{normalized_from}->{normalized_to}"
        duplicate_identity = (normalized_edge_type, normalized_from, normalized_to)
        duplicate_counts[duplicate_identity] = duplicate_counts.get(duplicate_identity, 0) + 1

        if not (_is_present_component(from_ref) and _is_present_component(to_ref)):
            continue
        from_node = node_index.get(from_ref)
        to_node = node_index.get(to_ref)
        if from_node is None or to_node is None:
            continue

        from_layer, from_kind = from_node
        to_layer, to_kind = to_node
        if not (
            _is_present_component(from_layer)
            and _is_present_component(from_kind)
            and _is_present_component(to_layer)
            and _is_present_component(to_kind)
        ):
            continue

        from_signature = f"{from_layer}.{from_kind}"
        to_signature = f"{to_layer}.{to_kind}"
        allowed_signature_sets = _EDGE_TYPING_MATRIX.get(edge_type)
        has_violation = (
            allowed_signature_sets is None
            or from_signature not in allowed_signature_sets[0]
            or to_signature not in allowed_signature_sets[1]
        )
        if has_violation:
            issue_key = ("edge_type_constraint_violation", subject_id, "type_constraint")
            if issue_key not in issue_map:
                issue_map[issue_key] = AdeuIntegrityReferenceIntegrityExtendedIssue.model_validate(
                    {
                        "kind": "edge_type_constraint_violation",
                        "subject_id": subject_id,
                        "related_id": "type_constraint",
                    }
                )

    for identity, duplicate_count in sorted(duplicate_counts.items()):
        if duplicate_count <= 1:
            continue
        subject_id = f"edge:{identity[0]}:{identity[1]}->{identity[2]}"
        issue_key = ("duplicate_edge_identity", subject_id, "duplicate_edge_identity")
        issue_map[issue_key] = AdeuIntegrityReferenceIntegrityExtendedIssue.model_validate(
            {
                "kind": "duplicate_edge_identity",
                "subject_id": subject_id,
                "related_id": "duplicate_edge_identity",
                "details": {
                    "duplicate_count": duplicate_count,
                },
            }
        )

    sorted_issues = sorted(issue_map.values(), key=_issue_sort_key)
    if len(sorted_issues) > _MAX_EMITTED_ISSUES:
        _raise_issue_cap_error()

    counts: dict[IntegrityReferenceIntegrityExtendedIssueKind, int] = {
        "edge_type_constraint_violation": 0,
        "duplicate_edge_identity": 0,
    }
    for issue in sorted_issues:
        counts[issue.kind] += 1

    return AdeuIntegrityReferenceIntegrityExtended.model_validate(
        {
            "schema": "adeu_integrity_reference_integrity_extended@0.1",
            "source_text_hash": source_text_hash,
            "summary": {
                "total_issues": len(sorted_issues),
                "edge_type_constraint_violation": counts["edge_type_constraint_violation"],
                "duplicate_edge_identity": counts["duplicate_edge_identity"],
            },
            "issues": [
                issue.model_dump(mode="json", by_alias=True, exclude_none=True)
                for issue in sorted_issues
            ],
        }
    )


def canonicalize_integrity_reference_integrity_extended_payload(
    payload: AdeuIntegrityReferenceIntegrityExtended | Mapping[str, Any],
) -> dict[str, Any]:
    diagnostics = (
        payload
        if isinstance(payload, AdeuIntegrityReferenceIntegrityExtended)
        else AdeuIntegrityReferenceIntegrityExtended.model_validate(payload)
    )
    return diagnostics.model_dump(mode="json", by_alias=True, exclude_none=True)
