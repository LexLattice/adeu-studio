from __future__ import annotations

from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, model_validator

from .models import AdeuCoreIR

IntegrityDanglingReferenceSchemaVersion = Literal["adeu_integrity_dangling_reference@0.1"]
IntegrityDanglingReferenceIssueKind = Literal[
    "missing_node_reference",
    "missing_edge_endpoint",
]
_MISSING_COMPONENT = "_MISSING_"


def _is_present_component(value: Any) -> bool:
    return isinstance(value, str) and value != ""


def _edge_component(value: Any) -> str:
    if _is_present_component(value):
        return value
    return _MISSING_COMPONENT


def _issue_sort_key(
    issue: "AdeuIntegrityDanglingReferenceIssue",
) -> tuple[IntegrityDanglingReferenceIssueKind, str, str]:
    return (issue.kind, issue.subject_id, issue.related_id)


class AdeuIntegrityDanglingReferenceSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_issues: int
    missing_node_reference: int
    missing_edge_endpoint: int

    @model_validator(mode="after")
    def _validate_total(self) -> "AdeuIntegrityDanglingReferenceSummary":
        expected_total = self.missing_node_reference + self.missing_edge_endpoint
        if self.total_issues != expected_total:
            raise ValueError("summary.total_issues must equal the sum of issue counts")
        return self


class AdeuIntegrityDanglingReferenceIssue(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: IntegrityDanglingReferenceIssueKind
    subject_id: str
    related_id: str = ""
    details: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_ids(self) -> "AdeuIntegrityDanglingReferenceIssue":
        if not self.subject_id:
            raise ValueError("issue.subject_id may not be empty")
        return self


class AdeuIntegrityDanglingReference(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: IntegrityDanglingReferenceSchemaVersion = "adeu_integrity_dangling_reference@0.1"
    source_text_hash: str
    summary: AdeuIntegrityDanglingReferenceSummary
    issues: list[AdeuIntegrityDanglingReferenceIssue]
    metadata: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuIntegrityDanglingReference":
        sorted_issues = sorted(self.issues, key=_issue_sort_key)
        if self.issues != sorted_issues:
            raise ValueError("issues must be sorted by (kind, subject_id, related_id)")

        counts: dict[IntegrityDanglingReferenceIssueKind, int] = {
            "missing_node_reference": 0,
            "missing_edge_endpoint": 0,
        }
        for issue in self.issues:
            counts[issue.kind] += 1

        expected_summary = {
            "total_issues": len(self.issues),
            "missing_node_reference": counts["missing_node_reference"],
            "missing_edge_endpoint": counts["missing_edge_endpoint"],
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


def _collect_node_ids(payload: Mapping[str, Any]) -> set[str]:
    raw_nodes = payload.get("nodes")
    if raw_nodes is None:
        return set()
    if not isinstance(raw_nodes, list):
        raise ValueError("nodes must be a list when present")

    node_ids: set[str] = set()
    for node in raw_nodes:
        if not isinstance(node, Mapping):
            continue
        node_id = node.get("id")
        if _is_present_component(node_id):
            node_ids.add(node_id)
    return node_ids


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


def build_integrity_dangling_reference_diagnostics(
    payload: AdeuCoreIR | Mapping[str, Any],
) -> AdeuIntegrityDanglingReference:
    raw_payload: Mapping[str, Any]
    if isinstance(payload, AdeuCoreIR):
        raw_payload = payload.model_dump(mode="json", by_alias=True, exclude_none=False)
    else:
        raw_payload = payload

    source_text_hash = _extract_source_text_hash(raw_payload)
    node_ids = _collect_node_ids(raw_payload)
    edges = _extract_edges(raw_payload)

    issues: list[AdeuIntegrityDanglingReferenceIssue] = []
    for edge in edges:
        edge_type, from_ref, to_ref = _edge_refs(edge)
        subject_id = (
            f"edge:{_edge_component(edge_type)}:"
            f"{_edge_component(from_ref)}->{_edge_component(to_ref)}"
        )

        if not _is_present_component(from_ref):
            issues.append(
                AdeuIntegrityDanglingReferenceIssue.model_validate(
                    {
                        "kind": "missing_edge_endpoint",
                        "subject_id": subject_id,
                        "related_id": "endpoint:from",
                    }
                )
            )
        if not _is_present_component(to_ref):
            issues.append(
                AdeuIntegrityDanglingReferenceIssue.model_validate(
                    {
                        "kind": "missing_edge_endpoint",
                        "subject_id": subject_id,
                        "related_id": "endpoint:to",
                    }
                )
            )
        missing_node_ids: set[str] = set()
        if _is_present_component(from_ref) and from_ref not in node_ids:
            missing_node_ids.add(from_ref)
        if _is_present_component(to_ref) and to_ref not in node_ids:
            missing_node_ids.add(to_ref)
        for missing_node_id in sorted(missing_node_ids):
            issues.append(
                AdeuIntegrityDanglingReferenceIssue.model_validate(
                    {
                        "kind": "missing_node_reference",
                        "subject_id": subject_id,
                        "related_id": missing_node_id,
                    }
                )
            )

    sorted_issues = sorted(issues, key=_issue_sort_key)
    counts: dict[IntegrityDanglingReferenceIssueKind, int] = {
        "missing_node_reference": 0,
        "missing_edge_endpoint": 0,
    }
    for issue in sorted_issues:
        counts[issue.kind] += 1

    return AdeuIntegrityDanglingReference.model_validate(
        {
            "schema": "adeu_integrity_dangling_reference@0.1",
            "source_text_hash": source_text_hash,
            "summary": {
                "total_issues": len(sorted_issues),
                "missing_node_reference": counts["missing_node_reference"],
                "missing_edge_endpoint": counts["missing_edge_endpoint"],
            },
            "issues": [
                issue.model_dump(mode="json", by_alias=True, exclude_none=True)
                for issue in sorted_issues
            ],
        }
    )


def canonicalize_integrity_dangling_reference_payload(
    payload: AdeuIntegrityDanglingReference | Mapping[str, Any],
) -> dict[str, Any]:
    report = (
        payload
        if isinstance(payload, AdeuIntegrityDanglingReference)
        else AdeuIntegrityDanglingReference.model_validate(payload)
    )
    return report.model_dump(mode="json", by_alias=True, exclude_none=True)
