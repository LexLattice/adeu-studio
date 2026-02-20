from __future__ import annotations

from collections import defaultdict
from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .models import AdeuCoreIR, CoreENode, CoreNode, Layer

AlignmentSchemaVersion = Literal["adeu_projection_alignment@0.1"]
AlignmentIssueKind = Literal[
    "missing_in_projection",
    "missing_in_extraction",
    "kind_mismatch",
    "edge_type_mismatch",
]


def _normalize_text(value: str) -> str:
    return " ".join(value.split()).strip().lower()


def _primary_node_text(node: CoreNode) -> str:
    if isinstance(node, CoreENode):
        return node.text
    return node.label


def _node_comparison_key(node: CoreNode) -> tuple[Layer, str]:
    return (node.layer, _normalize_text(_primary_node_text(node)))


def _node_comparison_id(key: tuple[Layer, str]) -> str:
    layer, normalized_text = key
    return f"node:{layer}:{normalized_text}"


def _edge_comparison_id(
    *,
    edge_type: str,
    from_key: tuple[Layer, str],
    to_key: tuple[Layer, str],
) -> str:
    return (
        f"edge:{edge_type}:"
        f"{_node_comparison_id(from_key)}->{_node_comparison_id(to_key)}"
    )


class AdeuProjectionAlignmentSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_issues: int = 0
    missing_in_projection: int = 0
    missing_in_extraction: int = 0
    kind_mismatch: int = 0
    edge_type_mismatch: int = 0

    @model_validator(mode="after")
    def _validate_total(self) -> "AdeuProjectionAlignmentSummary":
        expected_total = (
            self.missing_in_projection
            + self.missing_in_extraction
            + self.kind_mismatch
            + self.edge_type_mismatch
        )
        if self.total_issues != expected_total:
            raise ValueError("summary.total_issues must equal the sum of issue counts")
        return self


class AdeuProjectionAlignmentIssue(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: AlignmentIssueKind
    subject_id: str
    related_id: str = ""
    projection_kind: str | None = None
    extraction_kind: str | None = None
    projection_type: str | None = None
    extraction_type: str | None = None

    @model_validator(mode="after")
    def _validate_ids(self) -> "AdeuProjectionAlignmentIssue":
        if not self.subject_id:
            raise ValueError("issue.subject_id may not be empty")
        return self


def _issue_sort_key(
    issue: AdeuProjectionAlignmentIssue,
) -> tuple[AlignmentIssueKind, str, str]:
    return (issue.kind, issue.subject_id, issue.related_id)


class AdeuProjectionAlignment(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: AlignmentSchemaVersion = "adeu_projection_alignment@0.1"
    source_text_hash: str
    summary: AdeuProjectionAlignmentSummary
    issues: list[AdeuProjectionAlignmentIssue] = Field(default_factory=list)
    metadata: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuProjectionAlignment":
        sorted_issues = sorted(self.issues, key=_issue_sort_key)
        if self.issues != sorted_issues:
            raise ValueError("issues must be sorted by (kind, subject_id, related_id)")

        counts: dict[AlignmentIssueKind, int] = {
            "missing_in_projection": 0,
            "missing_in_extraction": 0,
            "kind_mismatch": 0,
            "edge_type_mismatch": 0,
        }
        for issue in self.issues:
            counts[issue.kind] += 1

        expected_summary = {
            "total_issues": len(self.issues),
            "missing_in_projection": counts["missing_in_projection"],
            "missing_in_extraction": counts["missing_in_extraction"],
            "kind_mismatch": counts["kind_mismatch"],
            "edge_type_mismatch": counts["edge_type_mismatch"],
        }
        actual_summary = self.summary.model_dump(mode="json")
        if actual_summary != expected_summary:
            raise ValueError("summary counts must match issues list counts exactly")
        return self


def _collect_nodes_by_key(core_ir: AdeuCoreIR) -> dict[tuple[Layer, str], list[CoreNode]]:
    nodes_by_key: dict[tuple[Layer, str], list[CoreNode]] = defaultdict(list)
    for node in core_ir.nodes:
        nodes_by_key[_node_comparison_key(node)].append(node)
    for key, nodes in nodes_by_key.items():
        nodes_by_key[key] = sorted(nodes, key=lambda node: node.id)
    return dict(nodes_by_key)


def _collect_edge_types_by_pair(
    core_ir: AdeuCoreIR,
) -> dict[tuple[tuple[Layer, str], tuple[Layer, str]], set[str]]:
    node_keys = {node.id: _node_comparison_key(node) for node in core_ir.nodes}
    pair_types: dict[tuple[tuple[Layer, str], tuple[Layer, str]], set[str]] = defaultdict(set)
    for edge in core_ir.edges:
        from_key = node_keys[edge.from_ref]
        to_key = node_keys[edge.to_ref]
        pair_types[(from_key, to_key)].add(edge.type)
    return dict(pair_types)


def _sorted_pairs(
    values: set[tuple[tuple[Layer, str], tuple[Layer, str]]],
) -> list[tuple[tuple[Layer, str], tuple[Layer, str]]]:
    return sorted(
        values,
        key=lambda pair: (
            _node_comparison_id(pair[0]),
            _node_comparison_id(pair[1]),
        ),
    )


def build_projection_alignment(
    *,
    projection: AdeuCoreIR | Mapping[str, Any],
    extraction: AdeuCoreIR | Mapping[str, Any],
) -> AdeuProjectionAlignment:
    projection_ir = (
        projection
        if isinstance(projection, AdeuCoreIR)
        else AdeuCoreIR.model_validate(projection)
    )
    extraction_ir = (
        extraction
        if isinstance(extraction, AdeuCoreIR)
        else AdeuCoreIR.model_validate(extraction)
    )

    if projection_ir.source_text_hash != extraction_ir.source_text_hash:
        raise ValueError("projection and extraction source_text_hash must match")

    issues: list[AdeuProjectionAlignmentIssue] = []

    projection_nodes = _collect_nodes_by_key(projection_ir)
    extraction_nodes = _collect_nodes_by_key(extraction_ir)
    node_keys = sorted(
        set(projection_nodes) | set(extraction_nodes),
        key=lambda key: _node_comparison_id(key),
    )
    for key in node_keys:
        comparison_id = _node_comparison_id(key)
        projection_entries = projection_nodes.get(key, [])
        extraction_entries = extraction_nodes.get(key, [])

        if not projection_entries:
            issues.append(
                AdeuProjectionAlignmentIssue.model_validate(
                    {
                        "kind": "missing_in_projection",
                        "subject_id": f"extraction:{comparison_id}",
                        "related_id": "",
                    }
                )
            )
            continue
        if not extraction_entries:
            issues.append(
                AdeuProjectionAlignmentIssue.model_validate(
                    {
                        "kind": "missing_in_extraction",
                        "subject_id": f"projection:{comparison_id}",
                        "related_id": "",
                    }
                )
            )
            continue

        projection_kind = projection_entries[0].kind
        extraction_kind = extraction_entries[0].kind
        if projection_kind != extraction_kind:
            issues.append(
                AdeuProjectionAlignmentIssue.model_validate(
                    {
                        "kind": "kind_mismatch",
                        "subject_id": f"projection:{comparison_id}",
                        "related_id": f"extraction:{comparison_id}",
                        "projection_kind": projection_kind,
                        "extraction_kind": extraction_kind,
                    }
                )
            )

    projection_pairs = _collect_edge_types_by_pair(projection_ir)
    extraction_pairs = _collect_edge_types_by_pair(extraction_ir)
    projection_pair_keys = set(projection_pairs)
    extraction_pair_keys = set(extraction_pairs)

    for pair in _sorted_pairs(projection_pair_keys - extraction_pair_keys):
        from_key, to_key = pair
        for edge_type in sorted(projection_pairs[pair]):
            issues.append(
                AdeuProjectionAlignmentIssue.model_validate(
                    {
                        "kind": "missing_in_extraction",
                        "subject_id": (
                            "projection:"
                            + _edge_comparison_id(
                                edge_type=edge_type,
                                from_key=from_key,
                                to_key=to_key,
                            )
                        ),
                        "related_id": "",
                    }
                )
            )

    for pair in _sorted_pairs(extraction_pair_keys - projection_pair_keys):
        from_key, to_key = pair
        for edge_type in sorted(extraction_pairs[pair]):
            issues.append(
                AdeuProjectionAlignmentIssue.model_validate(
                    {
                        "kind": "missing_in_projection",
                        "subject_id": (
                            "extraction:"
                            + _edge_comparison_id(
                                edge_type=edge_type,
                                from_key=from_key,
                                to_key=to_key,
                            )
                        ),
                        "related_id": "",
                    }
                )
            )

    for pair in _sorted_pairs(projection_pair_keys & extraction_pair_keys):
        projection_types = projection_pairs[pair]
        extraction_types = extraction_pairs[pair]
        if projection_types == extraction_types:
            continue
        from_key, to_key = pair
        # Reserve edge_type_mismatch for unambiguous 1:1 substitutions.
        if len(projection_types) == 1 and len(extraction_types) == 1:
            projection_type = next(iter(projection_types))
            extraction_type = next(iter(extraction_types))
            issues.append(
                AdeuProjectionAlignmentIssue.model_validate(
                    {
                        "kind": "edge_type_mismatch",
                        "subject_id": (
                            "projection:"
                            + _edge_comparison_id(
                                edge_type=projection_type,
                                from_key=from_key,
                                to_key=to_key,
                            )
                        ),
                        "related_id": (
                            "extraction:"
                            + _edge_comparison_id(
                                edge_type=extraction_type,
                                from_key=from_key,
                                to_key=to_key,
                            )
                        ),
                        "projection_type": projection_type,
                        "extraction_type": extraction_type,
                    }
                )
            )
            continue

        for edge_type in sorted(projection_types - extraction_types):
            issues.append(
                AdeuProjectionAlignmentIssue.model_validate(
                    {
                        "kind": "missing_in_extraction",
                        "subject_id": (
                            "projection:"
                            + _edge_comparison_id(
                                edge_type=edge_type,
                                from_key=from_key,
                                to_key=to_key,
                            )
                        ),
                        "related_id": "",
                    }
                )
            )

        for edge_type in sorted(extraction_types - projection_types):
            issues.append(
                AdeuProjectionAlignmentIssue.model_validate(
                    {
                        "kind": "missing_in_projection",
                        "subject_id": (
                            "extraction:"
                            + _edge_comparison_id(
                                edge_type=edge_type,
                                from_key=from_key,
                                to_key=to_key,
                            )
                        ),
                        "related_id": "",
                    }
                )
            )

    sorted_issues = sorted(issues, key=_issue_sort_key)
    counts: dict[AlignmentIssueKind, int] = {
        "missing_in_projection": 0,
        "missing_in_extraction": 0,
        "kind_mismatch": 0,
        "edge_type_mismatch": 0,
    }
    for issue in sorted_issues:
        counts[issue.kind] += 1

    return AdeuProjectionAlignment.model_validate(
        {
            "schema": "adeu_projection_alignment@0.1",
            "source_text_hash": projection_ir.source_text_hash,
            "summary": {
                "total_issues": len(sorted_issues),
                "missing_in_projection": counts["missing_in_projection"],
                "missing_in_extraction": counts["missing_in_extraction"],
                "kind_mismatch": counts["kind_mismatch"],
                "edge_type_mismatch": counts["edge_type_mismatch"],
            },
            "issues": [
                issue.model_dump(mode="json", by_alias=True, exclude_none=True)
                for issue in sorted_issues
            ],
        }
    )


def canonicalize_projection_alignment_payload(
    payload: AdeuProjectionAlignment | Mapping[str, Any],
) -> dict[str, Any]:
    report = (
        payload
        if isinstance(payload, AdeuProjectionAlignment)
        else AdeuProjectionAlignment.model_validate(payload)
    )
    return report.model_dump(mode="json", by_alias=True, exclude_none=True)
