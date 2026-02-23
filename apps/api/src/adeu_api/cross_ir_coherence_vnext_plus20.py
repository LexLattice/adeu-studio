from __future__ import annotations

from collections import Counter, defaultdict
from collections.abc import Mapping
from pathlib import Path
from typing import Annotated, Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .cross_ir_bridge_vnext_plus20 import (
    CrossIRBridgeVnextPlus20Error,
    build_cross_ir_bridge_manifest_vnext_plus20,
    canonical_bridge_manifest_hash_vnext_plus20,
    load_cross_ir_pair_artifacts_vnext_plus20,
)
from .hashing import canonical_json, sha256_text

CROSS_IR_COHERENCE_DIAGNOSTICS_SCHEMA = "adeu_cross_ir_coherence_diagnostics@0.1"
CROSS_IR_QUALITY_PROJECTION_SCHEMA = "cross_ir_quality_projection.vnext_plus20@1"

CrossIRIssueCode = Literal[
    "MISSING_CONCEPT_MAPPING",
    "MISSING_CORE_IR_MAPPING",
    "TOPOLOGY_DRIFT",
    "CLAIM_PROJECTION_GAP",
    "LINK_KIND_DRIFT",
    "SOURCE_HASH_MISMATCH",
    "TRUST_LABEL_MISMATCH",
]
CrossIRIssueSeverity = Literal["warn", "error"]

_ISSUE_SEVERITY_BY_CODE: dict[CrossIRIssueCode, CrossIRIssueSeverity] = {
    "MISSING_CONCEPT_MAPPING": "warn",
    "MISSING_CORE_IR_MAPPING": "warn",
    "TOPOLOGY_DRIFT": "warn",
    "CLAIM_PROJECTION_GAP": "error",
    "LINK_KIND_DRIFT": "warn",
    "SOURCE_HASH_MISMATCH": "error",
    "TRUST_LABEL_MISMATCH": "warn",
}

_CLAIM_PROJECTION_TARGET_KINDS: set[str] = {"E.Claim", "D.Norm", "D.Policy"}
_EXCEPTS_TARGET_SIGNATURE_TO_CATEGORY: dict[str, str] = {
    "D.PhysicalConstraint": "defeats",
    "D.Norm": "narrows",
    "D.Policy": "clarifies",
}
_CATEGORY_TO_LINK_KIND: dict[str, str] = {
    "defeats": "incompatibility",
    "narrows": "presupposition",
    "clarifies": "commitment",
}


def _is_hex64(value: str) -> bool:
    return len(value) == 64 and all(char in "0123456789abcdef" for char in value)


def _as_non_empty_str(value: Any) -> str | None:
    if isinstance(value, str) and value:
        return value
    return None


def _sorted_unique(values: list[str]) -> list[str]:
    return sorted(set(values))


def _issue_id(
    *,
    issue_code: CrossIRIssueCode,
    concept_refs: list[str],
    core_ir_refs: list[str],
    evidence: Mapping[str, Any],
) -> str:
    return sha256_text(
        canonical_json(
            {
                "issue_code": issue_code,
                "concept_refs": concept_refs,
                "core_ir_refs": core_ir_refs,
                "evidence": evidence,
            }
        )
    )[:16]


def _topology_relation_key(
    *,
    concept_relation_ref: str,
    core_ir_relation_ref: str | None,
) -> str:
    return sha256_text(
        canonical_json(
            {
                "concept_relation_ref": concept_relation_ref,
                "core_ir_relation_ref": core_ir_relation_ref or "",
            }
        )
    )[:16]


class _BridgeEntryEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: Literal["bridge_entry"] = "bridge_entry"
    entry_ref: str = Field(min_length=1)


class _UnmappedEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: Literal["unmapped"] = "unmapped"
    side: Literal["concept", "core_ir"]
    object_id: str = Field(min_length=1)


class _TopologyEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: Literal["topology"] = "topology"
    concept_relation_ref: str = Field(min_length=1)
    core_ir_relation_ref: str | None = None
    relation_key: str = Field(min_length=16, max_length=16)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_TopologyEvidence":
        if not all(char in "0123456789abcdef" for char in self.relation_key):
            raise ValueError("topology relation_key must be lowercase hex")
        expected = _topology_relation_key(
            concept_relation_ref=self.concept_relation_ref,
            core_ir_relation_ref=self.core_ir_relation_ref,
        )
        if expected != self.relation_key:
            raise ValueError("topology relation_key must match frozen deterministic hash")
        return self


class _HashesEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: Literal["hashes"] = "hashes"
    concept_source_text_hash: str = Field(min_length=64, max_length=64)
    core_ir_source_text_hash: str = Field(min_length=64, max_length=64)
    catalog_source_text_hash: str = Field(min_length=64, max_length=64)
    concept_source_excerpt_prefix: str | None = Field(default=None, max_length=50)
    core_ir_source_excerpt_prefix: str | None = Field(default=None, max_length=50)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_HashesEvidence":
        for name, value in (
            ("concept_source_text_hash", self.concept_source_text_hash),
            ("core_ir_source_text_hash", self.core_ir_source_text_hash),
            ("catalog_source_text_hash", self.catalog_source_text_hash),
        ):
            if not _is_hex64(value):
                raise ValueError(f"{name} must be a lowercase sha256 hex digest")
        return self


class _TrustLabelsEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: Literal["trust_labels"] = "trust_labels"
    concept_trust: str = Field(min_length=1)
    core_ir_trust: str = Field(min_length=1)


CrossIRIssueEvidence = Annotated[
    _BridgeEntryEvidence
    | _UnmappedEvidence
    | _TopologyEvidence
    | _HashesEvidence
    | _TrustLabelsEvidence,
    Field(discriminator="kind"),
]


class AdeuCrossIRCoherenceIssue(BaseModel):
    model_config = ConfigDict(extra="forbid")

    issue_id: str = Field(min_length=16, max_length=16)
    issue_code: CrossIRIssueCode
    severity: CrossIRIssueSeverity
    concept_refs: list[str] = Field(default_factory=list)
    core_ir_refs: list[str] = Field(default_factory=list)
    message: str = Field(min_length=1)
    evidence: CrossIRIssueEvidence

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuCrossIRCoherenceIssue":
        if self.concept_refs != sorted(self.concept_refs):
            raise ValueError("concept_refs must be lexicographically sorted")
        if len(set(self.concept_refs)) != len(self.concept_refs):
            raise ValueError("concept_refs may not contain duplicates")
        if self.core_ir_refs != sorted(self.core_ir_refs):
            raise ValueError("core_ir_refs must be lexicographically sorted")
        if len(set(self.core_ir_refs)) != len(self.core_ir_refs):
            raise ValueError("core_ir_refs may not contain duplicates")
        if _ISSUE_SEVERITY_BY_CODE[self.issue_code] != self.severity:
            raise ValueError("severity must match frozen issue-code mapping")
        if not all(char in "0123456789abcdef" for char in self.issue_id):
            raise ValueError("issue_id must be lowercase hex")

        evidence_payload = self.evidence.model_dump(mode="json", by_alias=True, exclude_none=True)
        expected_issue_id = _issue_id(
            issue_code=self.issue_code,
            concept_refs=self.concept_refs,
            core_ir_refs=self.core_ir_refs,
            evidence=evidence_payload,
        )
        if self.issue_id != expected_issue_id:
            raise ValueError("issue_id must match deterministic content hash")
        return self


class _IssueSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_issues: int = Field(ge=0)
    counts_by_code: dict[str, int] = Field(default_factory=dict)
    counts_by_severity: dict[str, int] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_IssueSummary":
        if list(self.counts_by_code.keys()) != sorted(self.counts_by_code.keys()):
            raise ValueError("counts_by_code keys must be lexicographically sorted")
        if any(key not in _ISSUE_SEVERITY_BY_CODE for key in self.counts_by_code):
            raise ValueError("counts_by_code contains unsupported issue_code")
        if any(not isinstance(value, int) or value < 0 for value in self.counts_by_code.values()):
            raise ValueError("counts_by_code values must be non-negative integers")

        if list(self.counts_by_severity.keys()) != sorted(self.counts_by_severity.keys()):
            raise ValueError("counts_by_severity keys must be lexicographically sorted")
        if any(key not in {"error", "warn"} for key in self.counts_by_severity):
            raise ValueError("counts_by_severity contains unsupported severity value")
        if any(
            not isinstance(value, int) or value < 0 for value in self.counts_by_severity.values()
        ):
            raise ValueError("counts_by_severity values must be non-negative integers")
        return self


class AdeuCrossIRCoherenceDiagnostics(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_cross_ir_coherence_diagnostics@0.1"] = (
        CROSS_IR_COHERENCE_DIAGNOSTICS_SCHEMA
    )
    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    bridge_manifest_hash: str = Field(min_length=64, max_length=64)
    issue_summary: _IssueSummary
    issues: list[AdeuCrossIRCoherenceIssue] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuCrossIRCoherenceDiagnostics":
        if not _is_hex64(self.bridge_manifest_hash):
            raise ValueError("bridge_manifest_hash must be a lowercase sha256 hex digest")

        issue_sort_keys = [
            (
                issue.issue_code,
                issue.concept_refs[0] if issue.concept_refs else "",
                issue.core_ir_refs[0] if issue.core_ir_refs else "",
                issue.issue_id,
            )
            for issue in self.issues
        ]
        if issue_sort_keys != sorted(issue_sort_keys):
            raise ValueError("issues must be lexicographically sorted by frozen ordering key")

        code_counts = Counter(issue.issue_code for issue in self.issues)
        severity_counts = Counter(issue.severity for issue in self.issues)
        expected_counts_by_code = {code: code_counts[code] for code in sorted(code_counts)}
        expected_counts_by_severity = {
            severity: severity_counts[severity] for severity in sorted(severity_counts)
        }
        if self.issue_summary.total_issues != len(self.issues):
            raise ValueError("issue_summary.total_issues must equal len(issues)")
        if self.issue_summary.counts_by_code != expected_counts_by_code:
            raise ValueError("issue_summary.counts_by_code must match issues payload")
        if self.issue_summary.counts_by_severity != expected_counts_by_severity:
            raise ValueError("issue_summary.counts_by_severity must match issues payload")
        return self


class CrossIRQualityProjectionVnextPlus20(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["cross_ir_quality_projection.vnext_plus20@1"] = (
        CROSS_IR_QUALITY_PROJECTION_SCHEMA
    )
    bridge_pair_count: int = Field(ge=0)
    coherence_issue_count: int = Field(ge=0)
    coherence_counts_by_code: dict[str, int] = Field(default_factory=dict)
    coherence_counts_by_severity: dict[str, int] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _validate_contract(self) -> "CrossIRQualityProjectionVnextPlus20":
        if list(self.coherence_counts_by_code.keys()) != sorted(
            self.coherence_counts_by_code.keys()
        ):
            raise ValueError("coherence_counts_by_code keys must be lexicographically sorted")
        if any(key not in _ISSUE_SEVERITY_BY_CODE for key in self.coherence_counts_by_code):
            raise ValueError("coherence_counts_by_code contains unsupported issue_code")
        if any(
            not isinstance(value, int) or value < 0
            for value in self.coherence_counts_by_code.values()
        ):
            raise ValueError("coherence_counts_by_code values must be non-negative integers")

        if list(self.coherence_counts_by_severity.keys()) != sorted(
            self.coherence_counts_by_severity.keys()
        ):
            raise ValueError("coherence_counts_by_severity keys must be lexicographically sorted")
        if any(key not in {"error", "warn"} for key in self.coherence_counts_by_severity):
            raise ValueError("coherence_counts_by_severity contains unsupported severity value")
        if any(
            not isinstance(value, int) or value < 0
            for value in self.coherence_counts_by_severity.values()
        ):
            raise ValueError("coherence_counts_by_severity values must be non-negative integers")

        if self.coherence_issue_count != sum(self.coherence_counts_by_code.values()):
            raise ValueError(
                "coherence_issue_count must equal sum(coherence_counts_by_code.values())"
            )
        if self.coherence_issue_count != sum(self.coherence_counts_by_severity.values()):
            raise ValueError(
                "coherence_issue_count must equal sum(coherence_counts_by_severity.values())"
            )
        return self


def _bridge_entry_sort_key(entry: Mapping[str, Any]) -> tuple[str, str, str, str, str]:
    return (
        str(entry.get("concept_object_id") or ""),
        str(entry.get("core_ir_object_id") or ""),
        str(entry.get("concept_kind") or ""),
        str(entry.get("core_ir_kind") or ""),
        str(entry.get("mapping_status") or ""),
    )


def _bridge_entry_ref(entry: Mapping[str, Any]) -> str:
    projection = {
        "concept_object_id": entry.get("concept_object_id"),
        "concept_kind": entry.get("concept_kind"),
        "core_ir_object_id": entry.get("core_ir_object_id"),
        "core_ir_kind": entry.get("core_ir_kind"),
        "mapping_status": entry.get("mapping_status"),
        "confidence_tag": entry.get("confidence_tag"),
    }
    return sha256_text(canonical_json(projection))[:16]


def _build_issue(
    *,
    issue_code: CrossIRIssueCode,
    concept_refs: list[str],
    core_ir_refs: list[str],
    message: str,
    evidence: CrossIRIssueEvidence,
) -> AdeuCrossIRCoherenceIssue:
    normalized_concept_refs = _sorted_unique(concept_refs)
    normalized_core_ir_refs = _sorted_unique(core_ir_refs)
    evidence_payload = evidence.model_dump(mode="json", by_alias=True, exclude_none=True)
    return AdeuCrossIRCoherenceIssue(
        issue_id=_issue_id(
            issue_code=issue_code,
            concept_refs=normalized_concept_refs,
            core_ir_refs=normalized_core_ir_refs,
            evidence=evidence_payload,
        ),
        issue_code=issue_code,
        severity=_ISSUE_SEVERITY_BY_CODE[issue_code],
        concept_refs=normalized_concept_refs,
        core_ir_refs=normalized_core_ir_refs,
        message=message,
        evidence=evidence_payload,
    )


def _core_node_signature(node: Mapping[str, Any]) -> str | None:
    layer = _as_non_empty_str(node.get("layer"))
    kind = _as_non_empty_str(node.get("kind"))
    if layer is None or kind is None:
        return None
    return f"{layer}.{kind}"


def _edge_signature(edge: Mapping[str, Any]) -> str | None:
    edge_type = _as_non_empty_str(edge.get("type"))
    from_ref = _as_non_empty_str(edge.get("from"))
    to_ref = _as_non_empty_str(edge.get("to"))
    if edge_type is None or from_ref is None or to_ref is None:
        return None
    return f"edge:{edge_type}:{from_ref}:{to_ref}"


def _parse_edge_signature(edge_signature: str) -> tuple[str, str, str] | None:
    if not edge_signature.startswith("edge:"):
        return None
    parts = edge_signature.split(":", 3)
    if len(parts) != 4:
        return None
    _, edge_type, from_ref, to_ref = parts
    if not edge_type or not from_ref or not to_ref:
        return None
    return (edge_type, from_ref, to_ref)


def _extract_trust_label(payload: Mapping[str, Any]) -> str | None:
    for key in ("mapping_trust", "solver_trust", "proof_trust"):
        value = _as_non_empty_str(payload.get(key))
        if value is not None:
            return value

    metadata = payload.get("metadata")
    if isinstance(metadata, Mapping):
        for key in ("mapping_trust", "solver_trust", "proof_trust"):
            value = _as_non_empty_str(metadata.get(key))
            if value is not None:
                return value

    context = payload.get("context")
    if isinstance(context, Mapping):
        for key in ("mapping_trust", "solver_trust", "proof_trust"):
            value = _as_non_empty_str(context.get(key))
            if value is not None:
                return value
    return None


def _extract_source_text_hash(payload: Mapping[str, Any]) -> str | None:
    direct = _as_non_empty_str(payload.get("source_text_hash"))
    if direct is not None and _is_hex64(direct):
        return direct

    metadata = payload.get("metadata")
    if isinstance(metadata, Mapping):
        nested = _as_non_empty_str(metadata.get("source_text_hash"))
        if nested is not None and _is_hex64(nested):
            return nested
    return None


def _extract_source_text(payload: Mapping[str, Any]) -> str | None:
    direct = payload.get("source_text")
    if isinstance(direct, str):
        return direct

    metadata = payload.get("metadata")
    if isinstance(metadata, Mapping):
        nested = metadata.get("source_text")
        if isinstance(nested, str):
            return nested
    return None


def _issue_sort_key(issue: AdeuCrossIRCoherenceIssue) -> tuple[str, str, str, str]:
    return (
        issue.issue_code,
        issue.concept_refs[0] if issue.concept_refs else "",
        issue.core_ir_refs[0] if issue.core_ir_refs else "",
        issue.issue_id,
    )


def build_cross_ir_coherence_diagnostics_vnext_plus20(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    catalog_path: Path | None = None,
) -> dict[str, Any]:
    artifacts = load_cross_ir_pair_artifacts_vnext_plus20(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        catalog_path=catalog_path,
    )
    bridge_manifest = build_cross_ir_bridge_manifest_vnext_plus20(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        catalog_path=catalog_path,
    )
    bridge_manifest_hash = canonical_bridge_manifest_hash_vnext_plus20(bridge_manifest)
    entries_raw = bridge_manifest.get("entries")
    if not isinstance(entries_raw, list):
        raise CrossIRBridgeVnextPlus20Error(
            code="URM_ADEU_CROSS_IR_PAYLOAD_INVALID",
            reason="bridge manifest entries must be a list",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
            },
        )

    entries: list[dict[str, Any]] = [
        dict(entry) for entry in entries_raw if isinstance(entry, Mapping)
    ]
    issues: list[AdeuCrossIRCoherenceIssue] = []

    intentional_concept_only = set(artifacts.intentional_concept_only_object_ids)
    intentional_core_ir_only = set(artifacts.intentional_core_ir_only_object_ids)

    for entry in entries:
        mapping_status = _as_non_empty_str(entry.get("mapping_status"))
        if mapping_status == "concept_only":
            concept_object_id = _as_non_empty_str(entry.get("concept_object_id"))
            if concept_object_id is None or concept_object_id in intentional_concept_only:
                continue
            issues.append(
                _build_issue(
                    issue_code="MISSING_CONCEPT_MAPPING",
                    concept_refs=[concept_object_id],
                    core_ir_refs=[],
                    message=(
                        "concept object is unmapped to core-ir and is not allowlisted "
                        "as intentional"
                    ),
                    evidence=_UnmappedEvidence(side="concept", object_id=concept_object_id),
                )
            )
        elif mapping_status == "core_ir_only":
            core_object_id = _as_non_empty_str(entry.get("core_ir_object_id"))
            if core_object_id is None or core_object_id in intentional_core_ir_only:
                continue
            issues.append(
                _build_issue(
                    issue_code="MISSING_CORE_IR_MAPPING",
                    concept_refs=[],
                    core_ir_refs=[core_object_id],
                    message=(
                        "core-ir object is unmapped to concept and is not allowlisted "
                        "as intentional"
                    ),
                    evidence=_UnmappedEvidence(side="core_ir", object_id=core_object_id),
                )
            )

    mapped_entries = sorted(
        [
            entry
            for entry in entries
            if _as_non_empty_str(entry.get("mapping_status")) == "mapped"
            and _as_non_empty_str(entry.get("concept_object_id")) is not None
            and _as_non_empty_str(entry.get("core_ir_object_id")) is not None
        ],
        key=_bridge_entry_sort_key,
    )
    mapped_entries_by_concept_id: dict[str, list[dict[str, Any]]] = defaultdict(list)
    mapped_sense_to_core_ids: dict[str, set[str]] = defaultdict(set)
    mapped_core_to_sense_ids: dict[str, set[str]] = defaultdict(set)
    for entry in mapped_entries:
        concept_object_id = str(entry["concept_object_id"])
        core_ir_object_id = str(entry["core_ir_object_id"])
        mapped_entries_by_concept_id[concept_object_id].append(entry)
        if entry.get("concept_kind") == "sense":
            mapped_sense_to_core_ids[concept_object_id].add(core_ir_object_id)
            mapped_core_to_sense_ids[core_ir_object_id].add(concept_object_id)

    concept_payload = artifacts.concept_payload
    core_payload = artifacts.core_payload

    concept_links_by_id: dict[str, dict[str, Any]] = {}
    concept_links_payload = concept_payload.get("links")
    if isinstance(concept_links_payload, list):
        for raw_link in concept_links_payload:
            if not isinstance(raw_link, Mapping):
                continue
            link_id = _as_non_empty_str(raw_link.get("id"))
            if link_id is None:
                continue
            concept_links_by_id[link_id] = dict(raw_link)

    core_nodes_by_id: dict[str, dict[str, Any]] = {}
    core_node_signature_by_id: dict[str, str] = {}
    core_nodes_payload = core_payload.get("nodes")
    if isinstance(core_nodes_payload, list):
        for raw_node in core_nodes_payload:
            if not isinstance(raw_node, Mapping):
                continue
            node_id = _as_non_empty_str(raw_node.get("id"))
            if node_id is None:
                continue
            node_payload = dict(raw_node)
            core_nodes_by_id[node_id] = node_payload
            node_signature = _core_node_signature(node_payload)
            if node_signature is not None:
                core_node_signature_by_id[node_id] = node_signature

    core_edges_by_signature: dict[str, dict[str, Any]] = {}
    core_edge_endpoint_pairs: set[tuple[str, str]] = set()
    core_edges_payload = core_payload.get("edges")
    if isinstance(core_edges_payload, list):
        for raw_edge in core_edges_payload:
            if not isinstance(raw_edge, Mapping):
                continue
            edge_payload = dict(raw_edge)
            signature = _edge_signature(edge_payload)
            if signature is None:
                continue
            core_edges_by_signature[signature] = edge_payload
            from_ref = _as_non_empty_str(edge_payload.get("from"))
            to_ref = _as_non_empty_str(edge_payload.get("to"))
            if from_ref is not None and to_ref is not None:
                core_edge_endpoint_pairs.add((from_ref, to_ref))

    concept_claim_ids: list[str] = []
    concept_claims_payload = concept_payload.get("claims")
    if isinstance(concept_claims_payload, list):
        for raw_claim in concept_claims_payload:
            if not isinstance(raw_claim, Mapping):
                continue
            claim_id = _as_non_empty_str(raw_claim.get("id"))
            if claim_id is not None:
                concept_claim_ids.append(claim_id)
    for claim_id in _sorted_unique(concept_claim_ids):
        claim_entries = [
            entry
            for entry in mapped_entries_by_concept_id.get(claim_id, [])
            if entry.get("concept_kind") == "claim"
        ]
        projected_entries = [
            entry
            for entry in claim_entries
            if entry.get("core_ir_kind") in _CLAIM_PROJECTION_TARGET_KINDS
        ]
        if projected_entries:
            continue
        if claim_entries:
            entry_ref = _bridge_entry_ref(claim_entries[0])
            core_refs = [
                str(entry["core_ir_object_id"])
                for entry in claim_entries
                if _as_non_empty_str(entry.get("core_ir_object_id")) is not None
            ]
            evidence: CrossIRIssueEvidence = _BridgeEntryEvidence(entry_ref=entry_ref)
        else:
            core_refs = []
            evidence = _UnmappedEvidence(side="concept", object_id=claim_id)
        issues.append(
            _build_issue(
                issue_code="CLAIM_PROJECTION_GAP",
                concept_refs=[claim_id],
                core_ir_refs=core_refs,
                message="concept claim has no mapped claim-like core-ir projection target",
                evidence=evidence,
            )
        )

    for entry in mapped_entries:
        if entry.get("concept_kind") != "link" or entry.get("core_ir_kind") != "edge_signature":
            continue
        link_id = _as_non_empty_str(entry.get("concept_object_id"))
        core_edge_signature = _as_non_empty_str(entry.get("core_ir_object_id"))
        if link_id is None or core_edge_signature is None:
            continue
        concept_link = concept_links_by_id.get(link_id)
        if concept_link is None:
            continue
        concept_link_kind = _as_non_empty_str(concept_link.get("kind"))
        if concept_link_kind is None:
            continue
        core_edge = core_edges_by_signature.get(core_edge_signature)
        if core_edge is None:
            parsed = _parse_edge_signature(core_edge_signature)
            if parsed is None:
                continue
            edge_type, from_ref, to_ref = parsed
            core_edge = {"type": edge_type, "from": from_ref, "to": to_ref}
        edge_type = _as_non_empty_str(core_edge.get("type"))
        to_ref = _as_non_empty_str(core_edge.get("to"))
        if edge_type != "excepts" or to_ref is None:
            continue
        to_signature = core_node_signature_by_id.get(to_ref)
        if to_signature is None:
            continue
        category = _EXCEPTS_TARGET_SIGNATURE_TO_CATEGORY.get(to_signature)
        if category is None:
            continue
        expected_link_kind = _CATEGORY_TO_LINK_KIND[category]
        if concept_link_kind == expected_link_kind:
            continue
        issues.append(
            _build_issue(
                issue_code="LINK_KIND_DRIFT",
                concept_refs=[link_id],
                core_ir_refs=[core_edge_signature],
                message=(
                    "mapped concept link kind disagrees with frozen core-ir "
                    "excepts category mapping"
                ),
                evidence=_BridgeEntryEvidence(entry_ref=_bridge_entry_ref(entry)),
            )
        )

    catalog_source_text_hash = artifacts.source_text_hash
    core_source_text_hash = _extract_source_text_hash(core_payload)
    concept_source_text_hash = _extract_source_text_hash(concept_payload)
    source_hash_mismatch = False
    if concept_source_text_hash is not None and core_source_text_hash is not None:
        source_hash_mismatch = concept_source_text_hash != core_source_text_hash
    if concept_source_text_hash is not None:
        source_hash_mismatch = source_hash_mismatch or (
            concept_source_text_hash != catalog_source_text_hash
        )
    if core_source_text_hash is not None:
        source_hash_mismatch = source_hash_mismatch or (
            core_source_text_hash != catalog_source_text_hash
        )

    if (
        source_hash_mismatch
        and concept_source_text_hash is not None
        and core_source_text_hash is not None
    ):
        hashes_evidence_payload: dict[str, Any] = {
            "kind": "hashes",
            "concept_source_text_hash": concept_source_text_hash,
            "core_ir_source_text_hash": core_source_text_hash,
            "catalog_source_text_hash": catalog_source_text_hash,
        }
        concept_source_text = _extract_source_text(concept_payload)
        core_source_text = _extract_source_text(core_payload)
        if concept_source_text is not None and core_source_text is not None:
            hashes_evidence_payload["concept_source_excerpt_prefix"] = concept_source_text[:50]
            hashes_evidence_payload["core_ir_source_excerpt_prefix"] = core_source_text[:50]
        issues.append(
            _build_issue(
                issue_code="SOURCE_HASH_MISMATCH",
                concept_refs=[],
                core_ir_refs=[],
                message=(
                    "concept/core-ir source_text_hash values diverge from each "
                    "other or catalog"
                ),
                evidence=_HashesEvidence.model_validate(hashes_evidence_payload),
            )
        )

    concept_trust = _extract_trust_label(concept_payload)
    core_ir_trust = _extract_trust_label(core_payload)
    if (
        concept_trust is not None
        and core_ir_trust is not None
        and concept_trust != core_ir_trust
    ):
        issues.append(
            _build_issue(
                issue_code="TRUST_LABEL_MISMATCH",
                concept_refs=[],
                core_ir_refs=[],
                message="concept/core-ir stored trust labels differ for this pairing context",
                evidence=_TrustLabelsEvidence(
                    concept_trust=concept_trust,
                    core_ir_trust=core_ir_trust,
                ),
            )
        )

    concept_relation_pairs: set[tuple[str, str]] = set()
    concept_links_sorted: list[tuple[str, str, str]] = []
    for link_id in sorted(concept_links_by_id.keys()):
        link = concept_links_by_id[link_id]
        src_sense_id = _as_non_empty_str(link.get("src_sense_id"))
        dst_sense_id = _as_non_empty_str(link.get("dst_sense_id"))
        if src_sense_id is None or dst_sense_id is None:
            continue
        concept_links_sorted.append((link_id, src_sense_id, dst_sense_id))
        concept_relation_pairs.add((src_sense_id, dst_sense_id))

    for link_id, src_sense_id, dst_sense_id in concept_links_sorted:
        mapped_src_core_ids = sorted(mapped_sense_to_core_ids.get(src_sense_id, set()))
        mapped_dst_core_ids = sorted(mapped_sense_to_core_ids.get(dst_sense_id, set()))
        if not mapped_src_core_ids or not mapped_dst_core_ids:
            continue
        has_corresponding_core_relation = any(
            (core_src_id, core_dst_id) in core_edge_endpoint_pairs
            for core_src_id in mapped_src_core_ids
            for core_dst_id in mapped_dst_core_ids
        )
        if has_corresponding_core_relation:
            continue
        issues.append(
            _build_issue(
                issue_code="TOPOLOGY_DRIFT",
                concept_refs=[link_id],
                core_ir_refs=[],
                message=(
                    "concept relation exists but no corresponding core-ir relation "
                    "exists for mapped endpoints"
                ),
                evidence=_TopologyEvidence(
                    concept_relation_ref=link_id,
                    core_ir_relation_ref=None,
                    relation_key=_topology_relation_key(
                        concept_relation_ref=link_id,
                        core_ir_relation_ref=None,
                    ),
                ),
            )
        )

    for core_edge_signature in sorted(core_edges_by_signature.keys()):
        core_edge = core_edges_by_signature[core_edge_signature]
        from_ref = _as_non_empty_str(core_edge.get("from"))
        to_ref = _as_non_empty_str(core_edge.get("to"))
        if from_ref is None or to_ref is None:
            continue
        mapped_src_sense_ids = sorted(mapped_core_to_sense_ids.get(from_ref, set()))
        mapped_dst_sense_ids = sorted(mapped_core_to_sense_ids.get(to_ref, set()))
        if not mapped_src_sense_ids or not mapped_dst_sense_ids:
            continue
        has_corresponding_concept_relation = any(
            (src_sense_id, dst_sense_id) in concept_relation_pairs
            for src_sense_id in mapped_src_sense_ids
            for dst_sense_id in mapped_dst_sense_ids
        )
        if has_corresponding_concept_relation:
            continue
        representative_concept_relation_ref = (
            f"sense:{mapped_src_sense_ids[0]}->{mapped_dst_sense_ids[0]}"
        )
        issues.append(
            _build_issue(
                issue_code="TOPOLOGY_DRIFT",
                concept_refs=[],
                core_ir_refs=[core_edge_signature],
                message=(
                    "core-ir relation exists but no corresponding concept relation "
                    "exists for mapped endpoints"
                ),
                evidence=_TopologyEvidence(
                    concept_relation_ref=representative_concept_relation_ref,
                    core_ir_relation_ref=core_edge_signature,
                    relation_key=_topology_relation_key(
                        concept_relation_ref=representative_concept_relation_ref,
                        core_ir_relation_ref=core_edge_signature,
                    ),
                ),
            )
        )

    issues = sorted(issues, key=_issue_sort_key)
    code_counts = Counter(issue.issue_code for issue in issues)
    severity_counts = Counter(issue.severity for issue in issues)
    issue_summary = _IssueSummary(
        total_issues=len(issues),
        counts_by_code={key: code_counts[key] for key in sorted(code_counts)},
        counts_by_severity={key: severity_counts[key] for key in sorted(severity_counts)},
    )
    artifact = AdeuCrossIRCoherenceDiagnostics(
        source_text_hash=artifacts.source_text_hash,
        core_ir_artifact_id=artifacts.core_ir_artifact_id,
        concept_artifact_id=artifacts.concept_artifact_id,
        bridge_manifest_hash=bridge_manifest_hash,
        issue_summary=issue_summary,
        issues=issues,
    )
    return artifact.model_dump(mode="json", by_alias=True, exclude_none=True)


def build_cross_ir_quality_projection_vnext_plus20(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    catalog_path: Path | None = None,
) -> dict[str, Any]:
    coherence = build_cross_ir_coherence_diagnostics_vnext_plus20(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        catalog_path=catalog_path,
    )
    issue_summary = coherence["issue_summary"]
    projection = CrossIRQualityProjectionVnextPlus20(
        bridge_pair_count=1,
        coherence_issue_count=int(issue_summary["total_issues"]),
        coherence_counts_by_code={
            str(key): int(value)
            for key, value in sorted(
                dict(issue_summary.get("counts_by_code", {})).items(),
                key=lambda item: item[0],
            )
        },
        coherence_counts_by_severity={
            str(key): int(value)
            for key, value in sorted(
                dict(issue_summary.get("counts_by_severity", {})).items(),
                key=lambda item: item[0],
            )
        },
    )
    return projection.model_dump(mode="json", by_alias=True, exclude_none=True)
