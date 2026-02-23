from __future__ import annotations

import json
import re
from collections.abc import Mapping
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Literal, NamedTuple

from adeu_concepts import ConceptIR
from adeu_core_ir import AdeuCoreIR
from pydantic import BaseModel, ConfigDict, Field, model_validator

from .adeu_concept_bridge import BRIDGE_MAPPING_VERSION
from .hashing import canonical_json, sha256_text

CROSS_IR_CATALOG_SCHEMA = "cross_ir.vnext_plus20_catalog@1"
CROSS_IR_BRIDGE_MANIFEST_SCHEMA = "adeu_cross_ir_bridge_manifest@0.1"
CROSS_IR_CATALOG_PATH = (
    Path(__file__).resolve().parents[2] / "fixtures" / "cross_ir" / "vnext_plus20_catalog.json"
)
_ADEU_CORE_IR_SCHEMA = "adeu_core_ir@0.1"
_ADEU_CONCEPTS_SCHEMA = "adeu.concepts.v0"
_HEX64_RE = re.compile(r"^[0-9a-f]{64}$")

CrossIRConceptKind = Literal["term", "sense", "claim", "link", "ambiguity"]
CrossIRCoreKind = Literal[
    "O.Entity",
    "O.Concept",
    "O.RelationType",
    "E.Claim",
    "E.Assumption",
    "E.Question",
    "E.Evidence",
    "D.PhysicalConstraint",
    "D.Norm",
    "D.Policy",
    "D.Exception",
    "U.Goal",
    "U.Metric",
    "U.Preference",
    "edge_signature",
]
CrossIRMappingStatus = Literal["mapped", "concept_only", "core_ir_only"]
CrossIRConfidenceTag = Literal["direct", "derived", "missing_provenance"]


class CrossIRBridgeVnextPlus20Error(ValueError):
    def __init__(self, *, code: str, reason: str, context: Mapping[str, Any] | None = None) -> None:
        super().__init__(reason)
        self.code = code
        self.reason = reason
        self.context = dict(context or {})


class CrossIRCatalogArtifactRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    artifact_ref_id: str = Field(min_length=1)
    schema: str = Field(min_length=1)
    path: str = Field(min_length=1)


class CrossIRCatalogEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    bridge_mapping_version: str = Field(min_length=1)
    mapping_hash: str = Field(min_length=64, max_length=64)
    created_at: str | None = None
    domain_id: str | None = None
    document_ref: str | None = None
    intentional_concept_only_object_ids: list[str] = Field(default_factory=list)
    intentional_core_ir_only_object_ids: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "CrossIRCatalogEntry":
        if self.bridge_mapping_version != BRIDGE_MAPPING_VERSION:
            raise ValueError(
                "bridge_mapping_version must match frozen continuity value "
                f"{BRIDGE_MAPPING_VERSION!r}"
            )
        if not _HEX64_RE.fullmatch(self.mapping_hash):
            raise ValueError("mapping_hash must be a lowercase sha256 hex digest")
        if self.intentional_concept_only_object_ids != sorted(
            self.intentional_concept_only_object_ids
        ):
            raise ValueError("intentional_concept_only_object_ids must be sorted")
        if len(set(self.intentional_concept_only_object_ids)) != len(
            self.intentional_concept_only_object_ids
        ):
            raise ValueError("intentional_concept_only_object_ids may not contain duplicates")
        if self.intentional_core_ir_only_object_ids != sorted(
            self.intentional_core_ir_only_object_ids
        ):
            raise ValueError("intentional_core_ir_only_object_ids must be sorted")
        if len(set(self.intentional_core_ir_only_object_ids)) != len(
            self.intentional_core_ir_only_object_ids
        ):
            raise ValueError("intentional_core_ir_only_object_ids may not contain duplicates")
        return self


class CrossIRCatalog(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["cross_ir.vnext_plus20_catalog@1"] = CROSS_IR_CATALOG_SCHEMA
    artifact_refs: list[CrossIRCatalogArtifactRef]
    entries: list[CrossIRCatalogEntry]

    @model_validator(mode="after")
    def _validate_contract(self) -> "CrossIRCatalog":
        artifact_ref_ids = [item.artifact_ref_id for item in self.artifact_refs]
        if artifact_ref_ids != sorted(artifact_ref_ids):
            raise ValueError("artifact_refs must be sorted by artifact_ref_id")
        if len(set(artifact_ref_ids)) != len(artifact_ref_ids):
            raise ValueError("artifact_refs contain duplicate artifact_ref_id values")

        sorted_entries = sorted(
            self.entries,
            key=lambda entry: (
                entry.source_text_hash,
                entry.core_ir_artifact_id,
                entry.concept_artifact_id,
            ),
        )
        if self.entries != sorted_entries:
            raise ValueError(
                "entries must be sorted by "
                "(source_text_hash, core_ir_artifact_id, concept_artifact_id)"
            )

        identity_values = [
            (entry.source_text_hash, entry.core_ir_artifact_id, entry.concept_artifact_id)
            for entry in self.entries
        ]
        if len(set(identity_values)) != len(identity_values):
            raise ValueError("entries contain duplicate pair identity tuples")

        known_refs = set(artifact_ref_ids)
        refs_by_id = {item.artifact_ref_id: item for item in self.artifact_refs}
        for entry in self.entries:
            if entry.core_ir_artifact_id not in known_refs:
                raise ValueError(
                    f"entry.core_ir_artifact_id not found in artifact_refs: "
                    f"{entry.core_ir_artifact_id}"
                )
            if entry.concept_artifact_id not in known_refs:
                raise ValueError(
                    f"entry.concept_artifact_id not found in artifact_refs: "
                    f"{entry.concept_artifact_id}"
                )
            if refs_by_id[entry.core_ir_artifact_id].schema != _ADEU_CORE_IR_SCHEMA:
                raise ValueError(
                    "entry.core_ir_artifact_id must point to adeu_core_ir@0.1 artifact ref"
                )
            if refs_by_id[entry.concept_artifact_id].schema != _ADEU_CONCEPTS_SCHEMA:
                raise ValueError(
                    "entry.concept_artifact_id must point to adeu.concepts.v0 artifact ref"
                )
        return self


class AdeuCrossIRBridgeManifestEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    concept_object_id: str | None = None
    concept_kind: CrossIRConceptKind | None = None
    core_ir_object_id: str | None = None
    core_ir_kind: CrossIRCoreKind | None = None
    mapping_status: CrossIRMappingStatus
    confidence_tag: CrossIRConfidenceTag

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuCrossIRBridgeManifestEntry":
        if self.mapping_status == "mapped":
            if (
                self.concept_object_id is None
                or self.concept_kind is None
                or self.core_ir_object_id is None
                or self.core_ir_kind is None
            ):
                raise ValueError(
                    "mapped entries must include both concept and core-ir identity fields"
                )
            return self

        if self.mapping_status == "concept_only":
            if self.concept_object_id is None or self.concept_kind is None:
                raise ValueError("concept_only entries must include concept identity fields")
            if self.core_ir_object_id is not None or self.core_ir_kind is not None:
                raise ValueError("concept_only entries may not include core-ir identity fields")
            return self

        if self.core_ir_object_id is None or self.core_ir_kind is None:
            raise ValueError("core_ir_only entries must include core-ir identity fields")
        if self.concept_object_id is not None or self.concept_kind is not None:
            raise ValueError("core_ir_only entries may not include concept identity fields")
        return self


class AdeuCrossIRBridgeManifest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_cross_ir_bridge_manifest@0.1"] = CROSS_IR_BRIDGE_MANIFEST_SCHEMA
    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    bridge_mapping_version: Literal["adeu_to_concepts.v1"] = BRIDGE_MAPPING_VERSION
    mapping_hash: str = Field(min_length=64, max_length=64)
    entries: list[AdeuCrossIRBridgeManifestEntry]
    unmapped_concept_objects: list[str] = Field(default_factory=list)
    unmapped_core_ir_objects: list[str] = Field(default_factory=list)
    created_at: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuCrossIRBridgeManifest":
        if not _HEX64_RE.fullmatch(self.mapping_hash):
            raise ValueError("mapping_hash must be a lowercase sha256 hex digest")

        entry_keys = [
            (
                entry.concept_object_id or "",
                entry.core_ir_object_id or "",
                entry.concept_kind or "",
                entry.core_ir_kind or "",
                entry.mapping_status,
            )
            for entry in self.entries
        ]
        if entry_keys != sorted(entry_keys):
            raise ValueError("entries must be sorted deterministically")

        if self.unmapped_concept_objects != sorted(self.unmapped_concept_objects):
            raise ValueError("unmapped_concept_objects must be sorted")
        if len(set(self.unmapped_concept_objects)) != len(self.unmapped_concept_objects):
            raise ValueError("unmapped_concept_objects may not contain duplicates")

        if self.unmapped_core_ir_objects != sorted(self.unmapped_core_ir_objects):
            raise ValueError("unmapped_core_ir_objects must be sorted")
        if len(set(self.unmapped_core_ir_objects)) != len(self.unmapped_core_ir_objects):
            raise ValueError("unmapped_core_ir_objects may not contain duplicates")

        concept_only_ids = sorted(
            entry.concept_object_id
            for entry in self.entries
            if entry.mapping_status == "concept_only" and entry.concept_object_id is not None
        )
        if concept_only_ids != self.unmapped_concept_objects:
            raise ValueError(
                "unmapped_concept_objects must match concept_only entries exactly"
            )

        core_only_ids = sorted(
            entry.core_ir_object_id
            for entry in self.entries
            if entry.mapping_status == "core_ir_only" and entry.core_ir_object_id is not None
        )
        if core_only_ids != self.unmapped_core_ir_objects:
            raise ValueError("unmapped_core_ir_objects must match core_ir_only entries exactly")

        return self


class _CrossIRCatalogIndex(NamedTuple):
    catalog_path: Path
    artifact_refs_by_id: dict[str, CrossIRCatalogArtifactRef]
    core_payloads_by_id: dict[str, dict[str, Any]]
    concept_payloads_by_id: dict[str, dict[str, Any]]
    entries_by_identity: dict[tuple[str, str, str], CrossIRCatalogEntry]


@dataclass(frozen=True)
class _ConceptObject:
    object_id: str
    kind: CrossIRConceptKind
    has_provenance: bool


@dataclass(frozen=True)
class _CoreObject:
    object_id: str
    kind: CrossIRCoreKind


def _cross_ir_bridge_error(
    *,
    code: str,
    reason: str,
    context: Mapping[str, Any] | None = None,
) -> CrossIRBridgeVnextPlus20Error:
    return CrossIRBridgeVnextPlus20Error(code=code, reason=reason, context=context)


def _resolved_catalog_path(catalog_path: Path | None) -> Path:
    selected = CROSS_IR_CATALOG_PATH if catalog_path is None else Path(catalog_path)
    return selected.resolve()


def _load_json_payload(*, path: Path, artifact_ref_id: str) -> dict[str, Any]:
    try:
        raw = path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir artifact fixture is missing",
            context={"artifact_ref_id": artifact_ref_id, "path": str(path)},
        ) from exc
    except OSError as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir artifact fixture is unreadable",
            context={"artifact_ref_id": artifact_ref_id, "path": str(path), "error": str(exc)},
        ) from exc

    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir artifact fixture JSON is invalid",
            context={"artifact_ref_id": artifact_ref_id, "path": str(path), "error": exc.msg},
        ) from exc

    if not isinstance(payload, dict):
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir artifact fixture payload must be an object",
            context={"artifact_ref_id": artifact_ref_id, "path": str(path)},
        )
    return payload


def _resolve_artifact_path(*, catalog_path: Path, artifact_path: str) -> Path:
    candidate = Path(artifact_path)
    if not candidate.is_absolute():
        candidate = catalog_path.parent / candidate
    return candidate.resolve()


def _validate_core_payload(
    *, payload: dict[str, Any], artifact_ref_id: str, path: Path
) -> dict[str, Any]:
    try:
        normalized = AdeuCoreIR.model_validate(payload)
    except Exception as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_PAYLOAD_INVALID",
            reason="core-ir payload failed schema validation",
            context={"artifact_ref_id": artifact_ref_id, "path": str(path), "error": str(exc)},
        ) from exc
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def _validate_concept_payload(
    *, payload: dict[str, Any], artifact_ref_id: str, path: Path
) -> dict[str, Any]:
    try:
        normalized = ConceptIR.model_validate(payload)
    except Exception as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_PAYLOAD_INVALID",
            reason="concept payload failed schema validation",
            context={"artifact_ref_id": artifact_ref_id, "path": str(path), "error": str(exc)},
        ) from exc
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


@lru_cache(maxsize=16)
def _catalog_index_for_path(catalog_path_value: str) -> _CrossIRCatalogIndex:
    catalog_path = Path(catalog_path_value)
    try:
        raw_payload = catalog_path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir catalog fixture is missing",
            context={"path": str(catalog_path)},
        ) from exc
    except OSError as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir catalog fixture is unreadable",
            context={"path": str(catalog_path), "error": str(exc)},
        ) from exc

    try:
        parsed = json.loads(raw_payload)
    except json.JSONDecodeError as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir catalog JSON is invalid",
            context={"path": str(catalog_path), "error": exc.msg},
        ) from exc

    if not isinstance(parsed, dict):
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir catalog payload must be an object",
            context={"path": str(catalog_path)},
        )

    try:
        catalog = CrossIRCatalog.model_validate(parsed)
    except Exception as exc:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason="cross-ir catalog payload failed schema validation",
            context={"path": str(catalog_path), "error": str(exc)},
        ) from exc

    artifact_refs_by_id = {
        artifact_ref.artifact_ref_id: artifact_ref for artifact_ref in catalog.artifact_refs
    }
    core_payloads_by_id: dict[str, dict[str, Any]] = {}
    concept_payloads_by_id: dict[str, dict[str, Any]] = {}

    for artifact_ref in catalog.artifact_refs:
        resolved_path = _resolve_artifact_path(
            catalog_path=catalog_path,
            artifact_path=artifact_ref.path,
        )
        payload = _load_json_payload(
            path=resolved_path,
            artifact_ref_id=artifact_ref.artifact_ref_id,
        )

        payload_schema = payload.get("schema")
        payload_schema_version = payload.get("schema_version")
        if artifact_ref.schema == _ADEU_CORE_IR_SCHEMA:
            if payload_schema != _ADEU_CORE_IR_SCHEMA:
                raise _cross_ir_bridge_error(
                    code="URM_ADEU_CROSS_IR_PAYLOAD_INVALID",
                    reason="core-ir payload schema mismatch",
                    context={
                        "artifact_ref_id": artifact_ref.artifact_ref_id,
                        "path": str(resolved_path),
                        "declared_schema": artifact_ref.schema,
                        "payload_schema": payload_schema,
                    },
                )
            core_payloads_by_id[artifact_ref.artifact_ref_id] = _validate_core_payload(
                payload=payload,
                artifact_ref_id=artifact_ref.artifact_ref_id,
                path=resolved_path,
            )
        elif artifact_ref.schema == _ADEU_CONCEPTS_SCHEMA:
            if payload_schema_version != _ADEU_CONCEPTS_SCHEMA:
                raise _cross_ir_bridge_error(
                    code="URM_ADEU_CROSS_IR_PAYLOAD_INVALID",
                    reason="concept payload schema_version mismatch",
                    context={
                        "artifact_ref_id": artifact_ref.artifact_ref_id,
                        "path": str(resolved_path),
                        "declared_schema": artifact_ref.schema,
                        "payload_schema_version": payload_schema_version,
                    },
                )
            concept_payloads_by_id[artifact_ref.artifact_ref_id] = _validate_concept_payload(
                payload=payload,
                artifact_ref_id=artifact_ref.artifact_ref_id,
                path=resolved_path,
            )
        else:
            raise _cross_ir_bridge_error(
                code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
                reason="cross-ir artifact ref uses unsupported schema",
                context={
                    "artifact_ref_id": artifact_ref.artifact_ref_id,
                    "schema": artifact_ref.schema,
                    "path": str(resolved_path),
                },
            )

    entries_by_identity: dict[tuple[str, str, str], CrossIRCatalogEntry] = {}
    for entry in catalog.entries:
        core_payload = core_payloads_by_id[entry.core_ir_artifact_id]
        core_source_text_hash = core_payload.get("source_text_hash")
        if core_source_text_hash != entry.source_text_hash:
            raise _cross_ir_bridge_error(
                code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
                reason="catalog source_text_hash does not match core-ir payload",
                context={
                    "source_text_hash": entry.source_text_hash,
                    "core_ir_artifact_id": entry.core_ir_artifact_id,
                    "payload_source_text_hash": core_source_text_hash,
                },
            )
        identity = (entry.source_text_hash, entry.core_ir_artifact_id, entry.concept_artifact_id)
        entries_by_identity[identity] = entry

    return _CrossIRCatalogIndex(
        catalog_path=catalog_path,
        artifact_refs_by_id=artifact_refs_by_id,
        core_payloads_by_id=core_payloads_by_id,
        concept_payloads_by_id=concept_payloads_by_id,
        entries_by_identity=entries_by_identity,
    )


def _catalog_index(*, catalog_path: Path | None = None) -> _CrossIRCatalogIndex:
    resolved_catalog_path = _resolved_catalog_path(catalog_path)
    return _catalog_index_for_path(str(resolved_catalog_path))


def _concept_has_provenance(raw: Mapping[str, Any]) -> bool:
    provenance = raw.get("provenance")
    if not isinstance(provenance, Mapping):
        return False
    return any(
        value not in (None, "", [])
        for value in (
            provenance.get("doc_ref"),
            provenance.get("span"),
            provenance.get("quote"),
        )
    )


def _concept_objects(payload: Mapping[str, Any]) -> list[_ConceptObject]:
    objects: list[_ConceptObject] = []
    for kind, field in (
        ("term", "terms"),
        ("sense", "senses"),
        ("claim", "claims"),
        ("link", "links"),
        ("ambiguity", "ambiguity"),
    ):
        items = payload.get(field)
        if not isinstance(items, list):
            continue
        for raw in items:
            if not isinstance(raw, Mapping):
                continue
            object_id = raw.get("id")
            if not isinstance(object_id, str) or not object_id:
                continue
            objects.append(
                _ConceptObject(
                    object_id=object_id,
                    kind=kind,
                    has_provenance=_concept_has_provenance(raw),
                )
            )
    return sorted(objects, key=lambda item: (item.object_id, item.kind))


def _core_objects(payload: Mapping[str, Any]) -> list[_CoreObject]:
    objects: list[_CoreObject] = []

    nodes = payload.get("nodes")
    if isinstance(nodes, list):
        for raw in nodes:
            if not isinstance(raw, Mapping):
                continue
            object_id = raw.get("id")
            layer = raw.get("layer")
            kind = raw.get("kind")
            if not isinstance(object_id, str) or not object_id:
                continue
            if not isinstance(layer, str) or not isinstance(kind, str):
                continue
            objects.append(_CoreObject(object_id=object_id, kind=f"{layer}.{kind}"))

    edges = payload.get("edges")
    if isinstance(edges, list):
        for raw in edges:
            if not isinstance(raw, Mapping):
                continue
            edge_type = raw.get("type")
            from_ref = raw.get("from")
            to_ref = raw.get("to")
            if (
                not isinstance(edge_type, str)
                or not isinstance(from_ref, str)
                or not isinstance(to_ref, str)
            ):
                continue
            objects.append(
                _CoreObject(
                    object_id=f"edge:{edge_type}:{from_ref}:{to_ref}",
                    kind="edge_signature",
                )
            )
    return sorted(objects, key=lambda item: (item.object_id, item.kind))


def _bridge_entries(
    *,
    concept_objects: list[_ConceptObject],
    core_objects: list[_CoreObject],
) -> tuple[list[AdeuCrossIRBridgeManifestEntry], list[str], list[str]]:
    core_by_id: dict[str, list[_CoreObject]] = {}
    for core_object in core_objects:
        core_by_id.setdefault(core_object.object_id, []).append(core_object)

    entries: list[AdeuCrossIRBridgeManifestEntry] = []
    matched_core_ids: set[str] = set()

    for concept_object in concept_objects:
        candidates = core_by_id.get(concept_object.object_id, [])
        if len(candidates) > 1:
            raise _cross_ir_bridge_error(
                code="URM_ADEU_CROSS_IR_REQUEST_INVALID",
                reason="ambiguous core-ir mapping candidates for concept object id",
                context={
                    "concept_object_id": concept_object.object_id,
                    "candidate_core_ir_kinds": sorted(item.kind for item in candidates),
                },
            )
        if len(candidates) == 1:
            candidate = candidates[0]
            matched_core_ids.add(candidate.object_id)
            confidence_tag: CrossIRConfidenceTag = (
                "direct" if concept_object.has_provenance else "missing_provenance"
            )
            entries.append(
                AdeuCrossIRBridgeManifestEntry(
                    concept_object_id=concept_object.object_id,
                    concept_kind=concept_object.kind,
                    core_ir_object_id=candidate.object_id,
                    core_ir_kind=candidate.kind,
                    mapping_status="mapped",
                    confidence_tag=confidence_tag,
                )
            )
        else:
            entries.append(
                AdeuCrossIRBridgeManifestEntry(
                    concept_object_id=concept_object.object_id,
                    concept_kind=concept_object.kind,
                    mapping_status="concept_only",
                    confidence_tag=(
                        "direct" if concept_object.has_provenance else "missing_provenance"
                    ),
                )
            )

    for core_object in core_objects:
        if core_object.object_id in matched_core_ids:
            continue
        entries.append(
            AdeuCrossIRBridgeManifestEntry(
                core_ir_object_id=core_object.object_id,
                core_ir_kind=core_object.kind,
                mapping_status="core_ir_only",
                confidence_tag="missing_provenance",
            )
        )

    entries = sorted(
        entries,
        key=lambda entry: (
            entry.concept_object_id or "",
            entry.core_ir_object_id or "",
            entry.concept_kind or "",
            entry.core_ir_kind or "",
            entry.mapping_status,
        ),
    )
    unmapped_concept_objects = sorted(
        entry.concept_object_id
        for entry in entries
        if entry.mapping_status == "concept_only" and entry.concept_object_id is not None
    )
    unmapped_core_ir_objects = sorted(
        entry.core_ir_object_id
        for entry in entries
        if entry.mapping_status == "core_ir_only" and entry.core_ir_object_id is not None
    )
    return entries, unmapped_concept_objects, unmapped_core_ir_objects


def list_cross_ir_catalog_pairs_vnext_plus20(
    *,
    catalog_path: Path | None = None,
) -> list[dict[str, str]]:
    index = _catalog_index(catalog_path=catalog_path)

    identities = sorted(index.entries_by_identity.keys())
    return [
        {
            "source_text_hash": source_text_hash,
            "core_ir_artifact_id": core_ir_artifact_id,
            "concept_artifact_id": concept_artifact_id,
        }
        for source_text_hash, core_ir_artifact_id, concept_artifact_id in identities
    ]


def build_cross_ir_bridge_manifest_vnext_plus20(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    catalog_path: Path | None = None,
) -> dict[str, Any]:
    identity = (source_text_hash, core_ir_artifact_id, concept_artifact_id)

    index = _catalog_index(catalog_path=catalog_path)
    entry = index.entries_by_identity.get(identity)
    if entry is None:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_ARTIFACT_NOT_FOUND",
            reason="cross-ir pair identity not found in catalog",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
            },
        )

    core_payload = index.core_payloads_by_id[entry.core_ir_artifact_id]
    concept_payload = index.concept_payloads_by_id[entry.concept_artifact_id]

    concept_objects = _concept_objects(concept_payload)
    core_objects = _core_objects(core_payload)
    entries, unmapped_concept_objects, unmapped_core_ir_objects = _bridge_entries(
        concept_objects=concept_objects,
        core_objects=core_objects,
    )
    missing_intentional_concept_only = sorted(
        set(entry.intentional_concept_only_object_ids) - set(unmapped_concept_objects)
    )
    if missing_intentional_concept_only:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason=(
                "catalog intentional_concept_only_object_ids must be present in "
                "computed unmapped_concept_objects"
            ),
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "missing_intentional_concept_only_object_ids": missing_intentional_concept_only,
            },
        )

    missing_intentional_core_ir_only = sorted(
        set(entry.intentional_core_ir_only_object_ids) - set(unmapped_core_ir_objects)
    )
    if missing_intentional_core_ir_only:
        raise _cross_ir_bridge_error(
            code="URM_ADEU_CROSS_IR_FIXTURE_INVALID",
            reason=(
                "catalog intentional_core_ir_only_object_ids must be present in "
                "computed unmapped_core_ir_objects"
            ),
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "missing_intentional_core_ir_only_object_ids": missing_intentional_core_ir_only,
            },
        )

    manifest = AdeuCrossIRBridgeManifest(
        source_text_hash=entry.source_text_hash,
        core_ir_artifact_id=entry.core_ir_artifact_id,
        concept_artifact_id=entry.concept_artifact_id,
        bridge_mapping_version=entry.bridge_mapping_version,
        mapping_hash=entry.mapping_hash,
        entries=entries,
        unmapped_concept_objects=unmapped_concept_objects,
        unmapped_core_ir_objects=unmapped_core_ir_objects,
        created_at=entry.created_at,
    )
    return manifest.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonical_bridge_manifest_hash_vnext_plus20(
    manifest: Mapping[str, Any],
) -> str:
    projection = {
        "source_text_hash": manifest["source_text_hash"],
        "core_ir_artifact_id": manifest["core_ir_artifact_id"],
        "concept_artifact_id": manifest["concept_artifact_id"],
        "bridge_mapping_version": manifest["bridge_mapping_version"],
        "entries": manifest["entries"],
        "unmapped_concept_objects": manifest["unmapped_concept_objects"],
        "unmapped_core_ir_objects": manifest["unmapped_core_ir_objects"],
    }
    return sha256_text(canonical_json(projection))
