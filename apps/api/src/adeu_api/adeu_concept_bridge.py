from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, cast

from adeu_concepts import (
    Ambiguity,
    Claim,
    ConceptContext,
    ConceptIR,
    InferentialLink,
    Term,
    TermSense,
)
from adeu_ir import AdeuIR, NormStatement, ProvenanceRef
from pydantic import BaseModel, ConfigDict, Field

from .hashing import canonical_json, sha256_text

BridgeConfidenceTag = Literal["direct", "derived", "missing_provenance"]
BridgeConceptKind = Literal["term", "sense", "claim", "link", "ambiguity"]

BRIDGE_MAPPING_VERSION = "adeu_to_concepts.v1"

_EXCEPTION_EFFECT_TO_LINK_KIND: dict[str, str] = {
    "defeats": "incompatibility",
    "narrows": "presupposition",
    "clarifies": "commitment",
}

_MAPPING_RULES: list[dict[str, str]] = [
    {
        "adeu_path": "O.entities",
        "concept_targets": "terms,senses",
        "mapping_mode": "direct",
    },
    {
        "adeu_path": "O.definitions",
        "concept_targets": "terms,senses",
        "mapping_mode": "direct",
    },
    {
        "adeu_path": "D_norm.statements",
        "concept_targets": "terms,senses,claims",
        "mapping_mode": "derived_with_provenance",
    },
    {
        "adeu_path": "D_norm.exceptions.effect=defeats",
        "concept_targets": "links(kind=incompatibility),ambiguity",
        "mapping_mode": "derived_with_provenance",
    },
    {
        "adeu_path": "D_norm.exceptions.effect=narrows",
        "concept_targets": "links(kind=presupposition),ambiguity",
        "mapping_mode": "derived_with_provenance",
    },
    {
        "adeu_path": "D_norm.exceptions.effect=clarifies",
        "concept_targets": "links(kind=commitment),ambiguity",
        "mapping_mode": "derived_with_provenance",
    },
]

_STATIC_CONFIG: dict[str, object] = {
    "exception_effect_to_link_kind": _EXCEPTION_EFFECT_TO_LINK_KIND,
    "exception_activation_strategy": "active_inactive_ambiguity",
    "id_prefixes": {
        "term_entity": "term_entity",
        "term_definition": "term_definition",
        "term_statement": "term_statement",
        "term_exception": "term_exception",
        "sense_entity": "sense_entity",
        "sense_definition": "sense_definition",
        "sense_statement": "sense_statement",
        "sense_exception_active": "sense_exception_active",
        "sense_exception_inactive": "sense_exception_inactive",
        "claim_statement": "claim_statement",
        "link_exception": "link_exception",
        "ambiguity_exception": "amb_exception",
    },
}


class BridgeManifestEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")
    adeu_object_id: str
    concept_object_id: str
    concept_kind: BridgeConceptKind
    confidence_tag: BridgeConfidenceTag


class BridgeManifest(BaseModel):
    model_config = ConfigDict(extra="forbid")
    adeu_to_concept_ids: dict[str, list[str]] = Field(default_factory=dict)
    entries: list[BridgeManifestEntry] = Field(default_factory=list)


@dataclass(frozen=True)
class AdeuConceptLiftResult:
    concept_ir: ConceptIR
    bridge_manifest: BridgeManifest
    bridge_mapping_version: str
    mapping_hash: str


@dataclass
class _IdFactory:
    used_ids: set[str]

    def make(self, *, prefix: str, source_id: str) -> str:
        token = _sanitize_id_token(source_id)
        base = f"{prefix}_{token}" if token else prefix
        candidate = base
        idx = 2
        while candidate in self.used_ids:
            candidate = f"{base}_{idx}"
            idx += 1
        self.used_ids.add(candidate)
        return candidate


def compute_mapping_hash() -> str:
    payload = {
        "bridge_mapping_version": BRIDGE_MAPPING_VERSION,
        "mapping_rules": _MAPPING_RULES,
        "static_config": _STATIC_CONFIG,
    }
    return sha256_text(canonical_json(payload))


def _sanitize_id_token(value: str) -> str:
    cleaned = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in value).strip("_")
    return cleaned or "id"


def _has_provenance(provenance: ProvenanceRef | None) -> bool:
    if provenance is None:
        return False
    return (
        provenance.doc_ref is not None
        or provenance.span is not None
        or provenance.quote is not None
    )


def _direct_confidence_tag(provenance: ProvenanceRef | None) -> BridgeConfidenceTag:
    return "direct" if _has_provenance(provenance) else "missing_provenance"


def _derived_confidence_tag(provenance: ProvenanceRef | None) -> BridgeConfidenceTag:
    return "derived" if _has_provenance(provenance) else "missing_provenance"


def _ref_text(ref: object | None) -> str:
    if ref is None:
        return "(none)"
    ref_type = getattr(ref, "ref_type", None)
    if ref_type == "entity":
        return f"entity:{getattr(ref, 'entity_id', '')}"
    if ref_type == "def":
        return f"definition:{getattr(ref, 'def_id', '')}"
    if ref_type == "doc":
        return f"doc:{getattr(ref, 'doc_ref', '')}"
    if ref_type == "text":
        return str(getattr(ref, "text", ""))
    return str(ref)


def _statement_label(statement_id: str, *, verb: str, subject_text: str) -> str:
    return f"{statement_id}: {subject_text} {verb}".strip()


def _statement_claim_text(statement: NormStatement) -> str:
    subject_text = _ref_text(statement.subject)
    verb = statement.action.verb
    object_text = _ref_text(statement.action.object)
    base = f"{statement.kind.upper()} {subject_text} {verb} {object_text}".strip()
    condition_text = statement.condition.text if statement.condition else None
    if condition_text and condition_text.strip():
        return f"{base} IF {condition_text.strip()}"
    return base


def _sort_bridge_manifest(entries: list[BridgeManifestEntry]) -> BridgeManifest:
    sorted_entries = sorted(
        entries,
        key=lambda item: (
            item.adeu_object_id,
            item.concept_kind,
            item.concept_object_id,
            item.confidence_tag,
        ),
    )
    map_builder: dict[str, list[str]] = {}
    for entry in sorted_entries:
        map_builder.setdefault(entry.adeu_object_id, []).append(entry.concept_object_id)

    adeu_to_concept_ids: dict[str, list[str]] = {}
    for adeu_object_id in sorted(map_builder.keys()):
        adeu_to_concept_ids[adeu_object_id] = sorted(set(map_builder[adeu_object_id]))

    return BridgeManifest(
        adeu_to_concept_ids=adeu_to_concept_ids,
        entries=sorted_entries,
    )


def lift_adeu_to_concepts(ir: AdeuIR) -> AdeuConceptLiftResult:
    id_factory = _IdFactory(used_ids=set())
    terms: list[Term] = []
    senses: list[TermSense] = []
    claims: list[Claim] = []
    links: list[InferentialLink] = []
    ambiguities: list[Ambiguity] = []
    bridge_entries: list[BridgeManifestEntry] = []

    statement_sense_ids: dict[str, str] = {}

    def add_manifest(
        *,
        adeu_object_id: str,
        concept_object_id: str,
        concept_kind: BridgeConceptKind,
        confidence_tag: BridgeConfidenceTag,
    ) -> None:
        bridge_entries.append(
            BridgeManifestEntry(
                adeu_object_id=adeu_object_id,
                concept_object_id=concept_object_id,
                concept_kind=concept_kind,
                confidence_tag=confidence_tag,
            )
        )

    for entity in sorted(ir.O.entities, key=lambda item: item.id):
        adeu_object_id = f"O.entities/{entity.id}"
        term_id = id_factory.make(prefix="term_entity", source_id=entity.id)
        sense_id = id_factory.make(prefix="sense_entity", source_id=entity.id)
        confidence_tag = _direct_confidence_tag(entity.provenance)
        terms.append(
            Term(
                id=term_id,
                label=entity.name,
                provenance=entity.provenance,
            )
        )
        senses.append(
            TermSense(
                id=sense_id,
                term_id=term_id,
                gloss=entity.kind or entity.name,
                provenance=entity.provenance,
            )
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=term_id,
            concept_kind="term",
            confidence_tag=confidence_tag,
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=sense_id,
            concept_kind="sense",
            confidence_tag=confidence_tag,
        )

    for definition in sorted(ir.O.definitions, key=lambda item: item.id):
        adeu_object_id = f"O.definitions/{definition.id}"
        term_id = id_factory.make(prefix="term_definition", source_id=definition.id)
        sense_id = id_factory.make(prefix="sense_definition", source_id=definition.id)
        confidence_tag = _direct_confidence_tag(definition.provenance)
        terms.append(
            Term(
                id=term_id,
                label=definition.term,
                provenance=definition.provenance,
            )
        )
        senses.append(
            TermSense(
                id=sense_id,
                term_id=term_id,
                gloss=definition.meaning,
                provenance=definition.provenance,
            )
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=term_id,
            concept_kind="term",
            confidence_tag=confidence_tag,
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=sense_id,
            concept_kind="sense",
            confidence_tag=confidence_tag,
        )

    for statement in sorted(ir.D_norm.statements, key=lambda item: item.id):
        adeu_object_id = f"D_norm.statements/{statement.id}"
        term_id = id_factory.make(prefix="term_statement", source_id=statement.id)
        sense_id = id_factory.make(prefix="sense_statement", source_id=statement.id)
        claim_id = id_factory.make(prefix="claim_statement", source_id=statement.id)
        confidence_tag = _direct_confidence_tag(statement.provenance)
        subject_text = _ref_text(statement.subject)
        terms.append(
            Term(
                id=term_id,
                label=_statement_label(
                    statement.id,
                    verb=statement.action.verb,
                    subject_text=subject_text,
                ),
                provenance=statement.provenance,
            )
        )
        senses.append(
            TermSense(
                id=sense_id,
                term_id=term_id,
                gloss=f"{statement.kind}:{statement.action.verb}",
                provenance=statement.provenance,
            )
        )
        claims.append(
            Claim(
                id=claim_id,
                sense_id=sense_id,
                text=_statement_claim_text(statement),
                provenance=statement.provenance,
            )
        )
        statement_sense_ids[statement.id] = sense_id
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=term_id,
            concept_kind="term",
            confidence_tag=confidence_tag,
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=sense_id,
            concept_kind="sense",
            confidence_tag=confidence_tag,
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=claim_id,
            concept_kind="claim",
            confidence_tag=confidence_tag,
        )

    for exception in sorted(ir.D_norm.exceptions, key=lambda item: item.id):
        adeu_object_id = f"D_norm.exceptions/{exception.id}"
        term_id = id_factory.make(prefix="term_exception", source_id=exception.id)
        active_sense_id = id_factory.make(prefix="sense_exception_active", source_id=exception.id)
        inactive_sense_id = id_factory.make(
            prefix="sense_exception_inactive",
            source_id=exception.id,
        )
        ambiguity_id = id_factory.make(prefix="amb_exception", source_id=exception.id)
        confidence_tag = _direct_confidence_tag(exception.provenance)
        derived_tag = _derived_confidence_tag(exception.provenance)
        terms.append(
            Term(
                id=term_id,
                label=f"exception:{exception.id}",
                provenance=exception.provenance,
            )
        )
        senses.append(
            TermSense(
                id=active_sense_id,
                term_id=term_id,
                gloss=f"active:{exception.effect}",
                provenance=exception.provenance,
            )
        )
        senses.append(
            TermSense(
                id=inactive_sense_id,
                term_id=term_id,
                gloss="inactive",
                provenance=exception.provenance,
            )
        )
        ambiguities.append(
            Ambiguity(
                id=ambiguity_id,
                term_id=term_id,
                options=[active_sense_id, inactive_sense_id],
            )
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=term_id,
            concept_kind="term",
            confidence_tag=confidence_tag,
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=active_sense_id,
            concept_kind="sense",
            confidence_tag=confidence_tag,
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=inactive_sense_id,
            concept_kind="sense",
            confidence_tag=derived_tag,
        )
        add_manifest(
            adeu_object_id=adeu_object_id,
            concept_object_id=ambiguity_id,
            concept_kind="ambiguity",
            confidence_tag=derived_tag,
        )

        link_kind = _EXCEPTION_EFFECT_TO_LINK_KIND.get(exception.effect, "presupposition")
        for applies_to_id in sorted(exception.applies_to):
            target_sense_id = statement_sense_ids.get(applies_to_id)
            if target_sense_id is None:
                continue
            link_id = id_factory.make(
                prefix="link_exception",
                source_id=f"{exception.id}_{applies_to_id}",
            )
            kind = cast(
                Literal["commitment", "incompatibility", "presupposition"],
                link_kind,
            )
            links.append(
                InferentialLink(
                    id=link_id,
                    kind=kind,
                    src_sense_id=target_sense_id,
                    dst_sense_id=active_sense_id,
                    provenance=exception.provenance,
                )
            )
            add_manifest(
                adeu_object_id=adeu_object_id,
                concept_object_id=link_id,
                concept_kind="link",
                confidence_tag=derived_tag,
            )

    concept_ir = ConceptIR(
        schema_version="adeu.concepts.v0",
        concept_id=f"concept_bridge_{_sanitize_id_token(ir.ir_id)}",
        context=ConceptContext(
            doc_id=ir.context.doc_id,
            domain_tags=sorted(
                {
                    "adeu_bridge",
                    f"jurisdiction:{ir.context.jurisdiction}",
                }
            ),
        ),
        terms=sorted(terms, key=lambda item: item.id),
        senses=sorted(senses, key=lambda item: item.id),
        claims=sorted(claims, key=lambda item: item.id),
        links=sorted(links, key=lambda item: item.id),
        ambiguity=sorted(ambiguities, key=lambda item: item.id),
        bridges=[],
    )

    return AdeuConceptLiftResult(
        concept_ir=concept_ir,
        bridge_manifest=_sort_bridge_manifest(bridge_entries),
        bridge_mapping_version=BRIDGE_MAPPING_VERSION,
        mapping_hash=compute_mapping_hash(),
    )
