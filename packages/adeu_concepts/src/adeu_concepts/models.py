from __future__ import annotations

from typing import Literal

from adeu_ir import ProvenanceRef
from pydantic import BaseModel, ConfigDict, Field

ConceptSchemaVersion = Literal["adeu.concepts.v0"]
InferentialLinkKind = Literal["commitment", "incompatibility", "presupposition"]


class ConceptContext(BaseModel):
    model_config = ConfigDict(extra="forbid")
    doc_id: str
    domain_tags: list[str] = Field(default_factory=list)


class Term(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    label: str
    provenance: ProvenanceRef | None = None


class TermSense(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    term_id: str
    gloss: str
    provenance: ProvenanceRef | None = None


class Claim(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    sense_id: str
    text: str
    provenance: ProvenanceRef | None = None


class InferentialLink(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    kind: InferentialLinkKind
    src_sense_id: str
    dst_sense_id: str
    provenance: ProvenanceRef | None = None


class Ambiguity(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    term_id: str
    options: list[str] = Field(min_length=2)


class ConceptBridge(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    kind: str
    src_sense_id: str
    dst_sense_id: str
    provenance: ProvenanceRef | None = None


class ConceptIR(BaseModel):
    model_config = ConfigDict(extra="forbid")
    schema_version: ConceptSchemaVersion = "adeu.concepts.v0"
    concept_id: str
    context: ConceptContext
    terms: list[Term] = Field(default_factory=list)
    senses: list[TermSense] = Field(default_factory=list)
    claims: list[Claim] = Field(default_factory=list)
    links: list[InferentialLink] = Field(default_factory=list)
    ambiguity: list[Ambiguity] = Field(default_factory=list)
    bridges: list[ConceptBridge] = Field(default_factory=list)
