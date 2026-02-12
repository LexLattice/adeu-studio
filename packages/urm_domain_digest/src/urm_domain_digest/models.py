from __future__ import annotations

from pydantic import BaseModel, ConfigDict, Field
from urm_runtime.domain_registry import WarrantTag as DomainWarrantTag

WarrantTag = DomainWarrantTag


class DigestTemplateMeta(BaseModel):
    model_config = ConfigDict(extra="forbid")

    template_id: str = Field(min_length=1)
    template_version: str = Field(min_length=1)
    schema_version: str = Field(min_length=1)
    domain_pack_id: str = Field(min_length=1)
    domain_pack_version: str = Field(min_length=1)
    role: str = Field(min_length=1)
    description: str = Field(min_length=1)


class IngestTextArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_text: str = Field(min_length=1)
    title: str | None = Field(default=None, min_length=1)


class ExtractDigestArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_text: str = Field(min_length=1)
    max_sentences: int = Field(default=2, ge=1, le=10)
    max_words: int = Field(default=80, ge=5, le=500)


class CheckConstraintsArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    digest_text: str = Field(min_length=1)
    min_words: int = Field(default=15, ge=1, le=500)
    max_words: int = Field(default=120, ge=1, le=1000)
    max_sentences: int = Field(default=4, ge=1, le=20)


class EvidenceRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: str = Field(min_length=1)
    ref: str = Field(min_length=1)
    note: str | None = None


class EmitArtifactArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    input_hash: str = Field(min_length=1)
    digest_text: str = Field(min_length=1)
    title: str | None = Field(default=None, min_length=1)
    checks: dict[str, bool] = Field(default_factory=dict)
    policy_hash: str = Field(default="unknown", min_length=1)
    evidence_refs: list[EvidenceRef] = Field(default_factory=list)
