from __future__ import annotations

from pydantic import BaseModel, ConfigDict, Field
from urm_runtime.domain_registry import WarrantTag as DomainWarrantTag

WarrantTag = DomainWarrantTag


class PaperTemplateMeta(BaseModel):
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


class ExtractAbstractArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_text: str = Field(min_length=1)


class CheckConstraintsArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    abstract_text: str = Field(min_length=1)
    min_words: int = Field(default=30, ge=1, le=500)
    max_words: int = Field(default=300, ge=1, le=1000)


class EmitArtifactArgs(BaseModel):
    model_config = ConfigDict(extra="forbid")

    title: str | None = Field(default=None, min_length=1)
    abstract_text: str = Field(min_length=1)
    checks: dict[str, bool] = Field(default_factory=dict)
