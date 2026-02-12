from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from urm_runtime.errors import URMError
from urm_runtime.hashing import canonical_json, sha256_text

from .models import (
    CheckConstraintsArgs,
    EmitArtifactArgs,
    ExtractAbstractArgs,
    IngestTextArgs,
    PaperTemplateMeta,
    WarrantTag,
)

DOMAIN_PACK_ID = "urm_domain_paper"
DOMAIN_PACK_VERSION = "0.0.0"
DEFAULT_TEMPLATE_ID = "paper.abstract.pipeline.v0"
SUPPORTED_TOOL_NAMES: frozenset[str] = frozenset(
    {
        "paper.ingest_text",
        "paper.extract_abstract_candidate",
        "paper.check_constraints",
        "paper.emit_artifact",
    }
)

_TEMPLATES: tuple[PaperTemplateMeta, ...] = (
    PaperTemplateMeta(
        template_id=DEFAULT_TEMPLATE_ID,
        template_version="v0",
        schema_version="paper.workflow.v0",
        domain_pack_id=DOMAIN_PACK_ID,
        domain_pack_version=DOMAIN_PACK_VERSION,
        role="pipeline_worker",
        description="Closed-world paper abstract processing over provided local text.",
    ),
)


@dataclass
class PaperDomainTools:
    domain_pack_id: str = DOMAIN_PACK_ID
    domain_pack_version: str = DOMAIN_PACK_VERSION

    def supports_tool(self, *, tool_name: str) -> bool:
        return tool_name in SUPPORTED_TOOL_NAMES

    def list_templates(self) -> list[PaperTemplateMeta]:
        return sorted(_TEMPLATES, key=lambda item: item.template_id)

    def call_tool(self, *, tool_name: str, arguments: dict[str, Any]) -> tuple[Any, WarrantTag]:
        if not self.supports_tool(tool_name=tool_name):
            raise URMError(
                code="URM_POLICY_DENIED",
                message="unsupported tool name",
                context={"tool_name": tool_name},
            )
        if tool_name == "paper.ingest_text":
            return self._ingest_text(arguments).model_dump(mode="json"), "observed"
        if tool_name == "paper.extract_abstract_candidate":
            return self._extract_abstract_candidate(arguments), "derived"
        if tool_name == "paper.check_constraints":
            return self._check_constraints(arguments), "checked"
        if tool_name == "paper.emit_artifact":
            return self._emit_artifact(arguments), "checked"
        raise AssertionError("unreachable: tool name validated via supports_tool")

    def _ingest_text(self, arguments: dict[str, Any]) -> IngestTextArgs:
        args = IngestTextArgs.model_validate(arguments)
        return args

    def _extract_abstract_candidate(self, arguments: dict[str, Any]) -> dict[str, Any]:
        args = ExtractAbstractArgs.model_validate(arguments)
        paragraph = _normalize_whitespace(_first_paragraph(args.source_text))
        words = _word_count(paragraph)
        return {
            "abstract_text": paragraph,
            "word_count": words,
            "candidate_hash": sha256_text(paragraph),
        }

    def _check_constraints(self, arguments: dict[str, Any]) -> dict[str, Any]:
        args = CheckConstraintsArgs.model_validate(arguments)
        word_count = _word_count(_normalize_whitespace(args.abstract_text))
        checks = {
            "min_words": word_count >= args.min_words,
            "max_words": word_count <= args.max_words,
        }
        return {
            "word_count": word_count,
            "min_words": args.min_words,
            "max_words": args.max_words,
            "checks": checks,
            "passes": all(checks.values()),
        }

    def _emit_artifact(self, arguments: dict[str, Any]) -> dict[str, Any]:
        args = EmitArtifactArgs.model_validate(arguments)
        abstract_text = _normalize_whitespace(args.abstract_text)
        payload = {
            "domain": "paper.abstract",
            "title": args.title or "Untitled",
            "abstract_text": abstract_text,
            "checks": dict(sorted(args.checks.items())),
        }
        return {
            "artifact_id": sha256_text(canonical_json(payload)),
            "status": "ok",
            "artifact": payload,
        }


def _normalize_whitespace(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _first_paragraph(text: str) -> str:
    if not text:
        return text
    paragraphs = [part.strip() for part in re.split(r"\n\s*\n", text) if part.strip()]
    if paragraphs:
        return paragraphs[0]
    return text


def _word_count(text: str) -> int:
    if not text:
        return 0
    return len(text.split())
