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

_DATE_ONLY_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
_ABSTRACT_HEADER_WITH_BODY_RE = re.compile(r"^\s*abstract\s*[:\-]\s*(.+)\s*$", re.IGNORECASE)
_ABSTRACT_HEADER_RE = re.compile(r"^\s*abstract\s*[:\-]?\s*$", re.IGNORECASE)
_SECTION_STOP_RE = re.compile(
    r"^\s*(keywords?|index\s+terms|introduction|[1i]+[\.\)]\s*introduction)\b",
    re.IGNORECASE,
)
_SENTENCE_BOUNDARY_RE = re.compile(r"[.!?](?:\s|$)")


@dataclass
class PaperDomainTools:
    domain_pack_id: str = DOMAIN_PACK_ID
    domain_pack_version: str = DOMAIN_PACK_VERSION

    def supports_tool(self, *, tool_name: str) -> bool:
        return tool_name in SUPPORTED_TOOL_NAMES

    def list_tools(self) -> list[str]:
        return sorted(SUPPORTED_TOOL_NAMES)

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
        paragraph, strategy = _select_abstract_candidate(args.source_text)
        words = _word_count(paragraph)
        sentence_count = _sentence_count(paragraph)
        return {
            "abstract_text": paragraph,
            "word_count": words,
            "sentence_count": sentence_count,
            "extract_strategy": strategy,
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


def _paragraphs(text: str) -> list[str]:
    if not text:
        return []
    return [_normalize_whitespace(part) for part in re.split(r"\n\s*\n", text) if part.strip()]


def _extract_abstract_section(text: str) -> str | None:
    lines = text.splitlines()
    collecting = False
    collected: list[str] = []

    for raw_line in lines:
        line = raw_line.strip()
        if not line and collecting:
            if collected:
                break
            continue

        inline_match = _ABSTRACT_HEADER_WITH_BODY_RE.match(line)
        if inline_match:
            body = _normalize_whitespace(inline_match.group(1))
            if body:
                collected.append(body)
            collecting = True
            continue

        if _ABSTRACT_HEADER_RE.match(line):
            collecting = True
            continue

        if collecting:
            if _SECTION_STOP_RE.match(line):
                break
            collected.append(line)

    candidate = _normalize_whitespace(" ".join(collected))
    return candidate or None


def _is_date_like(text: str) -> bool:
    value = _normalize_whitespace(text)
    return bool(_DATE_ONLY_RE.match(value))


def _sentence_count(text: str) -> int:
    if not text:
        return 0
    return len(_SENTENCE_BOUNDARY_RE.findall(text))


def _is_structurally_abstract_like(text: str) -> bool:
    if _is_date_like(text):
        return False
    if _word_count(text) < 20:
        return False
    return _sentence_count(text) >= 2


def _select_abstract_candidate(text: str) -> tuple[str, str]:
    section_candidate = _extract_abstract_section(text)
    if section_candidate and _is_structurally_abstract_like(section_candidate):
        return section_candidate, "abstract_section_marker"
    if section_candidate and not _is_date_like(section_candidate):
        return section_candidate, "abstract_section_fallback"

    first_nondatelike_paragraph: str | None = None
    for paragraph in _paragraphs(text):
        if _is_structurally_abstract_like(paragraph):
            return paragraph, "first_structural_paragraph"
        if first_nondatelike_paragraph is None and not _is_date_like(paragraph):
            first_nondatelike_paragraph = paragraph

    if first_nondatelike_paragraph is not None:
        return first_nondatelike_paragraph, "first_nondatelike_paragraph"

    return _normalize_whitespace(_first_paragraph(text)), "first_paragraph_fallback"


def _word_count(text: str) -> int:
    if not text:
        return 0
    return len(text.split())
