from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from urm_runtime.errors import URMError
from urm_runtime.hashing import canonical_json, sha256_text

from .models import (
    CheckConstraintsArgs,
    DigestTemplateMeta,
    EmitArtifactArgs,
    ExtractDigestArgs,
    IngestTextArgs,
    WarrantTag,
)

DOMAIN_PACK_ID = "urm_domain_digest"
DOMAIN_PACK_VERSION = "0.0.0"
DEFAULT_TEMPLATE_ID = "digest.pipeline.v0"
SUPPORTED_TOOL_NAMES: frozenset[str] = frozenset(
    {
        "digest.ingest_text",
        "digest.extract_digest_candidate",
        "digest.check_constraints",
        "digest.emit_artifact",
    }
)

_TEMPLATES: tuple[DigestTemplateMeta, ...] = (
    DigestTemplateMeta(
        template_id=DEFAULT_TEMPLATE_ID,
        template_version="v0",
        schema_version="digest.workflow.v0",
        domain_pack_id=DOMAIN_PACK_ID,
        domain_pack_version=DOMAIN_PACK_VERSION,
        role="pipeline_worker",
        description="Closed-world digest processing over provided local text.",
    ),
)


@dataclass
class DigestDomainTools:
    domain_pack_id: str = DOMAIN_PACK_ID
    domain_pack_version: str = DOMAIN_PACK_VERSION

    def supports_tool(self, *, tool_name: str) -> bool:
        return tool_name in SUPPORTED_TOOL_NAMES

    def list_tools(self) -> list[str]:
        return sorted(SUPPORTED_TOOL_NAMES)

    def list_templates(self) -> list[DigestTemplateMeta]:
        return sorted(_TEMPLATES, key=lambda item: item.template_id)

    def call_tool(self, *, tool_name: str, arguments: dict[str, Any]) -> tuple[Any, WarrantTag]:
        if not self.supports_tool(tool_name=tool_name):
            raise URMError(
                code="URM_POLICY_DENIED",
                message="unsupported tool name",
                context={"tool_name": tool_name},
            )
        if tool_name == "digest.ingest_text":
            return self._ingest_text(arguments), "observed"
        if tool_name == "digest.extract_digest_candidate":
            return self._extract_digest_candidate(arguments), "derived"
        if tool_name == "digest.check_constraints":
            return self._check_constraints(arguments), "checked"
        if tool_name == "digest.emit_artifact":
            return self._emit_artifact(arguments), "checked"
        raise AssertionError("unreachable: tool name validated via supports_tool")

    def _ingest_text(self, arguments: dict[str, Any]) -> dict[str, Any]:
        args = IngestTextArgs.model_validate(arguments)
        normalized = _normalize_whitespace(args.source_text)
        return {
            "title": args.title or "Untitled",
            "source_text": normalized,
            "input_hash": sha256_text(normalized),
            "word_count": _word_count(normalized),
        }

    def _extract_digest_candidate(self, arguments: dict[str, Any]) -> dict[str, Any]:
        args = ExtractDigestArgs.model_validate(arguments)
        normalized = _normalize_whitespace(args.source_text)
        sentences = _split_sentences(normalized)
        selected = sentences[: args.max_sentences]
        digest_text = _truncate_words(" ".join(selected), max_words=args.max_words)
        digest_text = _normalize_whitespace(digest_text)
        return {
            "digest_text": digest_text,
            "sentence_count": _sentence_count(digest_text),
            "word_count": _word_count(digest_text),
            "candidate_hash": sha256_text(digest_text),
            "input_hash": sha256_text(normalized),
        }

    def _check_constraints(self, arguments: dict[str, Any]) -> dict[str, Any]:
        args = CheckConstraintsArgs.model_validate(arguments)
        digest_text = _normalize_whitespace(args.digest_text)
        word_count = _word_count(digest_text)
        sentence_count = _sentence_count(digest_text)
        checks = {
            "min_words": word_count >= args.min_words,
            "max_words": word_count <= args.max_words,
            "max_sentences": sentence_count <= args.max_sentences,
        }
        return {
            "word_count": word_count,
            "sentence_count": sentence_count,
            "min_words": args.min_words,
            "max_words": args.max_words,
            "max_sentences": args.max_sentences,
            "checks": checks,
            "passes": all(checks.values()),
        }

    def _emit_artifact(self, arguments: dict[str, Any]) -> dict[str, Any]:
        args = EmitArtifactArgs.model_validate(arguments)
        digest_text = _normalize_whitespace(args.digest_text)
        checks = dict(sorted(args.checks.items()))
        evidence_refs = sorted(
            (
                {
                    "kind": item.kind,
                    "ref": item.ref,
                    "note": item.note,
                }
                for item in args.evidence_refs
            ),
            key=lambda item: (item["kind"], item["ref"], item["note"] or ""),
        )
        payload = {
            "schema_version": "digest.artifact.v1",
            "domain": "doc.digest",
            "title": args.title or "Untitled",
            "input_hash": args.input_hash,
            "policy_hash": args.policy_hash,
            "domain_pack_id": self.domain_pack_id,
            "domain_pack_version": self.domain_pack_version,
            "digest_text": digest_text,
            "checks": checks,
            "evidence_refs": evidence_refs,
        }
        return {
            "artifact_id": sha256_text(canonical_json(payload)),
            "status": "ok",
            "artifact": payload,
        }


def _normalize_whitespace(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _split_sentences(text: str) -> list[str]:
    if not text:
        return []
    chunks = [chunk.strip() for chunk in re.split(r"(?<=[.!?])\s+", text) if chunk.strip()]
    if chunks:
        return chunks
    return [text.strip()]


def _truncate_words(text: str, *, max_words: int) -> str:
    words = text.split()
    if len(words) <= max_words:
        return text
    return " ".join(words[:max_words])


def _word_count(text: str) -> int:
    if not text:
        return 0
    return len(text.split())


def _sentence_count(text: str) -> int:
    if not text:
        return 0
    return len(_split_sentences(text))
