from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from adeu_paper_semantics import (
    ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA,
    ADEU_PAPER_SEMANTIC_WORKER_REQUEST_SCHEMA,
    PaperSemanticArtifact,
)
from pydantic import ValidationError
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.errors import URMError
from urm_runtime.hashing import canonical_json, sha256_canonical_json, sha256_text
from urm_runtime.models import WorkerRunRequest
from urm_runtime.worker import CodexExecWorkerRunner

from .models import (
    ADEU_PAPER_SEMANTIC_WORKER_BRIDGE_RESULT_SCHEMA,
    SEMANTIC_DECOMPOSITION_TEMPLATE_ID,
    SEMANTIC_DECOMPOSITION_TOOL_NAME,
    CheckConstraintsArgs,
    EmitArtifactArgs,
    ExtractAbstractArgs,
    IngestTextArgs,
    PaperSemanticWorkerBridgeResult,
    PaperTemplateMeta,
    RunSemanticDecompositionArgs,
    WarrantTag,
    compute_bridge_result_id,
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
SEMANTIC_BRIDGE_TOOL_NAMES: frozenset[str] = frozenset({SEMANTIC_DECOMPOSITION_TOOL_NAME})

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
    PaperTemplateMeta(
        template_id=SEMANTIC_DECOMPOSITION_TEMPLATE_ID,
        template_version="v0",
        schema_version=ADEU_PAPER_SEMANTIC_WORKER_REQUEST_SCHEMA,
        domain_pack_id=DOMAIN_PACK_ID,
        domain_pack_version=DOMAIN_PACK_VERSION,
        role="pipeline_worker",
        description="Read-only paper semantic decomposition over a released V52-A worker request.",
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
    config: URMRuntimeConfig | None = None
    worker_runner: CodexExecWorkerRunner | None = None
    domain_pack_id: str = DOMAIN_PACK_ID
    domain_pack_version: str = DOMAIN_PACK_VERSION

    @classmethod
    def from_config(cls, *, config: URMRuntimeConfig | None = None) -> "PaperDomainTools":
        resolved = config or URMRuntimeConfig.from_env()
        return cls(config=resolved, worker_runner=CodexExecWorkerRunner(config=resolved))

    def _supported_tool_names(self) -> frozenset[str]:
        if self._semantic_bridge_available():
            return SUPPORTED_TOOL_NAMES | SEMANTIC_BRIDGE_TOOL_NAMES
        return SUPPORTED_TOOL_NAMES

    def _semantic_bridge_available(self) -> bool:
        return self.config is not None and self.worker_runner is not None

    def supports_tool(self, *, tool_name: str) -> bool:
        return tool_name in self._supported_tool_names()

    def list_tools(self) -> list[str]:
        return sorted(self._supported_tool_names())

    def list_templates(self) -> list[PaperTemplateMeta]:
        templates = _TEMPLATES if self._semantic_bridge_available() else (_TEMPLATES[0],)
        return sorted(templates, key=lambda item: item.template_id)

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
        if tool_name == SEMANTIC_DECOMPOSITION_TOOL_NAME:
            return self._run_semantic_decomposition(arguments).model_dump(
                mode="json", by_alias=True
            ), "checked"
        raise AssertionError("unreachable: tool name validated via supports_tool")

    def _ingest_text(self, arguments: dict[str, Any]) -> IngestTextArgs:
        args = IngestTextArgs.model_validate(arguments)
        return args

    def _extract_abstract_candidate(self, arguments: dict[str, Any]) -> dict[str, Any]:
        args = ExtractAbstractArgs.model_validate(arguments)
        paragraph, strategy = _select_abstract_candidate(args.source_text)
        words = _word_count(paragraph)
        sentence_count = _sentence_count(paragraph)
        candidate_date_like = _is_date_like(paragraph)
        return {
            "abstract_text": paragraph,
            "word_count": words,
            "sentence_count": sentence_count,
            "extract_strategy": strategy,
            "candidate_date_like": candidate_date_like,
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

    def _run_semantic_decomposition(
        self, arguments: dict[str, Any]
    ) -> PaperSemanticWorkerBridgeResult:
        request_ref, request_hash, return_schema = _extract_bridge_request_lineage(arguments)
        try:
            args = RunSemanticDecompositionArgs.model_validate(arguments)
        except ValidationError:
            return _build_bridge_result(
                bridge_status="fail_closed_invalid_request",
                request_ref=request_ref,
                request_hash=request_hash,
                return_schema=return_schema,
                domain_pack_id=self.domain_pack_id,
                domain_pack_version=self.domain_pack_version,
            )
        if not self._semantic_bridge_available():
            return _build_bridge_result(
                bridge_status="fail_closed_bridge_config_mismatch",
                request_ref=args.worker_request.request_id,
                request_hash=args.worker_request.request_hash,
                return_schema=args.worker_request.return_schema,
                domain_pack_id=self.domain_pack_id,
                domain_pack_version=self.domain_pack_version,
            )
        template = self._require_template(SEMANTIC_DECOMPOSITION_TEMPLATE_ID)
        request = WorkerRunRequest(
            provider="codex",
            role=template.role,
            client_request_id=f"paper-semantic-bridge:{args.worker_request.request_id}",
            prompt=_build_semantic_decomposition_prompt(args=args),
            template_id=template.template_id,
            template_version=template.template_version,
            schema_version=template.schema_version,
            domain_pack_id=template.domain_pack_id,
            domain_pack_version=template.domain_pack_version,
        )
        assert self.worker_runner is not None
        try:
            worker_result = self.worker_runner.run(request)
        except URMError:
            return _build_bridge_result(
                bridge_status="fail_closed_bridge_config_mismatch",
                request_ref=args.worker_request.request_id,
                request_hash=args.worker_request.request_hash,
                return_schema=args.worker_request.return_schema,
                domain_pack_id=self.domain_pack_id,
                domain_pack_version=self.domain_pack_version,
            )
        artifact_candidate = worker_result.artifact_candidate
        if worker_result.status != "ok" or artifact_candidate is None:
            return _build_bridge_result(
                bridge_status="fail_closed_bridge_config_mismatch",
                request_ref=args.worker_request.request_id,
                request_hash=args.worker_request.request_hash,
                return_schema=args.worker_request.return_schema,
                domain_pack_id=self.domain_pack_id,
                domain_pack_version=self.domain_pack_version,
                worker_id=worker_result.worker_id,
                evidence_id=worker_result.evidence_id,
                worker_status=worker_result.status,
                idempotent_replay=worker_result.idempotent_replay,
            )
        candidate_payload = artifact_candidate
        if isinstance(artifact_candidate, dict) and isinstance(
            artifact_candidate.get("artifact"), dict
        ):
            candidate_payload = artifact_candidate["artifact"]
        try:
            artifact = PaperSemanticArtifact.model_validate(candidate_payload)
        except ValidationError:
            return _build_bridge_result(
                bridge_status="fail_closed_bridge_config_mismatch",
                request_ref=args.worker_request.request_id,
                request_hash=args.worker_request.request_hash,
                return_schema=args.worker_request.return_schema,
                domain_pack_id=self.domain_pack_id,
                domain_pack_version=self.domain_pack_version,
                worker_id=worker_result.worker_id,
                evidence_id=worker_result.evidence_id,
                worker_status=worker_result.status,
                idempotent_replay=worker_result.idempotent_replay,
            )
        return _build_bridge_result(
            bridge_status=(
                "completed_checked_idempotent_replay"
                if worker_result.idempotent_replay
                else "completed_checked"
            ),
            request_ref=args.worker_request.request_id,
            request_hash=args.worker_request.request_hash,
            return_schema=args.worker_request.return_schema,
            domain_pack_id=self.domain_pack_id,
            domain_pack_version=self.domain_pack_version,
            artifact_ref=artifact.artifact_id,
            worker_id=worker_result.worker_id,
            evidence_id=worker_result.evidence_id,
            worker_status=worker_result.status,
            idempotent_replay=worker_result.idempotent_replay,
        )

    def _require_template(self, template_id: str) -> PaperTemplateMeta:
        for template in _TEMPLATES:
            if template.template_id == template_id:
                return template
        raise URMError(
            code="URM_POLICY_DENIED",
            message="unknown template_id",
            context={"template_id": template_id},
        )


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


def _extract_bridge_request_lineage(
    arguments: dict[str, Any],
) -> tuple[str | None, str | None, str]:
    worker_request = arguments.get("worker_request")
    if not isinstance(worker_request, dict):
        return (None, None, ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA)
    request_ref = worker_request.get("request_id")
    request_hash = worker_request.get("request_hash")
    return_schema = worker_request.get("return_schema")
    resolved_request_ref = request_ref if isinstance(request_ref, str) and request_ref else None
    resolved_request_hash = request_hash if isinstance(request_hash, str) and request_hash else None
    resolved_return_schema = (
        return_schema
        if return_schema == ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA
        else ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA
    )
    return (resolved_request_ref, resolved_request_hash, resolved_return_schema)


def _build_semantic_decomposition_prompt(*, args: RunSemanticDecompositionArgs) -> str:
    request_payload = canonical_json(args.worker_request.model_dump(mode="json", by_alias=True))
    return (
        "Return exactly one released adeu_paper_semantic_artifact@1 JSON object for the "
        "following released adeu_paper_semantic_worker_request@1. Preserve source-text and "
        "explicit span-anchor authority, keep interpretation advisory-only, and return JSON only."
        f"\n\nworker_request={request_payload}"
    )


def _build_bridge_result(
    *,
    bridge_status: str,
    request_ref: str | None,
    request_hash: str | None,
    return_schema: str,
    domain_pack_id: str,
    domain_pack_version: str,
    artifact_ref: str | None = None,
    worker_id: str | None = None,
    evidence_id: str | None = None,
    worker_status: str | None = None,
    idempotent_replay: bool = False,
) -> PaperSemanticWorkerBridgeResult:
    payload = {
        "schema": ADEU_PAPER_SEMANTIC_WORKER_BRIDGE_RESULT_SCHEMA,
        "bridge_status": bridge_status,
        "request_ref": request_ref,
        "request_hash": request_hash,
        "tool_name": SEMANTIC_DECOMPOSITION_TOOL_NAME,
        "template_id": SEMANTIC_DECOMPOSITION_TEMPLATE_ID,
        "template_version": "v0",
        "domain_pack_id": domain_pack_id,
        "domain_pack_version": domain_pack_version,
        "provider": "codex",
        "role": "pipeline_worker",
        "warrant_tag": "checked",
        "artifact_ref": artifact_ref,
        "worker_id": worker_id,
        "evidence_id": evidence_id,
        "worker_status": worker_status,
        "idempotent_replay": idempotent_replay,
        "return_schema": return_schema,
    }
    bridge_hash = sha256_canonical_json(payload)
    return PaperSemanticWorkerBridgeResult.model_validate(
        {
            **payload,
            "bridge_hash": bridge_hash,
            "bridge_result_id": compute_bridge_result_id(bridge_hash),
        }
    )
