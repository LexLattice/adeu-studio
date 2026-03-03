from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import yaml
from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json
from yaml.tokens import AliasToken, AnchorToken, TagToken

SEMANTIC_SOURCE_COLLECTION_SCHEMA = "semantic_source_collection@0.1"
SEMANTIC_SOURCE_DIAGNOSTICS_SCHEMA = "semantic_source_diagnostics@0.1"

_DEFAULT_DOCS_ROOT = "docs"
_DEFAULT_OUTPUT_BASE_DIR = "artifacts/semantic_compiler/v39"
_DEFAULT_NORMALIZED_OUTPUT = f"{_DEFAULT_OUTPUT_BASE_DIR}/semantic_source.normalized.json"
_DEFAULT_DIAGNOSTICS_OUTPUT = f"{_DEFAULT_OUTPUT_BASE_DIR}/semantic_source.diagnostics.json"

_EXPORT_CALL_PATTERN = "python -m adeu_semantic_source.compile"

_SEMANTIC_FENCE_LABEL_RE = re.compile(r"^adeu(\..+)?$")
_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")

_FRONTMATTER_SEMANTIC_PREFIXES = ("adeu_", "asc_")
_KNOWN_FRONTMATTER_SEMANTIC_KEYS = frozenset(
    {
        "adeu_module_id",
        "adeu_module_kind",
        "adeu_arc_id",
        "adeu_slice_id",
        "adeu_stop_gate_id",
        "adeu_title",
        "adeu_status",
        "adeu_depends_on",
        "asc_module_id",
        "asc_module_kind",
        "asc_arc_id",
        "asc_slice_id",
        "asc_stop_gate_id",
        "asc_title",
        "asc_status",
        "asc_depends_on",
    }
)

_IDENTIFIER_KEYS = (
    "module_id",
    "id",
    "lock_id",
    "assertion_id",
    "evidence_id",
    "arc_id",
    "slice_id",
    "stop_gate_id",
)

SSC0001_INPUT_INTERFACE_INVALID = "SSC0001"
SSC0002_DUPLICATE_INPUT = "SSC0002"
SSC0003_INPUT_OUTSIDE_DOCS_ROOT = "SSC0003"
SSC0004_MANIFEST_ENTRY_ABSOLUTE_PATH = "SSC0004"
SSC0005_INPUT_PATH_INVALID = "SSC0005"
SSC0006_FRONTMATTER_INVALID = "SSC0006"
SSC0007_FRONTMATTER_YAML_FEATURE_FORBIDDEN = "SSC0007"
SSC0008_FRONTMATTER_YAML_SHAPE_INVALID = "SSC0008"
SSC0009_FRONTMATTER_SEMANTIC_KEY_UNKNOWN = "SSC0009"
SSC0010_SEMANTIC_FENCE_STYLE_INVALID = "SSC0010"
SSC0011_SEMANTIC_FENCE_LABEL_INVALID = "SSC0011"
SSC0012_SEMANTIC_BLOCK_PAYLOAD_INVALID = "SSC0012"
SSC0013_DUPLICATE_IDENTIFIER = "SSC0013"
SSC0014_OUTPUT_PATH_POLICY_VIOLATION = "SSC0014"
SSC0015_SEMANTIC_DECLARATION_AMBIGUOUS = "SSC0015"


@dataclass(frozen=True)
class ClaimSite:
    path: str
    start_line: int

    def to_payload(self) -> dict[str, Any]:
        return {
            "path": self.path,
            "start_line": self.start_line,
        }


@dataclass(frozen=True)
class Diagnostic:
    code: str
    message: str
    path: str | None = None
    start_line: int = 1
    start_column: int = 1
    claim_sites: tuple[ClaimSite, ...] = ()

    def to_payload(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "code": self.code,
            "severity": "ERROR",
            "message": self.message,
            "start_line": self.start_line,
            "start_column": self.start_column,
        }
        if self.path is not None:
            payload["path"] = self.path
        if self.claim_sites:
            payload["claim_sites"] = [claim.to_payload() for claim in self.claim_sites]
        return payload


@dataclass(frozen=True)
class ParsedSemanticBlock:
    label: str
    payload: dict[str, Any]
    start_line: int
    end_line: int
    identifier: str | None


@dataclass(frozen=True)
class ParsedSemanticFile:
    path: str
    frontmatter_semantic: dict[str, Any]
    blocks: list[ParsedSemanticBlock]


@dataclass(frozen=True)
class CompileResult:
    success: bool
    normalized_payload: dict[str, Any] | None
    diagnostics_payload: dict[str, Any]
    normalized_output_path: Path
    diagnostics_output_path: Path


def _is_absolute_like(path_text: str) -> bool:
    return (
        path_text.startswith("/")
        or path_text.startswith("\\")
        or _WINDOWS_ABSOLUTE_PATH_RE.match(path_text) is not None
    )


def _normalize_relative_path(raw_path: str) -> str:
    value = raw_path.strip().replace("\\", "/")
    if not value:
        raise ValueError("path must not be empty")
    if _is_absolute_like(value):
        raise ValueError("absolute paths are not allowed")

    segments: list[str] = []
    for segment in value.split("/"):
        if segment in ("", "."):
            continue
        if segment == "..":
            if not segments:
                raise ValueError("path escapes repository root")
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise ValueError("path resolves to repository root")
    return "/".join(segments)


def _join_relative_paths(base: str, entry: str) -> str:
    if not base:
        return _normalize_relative_path(entry)
    return _normalize_relative_path(f"{base}/{entry}")


def _is_within_root(path: str, root: str) -> bool:
    return path == root or path.startswith(f"{root}/")


def _sort_diagnostics(diagnostics: Iterable[Diagnostic]) -> list[Diagnostic]:
    return sorted(
        diagnostics,
        key=lambda item: (
            item.path or "",
            item.start_line,
            item.code,
            item.message,
        ),
    )


def _canonical_clone(value: Any) -> Any:
    return json.loads(canonical_json(value))


def _normalize_content(text: str) -> str:
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    lines = normalized.split("\n")
    return "\n".join(line.rstrip(" \t") for line in lines)


def _scan_forbidden_yaml_features(text: str) -> None:
    tokens = yaml.scan(text)
    for token in tokens:
        if isinstance(token, (AnchorToken, AliasToken, TagToken)):
            raise ValueError("anchors, aliases, and tags are forbidden")


def _parse_yaml_mapping(text: str) -> dict[str, Any]:
    _scan_forbidden_yaml_features(text)
    payload = yaml.safe_load(text)
    if payload is None:
        return {}
    if not isinstance(payload, dict):
        raise ValueError("yaml payload must be a mapping")

    normalized: dict[str, Any] = {}
    for key, value in payload.items():
        if not isinstance(key, str):
            raise ValueError("yaml mapping keys must be strings")
        normalized[key] = value
    return _canonical_clone(normalized)


def _extract_frontmatter(
    *,
    path: str,
    lines: list[str],
) -> tuple[dict[str, Any], int, list[Diagnostic]]:
    diagnostics: list[Diagnostic] = []
    if not lines or lines[0] != "---":
        return {}, 0, diagnostics

    closing_line = -1
    for index in range(1, len(lines)):
        if lines[index] == "---":
            closing_line = index
            break

    if closing_line == -1:
        diagnostics.append(
            Diagnostic(
                code=SSC0006_FRONTMATTER_INVALID,
                message="frontmatter start marker found without closing marker",
                path=path,
                start_line=1,
            )
        )
        return {}, 0, diagnostics

    frontmatter_text = "\n".join(lines[1:closing_line])
    try:
        payload = _parse_yaml_mapping(frontmatter_text)
    except ValueError as exc:
        code = SSC0006_FRONTMATTER_INVALID
        if "anchors, aliases, and tags" in str(exc):
            code = SSC0007_FRONTMATTER_YAML_FEATURE_FORBIDDEN
        elif "mapping" in str(exc):
            code = SSC0008_FRONTMATTER_YAML_SHAPE_INVALID
        diagnostics.append(
            Diagnostic(
                code=code,
                message=f"invalid frontmatter: {exc}",
                path=path,
                start_line=1,
            )
        )
        return {}, closing_line + 1, diagnostics

    semantic_frontmatter: dict[str, Any] = {}
    for key in sorted(payload):
        if not key.startswith(_FRONTMATTER_SEMANTIC_PREFIXES):
            continue
        if key not in _KNOWN_FRONTMATTER_SEMANTIC_KEYS:
            diagnostics.append(
                Diagnostic(
                    code=SSC0009_FRONTMATTER_SEMANTIC_KEY_UNKNOWN,
                    message=f"unknown semantic frontmatter key: {key!r}",
                    path=path,
                    start_line=1,
                )
            )
            continue
        semantic_frontmatter[key] = payload[key]

    return _canonical_clone(semantic_frontmatter), closing_line + 1, diagnostics


def _extract_identifier(
    *,
    payload: dict[str, Any],
    path: str,
    start_line: int,
) -> tuple[str | None, Diagnostic | None]:
    present_keys = [key for key in _IDENTIFIER_KEYS if key in payload]
    if not present_keys:
        return None, None

    if len(present_keys) > 1:
        return None, Diagnostic(
            code=SSC0015_SEMANTIC_DECLARATION_AMBIGUOUS,
            message=(
                "ambiguous semantic declaration: multiple identifier keys present "
                f"({', '.join(present_keys)})"
            ),
            path=path,
            start_line=start_line,
        )

    key = present_keys[0]
    raw_value = payload[key]
    if not isinstance(raw_value, str) or not raw_value.strip():
        return None, Diagnostic(
            code=SSC0015_SEMANTIC_DECLARATION_AMBIGUOUS,
            message=f"identifier field {key!r} must be a non-empty string",
            path=path,
            start_line=start_line,
        )

    return raw_value.strip(), None


def _parse_semantic_blocks(
    *,
    path: str,
    lines: list[str],
    start_index: int,
) -> tuple[list[ParsedSemanticBlock], list[Diagnostic]]:
    diagnostics: list[Diagnostic] = []
    blocks: list[ParsedSemanticBlock] = []

    in_fence = False
    fence_style = ""
    fence_label = ""
    fence_semantic = False
    fence_start_line = 0
    fence_lines: list[str] = []

    for line_number, line in enumerate(lines, start=1):
        if line_number <= start_index:
            continue

        if in_fence:
            if line == fence_style:
                if fence_semantic:
                    payload_text = "\n".join(fence_lines)
                    try:
                        payload = _parse_yaml_mapping(payload_text)
                    except ValueError as exc:
                        diagnostics.append(
                            Diagnostic(
                                code=SSC0012_SEMANTIC_BLOCK_PAYLOAD_INVALID,
                                message=f"invalid semantic block payload: {exc}",
                                path=path,
                                start_line=fence_start_line,
                            )
                        )
                    else:
                        identifier, identifier_diag = _extract_identifier(
                            payload=payload,
                            path=path,
                            start_line=fence_start_line,
                        )
                        if identifier_diag is not None:
                            diagnostics.append(identifier_diag)
                        blocks.append(
                            ParsedSemanticBlock(
                                label=fence_label,
                                payload=payload,
                                start_line=fence_start_line,
                                end_line=line_number,
                                identifier=identifier,
                            )
                        )
                in_fence = False
                fence_style = ""
                fence_label = ""
                fence_semantic = False
                fence_start_line = 0
                fence_lines = []
                continue

            fence_lines.append(line)
            continue

        indented = line.startswith(" ") or line.startswith("\t")
        if indented:
            stripped = line.lstrip(" \t")
            if stripped.startswith("```") or stripped.startswith("~~~"):
                label = stripped[3:].strip()
                if label.startswith("adeu"):
                    diagnostics.append(
                        Diagnostic(
                            code=SSC0010_SEMANTIC_FENCE_STYLE_INVALID,
                            message="semantic fences must not be indented",
                            path=path,
                            start_line=line_number,
                        )
                    )
            continue

        if line.startswith("~~~"):
            label = line[3:].strip()
            if label.startswith("adeu"):
                diagnostics.append(
                    Diagnostic(
                        code=SSC0010_SEMANTIC_FENCE_STYLE_INVALID,
                        message="semantic fences must use triple backticks, not tildes",
                        path=path,
                        start_line=line_number,
                    )
                )
            in_fence = True
            fence_style = "~~~"
            fence_label = ""
            fence_semantic = False
            fence_start_line = line_number
            fence_lines = []
            continue

        if line.startswith("```"):
            if len(line) > 3 and line[3] == "`":
                diagnostics.append(
                    Diagnostic(
                        code=SSC0010_SEMANTIC_FENCE_STYLE_INVALID,
                        message="semantic fences must use exactly triple backticks",
                        path=path,
                        start_line=line_number,
                    )
                )
                continue

            label = line[3:].strip()
            semantic_candidate = label.startswith("adeu")
            label_valid = _SEMANTIC_FENCE_LABEL_RE.fullmatch(label) is not None
            if semantic_candidate and not label_valid:
                diagnostics.append(
                    Diagnostic(
                        code=SSC0011_SEMANTIC_FENCE_LABEL_INVALID,
                        message=f"invalid semantic fence label: {label!r}",
                        path=path,
                        start_line=line_number,
                    )
                )

            in_fence = True
            fence_style = "```"
            fence_label = label
            fence_semantic = semantic_candidate and label_valid
            fence_start_line = line_number
            fence_lines = []

    if in_fence and fence_semantic:
        diagnostics.append(
            Diagnostic(
                code=SSC0012_SEMANTIC_BLOCK_PAYLOAD_INVALID,
                message="semantic block is missing closing triple-backtick fence",
                path=path,
                start_line=fence_start_line,
            )
        )

    return blocks, diagnostics


def _build_file_semantic_hash(
    frontmatter_semantic: dict[str, Any],
    blocks: list[ParsedSemanticBlock],
) -> str:
    basis = {
        "frontmatter_semantic": frontmatter_semantic,
        "blocks": [
            {
                "label": block.label,
                "payload": block.payload,
                "identifier": block.identifier,
            }
            for block in blocks
        ],
    }
    return sha256_canonical_json(basis)


def _build_normalized_payload(
    *,
    docs_root: str,
    input_paths: list[str],
    parsed_files: list[ParsedSemanticFile],
) -> dict[str, Any]:
    files_payload: list[dict[str, Any]] = []
    for parsed in parsed_files:
        semantic_hash = _build_file_semantic_hash(parsed.frontmatter_semantic, parsed.blocks)
        files_payload.append(
            {
                "path": parsed.path,
                "frontmatter_semantic": parsed.frontmatter_semantic,
                "blocks": [
                    {
                        "label": block.label,
                        "payload": block.payload,
                        "identifier": block.identifier,
                    }
                    for block in parsed.blocks
                ],
                "semantic_hash": semantic_hash,
            }
        )

    hash_basis = {
        "schema": SEMANTIC_SOURCE_COLLECTION_SCHEMA,
        "files": [
            {
                "path": item["path"],
                "semantic_hash": item["semantic_hash"],
            }
            for item in files_payload
        ],
    }

    return {
        "schema": SEMANTIC_SOURCE_COLLECTION_SCHEMA,
        "compiler": {
            "name": "adeu_semantic_source",
            "version": "0.0.0",
            "export_call_pattern": _EXPORT_CALL_PATTERN,
        },
        "source_docs_root": docs_root,
        "input_interface": {
            "mode": "cli_explicit_paths",
            "inputs": input_paths,
        },
        "files": files_payload,
        "semantic_source_hash": sha256_canonical_json(hash_basis),
    }


def _build_diagnostics_payload(*, diagnostics: list[Diagnostic]) -> dict[str, Any]:
    return {
        "schema": SEMANTIC_SOURCE_DIAGNOSTICS_SCHEMA,
        "diagnostics": [diagnostic.to_payload() for diagnostic in diagnostics],
    }


def _serialize_payload(payload: dict[str, Any]) -> bytes:
    return (canonical_json(payload) + "\n").encode("utf-8")


def _validate_output_paths(*, root: Path) -> tuple[Path, Path]:
    normalized_rel = _normalize_relative_path(_DEFAULT_NORMALIZED_OUTPUT)
    diagnostics_rel = _normalize_relative_path(_DEFAULT_DIAGNOSTICS_OUTPUT)
    base_rel = _normalize_relative_path(_DEFAULT_OUTPUT_BASE_DIR)

    if not _is_within_root(normalized_rel, base_rel):
        raise ValueError("normalized output path violates base_dir policy")
    if not _is_within_root(diagnostics_rel, base_rel):
        raise ValueError("diagnostics output path violates base_dir policy")

    return root / normalized_rel, root / diagnostics_rel


def _read_manifest_entries(
    *,
    root: Path,
    manifest_path: str,
    diagnostics: list[Diagnostic],
) -> list[str]:
    entries: list[str] = []

    try:
        manifest_rel = _normalize_relative_path(manifest_path)
    except ValueError as exc:
        diagnostics.append(
            Diagnostic(
                code=SSC0005_INPUT_PATH_INVALID,
                message=f"invalid --inputs_manifest path: {exc}",
            )
        )
        return entries

    manifest_abs = root / manifest_rel
    if not manifest_abs.is_file():
        diagnostics.append(
            Diagnostic(
                code=SSC0005_INPUT_PATH_INVALID,
                message=f"manifest file does not exist: {manifest_rel}",
            )
        )
        return entries

    manifest_dir = manifest_rel.rsplit("/", 1)[0] if "/" in manifest_rel else ""

    for index, line in enumerate(manifest_abs.read_text(encoding="utf-8").splitlines(), start=1):
        entry = line.strip()
        if not entry:
            continue

        if _is_absolute_like(entry):
            diagnostics.append(
                Diagnostic(
                    code=SSC0004_MANIFEST_ENTRY_ABSOLUTE_PATH,
                    message=f"manifest entry must be relative: {entry!r}",
                    path=manifest_rel,
                    start_line=index,
                )
            )
            continue

        try:
            resolved = _join_relative_paths(manifest_dir, entry)
        except ValueError as exc:
            diagnostics.append(
                Diagnostic(
                    code=SSC0005_INPUT_PATH_INVALID,
                    message=f"invalid manifest entry {entry!r}: {exc}",
                    path=manifest_rel,
                    start_line=index,
                )
            )
            continue

        entries.append(resolved)

    return entries


def compile_semantic_source(
    *,
    inputs: list[str],
    inputs_manifest: str | None = None,
    repo_root_path: Path | None = None,
    docs_root: str = _DEFAULT_DOCS_ROOT,
    write_outputs: bool = True,
) -> CompileResult:
    root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path

    diagnostics: list[Diagnostic] = []

    try:
        docs_root_rel = _normalize_relative_path(docs_root)
    except ValueError as exc:
        diagnostics.append(
            Diagnostic(
                code=SSC0005_INPUT_PATH_INVALID,
                message=f"invalid docs root: {exc}",
            )
        )
        docs_root_rel = _DEFAULT_DOCS_ROOT

    collected_paths: list[str] = []
    for input_path in inputs:
        try:
            normalized = _normalize_relative_path(input_path)
        except ValueError as exc:
            diagnostics.append(
                Diagnostic(
                    code=SSC0005_INPUT_PATH_INVALID,
                    message=f"invalid --input path {input_path!r}: {exc}",
                )
            )
            continue
        collected_paths.append(normalized)

    if inputs_manifest is not None:
        collected_paths.extend(
            _read_manifest_entries(
                root=root,
                manifest_path=inputs_manifest,
                diagnostics=diagnostics,
            )
        )

    if not collected_paths and not diagnostics:
        diagnostics.append(
            Diagnostic(
                code=SSC0001_INPUT_INTERFACE_INVALID,
                message="at least one --input or --inputs_manifest entry is required",
            )
        )

    seen_paths: set[str] = set()
    deduped_paths: list[str] = []
    for normalized in collected_paths:
        if normalized in seen_paths:
            diagnostics.append(
                Diagnostic(
                    code=SSC0002_DUPLICATE_INPUT,
                    message=f"duplicate input path: {normalized}",
                    path=normalized,
                    start_line=1,
                )
            )
            continue
        seen_paths.add(normalized)
        deduped_paths.append(normalized)

    in_scope_paths: list[str] = []
    for normalized in deduped_paths:
        if not _is_within_root(normalized, docs_root_rel):
            diagnostics.append(
                Diagnostic(
                    code=SSC0003_INPUT_OUTSIDE_DOCS_ROOT,
                    message=(
                        f"input path must stay under docs root {docs_root_rel!r}: "
                        f"{normalized!r}"
                    ),
                    path=normalized,
                    start_line=1,
                )
            )
            continue
        in_scope_paths.append(normalized)

    parsed_files: list[ParsedSemanticFile] = []
    identifier_claims: dict[str, list[ClaimSite]] = {}

    for path_text in in_scope_paths:
        absolute_path = root / path_text
        if not absolute_path.is_file():
            diagnostics.append(
                Diagnostic(
                    code=SSC0005_INPUT_PATH_INVALID,
                    message=f"input file does not exist: {path_text}",
                    path=path_text,
                    start_line=1,
                )
            )
            continue

        raw_content = absolute_path.read_text(encoding="utf-8")
        normalized_content = _normalize_content(raw_content)
        lines = normalized_content.split("\n")

        frontmatter_semantic, body_start_index, frontmatter_diags = _extract_frontmatter(
            path=path_text,
            lines=lines,
        )
        diagnostics.extend(frontmatter_diags)

        blocks, block_diags = _parse_semantic_blocks(
            path=path_text,
            lines=lines,
            start_index=body_start_index,
        )
        diagnostics.extend(block_diags)

        parsed = ParsedSemanticFile(
            path=path_text,
            frontmatter_semantic=frontmatter_semantic,
            blocks=blocks,
        )
        parsed_files.append(parsed)

        for block in blocks:
            if block.identifier is None:
                continue
            identifier_claims.setdefault(block.identifier, []).append(
                ClaimSite(path=path_text, start_line=block.start_line)
            )

    for identifier, claims in sorted(identifier_claims.items()):
        if len(claims) <= 1:
            continue
        ordered_claims = tuple(sorted(claims, key=lambda claim: (claim.path, claim.start_line)))
        diagnostics.append(
            Diagnostic(
                code=SSC0013_DUPLICATE_IDENTIFIER,
                message=f"duplicate semantic identifier: {identifier}",
                path=ordered_claims[0].path,
                start_line=ordered_claims[0].start_line,
                claim_sites=ordered_claims,
            )
        )

    diagnostics = _sort_diagnostics(diagnostics)

    try:
        normalized_output_path, diagnostics_output_path = _validate_output_paths(root=root)
    except ValueError as exc:
        diagnostics.append(
            Diagnostic(
                code=SSC0014_OUTPUT_PATH_POLICY_VIOLATION,
                message=str(exc),
            )
        )
        diagnostics = _sort_diagnostics(diagnostics)
        fallback = root / _DEFAULT_OUTPUT_BASE_DIR
        normalized_output_path = fallback / "semantic_source.normalized.json"
        diagnostics_output_path = fallback / "semantic_source.diagnostics.json"

    diagnostics_payload = _build_diagnostics_payload(diagnostics=diagnostics)
    normalized_payload: dict[str, Any] | None = None
    success = len(diagnostics) == 0

    if success:
        normalized_payload = _build_normalized_payload(
            docs_root=docs_root_rel,
            input_paths=in_scope_paths,
            parsed_files=parsed_files,
        )

    if write_outputs:
        diagnostics_output_path.parent.mkdir(parents=True, exist_ok=True)
        diagnostics_output_path.write_bytes(_serialize_payload(diagnostics_payload))
        if normalized_payload is not None:
            normalized_output_path.parent.mkdir(parents=True, exist_ok=True)
            normalized_output_path.write_bytes(_serialize_payload(normalized_payload))

    return CompileResult(
        success=success,
        normalized_payload=normalized_payload,
        diagnostics_payload=diagnostics_payload,
        normalized_output_path=normalized_output_path,
        diagnostics_output_path=diagnostics_output_path,
    )


def assert_artifacts_clean(
    *,
    inputs: list[str],
    inputs_manifest: str | None = None,
    repo_root_path: Path | None = None,
    docs_root: str = _DEFAULT_DOCS_ROOT,
) -> None:
    result = compile_semantic_source(
        inputs=inputs,
        inputs_manifest=inputs_manifest,
        repo_root_path=repo_root_path,
        docs_root=docs_root,
        write_outputs=False,
    )
    if not result.success or result.normalized_payload is None:
        raise RuntimeError(canonical_json(result.diagnostics_payload))

    expected_normalized = _serialize_payload(result.normalized_payload)
    expected_diagnostics = _serialize_payload(result.diagnostics_payload)

    if not result.normalized_output_path.is_file():
        raise RuntimeError(
            f"missing generated normalized artifact: {result.normalized_output_path.as_posix()}"
        )
    if not result.diagnostics_output_path.is_file():
        raise RuntimeError(
            f"missing generated diagnostics artifact: {result.diagnostics_output_path.as_posix()}"
        )

    observed_normalized = result.normalized_output_path.read_bytes()
    observed_diagnostics = result.diagnostics_output_path.read_bytes()

    if observed_normalized != expected_normalized:
        raise RuntimeError(
            "generated semantic-source normalized artifact is out of date: "
            f"{result.normalized_output_path.as_posix()}"
        )
    if observed_diagnostics != expected_diagnostics:
        raise RuntimeError(
            "generated semantic-source diagnostics artifact is out of date: "
            f"{result.diagnostics_output_path.as_posix()}"
        )


def _build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="adeu_semantic_source.compile",
        description="Compile deterministic semantic-source artifacts for v39.",
    )
    parser.add_argument(
        "--input",
        action="append",
        default=[],
        help="Explicit repository-relative input path under docs/. May be passed multiple times.",
    )
    parser.add_argument(
        "--inputs_manifest",
        help=(
            "Repository-relative path to newline-delimited input paths "
            "(resolved relative to manifest)."
        ),
    )
    parser.add_argument(
        "--docs-root",
        default=_DEFAULT_DOCS_ROOT,
        help="Repository-relative docs root boundary (default: docs).",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_arg_parser()
    args = parser.parse_args(argv)

    result = compile_semantic_source(
        inputs=args.input,
        inputs_manifest=args.inputs_manifest,
        docs_root=args.docs_root,
        write_outputs=True,
    )

    if result.success:
        return 0

    sys.stderr.write(canonical_json(result.diagnostics_payload) + "\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
