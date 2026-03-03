from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterable

from adeu_commitments_ir import ADEU_COMMITMENTS_IR_SCHEMA
from adeu_commitments_ir.ids import stable_commitments_lock_id
from adeu_commitments_ir.models import canonicalize_commitments_ir_payload
from adeu_ir.repo import repo_root
from pydantic import ValidationError
from urm_runtime.hashing import canonical_json, sha256_canonical_json

SEMANTIC_SOURCE_COLLECTION_SCHEMA = "semantic_source_collection@0.1"
SEMANTIC_SOURCE_DIAGNOSTICS_SCHEMA = "semantic_source_diagnostics@0.1"
SEMANTIC_COMPILER_DIAGNOSTICS_SCHEMA = "semantic_compiler_diagnostics@0.1"
SEMANTIC_COMPILER_PASS_MANIFEST_SCHEMA = "semantic_compiler_pass_manifest@0.1"
SEMANTIC_COMPILER_SURFACE_SNAPSHOT_SCHEMA = "semantic_compiler_surface_snapshot@0.1"
SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA = "semantic_compiler_surface_diff@0.1"
SEMANTIC_COMPILER_EVIDENCE_MANIFEST_SCHEMA = "semantic_compiler_evidence_manifest@0.1"

_DEFAULT_INPUT_SEMANTIC_SOURCE = "artifacts/semantic_compiler/v39/semantic_source.normalized.json"
_DEFAULT_INPUT_SEMANTIC_DIAGNOSTICS = (
    "artifacts/semantic_compiler/v39/semantic_source.diagnostics.json"
)

_DEFAULT_OUTPUT_BASE_DIR = "artifacts/semantic_compiler/v40"
_DEFAULT_OUTPUT_IR = f"{_DEFAULT_OUTPUT_BASE_DIR}/commitments_ir.json"
_DEFAULT_OUTPUT_DIAGNOSTICS = f"{_DEFAULT_OUTPUT_BASE_DIR}/semantic_compiler.diagnostics.json"
_DEFAULT_OUTPUT_PASS_MANIFEST = f"{_DEFAULT_OUTPUT_BASE_DIR}/pass_manifest.json"
_DEFAULT_OUTPUT_V41_BASE_DIR = "artifacts/semantic_compiler/v41"
_DEFAULT_OUTPUT_SURFACE_SNAPSHOT = f"{_DEFAULT_OUTPUT_V41_BASE_DIR}/surface_snapshot.json"
_DEFAULT_OUTPUT_SURFACE_DIFF = f"{_DEFAULT_OUTPUT_V41_BASE_DIR}/surface_diff.json"
_DEFAULT_OUTPUT_EVIDENCE_MANIFEST = f"{_DEFAULT_OUTPUT_V41_BASE_DIR}/evidence_manifest.json"
_DEFAULT_OUTPUT_V41_DOCS_BASE_DIR = "docs/generated/semantic_compiler/v41"
_DEFAULT_OUTPUT_PR_SPLITS = f"{_DEFAULT_OUTPUT_V41_DOCS_BASE_DIR}/PR_SPLITS.md"
_DEFAULT_BASELINE_SURFACE_SNAPSHOT = "artifacts/semantic_compiler/v40/surface_snapshot.json"

_EXPORT_CALL_PATTERN = "python -m adeu_semantic_compiler.compile"

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")

_PASS_SEQUENCE: tuple[str, ...] = (
    "LoadCollection",
    "ValidateBlocks",
    "RevalidateNormalization",
    "BuildIR",
    "ResolveRefs",
    "TypecheckLocks",
)
_MUTATING_PASSES = frozenset({"BuildIR", "ResolveRefs"})

_ALLOWED_MODULE_KINDS = frozenset({"arc_lock", "slice_spec", "stop_gate"})
_ALLOWED_MODULE_STATUS = frozenset({"draft", "frozen", "superseded"})
_ALLOWED_EFFECT_TAGS = frozenset(
    {
        "schema_export",
        "contract_validation",
        "continuity_check",
        "artifact_generation",
        "diagnostics_emission",
    }
)
_ALLOWED_LOCK_KINDS = frozenset({"freeze", "required", "forbidden", "additive_only", "exact_set"})
_ALLOWED_LOCK_SEVERITIES = frozenset({"ERROR", "WARN"})
_ALLOWED_SURFACE_KINDS = frozenset({"schema", "manifest", "file", "markdown_json_block"})
_ALLOWED_ASSERTION_TYPES = frozenset(
    {"schema_contract", "continuity_guard", "surface_match", "determinism"}
)
_ALLOWED_EVIDENCE_TYPES = frozenset(
    {"test_report", "lint_output", "ci_run", "artifact_hash", "doc_json"}
)
_ALLOWED_TRUST_LANES = frozenset({"mapping", "solver", "proof", "tooling"})
_ALLOWED_EVIDENCE_QUALITY = frozenset({"low", "medium", "high"})

SCC0001_INPUT_SCHEMA_INVALID = "SCC0001"
SCC0002_INPUT_DIAGNOSTICS_FAIL_CLOSED = "SCC0002"
SCC0003_INPUT_DIAGNOSTICS_CARRIED = "SCC0003"
SCC0004_SEMANTIC_SOURCE_INVALID = "SCC0004"
SCC0005_BLOCK_LABEL_UNSUPPORTED = "SCC0005"
SCC0006_MODULE_KIND_INVALID = "SCC0006"
SCC0007_MODULE_ID_MISSING = "SCC0007"
SCC0008_MODULE_DECLARATION_INVALID = "SCC0008"
SCC0009_MODULE_ID_DUPLICATE = "SCC0009"
SCC0010_UNRESOLVED_REFERENCE = "SCC0010"
SCC0011_UNKNOWN_TOKEN = "SCC0011"
SCC0012_LOCK_TYPECHECK_INVALID = "SCC0012"
SCC0013_OUTPUT_PATH_POLICY_VIOLATION = "SCC0013"
SCC0014_PASS_HASH_IDENTITY_VIOLATION = "SCC0014"
SCC0015_INPUT_HANDOFF_INVALID = "SCC0015"
SCC0016_SURFACE_SELECTOR_INVALID = "SCC0016"
SCC0017_SURFACE_SIGNATURE_INVALID = "SCC0017"
SCC0018_DELTA_RULE_VIOLATION = "SCC0018"
SCC0019_EVIDENCE_MANIFEST_INVALID = "SCC0019"
SCC0020_PR_SPLIT_INVALID = "SCC0020"


@dataclass(frozen=True)
class CompilerDiagnostic:
    code: str
    severity: str
    message: str
    module_id: str = ""
    path: str | None = None
    start_line: int = 1
    start_column: int = 1
    details: dict[str, Any] | None = None

    def to_payload(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "code": self.code,
            "severity": self.severity,
            "message": self.message,
            "module_id": self.module_id,
            "start_line": self.start_line,
            "start_column": self.start_column,
        }
        if self.path is not None:
            payload["path"] = self.path
        if self.details is not None:
            payload["details"] = self.details
        return payload


@dataclass(frozen=True)
class PassEntry:
    name: str
    index: int
    input_sha256: str
    output_sha256: str

    def to_payload(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "index": self.index,
            "input_sha256": self.input_sha256,
            "output_sha256": self.output_sha256,
        }


@dataclass(frozen=True)
class CompileResult:
    success: bool
    commitments_ir_payload: dict[str, Any] | None
    diagnostics_payload: dict[str, Any]
    pass_manifest_payload: dict[str, Any]
    surface_snapshot_payload: dict[str, Any] | None
    surface_diff_payload: dict[str, Any] | None
    evidence_manifest_payload: dict[str, Any] | None
    pr_splits_markdown: str | None
    commitments_ir_output_path: Path
    diagnostics_output_path: Path
    pass_manifest_output_path: Path
    surface_snapshot_output_path: Path
    surface_diff_output_path: Path
    evidence_manifest_output_path: Path
    pr_splits_output_path: Path


def _canonical_clone(value: Any) -> Any:
    return json.loads(canonical_json(value))


def _json_safe(value: Any) -> Any:
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, dict):
        return {str(key): _json_safe(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_json_safe(item) for item in value]
    return repr(value)


def _serialize_payload(payload: dict[str, Any]) -> bytes:
    return (canonical_json(payload) + "\n").encode("utf-8")


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _normalize_utf8_nfc(text: str) -> str:
    try:
        encoded = text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"path is not utf-8 encodable: {exc}") from exc
    return unicodedata.normalize("NFC", encoded.decode("utf-8"))


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


def _is_within_root(path: str, root: str) -> bool:
    return path == root or path.startswith(f"{root}/")


def _sort_diagnostics(diagnostics: Iterable[CompilerDiagnostic]) -> list[CompilerDiagnostic]:
    return sorted(
        diagnostics,
        key=lambda item: (
            item.module_id,
            item.path or "",
            item.start_line,
            item.code,
            item.message,
        ),
    )


def _new_diag(
    *,
    code: str,
    severity: str,
    message: str,
    module_id: str = "",
    path: str | None = None,
    start_line: int = 1,
    start_column: int = 1,
    details: dict[str, Any] | None = None,
) -> CompilerDiagnostic:
    return CompilerDiagnostic(
        code=code,
        severity=severity,
        message=message,
        module_id=module_id,
        path=path,
        start_line=start_line,
        start_column=start_column,
        details=details,
    )


def _validate_output_paths(*, root: Path) -> tuple[Path, Path, Path]:
    base_rel = _normalize_relative_path(_DEFAULT_OUTPUT_BASE_DIR)
    ir_rel = _normalize_relative_path(_DEFAULT_OUTPUT_IR)
    diagnostics_rel = _normalize_relative_path(_DEFAULT_OUTPUT_DIAGNOSTICS)
    pass_manifest_rel = _normalize_relative_path(_DEFAULT_OUTPUT_PASS_MANIFEST)

    for candidate in (ir_rel, diagnostics_rel, pass_manifest_rel):
        if not _is_within_root(candidate, base_rel):
            raise ValueError(f"output path {candidate!r} violates base_dir policy {base_rel!r}")

    return root / ir_rel, root / diagnostics_rel, root / pass_manifest_rel


def _validate_v41_output_paths(*, root: Path) -> tuple[Path, Path, Path, Path]:
    artifacts_base_rel = _normalize_relative_path(_DEFAULT_OUTPUT_V41_BASE_DIR)
    docs_base_rel = _normalize_relative_path(_DEFAULT_OUTPUT_V41_DOCS_BASE_DIR)

    surface_snapshot_rel = _normalize_relative_path(_DEFAULT_OUTPUT_SURFACE_SNAPSHOT)
    surface_diff_rel = _normalize_relative_path(_DEFAULT_OUTPUT_SURFACE_DIFF)
    evidence_manifest_rel = _normalize_relative_path(_DEFAULT_OUTPUT_EVIDENCE_MANIFEST)
    pr_splits_rel = _normalize_relative_path(_DEFAULT_OUTPUT_PR_SPLITS)

    for artifact_rel in (surface_snapshot_rel, surface_diff_rel, evidence_manifest_rel):
        if not _is_within_root(artifact_rel, artifacts_base_rel):
            raise ValueError(
                f"output path {artifact_rel!r} violates artifacts_base policy {artifacts_base_rel!r}"
            )
    if not _is_within_root(pr_splits_rel, docs_base_rel):
        raise ValueError(f"output path {pr_splits_rel!r} violates docs_base policy {docs_base_rel!r}")

    return (
        root / surface_snapshot_rel,
        root / surface_diff_rel,
        root / evidence_manifest_rel,
        root / pr_splits_rel,
    )


def _build_diagnostics_payload(*, diagnostics: list[CompilerDiagnostic]) -> dict[str, Any]:
    return {
        "schema": SEMANTIC_COMPILER_DIAGNOSTICS_SCHEMA,
        "diagnostics": [item.to_payload() for item in diagnostics],
    }


def _build_pass_manifest_payload(*, entries: list[PassEntry]) -> dict[str, Any]:
    return {
        "schema": SEMANTIC_COMPILER_PASS_MANIFEST_SCHEMA,
        "pass_sequence": list(_PASS_SEQUENCE),
        "pass_manifest": [item.to_payload() for item in entries],
    }


def _read_json_object(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("json payload must be an object")
    return payload


def _load_json_artifact(
    *,
    root: Path,
    raw_path: str,
    diagnostics: list[CompilerDiagnostic],
    not_found_message: str,
) -> tuple[str | None, dict[str, Any] | None]:
    try:
        relative_path = _normalize_relative_path(raw_path)
    except ValueError as exc:
        diagnostics.append(
            _new_diag(
                code=SCC0001_INPUT_SCHEMA_INVALID,
                severity="ERROR",
                message=f"invalid artifact path {raw_path!r}: {exc}",
            )
        )
        return None, None

    absolute_path = root / relative_path
    if not absolute_path.is_file():
        diagnostics.append(
            _new_diag(
                code=SCC0001_INPUT_SCHEMA_INVALID,
                severity="ERROR",
                message=f"{not_found_message}: {relative_path}",
                path=relative_path,
            )
        )
        return relative_path, None

    try:
        payload = _read_json_object(absolute_path)
    except (ValueError, json.JSONDecodeError) as exc:
        diagnostics.append(
            _new_diag(
                code=SCC0001_INPUT_SCHEMA_INVALID,
                severity="ERROR",
                message=f"invalid json payload for {relative_path}: {exc}",
                path=relative_path,
            )
        )
        return relative_path, None

    return relative_path, payload


def _build_file_semantic_hash(
    frontmatter_semantic: dict[str, Any], blocks: list[dict[str, Any]]
) -> str:
    basis = {
        "frontmatter_semantic": frontmatter_semantic,
        "blocks": [
            {
                "label": block.get("label"),
                "payload": block.get("payload"),
                "identifier": block.get("identifier"),
            }
            for block in blocks
        ],
    }
    return sha256_canonical_json(basis)


def _normalize_string_list(value: Any) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, list):
        raise ValueError("expected list of strings")
    normalized = []
    for item in value:
        if not isinstance(item, str) or not item.strip():
            raise ValueError("list values must be non-empty strings")
        normalized.append(item.strip())
    return sorted(set(normalized))


def _module_kind_from_label(label: str) -> str | None:
    if label in ("adeu", "adeu.module"):
        return None
    if not label.startswith("adeu."):
        return None
    suffix = label.split(".", 1)[1]
    if suffix in _ALLOWED_MODULE_KINDS:
        return suffix
    return None


def _derive_arc_id(
    *, payload: dict[str, Any], frontmatter: dict[str, Any], module_id: str
) -> str | None:
    for key in ("arc_id", "adeu_arc_id", "asc_arc_id"):
        candidate = payload.get(key) if key in payload else frontmatter.get(key)
        if isinstance(candidate, str) and candidate.strip():
            return candidate.strip()
    parts = module_id.split(":")
    if len(parts) >= 2 and parts[1].strip():
        return parts[1].strip()
    return None


def _derive_slice_id(
    *, payload: dict[str, Any], frontmatter: dict[str, Any], module_id: str
) -> str | None:
    for key in ("slice_id", "adeu_slice_id", "asc_slice_id"):
        candidate = payload.get(key) if key in payload else frontmatter.get(key)
        if isinstance(candidate, str) and candidate.strip():
            return candidate.strip()
    parts = module_id.split(":")
    if len(parts) >= 3:
        suffix = ":".join(parts[2:]).strip()
        if suffix:
            return suffix
    return None


def _derive_stop_gate_id(*, payload: dict[str, Any], module_id: str) -> str | None:
    candidate = payload.get("stop_gate_id")
    if isinstance(candidate, str) and candidate.strip():
        return candidate.strip()
    parts = module_id.split(":")
    if len(parts) >= 2 and parts[1].strip():
        return parts[1].strip()
    return None


def _stringify_selector(value: Any) -> str:
    if isinstance(value, str):
        normalized = value.strip()
        if not normalized:
            raise ValueError("selector string must not be empty")
        return normalized
    if isinstance(value, (dict, list)):
        return canonical_json(value)
    raise ValueError("selector must be a string, object, or list")


def _stringify_target(value: Any) -> str:
    if isinstance(value, str):
        normalized = value.strip()
        if not normalized:
            raise ValueError("target string must not be empty")
        return normalized
    if isinstance(value, (dict, list)):
        return canonical_json(value)
    raise ValueError("target must be a string, object, or list")


def _derived_id(prefix: str, *parts: str) -> str:
    digest = sha256_canonical_json({"parts": list(parts)})[:16]
    return f"{prefix}_{digest}"


def _pass_load_collection(
    state: dict[str, Any], diagnostics: list[CompilerDiagnostic]
) -> dict[str, Any]:
    semantic_source = state.get("semantic_source")
    if not isinstance(semantic_source, dict):
        diagnostics.append(
            _new_diag(
                code=SCC0001_INPUT_SCHEMA_INVALID,
                severity="ERROR",
                message="semantic source payload must be a json object",
            )
        )
        return state

    if semantic_source.get("schema") != SEMANTIC_SOURCE_COLLECTION_SCHEMA:
        diagnostics.append(
            _new_diag(
                code=SCC0001_INPUT_SCHEMA_INVALID,
                severity="ERROR",
                message=(
                    f"semantic source payload schema must be {SEMANTIC_SOURCE_COLLECTION_SCHEMA!r}"
                ),
            )
        )
    return state


def _pass_validate_blocks(
    state: dict[str, Any], diagnostics: list[CompilerDiagnostic]
) -> dict[str, Any]:
    semantic_source = state.get("semantic_source")
    if not isinstance(semantic_source, dict):
        return state

    files = semantic_source.get("files")
    if not isinstance(files, list):
        diagnostics.append(
            _new_diag(
                code=SCC0004_SEMANTIC_SOURCE_INVALID,
                severity="ERROR",
                message="semantic source files must be a list",
            )
        )
        return state

    for file_item in files:
        if not isinstance(file_item, dict):
            diagnostics.append(
                _new_diag(
                    code=SCC0004_SEMANTIC_SOURCE_INVALID,
                    severity="ERROR",
                    message="semantic source file entry must be an object",
                )
            )
            continue

        path = file_item.get("path")
        if not isinstance(path, str) or not path:
            diagnostics.append(
                _new_diag(
                    code=SCC0004_SEMANTIC_SOURCE_INVALID,
                    severity="ERROR",
                    message="semantic source file path must be a non-empty string",
                )
            )
            continue

        blocks = file_item.get("blocks")
        if not isinstance(blocks, list):
            diagnostics.append(
                _new_diag(
                    code=SCC0004_SEMANTIC_SOURCE_INVALID,
                    severity="ERROR",
                    message="semantic source file blocks must be a list",
                    path=path,
                )
            )
            continue

        for block in blocks:
            if not isinstance(block, dict):
                diagnostics.append(
                    _new_diag(
                        code=SCC0004_SEMANTIC_SOURCE_INVALID,
                        severity="ERROR",
                        message="semantic block entry must be an object",
                        path=path,
                    )
                )
                continue

            label = block.get("label")
            if not isinstance(label, str) or not label.startswith("adeu"):
                diagnostics.append(
                    _new_diag(
                        code=SCC0005_BLOCK_LABEL_UNSUPPORTED,
                        severity="ERROR",
                        message="semantic block label must start with 'adeu'",
                        path=path,
                        start_line=int(block.get("start_line", 1))
                        if isinstance(block.get("start_line"), int)
                        else 1,
                    )
                )
                continue

            if _module_kind_from_label(label) is None and label not in ("adeu", "adeu.module"):
                diagnostics.append(
                    _new_diag(
                        code=SCC0005_BLOCK_LABEL_UNSUPPORTED,
                        severity="ERROR",
                        message=f"unsupported semantic block label for v40 core: {label!r}",
                        path=path,
                        start_line=int(block.get("start_line", 1))
                        if isinstance(block.get("start_line"), int)
                        else 1,
                    )
                )

            payload = block.get("payload")
            if not isinstance(payload, dict):
                diagnostics.append(
                    _new_diag(
                        code=SCC0004_SEMANTIC_SOURCE_INVALID,
                        severity="ERROR",
                        message="semantic block payload must be an object",
                        path=path,
                        start_line=int(block.get("start_line", 1))
                        if isinstance(block.get("start_line"), int)
                        else 1,
                    )
                )

    return state


def _pass_revalidate_normalization(
    state: dict[str, Any], diagnostics: list[CompilerDiagnostic]
) -> dict[str, Any]:
    semantic_source = state.get("semantic_source")
    if not isinstance(semantic_source, dict):
        return state

    docs_root = semantic_source.get("source_docs_root")
    if not isinstance(docs_root, str) or not docs_root.strip():
        diagnostics.append(
            _new_diag(
                code=SCC0004_SEMANTIC_SOURCE_INVALID,
                severity="ERROR",
                message="source_docs_root must be a non-empty string",
            )
        )
        return state

    try:
        docs_root_rel = _normalize_relative_path(docs_root)
    except ValueError as exc:
        diagnostics.append(
            _new_diag(
                code=SCC0004_SEMANTIC_SOURCE_INVALID,
                severity="ERROR",
                message=f"source_docs_root is invalid: {exc}",
            )
        )
        return state

    files = semantic_source.get("files")
    if not isinstance(files, list):
        return state

    hash_basis_files: list[dict[str, str]] = []
    for file_item in files:
        if not isinstance(file_item, dict):
            continue

        path = file_item.get("path")
        if not isinstance(path, str):
            continue

        try:
            path_norm = _normalize_relative_path(path)
        except ValueError as exc:
            diagnostics.append(
                _new_diag(
                    code=SCC0004_SEMANTIC_SOURCE_INVALID,
                    severity="ERROR",
                    message=f"invalid semantic source path {path!r}: {exc}",
                    path=path,
                )
            )
            continue

        if not _is_within_root(path_norm, docs_root_rel):
            diagnostics.append(
                _new_diag(
                    code=SCC0004_SEMANTIC_SOURCE_INVALID,
                    severity="ERROR",
                    message=(
                        f"semantic source file {path_norm!r} escapes docs root {docs_root_rel!r}"
                    ),
                    path=path_norm,
                )
            )

        frontmatter_semantic = file_item.get("frontmatter_semantic")
        blocks = file_item.get("blocks")
        if not isinstance(frontmatter_semantic, dict) or not isinstance(blocks, list):
            continue

        recomputed_hash = _build_file_semantic_hash(frontmatter_semantic, blocks)
        expected_hash = file_item.get("semantic_hash")
        if expected_hash != recomputed_hash:
            diagnostics.append(
                _new_diag(
                    code=SCC0004_SEMANTIC_SOURCE_INVALID,
                    severity="ERROR",
                    message="semantic_hash mismatch for normalized semantic source file",
                    path=path_norm,
                    details={
                        "expected": expected_hash,
                        "recomputed": recomputed_hash,
                    },
                )
            )

        hash_basis_files.append({"path": path_norm, "semantic_hash": recomputed_hash})

    source_hash_basis = {
        "schema": SEMANTIC_SOURCE_COLLECTION_SCHEMA,
        "files": hash_basis_files,
    }
    recomputed_source_hash = sha256_canonical_json(source_hash_basis)
    expected_source_hash = semantic_source.get("semantic_source_hash")
    if expected_source_hash != recomputed_source_hash:
        diagnostics.append(
            _new_diag(
                code=SCC0004_SEMANTIC_SOURCE_INVALID,
                severity="ERROR",
                message="semantic_source_hash mismatch for normalized semantic source collection",
                details={
                    "expected": expected_source_hash,
                    "recomputed": recomputed_source_hash,
                },
            )
        )

    return state


def _pass_build_ir(state: dict[str, Any], diagnostics: list[CompilerDiagnostic]) -> dict[str, Any]:
    semantic_source = state.get("semantic_source")
    if not isinstance(semantic_source, dict):
        return state

    files = semantic_source.get("files")
    if not isinstance(files, list):
        return state

    modules: list[dict[str, Any]] = []
    module_claims: dict[str, list[dict[str, Any]]] = {}

    source_files: list[dict[str, str]] = []
    for file_item in files:
        if not isinstance(file_item, dict):
            continue
        path = file_item.get("path")
        frontmatter = file_item.get("frontmatter_semantic")
        blocks = file_item.get("blocks")
        if (
            not isinstance(path, str)
            or not isinstance(frontmatter, dict)
            or not isinstance(blocks, list)
        ):
            continue

        file_hash_basis = {
            "path": path,
            "frontmatter_semantic": frontmatter,
            "blocks": blocks,
        }
        source_files.append(
            {
                "path": path,
                "semantic_source_hash": str(file_item.get("semantic_hash", "")),
                "file_hash": sha256_canonical_json(file_hash_basis),
            }
        )

        for block in blocks:
            if not isinstance(block, dict):
                continue

            payload = block.get("payload")
            label = block.get("label")
            if not isinstance(payload, dict) or not isinstance(label, str):
                continue

            module_kind: str | None = None
            payload_kind = payload.get("module_kind")
            if isinstance(payload_kind, str) and payload_kind.strip():
                module_kind = payload_kind.strip()
            if module_kind is None:
                module_kind = _module_kind_from_label(label)
            if module_kind is None:
                frontmatter_kind = frontmatter.get("adeu_module_kind") or frontmatter.get(
                    "asc_module_kind"
                )
                if isinstance(frontmatter_kind, str) and frontmatter_kind.strip():
                    module_kind = frontmatter_kind.strip()

            start_line = block.get("start_line")
            if not isinstance(start_line, int) or start_line < 1:
                start_line = 1

            end_line = block.get("end_line")
            if not isinstance(end_line, int) or end_line <= start_line:
                end_line = start_line + 1

            if module_kind not in _ALLOWED_MODULE_KINDS:
                diagnostics.append(
                    _new_diag(
                        code=SCC0006_MODULE_KIND_INVALID,
                        severity="ERROR",
                        message="module_kind must be one of arc_lock/slice_spec/stop_gate",
                        path=path,
                        start_line=start_line,
                    )
                )
                continue

            module_id_raw = payload.get("module_id") or block.get("identifier")
            if not isinstance(module_id_raw, str) or not module_id_raw.strip():
                diagnostics.append(
                    _new_diag(
                        code=SCC0007_MODULE_ID_MISSING,
                        severity="ERROR",
                        message="module_id is required for each compiled semantic block",
                        path=path,
                        start_line=start_line,
                    )
                )
                continue
            module_id = module_id_raw.strip()

            title_raw = payload.get("title")
            if isinstance(title_raw, str) and title_raw.strip():
                title = title_raw.strip()
            else:
                title = module_id

            status_raw = payload.get("status")
            if status_raw is None:
                status_raw = (
                    frontmatter.get("adeu_status") or frontmatter.get("asc_status") or "draft"
                )
            if not isinstance(status_raw, str) or status_raw not in _ALLOWED_MODULE_STATUS:
                diagnostics.append(
                    _new_diag(
                        code=SCC0008_MODULE_DECLARATION_INVALID,
                        severity="ERROR",
                        message=f"invalid module status: {status_raw!r}",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue

            depends_source = payload.get("depends_on")
            if depends_source is None:
                depends_source = frontmatter.get("adeu_depends_on") or frontmatter.get(
                    "asc_depends_on"
                )
            try:
                depends_on = _normalize_string_list(depends_source)
            except ValueError as exc:
                diagnostics.append(
                    _new_diag(
                        code=SCC0008_MODULE_DECLARATION_INVALID,
                        severity="ERROR",
                        message=f"depends_on must be a list of non-empty strings: {exc}",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue

            effects_declared: list[str] = []
            try:
                raw_effects = _normalize_string_list(payload.get("effects_declared"))
            except ValueError as exc:
                diagnostics.append(
                    _new_diag(
                        code=SCC0011_UNKNOWN_TOKEN,
                        severity="ERROR",
                        message=f"effects_declared must be a list of strings: {exc}",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue
            unknown_effects = [token for token in raw_effects if token not in _ALLOWED_EFFECT_TAGS]
            if unknown_effects:
                diagnostics.append(
                    _new_diag(
                        code=SCC0011_UNKNOWN_TOKEN,
                        severity="ERROR",
                        message=f"unknown effects_declared tokens: {unknown_effects}",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue
            effects_declared = raw_effects

            locks_payload: list[dict[str, Any]] = []
            raw_locks = payload.get("locks", [])
            if raw_locks is None:
                raw_locks = []
            if not isinstance(raw_locks, list):
                diagnostics.append(
                    _new_diag(
                        code=SCC0012_LOCK_TYPECHECK_INVALID,
                        severity="ERROR",
                        message="locks must be a list",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue
            lock_failure = False
            for index, lock_item in enumerate(raw_locks):
                if not isinstance(lock_item, dict):
                    diagnostics.append(
                        _new_diag(
                            code=SCC0012_LOCK_TYPECHECK_INVALID,
                            severity="ERROR",
                            message="lock entry must be an object",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    lock_failure = True
                    break
                kind = lock_item.get("kind")
                severity = lock_item.get("severity", "ERROR")
                if kind not in _ALLOWED_LOCK_KINDS or severity not in _ALLOWED_LOCK_SEVERITIES:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0012_LOCK_TYPECHECK_INVALID,
                            severity="ERROR",
                            message="lock kind/severity is invalid",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    lock_failure = True
                    break
                try:
                    target = _stringify_target(lock_item.get("target"))
                except ValueError as exc:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0012_LOCK_TYPECHECK_INVALID,
                            severity="ERROR",
                            message=f"invalid lock target: {exc}",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    lock_failure = True
                    break
                params = lock_item.get("params", {})
                if params is None:
                    params = {}
                if not isinstance(params, dict):
                    diagnostics.append(
                        _new_diag(
                            code=SCC0012_LOCK_TYPECHECK_INVALID,
                            severity="ERROR",
                            message="lock params must be an object",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    lock_failure = True
                    break

                lock_id = lock_item.get("lock_id")
                if not isinstance(lock_id, str) or not lock_id.strip():
                    lock_id = stable_commitments_lock_id(
                        module_id=module_id,
                        lock_kind=kind,
                        target=target,
                    )

                locks_payload.append(
                    {
                        "lock_id": lock_id,
                        "kind": kind,
                        "severity": severity,
                        "target": target,
                        "params": params,
                        "source": {
                            "path": path,
                            "span": {
                                "start": start_line,
                                "end": end_line,
                            },
                        },
                    }
                )
            if lock_failure:
                continue

            surfaces_payload: list[dict[str, Any]] = []
            raw_surfaces = payload.get("surfaces", [])
            if raw_surfaces is None:
                raw_surfaces = []
            if not isinstance(raw_surfaces, list):
                diagnostics.append(
                    _new_diag(
                        code=SCC0008_MODULE_DECLARATION_INVALID,
                        severity="ERROR",
                        message="surfaces must be a list",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue
            surface_failure = False
            for surface_item in raw_surfaces:
                if not isinstance(surface_item, dict):
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message="surface entry must be an object",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    surface_failure = True
                    break
                surface_id = surface_item.get("surface_id")
                surface_kind = surface_item.get("surface_kind")
                if not isinstance(surface_id, str) or not surface_id.strip():
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message="surface_id must be a non-empty string",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    surface_failure = True
                    break
                if surface_kind not in _ALLOWED_SURFACE_KINDS:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0011_UNKNOWN_TOKEN,
                            severity="ERROR",
                            message=f"unknown surface_kind token: {surface_kind!r}",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    surface_failure = True
                    break
                try:
                    selector = _stringify_selector(surface_item.get("selector"))
                except ValueError as exc:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message=f"invalid surface selector: {exc}",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    surface_failure = True
                    break
                surfaces_payload.append(
                    {
                        "surface_id": surface_id.strip(),
                        "surface_kind": surface_kind,
                        "selector": selector,
                    }
                )
            if surface_failure:
                continue

            assertions_payload: list[dict[str, Any]] = []
            raw_assertions = payload.get("assertions", [])
            if raw_assertions is None:
                raw_assertions = []
            if not isinstance(raw_assertions, list):
                diagnostics.append(
                    _new_diag(
                        code=SCC0008_MODULE_DECLARATION_INVALID,
                        severity="ERROR",
                        message="assertions must be a list",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue
            assertion_failure = False
            for assertion_item in raw_assertions:
                if not isinstance(assertion_item, dict):
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message="assertion entry must be an object",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    assertion_failure = True
                    break
                assertion_type = assertion_item.get("assertion_type") or assertion_item.get("type")
                if assertion_type not in _ALLOWED_ASSERTION_TYPES:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0011_UNKNOWN_TOKEN,
                            severity="ERROR",
                            message=f"unknown assertion_type token: {assertion_type!r}",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    assertion_failure = True
                    break
                try:
                    target = _stringify_target(assertion_item.get("target"))
                except ValueError as exc:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message=f"invalid assertion target: {exc}",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    assertion_failure = True
                    break
                expected = assertion_item.get("expected", {})
                if expected is None:
                    expected = {}
                if not isinstance(expected, dict):
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message="assertion expected value must be an object",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    assertion_failure = True
                    break
                assertion_id = assertion_item.get("assertion_id")
                if not isinstance(assertion_id, str) or not assertion_id.strip():
                    assertion_id = _derived_id(module_id, "assertion", assertion_type, target)
                assertions_payload.append(
                    {
                        "assertion_id": assertion_id,
                        "assertion_type": assertion_type,
                        "target": target,
                        "expected": expected,
                    }
                )
            if assertion_failure:
                continue

            evidence_payload: list[dict[str, Any]] = []
            raw_evidence = payload.get("evidence_requirements", [])
            if raw_evidence is None:
                raw_evidence = []
            if not isinstance(raw_evidence, list):
                diagnostics.append(
                    _new_diag(
                        code=SCC0008_MODULE_DECLARATION_INVALID,
                        severity="ERROR",
                        message="evidence_requirements must be a list",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue
            evidence_failure = False
            for evidence_item in raw_evidence:
                if not isinstance(evidence_item, dict):
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message="evidence requirement entry must be an object",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    evidence_failure = True
                    break
                evidence_type = evidence_item.get("evidence_type")
                trust_lane = evidence_item.get("trust_lane")
                quality = evidence_item.get("quality")
                if quality is None:
                    quality = evidence_item.get("quality_level")
                if evidence_type not in _ALLOWED_EVIDENCE_TYPES:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0011_UNKNOWN_TOKEN,
                            severity="ERROR",
                            message=f"unknown evidence_type token: {evidence_type!r}",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    evidence_failure = True
                    break
                if trust_lane not in _ALLOWED_TRUST_LANES:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0011_UNKNOWN_TOKEN,
                            severity="ERROR",
                            message=f"unknown trust_lane token: {trust_lane!r}",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    evidence_failure = True
                    break
                if quality not in _ALLOWED_EVIDENCE_QUALITY:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0011_UNKNOWN_TOKEN,
                            severity="ERROR",
                            message=f"unknown evidence quality token: {quality!r}",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    evidence_failure = True
                    break
                evidence_id = evidence_item.get("evidence_id")
                if not isinstance(evidence_id, str) or not evidence_id.strip():
                    evidence_id = _derived_id(module_id, "evidence", evidence_type, trust_lane)
                required = evidence_item.get("required", True)
                if not isinstance(required, bool):
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message="evidence required must be boolean",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    evidence_failure = True
                    break
                evidence_payload.append(
                    {
                        "evidence_id": evidence_id,
                        "evidence_type": evidence_type,
                        "trust_lane": trust_lane,
                        "quality": quality,
                        "required": required,
                    }
                )
            if evidence_failure:
                continue

            module_payload: dict[str, Any] = {
                "module_id": module_id,
                "module_kind": module_kind,
                "title": title,
                "status": status_raw,
                "source": {
                    "path": path,
                    "span": {
                        "start": start_line,
                        "end": end_line,
                    },
                },
                "depends_on": depends_on,
                "effects_declared": effects_declared,
                "locks": sorted(locks_payload, key=lambda row: row["lock_id"]),
                "surfaces": sorted(surfaces_payload, key=lambda row: row["surface_id"]),
                "assertions": sorted(assertions_payload, key=lambda row: row["assertion_id"]),
                "evidence_requirements": sorted(
                    evidence_payload,
                    key=lambda row: row["evidence_id"],
                ),
            }

            arc_id = _derive_arc_id(payload=payload, frontmatter=frontmatter, module_id=module_id)
            if arc_id is None:
                diagnostics.append(
                    _new_diag(
                        code=SCC0008_MODULE_DECLARATION_INVALID,
                        severity="ERROR",
                        message="arc_id is required for compiled module",
                        module_id=module_id,
                        path=path,
                        start_line=start_line,
                    )
                )
                continue

            module_payload["arc_id"] = arc_id
            if module_kind == "slice_spec":
                slice_id = _derive_slice_id(
                    payload=payload, frontmatter=frontmatter, module_id=module_id
                )
                if slice_id is None:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message="slice_id is required for slice_spec modules",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    continue
                module_payload["slice_id"] = slice_id
            elif module_kind == "stop_gate":
                stop_gate_id = _derive_stop_gate_id(payload=payload, module_id=module_id)
                if stop_gate_id is None:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0008_MODULE_DECLARATION_INVALID,
                            severity="ERROR",
                            message="stop_gate_id is required for stop_gate modules",
                            module_id=module_id,
                            path=path,
                            start_line=start_line,
                        )
                    )
                    continue
                module_payload["stop_gate_id"] = stop_gate_id

            module_hash_basis = _canonical_clone(module_payload)
            module_payload["module_hash"] = sha256_canonical_json(module_hash_basis)

            modules.append(module_payload)
            module_claims.setdefault(module_id, []).append(
                {
                    "path": path,
                    "start_line": start_line,
                }
            )

    duplicate_module_ids = sorted(
        module_id for module_id, claims in module_claims.items() if len(claims) > 1
    )
    if duplicate_module_ids:
        for module_id in duplicate_module_ids:
            claims = sorted(
                module_claims[module_id],
                key=lambda row: (row["path"], row["start_line"]),
            )
            diagnostics.append(
                _new_diag(
                    code=SCC0009_MODULE_ID_DUPLICATE,
                    severity="ERROR",
                    message=f"duplicate module_id detected: {module_id}",
                    module_id=module_id,
                    path=claims[0]["path"],
                    start_line=int(claims[0]["start_line"]),
                    details={"claim_sites": claims},
                )
            )

    modules = sorted(modules, key=lambda row: (row["module_kind"], row["module_id"]))
    source_files = sorted(source_files, key=lambda row: row["path"])
    source_set_hash = sha256_canonical_json(
        {
            "files": [
                {
                    "path": item["path"],
                    "semantic_source_hash": item["semantic_source_hash"],
                    "file_hash": item["file_hash"],
                }
                for item in source_files
            ]
        }
    )

    ir_payload: dict[str, Any] = {
        "schema": ADEU_COMMITMENTS_IR_SCHEMA,
        "compiler": {
            "name": "adeu_semantic_compiler",
            "version": "0.0.0",
            "pass_versions": sorted(
                [
                    "build_ir@1",
                    "load_collection@1",
                    "revalidate_normalization@1",
                    "resolve_refs@1",
                    "typecheck_locks@1",
                    "validate_blocks@1",
                ]
            ),
            "config_hash": sha256_canonical_json(
                {
                    "export_call_pattern": _EXPORT_CALL_PATTERN,
                    "input_contract_id": SEMANTIC_SOURCE_COLLECTION_SCHEMA,
                    "pass_sequence": list(_PASS_SEQUENCE),
                }
            ),
        },
        "source_set": {
            "repo_root_rel": str(semantic_source.get("source_docs_root", "docs")),
            "files": source_files,
            "source_set_hash": source_set_hash,
        },
        "modules": modules,
        "diagnostics": [],
    }

    try:
        normalized_ir = canonicalize_commitments_ir_payload(ir_payload)
    except ValidationError as exc:
        validation_errors = _json_safe(exc.errors(include_url=False))
        diagnostics.append(
            _new_diag(
                code=SCC0008_MODULE_DECLARATION_INVALID,
                severity="ERROR",
                message="compiled commitments IR payload is invalid",
                details={"validation_errors": validation_errors},
            )
        )
        return {
            **state,
            "commitments_ir": None,
        }

    return {
        **state,
        "commitments_ir": normalized_ir,
    }


def _pass_resolve_refs(
    state: dict[str, Any], diagnostics: list[CompilerDiagnostic]
) -> dict[str, Any]:
    commitments_ir = state.get("commitments_ir")
    if not isinstance(commitments_ir, dict):
        return {
            **state,
            "resolve_refs": {
                "checked": False,
                "unresolved_count": 0,
            },
        }

    modules = commitments_ir.get("modules")
    if not isinstance(modules, list):
        return {
            **state,
            "resolve_refs": {
                "checked": False,
                "unresolved_count": 0,
            },
        }

    known_ids = {
        module.get("module_id")
        for module in modules
        if isinstance(module, dict) and isinstance(module.get("module_id"), str)
    }

    unresolved_count = 0
    for module in modules:
        if not isinstance(module, dict):
            continue
        module_id = module.get("module_id")
        if not isinstance(module_id, str):
            continue
        depends_on = module.get("depends_on", [])
        if not isinstance(depends_on, list):
            continue
        for dependency in depends_on:
            if dependency in known_ids:
                continue
            unresolved_count += 1
            source = module.get("source") if isinstance(module.get("source"), dict) else {}
            diagnostics.append(
                _new_diag(
                    code=SCC0010_UNRESOLVED_REFERENCE,
                    severity="ERROR",
                    message=f"unresolved module dependency: {dependency!r}",
                    module_id=module_id,
                    path=source.get("path") if isinstance(source.get("path"), str) else None,
                    start_line=1,
                )
            )

    return {
        **state,
        "resolve_refs": {
            "checked": True,
            "unresolved_count": unresolved_count,
        },
    }


def _pass_typecheck_locks(
    state: dict[str, Any], diagnostics: list[CompilerDiagnostic]
) -> dict[str, Any]:
    commitments_ir = state.get("commitments_ir")
    if not isinstance(commitments_ir, dict):
        return state

    modules = commitments_ir.get("modules")
    if not isinstance(modules, list):
        return state

    for module in modules:
        if not isinstance(module, dict):
            continue
        module_id = module.get("module_id")
        source = module.get("source") if isinstance(module.get("source"), dict) else {}
        path = source.get("path") if isinstance(source.get("path"), str) else None
        locks = module.get("locks", [])
        if not isinstance(locks, list):
            continue

        for lock in locks:
            if not isinstance(lock, dict):
                diagnostics.append(
                    _new_diag(
                        code=SCC0012_LOCK_TYPECHECK_INVALID,
                        severity="ERROR",
                        message="lock entry must be an object",
                        module_id=module_id if isinstance(module_id, str) else "",
                        path=path,
                    )
                )
                continue

            kind = lock.get("kind")
            params = lock.get("params", {})
            if kind == "exact_set":
                allowed = params.get("allowed") if isinstance(params, dict) else None
                if not isinstance(allowed, list) or not all(
                    isinstance(item, str) and item.strip() for item in allowed
                ):
                    diagnostics.append(
                        _new_diag(
                            code=SCC0012_LOCK_TYPECHECK_INVALID,
                            severity="ERROR",
                            message=(
                                "exact_set locks must provide params.allowed "
                                "as non-empty string list"
                            ),
                            module_id=module_id if isinstance(module_id, str) else "",
                            path=path,
                        )
                    )

    return state


_PASS_HANDLERS: dict[str, Callable[[dict[str, Any], list[CompilerDiagnostic]], dict[str, Any]]] = {
    "LoadCollection": _pass_load_collection,
    "ValidateBlocks": _pass_validate_blocks,
    "RevalidateNormalization": _pass_revalidate_normalization,
    "BuildIR": _pass_build_ir,
    "ResolveRefs": _pass_resolve_refs,
    "TypecheckLocks": _pass_typecheck_locks,
}


def _run_pass_pipeline(
    *,
    initial_state: dict[str, Any],
    diagnostics: list[CompilerDiagnostic],
) -> tuple[dict[str, Any], list[PassEntry]]:
    state = initial_state
    entries: list[PassEntry] = []

    for index, pass_name in enumerate(_PASS_SEQUENCE):
        input_hash = sha256_canonical_json(state)
        output_state = _PASS_HANDLERS[pass_name](state, diagnostics)
        output_hash = sha256_canonical_json(output_state)

        if pass_name in _MUTATING_PASSES and input_hash == output_hash:
            diagnostics.append(
                _new_diag(
                    code=SCC0014_PASS_HASH_IDENTITY_VIOLATION,
                    severity="ERROR",
                    message=f"mutating pass produced identical input/output hash: {pass_name}",
                )
            )

        entries.append(
            PassEntry(
                name=pass_name,
                index=index,
                input_sha256=input_hash,
                output_sha256=output_hash,
            )
        )
        state = output_state

    return state, entries


@dataclass(frozen=True)
class SurfaceRecord:
    surface_id: str
    module_id: str
    module_kind: str
    slice_id: str
    surface_kind: str
    selector: str
    selector_path: str
    signature_sha256: str
    keyset: tuple[str, ...]

    def to_payload(self) -> dict[str, Any]:
        return {
            "surface_id": self.surface_id,
            "module_id": self.module_id,
            "module_kind": self.module_kind,
            "slice_id": self.slice_id,
            "surface_kind": self.surface_kind,
            "selector": self.selector,
            "selector_path": self.selector_path,
            "signature_sha256": self.signature_sha256,
            "keyset": list(self.keyset),
        }


def _normalize_surface_selector_path(raw_selector: str) -> str:
    normalized = _normalize_utf8_nfc(raw_selector.strip().replace("\\", "/"))
    if not normalized:
        raise ValueError("selector path must not be empty")
    return _normalize_relative_path(normalized)


def _parse_markdown_surface_selector(selector: str) -> tuple[str, str]:
    selector_text = _normalize_utf8_nfc(selector.strip())
    if not selector_text:
        raise ValueError("markdown_json_block selector must not be empty")

    selector_payload: dict[str, Any] | None = None
    if selector_text.startswith("{"):
        try:
            decoded = json.loads(selector_text)
        except json.JSONDecodeError as exc:
            raise ValueError(f"invalid markdown selector json: {exc}") from exc
        if not isinstance(decoded, dict):
            raise ValueError("markdown selector json must be an object")
        selector_payload = decoded
    elif "#" in selector_text:
        path_raw, schema_raw = selector_text.split("#", 1)
        selector_payload = {"path": path_raw, "schema": schema_raw}
    else:
        raise ValueError("markdown selector must be object-json or '<path>#<schema>'")

    path_candidate = selector_payload.get("path")
    schema_candidate = selector_payload.get("schema")
    if schema_candidate is None:
        schema_candidate = selector_payload.get("schema_selector")
    if not isinstance(path_candidate, str) or not path_candidate.strip():
        raise ValueError("markdown selector path is required")
    if not isinstance(schema_candidate, str) or not schema_candidate.strip():
        raise ValueError("markdown selector schema is required")

    return (
        _normalize_surface_selector_path(path_candidate),
        schema_candidate.strip(),
    )


def _extract_top_level_keyset(value: Any) -> tuple[str, ...]:
    if not isinstance(value, dict):
        raise ValueError("structured keyset extraction requires object payload")
    keyset = sorted({str(key) for key in value.keys()})
    return tuple(keyset)


_MARKDOWN_JSON_BLOCK_RE = re.compile(r"```(?:json)?[ \t]*\n(.*?)\n```", re.IGNORECASE | re.DOTALL)


def _extract_markdown_json_blocks(
    *,
    markdown_text: str,
    schema_selector: str,
) -> list[tuple[str, int, dict[str, Any]]]:
    selected: list[tuple[str, int, dict[str, Any]]] = []
    seen_keys: set[tuple[str, int]] = set()
    ordinal = 0

    for match in _MARKDOWN_JSON_BLOCK_RE.finditer(markdown_text):
        block_text = match.group(1).strip()
        if not block_text:
            continue
        try:
            decoded = json.loads(block_text)
        except json.JSONDecodeError:
            continue
        if not isinstance(decoded, dict):
            continue
        block_schema = decoded.get("schema")
        if not isinstance(block_schema, str) or not block_schema.strip():
            raise ValueError("markdown_json_block entry missing schema selector")
        block_schema = block_schema.strip()
        block_index = decoded.get("block_index", ordinal)
        ordinal += 1
        if not isinstance(block_index, int) or block_index < 0:
            raise ValueError("markdown_json_block block_index must be non-negative integer")
        unique_key = (block_schema, block_index)
        if unique_key in seen_keys:
            raise ValueError(f"duplicate markdown_json_block key detected: {unique_key!r}")
        seen_keys.add(unique_key)
        if block_schema != schema_selector:
            continue
        selected.append((block_schema, block_index, _canonical_clone(decoded)))

    if not selected:
        raise ValueError(f"no markdown_json_block entries found for schema selector {schema_selector!r}")
    selected.sort(key=lambda row: (row[0], row[1]))
    return selected


def _parse_json_file(path: Path) -> dict[str, Any]:
    raw_text = path.read_text(encoding="utf-8")
    payload = json.loads(raw_text)
    if not isinstance(payload, dict):
        raise ValueError("json surface payload must be an object")
    return payload


def _validate_v40_pass_manifest_contract(
    *,
    pass_manifest_payload: dict[str, Any],
) -> tuple[bool, str]:
    if pass_manifest_payload.get("schema") != SEMANTIC_COMPILER_PASS_MANIFEST_SCHEMA:
        return False, "pass manifest schema mismatch"
    sequence = pass_manifest_payload.get("pass_sequence")
    entries = pass_manifest_payload.get("pass_manifest")
    if sequence != list(_PASS_SEQUENCE):
        return False, "pass sequence does not match frozen contract"
    if not isinstance(entries, list) or len(entries) != len(_PASS_SEQUENCE):
        return False, "pass manifest entries are missing or incomplete"
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            return False, "pass manifest entry is not an object"
        expected_keys = {"name", "index", "input_sha256", "output_sha256"}
        if set(entry) != expected_keys:
            return False, "pass manifest entry fields drift from frozen contract"
        if entry.get("name") != _PASS_SEQUENCE[index]:
            return False, "pass manifest name/order drift detected"
        if entry.get("index") != index:
            return False, "pass manifest index drift detected"
        in_hash = entry.get("input_sha256")
        out_hash = entry.get("output_sha256")
        if not isinstance(in_hash, str) or not re.fullmatch(r"[0-9a-f]{64}", in_hash):
            return False, "pass manifest input_sha256 is invalid"
        if not isinstance(out_hash, str) or not re.fullmatch(r"[0-9a-f]{64}", out_hash):
            return False, "pass manifest output_sha256 is invalid"
    return True, ""


def _build_surface_records(
    *,
    root: Path,
    commitments_ir_payload: dict[str, Any],
    diagnostics: list[CompilerDiagnostic],
) -> tuple[list[SurfaceRecord], dict[str, dict[str, Any]]]:
    modules = commitments_ir_payload.get("modules")
    if not isinstance(modules, list):
        diagnostics.append(
            _new_diag(
                code=SCC0015_INPUT_HANDOFF_INVALID,
                severity="ERROR",
                message="commitments ir modules must be a list for v41 surface extraction",
            )
        )
        return [], {}

    records: list[SurfaceRecord] = []
    owners: dict[str, dict[str, Any]] = {}

    for module in modules:
        if not isinstance(module, dict):
            continue
        module_id = module.get("module_id")
        module_kind = module.get("module_kind")
        if not isinstance(module_id, str) or not isinstance(module_kind, str):
            continue
        slice_id = module.get("slice_id")
        if not isinstance(slice_id, str):
            slice_id = ""
        raw_surfaces = module.get("surfaces", [])
        if not isinstance(raw_surfaces, list):
            diagnostics.append(
                _new_diag(
                    code=SCC0016_SURFACE_SELECTOR_INVALID,
                    severity="ERROR",
                    message="compiled module surfaces must be a list",
                    module_id=module_id,
                )
            )
            continue

        for surface in raw_surfaces:
            if not isinstance(surface, dict):
                diagnostics.append(
                    _new_diag(
                        code=SCC0016_SURFACE_SELECTOR_INVALID,
                        severity="ERROR",
                        message="surface entry must be an object",
                        module_id=module_id,
                    )
                )
                continue
            surface_id = surface.get("surface_id")
            surface_kind = surface.get("surface_kind")
            selector = surface.get("selector")
            if not isinstance(surface_id, str) or not surface_id.strip():
                diagnostics.append(
                    _new_diag(
                        code=SCC0016_SURFACE_SELECTOR_INVALID,
                        severity="ERROR",
                        message="surface_id must be a non-empty string",
                        module_id=module_id,
                    )
                )
                continue
            if surface_kind not in _ALLOWED_SURFACE_KINDS:
                diagnostics.append(
                    _new_diag(
                        code=SCC0016_SURFACE_SELECTOR_INVALID,
                        severity="ERROR",
                        message=f"unknown surface_kind in v41 surface extraction: {surface_kind!r}",
                        module_id=module_id,
                    )
                )
                continue
            if not isinstance(selector, str) or not selector.strip():
                diagnostics.append(
                    _new_diag(
                        code=SCC0016_SURFACE_SELECTOR_INVALID,
                        severity="ERROR",
                        message="surface selector must be a non-empty string",
                        module_id=module_id,
                    )
                )
                continue
            surface_id = surface_id.strip()
            if surface_id in owners:
                diagnostics.append(
                    _new_diag(
                        code=SCC0020_PR_SPLIT_INVALID,
                        severity="ERROR",
                        message=(
                            f"surface ownership is ambiguous for {surface_id!r}; "
                            "multi-owner surfaces are forbidden in v41"
                        ),
                        module_id=module_id,
                        details={"existing_owner": owners[surface_id]["module_id"]},
                    )
                )
                continue

            try:
                if surface_kind in {"schema", "manifest"}:
                    selector_path = _normalize_surface_selector_path(selector)
                    absolute_path = root / selector_path
                    payload = _parse_json_file(absolute_path)
                    signature_sha = sha256_canonical_json(payload)
                    keyset = _extract_top_level_keyset(payload)
                elif surface_kind == "file":
                    selector_path = _normalize_surface_selector_path(selector)
                    absolute_path = root / selector_path
                    if absolute_path.is_symlink():
                        raise ValueError("file surface selector resolves to symlink entry")
                    if not absolute_path.is_file():
                        raise ValueError("file surface selector does not resolve to file")
                    signature_sha = _sha256_bytes(absolute_path.read_bytes())
                    keyset = tuple()
                else:
                    selector_path, schema_selector = _parse_markdown_surface_selector(selector)
                    absolute_path = root / selector_path
                    markdown_text = absolute_path.read_text(encoding="utf-8")
                    blocks = _extract_markdown_json_blocks(
                        markdown_text=markdown_text,
                        schema_selector=schema_selector,
                    )
                    signature_payload = {
                        "schema_selector": schema_selector,
                        "blocks": [
                            {
                                "schema": schema_name,
                                "block_index": block_index,
                                "payload": block_payload,
                            }
                            for schema_name, block_index, block_payload in blocks
                        ],
                    }
                    signature_sha = sha256_canonical_json(signature_payload)
                    merged_keyset: set[str] = set()
                    for _, _, payload in blocks:
                        merged_keyset.update(_extract_top_level_keyset(payload))
                    keyset = tuple(sorted(merged_keyset))
            except (OSError, ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
                diagnostics.append(
                    _new_diag(
                        code=SCC0017_SURFACE_SIGNATURE_INVALID,
                        severity="ERROR",
                        message=f"surface signature extraction failed: {exc}",
                        module_id=module_id,
                        details={
                            "surface_id": surface_id,
                            "surface_kind": surface_kind,
                        },
                    )
                )
                continue

            owners[surface_id] = {
                "module_id": module_id,
                "module_kind": module_kind,
                "slice_id": slice_id,
            }
            records.append(
                SurfaceRecord(
                    surface_id=surface_id,
                    module_id=module_id,
                    module_kind=module_kind,
                    slice_id=slice_id,
                    surface_kind=surface_kind,
                    selector=selector,
                    selector_path=selector_path,
                    signature_sha256=signature_sha,
                    keyset=keyset,
                )
            )

    records.sort(key=lambda item: item.surface_id)
    return records, owners


def _load_baseline_surface_snapshot(
    *,
    root: Path,
    diagnostics: list[CompilerDiagnostic],
) -> tuple[bool, dict[str, dict[str, Any]]]:
    baseline_rel = _normalize_relative_path(_DEFAULT_BASELINE_SURFACE_SNAPSHOT)
    baseline_path = root / baseline_rel
    if not baseline_path.is_file():
        return False, {}

    try:
        payload = _read_json_object(baseline_path)
    except (ValueError, json.JSONDecodeError) as exc:
        diagnostics.append(
            _new_diag(
                code=SCC0015_INPUT_HANDOFF_INVALID,
                severity="ERROR",
                message=f"baseline surface snapshot is invalid: {exc}",
                path=baseline_rel,
            )
        )
        return True, {}

    if payload.get("schema") != SEMANTIC_COMPILER_SURFACE_SNAPSHOT_SCHEMA:
        diagnostics.append(
            _new_diag(
                code=SCC0015_INPUT_HANDOFF_INVALID,
                severity="ERROR",
                message=(
                    "baseline surface snapshot schema mismatch: expected "
                    f"{SEMANTIC_COMPILER_SURFACE_SNAPSHOT_SCHEMA!r}"
                ),
                path=baseline_rel,
            )
        )
        return True, {}

    rows = payload.get("surfaces")
    if not isinstance(rows, list):
        diagnostics.append(
            _new_diag(
                code=SCC0015_INPUT_HANDOFF_INVALID,
                severity="ERROR",
                message="baseline surface snapshot must contain surfaces list",
                path=baseline_rel,
            )
        )
        return True, {}

    baseline_map: dict[str, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        surface_id = row.get("surface_id")
        surface_kind = row.get("surface_kind")
        signature_sha = row.get("signature_sha256")
        if (
            not isinstance(surface_id, str)
            or not surface_id
            or surface_kind not in _ALLOWED_SURFACE_KINDS
            or not isinstance(signature_sha, str)
            or not re.fullmatch(r"[0-9a-f]{64}", signature_sha)
        ):
            diagnostics.append(
                _new_diag(
                    code=SCC0015_INPUT_HANDOFF_INVALID,
                    severity="ERROR",
                    message="baseline surface snapshot entry is invalid",
                    path=baseline_rel,
                )
            )
            continue
        raw_keyset = row.get("keyset", [])
        if not isinstance(raw_keyset, list) or not all(isinstance(item, str) for item in raw_keyset):
            diagnostics.append(
                _new_diag(
                    code=SCC0015_INPUT_HANDOFF_INVALID,
                    severity="ERROR",
                    message="baseline keyset must be list[str]",
                    path=baseline_rel,
                )
            )
            continue
        baseline_map[surface_id] = {
            "surface_id": surface_id,
            "surface_kind": surface_kind,
            "signature_sha256": signature_sha,
            "keyset": tuple(sorted(set(raw_keyset))),
        }
    return True, baseline_map


def _collect_surface_rule_modes(
    *,
    commitments_ir_payload: dict[str, Any],
    known_surface_ids: set[str],
    diagnostics: list[CompilerDiagnostic],
) -> dict[str, str]:
    modules = commitments_ir_payload.get("modules")
    if not isinstance(modules, list):
        return {}
    modes: dict[str, str] = {}
    for module in modules:
        if not isinstance(module, dict):
            continue
        module_id = module.get("module_id")
        if not isinstance(module_id, str):
            module_id = ""
        locks = module.get("locks", [])
        if not isinstance(locks, list):
            continue
        for lock in locks:
            if not isinstance(lock, dict):
                continue
            kind = lock.get("kind")
            if kind not in {"freeze", "additive_only", "exact_set"}:
                continue
            target = lock.get("target")
            if not isinstance(target, str) or target not in known_surface_ids:
                continue
            previous = modes.get(target)
            if previous is not None and previous != kind:
                diagnostics.append(
                    _new_diag(
                        code=SCC0018_DELTA_RULE_VIOLATION,
                        severity="ERROR",
                        message=(
                            f"surface {target!r} has ambiguous delta lock modes: "
                            f"{previous!r} vs {kind!r}"
                        ),
                        module_id=module_id,
                    )
                )
                continue
            modes[target] = kind
    return modes


def _evaluate_surface_diff(
    *,
    current_records: list[SurfaceRecord],
    baseline_present: bool,
    baseline_map: dict[str, dict[str, Any]],
    surface_modes: dict[str, str],
    diagnostics: list[CompilerDiagnostic],
) -> dict[str, Any]:
    current_map = {item.surface_id: item for item in current_records}
    if not baseline_present:
        return {
            "schema": SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA,
            "baseline_present": False,
            "delta_eval_mode": "no_baseline",
            "adds": [item.to_payload() for item in current_records],
            "removes": [],
            "changes": [],
        }

    adds: list[dict[str, Any]] = []
    removes: list[dict[str, Any]] = []
    changes: list[dict[str, Any]] = []

    all_ids = sorted(set(current_map) | set(baseline_map))
    for surface_id in all_ids:
        mode = surface_modes.get(surface_id, "freeze")
        current = current_map.get(surface_id)
        baseline = baseline_map.get(surface_id)

        if baseline is None and current is not None:
            adds.append(current.to_payload())
            continue

        if baseline is not None and current is None:
            removes.append(_canonical_clone(baseline))
            diagnostics.append(
                _new_diag(
                    code=SCC0018_DELTA_RULE_VIOLATION,
                    severity="ERROR",
                    message=f"surface removed under locked delta mode {mode!r}: {surface_id}",
                    details={"surface_id": surface_id, "mode": mode},
                )
            )
            continue

        if baseline is None or current is None:
            continue

        signature_changed = current.signature_sha256 != baseline["signature_sha256"]
        if signature_changed:
            changes.append(
                {
                    "surface_id": surface_id,
                    "surface_kind": current.surface_kind,
                    "selector": current.selector,
                    "module_id": current.module_id,
                    "slice_id": current.slice_id,
                    "previous_signature_sha256": baseline["signature_sha256"],
                    "current_signature_sha256": current.signature_sha256,
                }
            )

        baseline_keyset = set(baseline["keyset"])
        current_keyset = set(current.keyset)
        if mode == "freeze":
            if signature_changed:
                diagnostics.append(
                    _new_diag(
                        code=SCC0018_DELTA_RULE_VIOLATION,
                        severity="ERROR",
                        message=f"freeze violation for surface {surface_id!r}",
                        module_id=current.module_id,
                        details={
                            "surface_id": surface_id,
                            "previous_signature_sha256": baseline["signature_sha256"],
                            "current_signature_sha256": current.signature_sha256,
                        },
                    )
                )
        elif mode == "exact_set":
            if current.surface_kind == "file":
                if signature_changed:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0018_DELTA_RULE_VIOLATION,
                            severity="ERROR",
                            message=f"exact_set violation for file surface {surface_id!r}",
                            module_id=current.module_id,
                        )
                    )
            elif baseline_keyset != current_keyset:
                diagnostics.append(
                    _new_diag(
                        code=SCC0018_DELTA_RULE_VIOLATION,
                        severity="ERROR",
                        message=f"exact_set keyset violation for surface {surface_id!r}",
                        module_id=current.module_id,
                        details={
                            "baseline_keyset": sorted(baseline_keyset),
                            "current_keyset": sorted(current_keyset),
                        },
                    )
                )
        elif mode == "additive_only":
            if current.surface_kind == "file":
                if signature_changed:
                    diagnostics.append(
                        _new_diag(
                            code=SCC0018_DELTA_RULE_VIOLATION,
                            severity="ERROR",
                            message=f"additive_only violation for file surface {surface_id!r}",
                            module_id=current.module_id,
                        )
                    )
            elif not baseline_keyset.issubset(current_keyset):
                diagnostics.append(
                    _new_diag(
                        code=SCC0018_DELTA_RULE_VIOLATION,
                        severity="ERROR",
                        message=f"additive_only keyset violation for surface {surface_id!r}",
                        module_id=current.module_id,
                        details={
                            "baseline_keyset": sorted(baseline_keyset),
                            "current_keyset": sorted(current_keyset),
                        },
                    )
                )

    return {
        "schema": SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA,
        "baseline_present": True,
        "delta_eval_mode": "baseline_compare",
        "adds": adds,
        "removes": removes,
        "changes": changes,
    }


def _collect_required_evidence(commitments_ir_payload: dict[str, Any]) -> list[dict[str, Any]]:
    modules = commitments_ir_payload.get("modules")
    if not isinstance(modules, list):
        return []
    required: list[dict[str, Any]] = []
    for module in modules:
        if not isinstance(module, dict):
            continue
        module_id = module.get("module_id")
        if not isinstance(module_id, str):
            continue
        evidence_requirements = module.get("evidence_requirements", [])
        if not isinstance(evidence_requirements, list):
            continue
        for evidence in evidence_requirements:
            if not isinstance(evidence, dict):
                continue
            evidence_type = evidence.get("evidence_type")
            if not isinstance(evidence_type, str):
                continue
            surface_id = evidence.get("surface_id")
            if not isinstance(surface_id, str):
                surface_id = ""
            required.append(
                {
                    "module_id": module_id,
                    "evidence_id": str(evidence.get("evidence_id", "")),
                    "evidence_type": evidence_type,
                    "surface_id": surface_id,
                    "trust_lane": str(evidence.get("trust_lane", "")),
                    "quality": str(evidence.get("quality", "")),
                    "required": bool(evidence.get("required", True)),
                }
            )
    required.sort(
        key=lambda row: (
            row["evidence_type"],
            row["surface_id"],
            row["module_id"],
            row["evidence_id"],
        )
    )
    return required


def _build_pr_splits_markdown(
    *,
    diff_payload: dict[str, Any],
    current_records: list[SurfaceRecord],
    diagnostics: list[CompilerDiagnostic],
) -> str:
    by_surface_id = {item.surface_id: item for item in current_records}
    changed: list[tuple[str, str]] = []
    for row in diff_payload.get("adds", []):
        if isinstance(row, dict) and isinstance(row.get("surface_id"), str):
            changed.append((row["surface_id"], "add"))
    for row in diff_payload.get("changes", []):
        if isinstance(row, dict) and isinstance(row.get("surface_id"), str):
            changed.append((row["surface_id"], "change"))
    for row in diff_payload.get("removes", []):
        if isinstance(row, dict) and isinstance(row.get("surface_id"), str):
            changed.append((row["surface_id"], "remove"))

    changed.sort(key=lambda row: (row[0], row[1]))
    grouped: dict[tuple[str, str], list[tuple[str, str, str]]] = {}
    for surface_id, change_type in changed:
        owner = by_surface_id.get(surface_id)
        if owner is None:
            diagnostics.append(
                _new_diag(
                    code=SCC0020_PR_SPLIT_INVALID,
                    severity="ERROR",
                    message=(
                        f"unable to map changed surface {surface_id!r} to owning module "
                        "from commitments ir"
                    ),
                )
            )
            continue
        group_key = (owner.slice_id, owner.module_id)
        grouped.setdefault(group_key, []).append((surface_id, owner.surface_kind, change_type))

    lines = [
        "# Semantic Compiler v41 PR Splits",
        "",
        "Generated from `surface_diff` and commitments IR ownership mapping.",
        "",
    ]
    if not grouped:
        lines.extend(["No changed surfaces.", ""])
        return "\n".join(lines)

    for slice_id, module_id in sorted(grouped.keys(), key=lambda row: (row[0], row[1])):
        display_slice = slice_id if slice_id else "<none>"
        lines.append(f"## Slice `{display_slice}` / Module `{module_id}`")
        lines.append("")
        for surface_id, surface_kind, change_type in sorted(grouped[(slice_id, module_id)]):
            lines.append(f"- `{surface_id}` (`{surface_kind}`) `{change_type}`")
        lines.append("")
    return "\n".join(lines)


def _build_v41_surface_artifacts(
    *,
    root: Path,
    commitments_ir_payload: dict[str, Any],
    diagnostics_payload: dict[str, Any],
    pass_manifest_payload: dict[str, Any],
    diagnostics: list[CompilerDiagnostic],
) -> tuple[dict[str, Any] | None, dict[str, Any] | None, dict[str, Any] | None, str | None]:
    if diagnostics_payload.get("schema") != SEMANTIC_COMPILER_DIAGNOSTICS_SCHEMA:
        diagnostics.append(
            _new_diag(
                code=SCC0015_INPUT_HANDOFF_INVALID,
                severity="ERROR",
                message="v40 diagnostics payload schema mismatch",
            )
        )
        return None, None, None, None
    diagnostic_rows = diagnostics_payload.get("diagnostics")
    if not isinstance(diagnostic_rows, list):
        diagnostics.append(
            _new_diag(
                code=SCC0015_INPUT_HANDOFF_INVALID,
                severity="ERROR",
                message="v40 diagnostics payload must contain diagnostics list",
            )
        )
        return None, None, None, None
    if any(
        isinstance(row, dict) and str(row.get("severity", "")).upper() == "ERROR"
        for row in diagnostic_rows
    ):
        diagnostics.append(
            _new_diag(
                code=SCC0015_INPUT_HANDOFF_INVALID,
                severity="ERROR",
                message="v40 diagnostics contain error-level entries; v41 fail-closed",
            )
        )
        return None, None, None, None

    pass_manifest_ok, pass_manifest_error = _validate_v40_pass_manifest_contract(
        pass_manifest_payload=pass_manifest_payload
    )
    if not pass_manifest_ok:
        diagnostics.append(
            _new_diag(
                code=SCC0015_INPUT_HANDOFF_INVALID,
                severity="ERROR",
                message=f"v40 pass manifest continuity check failed: {pass_manifest_error}",
            )
        )
        return None, None, None, None

    current_records, owners = _build_surface_records(
        root=root,
        commitments_ir_payload=commitments_ir_payload,
        diagnostics=diagnostics,
    )
    baseline_present, baseline_map = _load_baseline_surface_snapshot(root=root, diagnostics=diagnostics)
    known_surface_ids = set(baseline_map) | {record.surface_id for record in current_records}
    surface_modes = _collect_surface_rule_modes(
        commitments_ir_payload=commitments_ir_payload,
        known_surface_ids=known_surface_ids,
        diagnostics=diagnostics,
    )

    snapshot_payload = {
        "schema": SEMANTIC_COMPILER_SURFACE_SNAPSHOT_SCHEMA,
        "arc": "vnext_plus41",
        "compiler_entrypoint": _EXPORT_CALL_PATTERN,
        "surfaces": [record.to_payload() for record in current_records],
    }
    diff_payload = _evaluate_surface_diff(
        current_records=current_records,
        baseline_present=baseline_present,
        baseline_map=baseline_map,
        surface_modes=surface_modes,
        diagnostics=diagnostics,
    )
    pr_splits_markdown = _build_pr_splits_markdown(
        diff_payload=diff_payload,
        current_records=current_records,
        diagnostics=diagnostics,
    )

    ordered_surface_selectors = [
        {
            "surface_id": record.surface_id,
            "surface_kind": record.surface_kind,
            "selector": record.selector,
        }
        for record in current_records
    ]
    ordered_surface_signatures = [
        {
            "surface_id": record.surface_id,
            "signature_sha256": record.signature_sha256,
        }
        for record in current_records
    ]
    source_set_hash = sha256_canonical_json(
        {
            "ordered_surface_selectors": ordered_surface_selectors,
            "ordered_surface_signature_hashes": ordered_surface_signatures,
            "pass_manifest_payload_hash": sha256_canonical_json(pass_manifest_payload),
        }
    )
    required_evidence = _collect_required_evidence(commitments_ir_payload)

    snapshot_bytes = _serialize_payload(snapshot_payload)
    diff_bytes = _serialize_payload(diff_payload)
    pr_splits_bytes = pr_splits_markdown.encode("utf-8")
    evidence_manifest_payload = {
        "schema": SEMANTIC_COMPILER_EVIDENCE_MANIFEST_SCHEMA,
        "arc": "vnext_plus41",
        "compiler_entrypoint": _EXPORT_CALL_PATTERN,
        "source_set_hash": source_set_hash,
        "required_evidence": required_evidence,
        "artifacts": {
            "surface_snapshot": _DEFAULT_OUTPUT_SURFACE_SNAPSHOT,
            "surface_diff": _DEFAULT_OUTPUT_SURFACE_DIFF,
            "evidence_manifest": _DEFAULT_OUTPUT_EVIDENCE_MANIFEST,
            "pr_splits_markdown": _DEFAULT_OUTPUT_PR_SPLITS,
        },
        "artifact_hashes": {
            "surface_snapshot": _sha256_bytes(snapshot_bytes),
            "surface_diff": _sha256_bytes(diff_bytes),
            "pr_splits_markdown": _sha256_bytes(pr_splits_bytes),
        },
    }

    required_fields = {
        "schema",
        "arc",
        "compiler_entrypoint",
        "source_set_hash",
        "required_evidence",
        "artifacts",
        "artifact_hashes",
    }
    if set(evidence_manifest_payload) != required_fields:
        diagnostics.append(
            _new_diag(
                code=SCC0019_EVIDENCE_MANIFEST_INVALID,
                severity="ERROR",
                message="evidence manifest fields drift from frozen contract",
            )
        )

    # Ensure the internal owner-map assignment remains deterministic and complete.
    if set(owners) != {record.surface_id for record in current_records}:
        diagnostics.append(
            _new_diag(
                code=SCC0020_PR_SPLIT_INVALID,
                severity="ERROR",
                message="surface ownership map is inconsistent with extracted surface registry",
            )
        )

    return snapshot_payload, diff_payload, evidence_manifest_payload, pr_splits_markdown


def compile_semantic_compiler(
    *,
    semantic_source_path: str = _DEFAULT_INPUT_SEMANTIC_SOURCE,
    semantic_source_diagnostics_path: str = _DEFAULT_INPUT_SEMANTIC_DIAGNOSTICS,
    repo_root_path: Path | None = None,
    write_outputs: bool = True,
) -> CompileResult:
    root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path

    diagnostics: list[CompilerDiagnostic] = []

    had_existing_v40_inputs = False
    try:
        existing_ir_rel = _normalize_relative_path(_DEFAULT_OUTPUT_IR)
        existing_diag_rel = _normalize_relative_path(_DEFAULT_OUTPUT_DIAGNOSTICS)
        existing_manifest_rel = _normalize_relative_path(_DEFAULT_OUTPUT_PASS_MANIFEST)
        had_existing_v40_inputs = all(
            (root / rel).is_file() for rel in (existing_ir_rel, existing_diag_rel, existing_manifest_rel)
        )
    except ValueError:
        had_existing_v40_inputs = False

    try:
        (
            commitments_ir_output_path,
            diagnostics_output_path,
            pass_manifest_output_path,
        ) = _validate_output_paths(root=root)
    except ValueError as exc:
        diagnostics.append(
            _new_diag(
                code=SCC0013_OUTPUT_PATH_POLICY_VIOLATION,
                severity="ERROR",
                message=str(exc),
            )
        )
        fallback_base = root / _DEFAULT_OUTPUT_BASE_DIR
        commitments_ir_output_path = fallback_base / "commitments_ir.json"
        diagnostics_output_path = fallback_base / "semantic_compiler.diagnostics.json"
        pass_manifest_output_path = fallback_base / "pass_manifest.json"

    try:
        (
            surface_snapshot_output_path,
            surface_diff_output_path,
            evidence_manifest_output_path,
            pr_splits_output_path,
        ) = _validate_v41_output_paths(root=root)
    except ValueError as exc:
        diagnostics.append(
            _new_diag(
                code=SCC0013_OUTPUT_PATH_POLICY_VIOLATION,
                severity="ERROR",
                message=str(exc),
            )
        )
        fallback_base = root / _DEFAULT_OUTPUT_V41_BASE_DIR
        surface_snapshot_output_path = fallback_base / "surface_snapshot.json"
        surface_diff_output_path = fallback_base / "surface_diff.json"
        evidence_manifest_output_path = fallback_base / "evidence_manifest.json"
        pr_splits_output_path = root / _DEFAULT_OUTPUT_PR_SPLITS

    _, semantic_source_payload = _load_json_artifact(
        root=root,
        raw_path=semantic_source_path,
        diagnostics=diagnostics,
        not_found_message="semantic source artifact does not exist",
    )
    _, semantic_source_diagnostics_payload = _load_json_artifact(
        root=root,
        raw_path=semantic_source_diagnostics_path,
        diagnostics=diagnostics,
        not_found_message="semantic source diagnostics artifact does not exist",
    )

    if semantic_source_payload is not None:
        if semantic_source_payload.get("schema") != SEMANTIC_SOURCE_COLLECTION_SCHEMA:
            diagnostics.append(
                _new_diag(
                    code=SCC0001_INPUT_SCHEMA_INVALID,
                    severity="ERROR",
                    message=(
                        "semantic source artifact schema mismatch: expected "
                        f"{SEMANTIC_SOURCE_COLLECTION_SCHEMA!r}"
                    ),
                )
            )

    carried_input_warnings: list[CompilerDiagnostic] = []
    if semantic_source_diagnostics_payload is not None:
        if semantic_source_diagnostics_payload.get("schema") != SEMANTIC_SOURCE_DIAGNOSTICS_SCHEMA:
            diagnostics.append(
                _new_diag(
                    code=SCC0001_INPUT_SCHEMA_INVALID,
                    severity="ERROR",
                    message=(
                        "semantic source diagnostics artifact schema mismatch: expected "
                        f"{SEMANTIC_SOURCE_DIAGNOSTICS_SCHEMA!r}"
                    ),
                )
            )
        raw_diagnostics = semantic_source_diagnostics_payload.get("diagnostics")
        if not isinstance(raw_diagnostics, list):
            diagnostics.append(
                _new_diag(
                    code=SCC0001_INPUT_SCHEMA_INVALID,
                    severity="ERROR",
                    message="semantic source diagnostics payload must contain diagnostics list",
                )
            )
        else:
            source_errors: list[dict[str, Any]] = []
            source_warnings: list[dict[str, Any]] = []
            for item in raw_diagnostics:
                if not isinstance(item, dict):
                    source_errors.append({"code": None, "message": "invalid diagnostic object"})
                    continue
                severity = str(item.get("severity", "ERROR")).upper()
                if severity == "ERROR":
                    source_errors.append(item)
                else:
                    source_warnings.append(item)

            if source_errors:
                diagnostics.append(
                    _new_diag(
                        code=SCC0002_INPUT_DIAGNOSTICS_FAIL_CLOSED,
                        severity="ERROR",
                        message="semantic source diagnostics contain error-level entries",
                        details={
                            "error_count": len(source_errors),
                            "codes": [item.get("code") for item in source_errors],
                        },
                    )
                )

            for item in sorted(
                source_warnings,
                key=lambda row: (
                    str(row.get("path", "")),
                    int(row.get("start_line", 1)) if isinstance(row.get("start_line"), int) else 1,
                    str(row.get("code", "")),
                    str(row.get("message", "")),
                ),
            ):
                carried_input_warnings.append(
                    _new_diag(
                        code=SCC0003_INPUT_DIAGNOSTICS_CARRIED,
                        severity="WARN",
                        message=f"carried source diagnostic: {item.get('code', 'UNKNOWN')}",
                        path=item.get("path") if isinstance(item.get("path"), str) else None,
                        start_line=item.get("start_line")
                        if isinstance(item.get("start_line"), int)
                        else 1,
                        start_column=item.get("start_column")
                        if isinstance(item.get("start_column"), int)
                        else 1,
                        details={
                            "source_diagnostic": _canonical_clone(item),
                        },
                    )
                )

    diagnostics.extend(carried_input_warnings)

    initial_state: dict[str, Any] = {
        "semantic_source": semantic_source_payload
        if isinstance(semantic_source_payload, dict)
        else {},
        "semantic_source_diagnostics": semantic_source_diagnostics_payload
        if isinstance(semantic_source_diagnostics_payload, dict)
        else {},
    }

    final_state, pass_entries = _run_pass_pipeline(
        initial_state=initial_state, diagnostics=diagnostics
    )

    diagnostics = _sort_diagnostics(diagnostics)
    diagnostics_payload = _build_diagnostics_payload(diagnostics=diagnostics)
    pass_manifest_payload = _build_pass_manifest_payload(entries=pass_entries)

    commitments_ir_payload = (
        final_state.get("commitments_ir")
        if isinstance(final_state.get("commitments_ir"), dict)
        else None
    )

    has_error = any(item.severity == "ERROR" for item in diagnostics)
    success = (not has_error) and commitments_ir_payload is not None

    surface_snapshot_payload: dict[str, Any] | None = None
    surface_diff_payload: dict[str, Any] | None = None
    evidence_manifest_payload: dict[str, Any] | None = None
    pr_splits_markdown: str | None = None
    if success and commitments_ir_payload is not None:
        (
            surface_snapshot_payload,
            surface_diff_payload,
            evidence_manifest_payload,
            pr_splits_markdown,
        ) = _build_v41_surface_artifacts(
            root=root,
            commitments_ir_payload=commitments_ir_payload,
            diagnostics_payload=diagnostics_payload,
            pass_manifest_payload=pass_manifest_payload,
            diagnostics=diagnostics,
        )
        diagnostics = _sort_diagnostics(diagnostics)
        diagnostics_payload = _build_diagnostics_payload(diagnostics=diagnostics)
        has_error = any(item.severity == "ERROR" for item in diagnostics)
        success = (
            (not has_error)
            and commitments_ir_payload is not None
            and surface_snapshot_payload is not None
            and surface_diff_payload is not None
            and evidence_manifest_payload is not None
            and pr_splits_markdown is not None
        )

    if write_outputs:
        if not had_existing_v40_inputs:
            diagnostics_output_path.parent.mkdir(parents=True, exist_ok=True)
            diagnostics_output_path.write_bytes(_serialize_payload(diagnostics_payload))

            pass_manifest_output_path.parent.mkdir(parents=True, exist_ok=True)
            pass_manifest_output_path.write_bytes(_serialize_payload(pass_manifest_payload))

            if commitments_ir_payload is not None:
                commitments_ir_output_path.parent.mkdir(parents=True, exist_ok=True)
                commitments_ir_output_path.write_bytes(_serialize_payload(commitments_ir_payload))

        if (
            success
            and surface_snapshot_payload is not None
            and surface_diff_payload is not None
            and evidence_manifest_payload is not None
            and pr_splits_markdown is not None
        ):
            surface_snapshot_output_path.parent.mkdir(parents=True, exist_ok=True)
            surface_snapshot_output_path.write_bytes(_serialize_payload(surface_snapshot_payload))

            surface_diff_output_path.parent.mkdir(parents=True, exist_ok=True)
            surface_diff_output_path.write_bytes(_serialize_payload(surface_diff_payload))

            evidence_manifest_output_path.parent.mkdir(parents=True, exist_ok=True)
            evidence_manifest_output_path.write_bytes(_serialize_payload(evidence_manifest_payload))

            pr_splits_output_path.parent.mkdir(parents=True, exist_ok=True)
            pr_splits_output_path.write_text(pr_splits_markdown, encoding="utf-8")

    return CompileResult(
        success=success,
        commitments_ir_payload=commitments_ir_payload if success else None,
        diagnostics_payload=diagnostics_payload,
        pass_manifest_payload=pass_manifest_payload,
        surface_snapshot_payload=surface_snapshot_payload if success else None,
        surface_diff_payload=surface_diff_payload if success else None,
        evidence_manifest_payload=evidence_manifest_payload if success else None,
        pr_splits_markdown=pr_splits_markdown if success else None,
        commitments_ir_output_path=commitments_ir_output_path,
        diagnostics_output_path=diagnostics_output_path,
        pass_manifest_output_path=pass_manifest_output_path,
        surface_snapshot_output_path=surface_snapshot_output_path,
        surface_diff_output_path=surface_diff_output_path,
        evidence_manifest_output_path=evidence_manifest_output_path,
        pr_splits_output_path=pr_splits_output_path,
    )


def assert_artifacts_clean(
    *,
    semantic_source_path: str = _DEFAULT_INPUT_SEMANTIC_SOURCE,
    semantic_source_diagnostics_path: str = _DEFAULT_INPUT_SEMANTIC_DIAGNOSTICS,
    repo_root_path: Path | None = None,
    ) -> None:
    result = compile_semantic_compiler(
        semantic_source_path=semantic_source_path,
        semantic_source_diagnostics_path=semantic_source_diagnostics_path,
        repo_root_path=repo_root_path,
        write_outputs=False,
    )

    if (
        not result.success
        or result.commitments_ir_payload is None
        or result.surface_snapshot_payload is None
        or result.surface_diff_payload is None
        or result.evidence_manifest_payload is None
        or result.pr_splits_markdown is None
    ):
        raise RuntimeError(canonical_json(result.diagnostics_payload))

    expected_ir = _serialize_payload(result.commitments_ir_payload)
    expected_diagnostics = _serialize_payload(result.diagnostics_payload)
    expected_pass_manifest = _serialize_payload(result.pass_manifest_payload)
    expected_surface_snapshot = _serialize_payload(result.surface_snapshot_payload)
    expected_surface_diff = _serialize_payload(result.surface_diff_payload)
    expected_evidence_manifest = _serialize_payload(result.evidence_manifest_payload)
    expected_pr_splits = result.pr_splits_markdown.encode("utf-8")

    if not result.commitments_ir_output_path.is_file():
        raise RuntimeError(
            f"missing generated commitments ir artifact: "
            f"{result.commitments_ir_output_path.as_posix()}"
        )
    if not result.diagnostics_output_path.is_file():
        raise RuntimeError(
            f"missing generated compiler diagnostics artifact: "
            f"{result.diagnostics_output_path.as_posix()}"
        )
    if not result.pass_manifest_output_path.is_file():
        raise RuntimeError(
            f"missing generated pass manifest artifact: "
            f"{result.pass_manifest_output_path.as_posix()}"
        )
    if not result.surface_snapshot_output_path.is_file():
        raise RuntimeError(
            f"missing generated surface snapshot artifact: "
            f"{result.surface_snapshot_output_path.as_posix()}"
        )
    if not result.surface_diff_output_path.is_file():
        raise RuntimeError(
            f"missing generated surface diff artifact: "
            f"{result.surface_diff_output_path.as_posix()}"
        )
    if not result.evidence_manifest_output_path.is_file():
        raise RuntimeError(
            f"missing generated evidence manifest artifact: "
            f"{result.evidence_manifest_output_path.as_posix()}"
        )
    if not result.pr_splits_output_path.is_file():
        raise RuntimeError(
            f"missing generated pr splits artifact: "
            f"{result.pr_splits_output_path.as_posix()}"
        )

    observed_ir = result.commitments_ir_output_path.read_bytes()
    observed_diagnostics = result.diagnostics_output_path.read_bytes()
    observed_pass_manifest = result.pass_manifest_output_path.read_bytes()
    observed_surface_snapshot = result.surface_snapshot_output_path.read_bytes()
    observed_surface_diff = result.surface_diff_output_path.read_bytes()
    observed_evidence_manifest = result.evidence_manifest_output_path.read_bytes()
    observed_pr_splits = result.pr_splits_output_path.read_bytes()

    if observed_ir != expected_ir:
        raise RuntimeError(
            "generated commitments ir artifact is out of date: "
            f"{result.commitments_ir_output_path.as_posix()}"
        )
    if observed_diagnostics != expected_diagnostics:
        raise RuntimeError(
            "generated compiler diagnostics artifact is out of date: "
            f"{result.diagnostics_output_path.as_posix()}"
        )
    if observed_pass_manifest != expected_pass_manifest:
        raise RuntimeError(
            "generated pass manifest artifact is out of date: "
            f"{result.pass_manifest_output_path.as_posix()}"
        )
    if observed_surface_snapshot != expected_surface_snapshot:
        raise RuntimeError(
            "generated surface snapshot artifact is out of date: "
            f"{result.surface_snapshot_output_path.as_posix()}"
        )
    if observed_surface_diff != expected_surface_diff:
        raise RuntimeError(
            "generated surface diff artifact is out of date: "
            f"{result.surface_diff_output_path.as_posix()}"
        )
    if observed_evidence_manifest != expected_evidence_manifest:
        raise RuntimeError(
            "generated evidence manifest artifact is out of date: "
            f"{result.evidence_manifest_output_path.as_posix()}"
        )
    if observed_pr_splits != expected_pr_splits:
        raise RuntimeError(
            "generated pr splits artifact is out of date: "
            f"{result.pr_splits_output_path.as_posix()}"
        )


def _build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="adeu_semantic_compiler.compile",
        description=(
            "Compile deterministic semantic compiler artifacts "
            "(v40 core outputs + v41 surface governance outputs)."
        ),
    )
    parser.add_argument(
        "--semantic-source",
        default=_DEFAULT_INPUT_SEMANTIC_SOURCE,
        help="Repository-relative semantic source artifact path.",
    )
    parser.add_argument(
        "--semantic-source-diagnostics",
        default=_DEFAULT_INPUT_SEMANTIC_DIAGNOSTICS,
        help="Repository-relative semantic source diagnostics artifact path.",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_arg_parser()
    args = parser.parse_args(argv)

    result = compile_semantic_compiler(
        semantic_source_path=args.semantic_source,
        semantic_source_diagnostics_path=args.semantic_source_diagnostics,
        write_outputs=True,
    )
    if result.success:
        return 0

    sys.stderr.write(canonical_json(result.diagnostics_payload) + "\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
