from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json

LINT_SCHEMA = "recursive_coordinate_warning_lint@1"
COORDINATE_SCHEMA = "recursive_schema_coordinate@1"

DEFAULT_DOCS: tuple[str, ...] = (
    "docs/DRAFT_RECURSIVE_COORDINATE_SEED_PLACEMENT_REPORT_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_STRESS_CELL_PLACEMENT_REPORT_v0.md",
)

ALLOWED_PLACEMENT_BASES: tuple[str, ...] = (
    "doctrine_surface",
    "schema_kind_definition",
    "artifact_instance",
    "runtime_kind_definition",
)
ALLOWED_BINDING_DEPTHS: tuple[str, ...] = ("meta", "family", "bounded", "instance")
ALLOWED_FORCE_BANDS: tuple[str, ...] = (
    "observational",
    "interpretive",
    "governing",
    "operative",
)
PROMOTION_FIELD_NAMES: tuple[str, ...] = (
    "promotion_claim",
    "promotion_from_coordinate",
    "promotion_from_force",
    "promotion_basis",
    "promotion_note",
    "promotion_requested",
)
COORDINATE_SCHEMA_FIELD_RE = re.compile(
    rf'"schema"\s*:\s*"{re.escape(COORDINATE_SCHEMA)}"'
)


@dataclass
class LintResult:
    checked_docs: list[str] = field(default_factory=list)
    checked_record_count: int = 0
    warnings: list[dict[str, Any]] = field(default_factory=list)

    def add_doc(self, path: str) -> None:
        self.checked_docs.append(path)

    def add_warning(
        self,
        *,
        code: str,
        doc_path: str,
        block_index: int,
        placement_subject_ref: str | None,
        details: dict[str, Any],
    ) -> None:
        self.warnings.append(
            {
                "code": code,
                "doc_path": doc_path,
                "block_index": block_index,
                "placement_subject_ref": placement_subject_ref,
                "details": details,
            }
        )

    def finalize(self) -> dict[str, Any]:
        return {
            "schema": LINT_SCHEMA,
            "checked_docs": sorted(set(self.checked_docs)),
            "checked_record_count": self.checked_record_count,
            "warning_count": len(self.warnings),
            "warnings": sorted(
                self.warnings,
                key=lambda row: (
                    str(row["code"]),
                    str(row["doc_path"]),
                    int(row["block_index"]),
                    str(row["placement_subject_ref"] or ""),
                    canonical_json(row["details"]),
                ),
            ),
        }


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run a warning-only lint prototype over embedded recursive_schema_coordinate@1 "
            "records in curated markdown pilot reports."
        )
    )
    parser.add_argument(
        "--doc",
        action="append",
        dest="docs",
        default=None,
        help=(
            "Markdown doc to lint. May be repeated. Defaults to the seed and stress-cell "
            "pilot reports."
        ),
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Repository root path. Defaults to discovery from script location.",
    )
    return parser.parse_args(argv)


def _repo_root_from_script() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        git_marker = parent / ".git"
        if git_marker.is_dir() or git_marker.is_file():
            return parent
    raise FileNotFoundError("repository root not found from script location")


def _resolve_doc_path(*, repo_root: Path, value: str) -> Path:
    path = Path(value)
    return path if path.is_absolute() else repo_root / path


def _display_path(*, repo_root: Path, path: Path) -> str:
    try:
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def _extract_json_blocks(text: str) -> list[str]:
    lines = text.splitlines()
    blocks: list[str] = []
    index = 0
    while index < len(lines):
        if lines[index].strip() != "```json":
            index += 1
            continue
        index += 1
        block_lines: list[str] = []
        while index < len(lines) and lines[index].strip() != "```":
            block_lines.append(lines[index])
            index += 1
        blocks.append("\n".join(block_lines).strip())
        if index < len(lines):
            index += 1
    return blocks


def _occupancy_status(*, binding_depth: str, institutional_force: str) -> str:
    if binding_depth == "meta" and institutional_force == "operative":
        return "reserved"
    if binding_depth in {"family", "bounded"} and institutional_force == "operative":
        return "invalid"
    if binding_depth == "instance" and institutional_force == "interpretive":
        return "lawful_rare"
    return "lawful_core"


def _iter_coordinate_records(*, doc_path: Path) -> list[tuple[int, dict[str, Any]]]:
    text = doc_path.read_text(encoding="utf-8")
    records: list[tuple[int, dict[str, Any]]] = []
    for block_index, block_text in enumerate(_extract_json_blocks(text), start=1):
        try:
            payload = json.loads(block_text)
        except json.JSONDecodeError as exc:
            if _looks_like_coordinate_record_block(block_text):
                message = (
                    f"{doc_path}: invalid {COORDINATE_SCHEMA} json block at "
                    f"index {block_index}: {exc}"
                )
                raise ValueError(
                    message
                ) from exc
            continue
        if not isinstance(payload, dict):
            continue
        if payload.get("schema") == COORDINATE_SCHEMA:
            records.append((block_index, payload))
    return records


def _looks_like_coordinate_record_block(block_text: str) -> bool:
    return COORDINATE_SCHEMA_FIELD_RE.search(block_text) is not None


def _warn_missing_placement_basis(
    *,
    payload: dict[str, Any],
    doc_path: str,
    block_index: int,
    result: LintResult,
) -> None:
    placement_basis = payload.get("placement_basis")
    if isinstance(placement_basis, str) and placement_basis in ALLOWED_PLACEMENT_BASES:
        return
    result.add_warning(
        code="MISSING_PLACEMENT_BASIS",
        doc_path=doc_path,
        block_index=block_index,
        placement_subject_ref=_placement_subject_ref(payload),
        details={
            "expected_allowed_values": list(ALLOWED_PLACEMENT_BASES),
            "actual": placement_basis,
        },
    )


def _warn_missing_required_coverage_scope(
    *,
    payload: dict[str, Any],
    doc_path: str,
    block_index: int,
    result: LintResult,
) -> None:
    coordinate = payload.get("coordinate")
    if not isinstance(coordinate, dict):
        return
    binding_depth = coordinate.get("binding_depth")
    force = coordinate.get("institutional_force")
    if binding_depth != "meta" or force not in {"observational", "interpretive"}:
        return
    if isinstance(payload.get("coverage_scope"), dict):
        return
    result.add_warning(
        code="MISSING_REQUIRED_COVERAGE_SCOPE",
        doc_path=doc_path,
        block_index=block_index,
        placement_subject_ref=_placement_subject_ref(payload),
        details={
            "binding_depth": binding_depth,
            "institutional_force": force,
        },
    )


def _warn_invalid_occupancy(
    *,
    payload: dict[str, Any],
    doc_path: str,
    block_index: int,
    result: LintResult,
) -> None:
    coordinate = payload.get("coordinate")
    if not isinstance(coordinate, dict):
        return
    binding_depth = coordinate.get("binding_depth")
    force = coordinate.get("institutional_force")
    if binding_depth not in ALLOWED_BINDING_DEPTHS or force not in ALLOWED_FORCE_BANDS:
        return
    status = _occupancy_status(binding_depth=binding_depth, institutional_force=force)
    if status != "invalid":
        return
    result.add_warning(
        code="INVALID_OCCUPANCY",
        doc_path=doc_path,
        block_index=block_index,
        placement_subject_ref=_placement_subject_ref(payload),
        details={
            "binding_depth": binding_depth,
            "institutional_force": force,
            "occupancy_status": status,
        },
    )


def _warn_unresolved_dominant_force_band(
    *,
    payload: dict[str, Any],
    doc_path: str,
    block_index: int,
    result: LintResult,
) -> None:
    coordinate = payload.get("coordinate")
    force_profile = payload.get("force_profile")
    binding_depth: str | None = None
    coordinate_force: str | None = None
    if isinstance(coordinate, dict):
        binding_depth = coordinate.get("binding_depth")
        coordinate_force = coordinate.get("institutional_force")
    if not isinstance(force_profile, dict):
        result.add_warning(
            code="UNRESOLVED_DOMINANT_FORCE_BAND",
            doc_path=doc_path,
            block_index=block_index,
            placement_subject_ref=_placement_subject_ref(payload),
            details={"reason": "missing_force_profile"},
        )
        return
    dominant_band = force_profile.get("dominant_band")
    support_qualifiers = force_profile.get("support_qualifiers")
    if dominant_band not in ALLOWED_FORCE_BANDS:
        result.add_warning(
            code="UNRESOLVED_DOMINANT_FORCE_BAND",
            doc_path=doc_path,
            block_index=block_index,
            placement_subject_ref=_placement_subject_ref(payload),
            details={"reason": "invalid_dominant_band", "actual": dominant_band},
        )
        return
    if not isinstance(support_qualifiers, list) or not all(
        isinstance(item, str) for item in support_qualifiers
    ):
        result.add_warning(
            code="UNRESOLVED_DOMINANT_FORCE_BAND",
            doc_path=doc_path,
            block_index=block_index,
            placement_subject_ref=_placement_subject_ref(payload),
            details={"reason": "invalid_support_qualifiers"},
        )
        return
    if coordinate_force in ALLOWED_FORCE_BANDS and dominant_band != coordinate_force:
        result.add_warning(
            code="UNRESOLVED_DOMINANT_FORCE_BAND",
            doc_path=doc_path,
            block_index=block_index,
            placement_subject_ref=_placement_subject_ref(payload),
            details={
                "reason": "dominant_band_coordinate_mismatch",
                "coordinate_institutional_force": coordinate_force,
                "dominant_band": dominant_band,
                "binding_depth": binding_depth,
            },
        )


def _warn_promotion_without_witness(
    *,
    payload: dict[str, Any],
    doc_path: str,
    block_index: int,
    result: LintResult,
) -> None:
    has_explicit_promotion_claim = any(
        field_name in payload for field_name in PROMOTION_FIELD_NAMES
    )
    if not has_explicit_promotion_claim:
        return
    derivation_witness_refs = payload.get("derivation_witness_refs")
    if isinstance(derivation_witness_refs, list) and derivation_witness_refs:
        return
    result.add_warning(
        code="PROMOTION_WITHOUT_WITNESS",
        doc_path=doc_path,
        block_index=block_index,
        placement_subject_ref=_placement_subject_ref(payload),
        details={
            "promotion_fields": sorted(
                field_name for field_name in PROMOTION_FIELD_NAMES if field_name in payload
            )
        },
    )


def _placement_subject_ref(payload: dict[str, Any]) -> str | None:
    value = payload.get("placement_subject_ref")
    return value if isinstance(value, str) and value else None


def lint_docs(*, repo_root: Path, docs: list[str]) -> dict[str, Any]:
    result = LintResult()
    for doc_value in docs:
        path = _resolve_doc_path(repo_root=repo_root, value=doc_value)
        if not path.is_file():
            raise FileNotFoundError(f"coordinate lint doc not found: {path}")
        display_path = _display_path(repo_root=repo_root, path=path)
        result.add_doc(display_path)
        records = _iter_coordinate_records(doc_path=path)
        result.checked_record_count += len(records)
        for block_index, payload in records:
            _warn_missing_placement_basis(
                payload=payload,
                doc_path=display_path,
                block_index=block_index,
                result=result,
            )
            _warn_missing_required_coverage_scope(
                payload=payload,
                doc_path=display_path,
                block_index=block_index,
                result=result,
            )
            _warn_invalid_occupancy(
                payload=payload,
                doc_path=display_path,
                block_index=block_index,
                result=result,
            )
            _warn_unresolved_dominant_force_band(
                payload=payload,
                doc_path=display_path,
                block_index=block_index,
                result=result,
            )
            _warn_promotion_without_witness(
                payload=payload,
                doc_path=display_path,
                block_index=block_index,
                result=result,
            )
    return result.finalize()


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    repo_root = args.repo_root or _repo_root_from_script()
    docs = list(args.docs or DEFAULT_DOCS)
    payload = lint_docs(repo_root=repo_root, docs=docs)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
