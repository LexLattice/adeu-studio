from __future__ import annotations

import copy
import json
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from typing import Any

from adeu_ir.models import JsonPatchOp
from pydantic import ValidationError

from .models import ConceptIR

DEFAULT_ALLOWED_PREFIXES = (
    "/claims",
    "/links",
    "/senses",
    "/terms",
    "/ambiguity",
)


@dataclass(frozen=True)
class ConceptPatchError:
    op_index: int
    path: str
    code: str
    message: str


@dataclass(frozen=True)
class ConceptPatchValidationError(Exception):
    errors: tuple[ConceptPatchError, ...]


def _issue(
    *,
    op_index: int,
    path: str,
    code: str,
    message: str,
) -> ConceptPatchError:
    return ConceptPatchError(
        op_index=op_index,
        path=path,
        code=code,
        message=message,
    )


def _raise_issue(
    *,
    op_index: int,
    path: str,
    code: str,
    message: str,
) -> None:
    raise ConceptPatchValidationError(
        errors=(
            _issue(
                op_index=op_index,
                path=path,
                code=code,
                message=message,
            ),
        )
    )


def _encode_patch_size_bytes(patch_ops: Iterable[JsonPatchOp]) -> int:
    payload = [
        op.model_dump(mode="json", by_alias=True, exclude_none=True) for op in patch_ops
    ]
    return len(json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8"))


def _allowed_path(path: str, *, allowed_prefixes: tuple[str, ...]) -> bool:
    for prefix in allowed_prefixes:
        if path == prefix or path.startswith(prefix + "/"):
            return True
    return False


def _parse_pointer(path: str, *, op_index: int) -> list[str]:
    if not path.startswith("/"):
        _raise_issue(
            op_index=op_index,
            path=path,
            code="PATCH_PATH_INVALID",
            message="json pointer path must start with '/'",
        )
    parts = path.split("/")[1:]
    return [part.replace("~1", "/").replace("~0", "~") for part in parts]


def _resolve_parent(doc: Any, path: str, *, op_index: int) -> tuple[Any, str]:
    parts = _parse_pointer(path, op_index=op_index)
    if not parts:
        _raise_issue(
            op_index=op_index,
            path=path,
            code="PATCH_PATH_INVALID",
            message="patching the document root is not allowed",
        )

    cur: Any = doc
    for seg in parts[:-1]:
        if isinstance(cur, dict):
            if seg not in cur:
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code="PATCH_TARGET_MISSING",
                    message="path does not exist",
                )
            cur = cur[seg]
            continue
        if isinstance(cur, list):
            try:
                idx = int(seg)
            except ValueError as exc:
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code="PATCH_PATH_INVALID",
                    message="list segment must be an int index",
                )
                raise AssertionError("unreachable") from exc
            if idx < 0 or idx >= len(cur):
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code="PATCH_TARGET_MISSING",
                    message="list index out of range",
                )
            cur = cur[idx]
            continue
        _raise_issue(
            op_index=op_index,
            path=path,
            code="PATCH_PATH_INVALID",
            message="path traversal hit a non-container",
        )

    return cur, parts[-1]


def _get_value(doc: Any, path: str, *, op_index: int) -> Any:
    parts = _parse_pointer(path, op_index=op_index)
    cur: Any = doc
    for seg in parts:
        if isinstance(cur, dict):
            if seg not in cur:
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code="PATCH_TARGET_MISSING",
                    message="path does not exist",
                )
            cur = cur[seg]
            continue
        if isinstance(cur, list):
            try:
                idx = int(seg)
            except ValueError as exc:
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code="PATCH_PATH_INVALID",
                    message="list segment must be an int index",
                )
                raise AssertionError("unreachable") from exc
            if idx < 0 or idx >= len(cur):
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code="PATCH_TARGET_MISSING",
                    message="list index out of range",
                )
            cur = cur[idx]
            continue
        _raise_issue(
            op_index=op_index,
            path=path,
            code="PATCH_PATH_INVALID",
            message="path traversal hit a non-container",
        )
    return cur


def _sorted_errors(errors: list[ConceptPatchError]) -> tuple[ConceptPatchError, ...]:
    return tuple(
        sorted(
            errors,
            key=lambda err: (err.op_index, err.path, err.code),
        )
    )


def _raise_errors(errors: list[ConceptPatchError]) -> None:
    if not errors:
        return
    raise ConceptPatchValidationError(errors=_sorted_errors(errors))


def _collect_reference_integrity_errors(concept: ConceptIR) -> list[ConceptPatchError]:
    errors: list[ConceptPatchError] = []
    term_ids = {term.id for term in concept.terms}
    sense_ids = {sense.id for sense in concept.senses}
    sense_term_by_id = {sense.id: sense.term_id for sense in concept.senses}

    for idx, sense in enumerate(concept.senses):
        if sense.term_id not in term_ids:
            errors.append(
                _issue(
                    op_index=-1,
                    path=f"/senses/{idx}/term_id",
                    code="REFERENCE_INTEGRITY",
                    message=f"sense references unknown term_id {sense.term_id!r}",
                )
            )

    for idx, claim in enumerate(concept.claims):
        if claim.sense_id not in sense_ids:
            errors.append(
                _issue(
                    op_index=-1,
                    path=f"/claims/{idx}/sense_id",
                    code="REFERENCE_INTEGRITY",
                    message=f"claim references unknown sense_id {claim.sense_id!r}",
                )
            )

    for idx, link in enumerate(concept.links):
        if link.src_sense_id not in sense_ids:
            errors.append(
                _issue(
                    op_index=-1,
                    path=f"/links/{idx}/src_sense_id",
                    code="REFERENCE_INTEGRITY",
                    message=f"link source sense_id unresolved: {link.src_sense_id!r}",
                )
            )
        if link.dst_sense_id not in sense_ids:
            errors.append(
                _issue(
                    op_index=-1,
                    path=f"/links/{idx}/dst_sense_id",
                    code="REFERENCE_INTEGRITY",
                    message=f"link destination sense_id unresolved: {link.dst_sense_id!r}",
                )
            )

    for idx, ambiguity in enumerate(concept.ambiguity):
        if ambiguity.term_id not in term_ids:
            errors.append(
                _issue(
                    op_index=-1,
                    path=f"/ambiguity/{idx}/term_id",
                    code="REFERENCE_INTEGRITY",
                    message=f"ambiguity references unknown term_id {ambiguity.term_id!r}",
                )
            )

        option_set = set(ambiguity.options)
        if len(option_set) != len(ambiguity.options):
            errors.append(
                _issue(
                    op_index=-1,
                    path=f"/ambiguity/{idx}/options",
                    code="REFERENCE_INTEGRITY",
                    message="ambiguity options must be unique",
                )
            )

        for option_idx, sense_id in enumerate(ambiguity.options):
            if sense_id not in sense_ids:
                errors.append(
                    _issue(
                        op_index=-1,
                        path=f"/ambiguity/{idx}/options/{option_idx}",
                        code="REFERENCE_INTEGRITY",
                        message=f"ambiguity option references unknown sense_id {sense_id!r}",
                    )
                )
                continue

            if sense_term_by_id.get(sense_id) != ambiguity.term_id:
                errors.append(
                    _issue(
                        op_index=-1,
                        path=f"/ambiguity/{idx}/options/{option_idx}",
                        code="REFERENCE_INTEGRITY",
                        message=(
                            "ambiguity options must reference senses belonging to "
                            "the ambiguity term"
                        ),
                    )
                )

        detail_keys = set(ambiguity.option_details_by_id.keys())
        if not detail_keys.issubset(option_set):
            extra = sorted(detail_keys - option_set)
            errors.append(
                _issue(
                    op_index=-1,
                    path=f"/ambiguity/{idx}/option_details_by_id",
                    code="REFERENCE_INTEGRITY",
                    message=(
                        "option_details_by_id keys must be a subset of ambiguity options "
                        f"(extra={extra})"
                    ),
                )
            )

        for option_key in sorted(detail_keys):
            option = ambiguity.option_details_by_id[option_key]
            if option.option_id != option_key:
                errors.append(
                    _issue(
                        op_index=-1,
                        path=f"/ambiguity/{idx}/option_details_by_id/{option_key}/option_id",
                        code="REFERENCE_INTEGRITY",
                        message=(
                            "option_details_by_id key must match AmbiguityOption.option_id "
                            f"(got key={option_key!r}, option_id={option.option_id!r})"
                        ),
                    )
                )

        if ambiguity.option_labels_by_id is not None:
            label_keys = set(ambiguity.option_labels_by_id.keys())
            if not label_keys.issubset(option_set):
                extra = sorted(label_keys - option_set)
                errors.append(
                    _issue(
                        op_index=-1,
                        path=f"/ambiguity/{idx}/option_labels_by_id",
                        code="REFERENCE_INTEGRITY",
                        message=(
                            "option_labels_by_id keys must be a subset of ambiguity options "
                            f"(extra={extra})"
                        ),
                    )
                )

    return errors


def apply_concept_json_patch(
    concept: ConceptIR,
    patch_ops: list[JsonPatchOp],
    *,
    allowed_prefixes: tuple[str, ...] = DEFAULT_ALLOWED_PREFIXES,
    max_ops: int = 50,
    max_bytes: int = 20_000,
) -> ConceptIR:
    errors: list[ConceptPatchError] = []
    if len(patch_ops) > max_ops:
        errors.append(
            _issue(
                op_index=-1,
                path="/ambiguity",
                code="PATCH_TOO_LARGE",
                message=f"patch too large: {len(patch_ops)} ops (max {max_ops})",
            )
        )
        _raise_errors(errors)

    size_bytes = _encode_patch_size_bytes(patch_ops)
    if size_bytes > max_bytes:
        errors.append(
            _issue(
                op_index=-1,
                path="/ambiguity",
                code="PATCH_TOO_LARGE",
                message=f"patch too large: {size_bytes} bytes (max {max_bytes})",
            )
        )
        _raise_errors(errors)

    doc = copy.deepcopy(concept.model_dump(mode="json", by_alias=True))

    for op_index, op in enumerate(patch_ops):
        if op.op in ("move", "copy"):
            errors.append(
                _issue(
                    op_index=op_index,
                    path=op.path,
                    code="PATCH_OP_UNSUPPORTED",
                    message=f"op {op.op!r} is not allowed",
                )
            )
            continue

        if not _allowed_path(op.path, allowed_prefixes=allowed_prefixes):
            errors.append(
                _issue(
                    op_index=op_index,
                    path=op.path,
                    code="PATCH_PATH_NOT_ALLOWED",
                    message="path is not allowed by sandbox",
                )
            )
            continue

        if op.op in ("add", "replace", "test") and op.value is None:
            errors.append(
                _issue(
                    op_index=op_index,
                    path=op.path,
                    code="PATCH_VALUE_REQUIRED",
                    message=f"op {op.op!r} requires value",
                )
            )
            continue

        try:
            if op.op in ("remove", "replace", "test"):
                _get_value(doc, op.path, op_index=op_index)

            if op.op == "test":
                cur = _get_value(doc, op.path, op_index=op_index)
                if cur != op.value:
                    errors.append(
                        _issue(
                            op_index=op_index,
                            path=op.path,
                            code="PATCH_TEST_FAILED",
                            message="test op failed (value mismatch)",
                        )
                    )
                continue

            parent, last = _resolve_parent(doc, op.path, op_index=op_index)

            if op.op == "add":
                if isinstance(parent, dict):
                    parent[last] = op.value
                    continue
                if isinstance(parent, list):
                    if last == "-":
                        parent.append(op.value)
                        continue
                    try:
                        idx = int(last)
                    except ValueError:
                        errors.append(
                            _issue(
                                op_index=op_index,
                                path=op.path,
                                code="PATCH_PATH_INVALID",
                                message="list segment must be an int index or '-'",
                            )
                        )
                        continue
                    if idx < 0 or idx > len(parent):
                        errors.append(
                            _issue(
                                op_index=op_index,
                                path=op.path,
                                code="PATCH_TARGET_MISSING",
                                message="list index out of range for add",
                            )
                        )
                        continue
                    parent.insert(idx, op.value)
                    continue
                errors.append(
                    _issue(
                        op_index=op_index,
                        path=op.path,
                        code="PATCH_PATH_INVALID",
                        message="add parent is not a container",
                    )
                )
                continue

            if op.op == "replace":
                if isinstance(parent, dict):
                    if last not in parent:
                        errors.append(
                            _issue(
                                op_index=op_index,
                                path=op.path,
                                code="PATCH_TARGET_MISSING",
                                message="replace target does not exist",
                            )
                        )
                        continue
                    parent[last] = op.value
                    continue
                if isinstance(parent, list):
                    try:
                        idx = int(last)
                    except ValueError:
                        errors.append(
                            _issue(
                                op_index=op_index,
                                path=op.path,
                                code="PATCH_PATH_INVALID",
                                message="list segment must be an int index",
                            )
                        )
                        continue
                    if idx < 0 or idx >= len(parent):
                        errors.append(
                            _issue(
                                op_index=op_index,
                                path=op.path,
                                code="PATCH_TARGET_MISSING",
                                message="list index out of range",
                            )
                        )
                        continue
                    parent[idx] = op.value
                    continue
                errors.append(
                    _issue(
                        op_index=op_index,
                        path=op.path,
                        code="PATCH_PATH_INVALID",
                        message="replace parent is not a container",
                    )
                )
                continue

            if op.op == "remove":
                if isinstance(parent, dict):
                    if last not in parent:
                        errors.append(
                            _issue(
                                op_index=op_index,
                                path=op.path,
                                code="PATCH_TARGET_MISSING",
                                message="remove target does not exist",
                            )
                        )
                        continue
                    del parent[last]
                    continue
                if isinstance(parent, list):
                    try:
                        idx = int(last)
                    except ValueError:
                        errors.append(
                            _issue(
                                op_index=op_index,
                                path=op.path,
                                code="PATCH_PATH_INVALID",
                                message="list segment must be an int index",
                            )
                        )
                        continue
                    if idx < 0 or idx >= len(parent):
                        errors.append(
                            _issue(
                                op_index=op_index,
                                path=op.path,
                                code="PATCH_TARGET_MISSING",
                                message="list index out of range",
                            )
                        )
                        continue
                    parent.pop(idx)
                    continue
                errors.append(
                    _issue(
                        op_index=op_index,
                        path=op.path,
                        code="PATCH_PATH_INVALID",
                        message="remove parent is not a container",
                    )
                )
                continue

            errors.append(
                _issue(
                    op_index=op_index,
                    path=op.path,
                    code="PATCH_OP_UNSUPPORTED",
                    message=f"unsupported op: {op.op!r}",
                )
            )
        except ConceptPatchValidationError as exc:
            errors.extend(exc.errors)

    _raise_errors(errors)

    try:
        patched = ConceptIR.model_validate(doc)
    except ValidationError as exc:
        schema_errors: list[ConceptPatchError] = []
        for err in exc.errors():
            loc = err.get("loc", ())
            path = "/" + "/".join(str(part) for part in loc) if loc else "/"
            schema_errors.append(
                _issue(
                    op_index=-1,
                    path=path,
                    code="PATCH_IR_INVALID",
                    message=str(err.get("msg", "patched concept IR failed validation")),
                )
            )
        _raise_errors(schema_errors)
        raise AssertionError("unreachable")

    reference_errors = _collect_reference_integrity_errors(patched)
    _raise_errors(reference_errors)
    return patched


def apply_concept_ambiguity_option(
    concept: ConceptIR,
    *,
    ambiguity_id: str,
    option_id: str,
    variants_by_id: Mapping[str, ConceptIR] | None = None,
) -> ConceptIR:
    ambiguity = next((item for item in concept.ambiguity if item.id == ambiguity_id), None)
    if ambiguity is None:
        _raise_issue(
            op_index=-1,
            path="/ambiguity",
            code="AMBIGUITY_NOT_FOUND",
            message=f"unknown ambiguity id: {ambiguity_id!r}",
        )

    option = ambiguity.option_details_by_id.get(option_id)
    if option is None:
        _raise_issue(
            op_index=-1,
            path=f"/ambiguity/{ambiguity_id}/option_details_by_id",
            code="OPTION_NOT_FOUND",
            message=f"unknown ambiguity option id: {option_id!r}",
        )

    if option.option_id != option_id:
        _raise_issue(
            op_index=-1,
            path=f"/ambiguity/{ambiguity_id}/option_details_by_id/{option_id}/option_id",
            code="OPTION_ID_MISMATCH",
            message=(
                "option_details_by_id key must match AmbiguityOption.option_id "
                f"(got key={option_id!r}, option_id={option.option_id!r})"
            ),
        )

    if option.variant_ir_id is not None:
        if variants_by_id is None:
            _raise_issue(
                op_index=-1,
                path="/ambiguity",
                code="VARIANT_MAPPING_REQUIRED",
                message=(
                    "missing variants_by_id mapping for "
                    f"variant_ir_id: {option.variant_ir_id!r}"
                ),
            )
        variant = variants_by_id.get(option.variant_ir_id)
        if variant is None:
            _raise_issue(
                op_index=-1,
                path="/ambiguity",
                code="VARIANT_NOT_FOUND",
                message=f"unknown variant_ir_id: {option.variant_ir_id!r}",
            )
        return variant

    if not option.patch:
        _raise_issue(
            op_index=-1,
            path=f"/ambiguity/{ambiguity_id}/option_details_by_id/{option_id}/patch",
            code="OPTION_NOT_ACTIONABLE",
            message="patch option must include at least one op",
        )

    return apply_concept_json_patch(concept, option.patch)
