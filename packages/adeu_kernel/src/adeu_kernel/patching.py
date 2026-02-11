from __future__ import annotations

import copy
from collections.abc import Mapping
from dataclasses import dataclass

from adeu_ir import AdeuIR, CheckReason, ReasonCode, ReasonSeverity
from adeu_ir.models import Ambiguity, AmbiguityOption, JsonPatchOp
from adeu_patch_core import PatchCoreValidationError, apply_patch_ops, encode_patch_size_bytes
from pydantic import ValidationError

DEFAULT_ALLOWED_PREFIXES = (
    "/D_norm/statements",
    "/D_norm/exceptions",
    "/O/entities",
    "/O/definitions",
    "/bridges",
    "/ambiguity",
    "/context/time_eval",
)


@dataclass(frozen=True)
class PatchValidationError(Exception):
    reason: CheckReason


def _err(message: str, *, json_path: str | None = None) -> PatchValidationError:
    return PatchValidationError(
        reason=CheckReason(
            code=ReasonCode.AMBIGUITY_OPTION_INVALID,
            severity=ReasonSeverity.ERROR,
            message=message,
            json_path=json_path,
        )
    )


def apply_json_patch(
    ir: AdeuIR,
    patch_ops: list[JsonPatchOp],
    *,
    allowed_prefixes: tuple[str, ...] = DEFAULT_ALLOWED_PREFIXES,
    max_ops: int = 50,
    max_bytes: int = 20_000,
) -> AdeuIR:
    """
    Applies a sandboxed subset of JSON Patch to an ADEU IR.

    Fail-closed semantics: if any op is invalid or would produce an invalid IR,
    no output is returned.
    """
    if len(patch_ops) > max_ops:
        raise _err(f"patch too large: {len(patch_ops)} ops (max {max_ops})")

    size_bytes = encode_patch_size_bytes(patch_ops)
    if size_bytes > max_bytes:
        raise _err(f"patch too large: {size_bytes} bytes (max {max_bytes})")

    doc = copy.deepcopy(ir.model_dump(mode="json", by_alias=True))

    try:
        apply_patch_ops(
            doc,
            patch_ops,
            allowed_prefixes=allowed_prefixes,
            disallowed_ops=frozenset({"move", "copy"}),
            value_policy="non_null",
            collect_errors=False,
        )
    except PatchCoreValidationError as exc:
        error = exc.errors[0]
        raise _err(error.message, json_path=error.path) from exc

    try:
        return AdeuIR.model_validate(doc)
    except ValidationError as exc:
        raise _err(f"patched IR did not validate: {exc}") from exc


def apply_ambiguity_option_patch(ir: AdeuIR, *, option: AmbiguityOption) -> AdeuIR:
    if option.variant_ir_id is not None:
        raise _err("variant_ir_id options must be applied by loading that variant", json_path=None)
    if not option.patch:
        raise _err("patch option must include at least one op", json_path=None)
    return apply_json_patch(ir, option.patch)


def apply_ambiguity_option(
    ir: AdeuIR,
    *,
    ambiguity_id: str,
    option_id: str,
    variants_by_id: Mapping[str, AdeuIR] | None = None,
) -> AdeuIR:
    ambiguity: Ambiguity | None = next((a for a in ir.ambiguity if a.id == ambiguity_id), None)
    if ambiguity is None:
        raise _err(f"unknown ambiguity id: {ambiguity_id!r}", json_path="/ambiguity")

    option: AmbiguityOption | None = next(
        (o for o in ambiguity.options if o.option_id == option_id), None
    )
    if option is None:
        raise _err(
            f"unknown ambiguity option id: {option_id!r}",
            json_path=f"/ambiguity/{ambiguity_id}/options",
        )

    if option.variant_ir_id is not None:
        if variants_by_id is None:
            raise _err(
                f"missing variants_by_id mapping for variant_ir_id: {option.variant_ir_id!r}",
                json_path="/ambiguity",
            )
        variant = variants_by_id.get(option.variant_ir_id)
        if variant is None:
            raise _err(
                f"unknown variant_ir_id: {option.variant_ir_id!r}",
                json_path="/ambiguity",
            )
        return variant

    return apply_ambiguity_option_patch(ir, option=option)
