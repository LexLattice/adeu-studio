from __future__ import annotations

import json
from pathlib import Path

from adeu_ir import AdeuIR
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, apply_ambiguity_option, check


def _load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def test_apply_ambiguity_option_patch_fixture() -> None:
    root = repo_root(anchor=Path(__file__))
    fixture_dir = root / "examples" / "fixtures" / "apply_ambiguity_patch"

    before_payload = _load_json(fixture_dir / "proposals" / "var1.json")
    before_ir = AdeuIR.model_validate(before_payload)

    patched = apply_ambiguity_option(
        before_ir,
        ambiguity_id="amb_time_1",
        option_id="opt_set_time",
    )

    expected_ir_payload = _load_json(fixture_dir / "expected" / "apply" / "patched_ir.json")
    expected_ir = AdeuIR.model_validate(expected_ir_payload)

    actual_ir = patched.model_dump(mode="json", exclude_none=True, exclude_defaults=True)
    expected_ir_dump = expected_ir.model_dump(mode="json", exclude_none=True, exclude_defaults=True)
    assert actual_ir == expected_ir_dump

    report = check(patched, mode=KernelMode.LAX)
    expected_report = _load_json(fixture_dir / "expected" / "apply" / "patched_report.json")
    actual_report = report.model_dump(mode="json", exclude_none=True)
    assert actual_report == expected_report


def test_apply_ambiguity_option_variant_fixture() -> None:
    root = repo_root(anchor=Path(__file__))
    fixture_dir = root / "examples" / "fixtures" / "variant_backed_ambiguity_option"

    base_payload = _load_json(fixture_dir / "proposals" / "var1.json")
    variant_payload = _load_json(fixture_dir / "proposals" / "var2.json")
    base_ir = AdeuIR.model_validate(base_payload)
    variant_ir = AdeuIR.model_validate(variant_payload)

    applied = apply_ambiguity_option(
        base_ir,
        ambiguity_id="amb_variant_1",
        option_id="opt_use_variant",
        variants_by_id={variant_ir.ir_id: variant_ir},
    )

    assert (
        applied.model_dump(mode="json", exclude_none=True)
        == variant_ir.model_dump(mode="json", exclude_none=True)
    )
