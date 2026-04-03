from __future__ import annotations

import json
from pathlib import Path

from adeu_semantic_forms_v0 import (
    build_reference_repo_policy_work_profile,
    build_reference_transform_contract,
    parse_nl_to_semantic_form,
    transform_normal_form_to_binding_seed,
)


REFERENCE_TEXT = (
    "Prepare a read-only taskpack binding seed for the released symbol catalog under "
    "release_surface:owner. Use the default codex worker. Allow "
    "packages/adeu_agent_harness/src/adeu_agent_harness/taskpack_binding.py and "
    "packages/adeu_agent_harness/tests/test_taskpack_binding.py. "
    "Forbid network calls and multi-worker topology."
)

AMBIGUOUS_TEXT = (
    "Prepare a read-only binding seed for the catalog under the owner rule. "
    "Use the default codex worker."
)

UNSUPPORTED_TEXT = (
    "Pick whatever policy seems closest and modify the repo if needed."
)


def write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    out_dir = Path(__file__).parent
    out_dir.mkdir(parents=True, exist_ok=True)

    profile = build_reference_repo_policy_work_profile()
    contract = build_reference_transform_contract(profile.profile_id)
    parse_result = parse_nl_to_semantic_form(text=REFERENCE_TEXT, profile=profile)
    assert len(parse_result.candidates) == 1
    normal_form = parse_result.candidates[0].normal_form
    transform_result = transform_normal_form_to_binding_seed(
        normal_form=normal_form,
        profile=profile,
        contract=contract,
    )
    ambiguous_result = parse_nl_to_semantic_form(text=AMBIGUOUS_TEXT, profile=profile)
    unsupported_result = parse_nl_to_semantic_form(text=UNSUPPORTED_TEXT, profile=profile)

    write_json(out_dir / "sample_semantic_parse_profile.json", profile.model_dump(mode="json", exclude_none=True))
    write_json(out_dir / "sample_semantic_parse_result.json", parse_result.model_dump(mode="json", exclude_none=True))
    write_json(out_dir / "sample_semantic_normal_form.json", normal_form.model_dump(mode="json", exclude_none=True))
    write_json(out_dir / "sample_semantic_transform_contract.json", contract.model_dump(mode="json", exclude_none=True))
    write_json(out_dir / "sample_semantic_transform_result.json", transform_result.model_dump(mode="json", exclude_none=True))
    write_json(out_dir / "sample_semantic_parse_result_ambiguous.json", ambiguous_result.model_dump(mode="json", exclude_none=True))
    write_json(out_dir / "sample_semantic_parse_result_unsupported.json", unsupported_result.model_dump(mode="json", exclude_none=True))


if __name__ == "__main__":
    main()
