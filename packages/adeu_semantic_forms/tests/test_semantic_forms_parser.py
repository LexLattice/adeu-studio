from __future__ import annotations

import copy
import json
from pathlib import Path

from adeu_semantic_forms import (
    SemanticNormalForm,
    SemanticParseCandidate,
    build_reference_repo_policy_work_profile,
    parse_nl_to_semantic_result,
)
from adeu_semantic_forms.parser import _dedupe_candidates


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v49b" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_parser_outputs_replay_committed_fixtures() -> None:
    profile = build_reference_repo_policy_work_profile()

    for fixture_name in [
        "reference_semantic_parse_result_resolved_singleton.json",
        "reference_semantic_parse_result_typed_alternatives.json",
        "reference_semantic_parse_result_clarification_required.json",
        "reference_semantic_parse_result_rejected_unsupported.json",
        "reference_semantic_parse_result_exact_anchor_precedence.json",
    ]:
        fixture = _read_json(fixture_name)

        result = parse_nl_to_semantic_result(
            text=str(fixture["input_text"]),
            profile=profile,
        )

        assert result.model_dump(mode="json", by_alias=True, exclude_none=True) == fixture


def test_typed_alternatives_are_sorted_by_semantic_hash() -> None:
    payload = _read_json("reference_semantic_parse_result_typed_alternatives.json")
    profile = build_reference_repo_policy_work_profile()

    result = parse_nl_to_semantic_result(
        text=str(payload["input_text"]),
        profile=profile,
    )

    hashes = [candidate.normal_form.semantic_hash for candidate in result.candidates]
    assert hashes == sorted(hashes)
    assert [candidate.candidate_rank for candidate in result.candidates] == [1, 2]


def test_clarification_required_emits_zero_candidates_only() -> None:
    payload = _read_json("reference_semantic_parse_result_clarification_required.json")
    profile = build_reference_repo_policy_work_profile()

    result = parse_nl_to_semantic_result(
        text=str(payload["input_text"]),
        profile=profile,
    )

    assert result.parse_status == "clarification_required"
    assert result.candidates == []
    assert len(result.ambiguities) == 1


def test_exact_anchor_text_outranks_normalized_alias_match() -> None:
    payload = _read_json("reference_semantic_parse_result_exact_anchor_precedence.json")
    profile = build_reference_repo_policy_work_profile()

    result = parse_nl_to_semantic_result(
        text=str(payload["input_text"]),
        profile=profile,
    )

    scope_core = next(
        core
        for core in result.candidates[0].normal_form.statement_cores
        if core.relation_kind == "bind_scope_anchor"
    )

    assert result.parse_status == "resolved_singleton"
    assert result.ambiguities == []
    assert scope_core.object_value == "repo_symbol_catalog"


def test_all_recovered_forbid_effects_are_preserved() -> None:
    payload = _read_json("reference_semantic_parse_result_resolved_singleton.json")
    profile = build_reference_repo_policy_work_profile()

    result = parse_nl_to_semantic_result(
        text=str(payload["input_text"]),
        profile=profile,
    )

    forbid_effects = sorted(
        core.object_value
        for core in result.candidates[0].normal_form.statement_cores
        if core.relation_kind == "forbid_effect"
    )

    assert forbid_effects == ["multi_worker_topology", "network_calls"]


def test_dedupe_candidates_collapses_same_semantic_hash() -> None:
    payload = _read_json("reference_semantic_parse_result_resolved_singleton.json")
    candidate_payload = payload["candidates"][0]
    normal_form = SemanticNormalForm.model_validate(candidate_payload["normal_form"])

    first = SemanticParseCandidate.model_validate(candidate_payload)
    second_payload = copy.deepcopy(candidate_payload)
    second_payload["candidate_rank"] = 7
    second_payload["candidate_id"] = "candidate:7:placeholder"
    second_payload["evidence_summary"] = candidate_payload["evidence_summary"] + [
        "scope_anchor=repo_symbol_catalog"
    ]
    second = SemanticParseCandidate.model_validate(
        {
            **second_payload,
            "normal_form": normal_form.model_dump(mode="json", by_alias=True, exclude_none=True),
        }
    )

    deduped = _dedupe_candidates([second, first])

    assert len(deduped) == 1
    assert deduped[0].candidate_rank == 1
    assert deduped[0].candidate_id == f"candidate:1:{normal_form.semantic_hash[:16]}"
    assert deduped[0].evidence_summary == sorted(
        dict.fromkeys(candidate_payload["evidence_summary"])
    )
