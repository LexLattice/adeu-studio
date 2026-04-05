from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_reasoning_assessment import (
    ReasoningProbeSuite,
    ReasoningTemplateProbe,
    StructuralFailureTaxonomy,
    StructuralReasoningDifferential,
    StructuralReasoningTrace,
    build_reasoning_probe_suite,
    canonical_json,
    diagnose_condition_pair_differential,
    normalize_trace_to_taxonomy,
)
from adeu_reasoning_assessment.probe_library import (
    ProbeSuiteMemberSpec,
    supported_consumer_compatibility_refs,
)

V44C_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v44c"
V44D_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v44d"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _load_v44c_bundle(
    name: str,
) -> tuple[
    dict[str, ReasoningTemplateProbe],
    dict[str, StructuralReasoningTrace],
    dict[str, StructuralFailureTaxonomy],
]:
    payload = _load_json(V44C_FIXTURE_ROOT, name)
    assert isinstance(payload, dict)
    return (
        {
            role: ReasoningTemplateProbe.model_validate(value)
            for role, value in payload["condition_probes"].items()
        },
        {
            role: StructuralReasoningTrace.model_validate(value)
            for role, value in payload["condition_traces"].items()
        },
        {
            role: StructuralFailureTaxonomy.model_validate(value)
            for role, value in payload["condition_taxonomies"].items()
        },
    )


def test_reference_probe_suite_fixture_validates_and_matches_builder() -> None:
    expected = ReasoningProbeSuite.model_validate(
        _load_json(V44D_FIXTURE_ROOT, "reference_reasoning_probe_suite.json")
    )
    differential_bundle = _load_v44c_bundle(
        "reference_differential_input_knowledge_deficit.json"
    )
    condition_probes, _condition_traces, _condition_taxonomies = differential_bundle
    branching_probe = ReasoningTemplateProbe.model_validate(
        _load_json(V44D_FIXTURE_ROOT, "reference_reasoning_template_probe_branching.json")
    )
    local_repair_probe = ReasoningTemplateProbe.model_validate(
        _load_json(V44D_FIXTURE_ROOT, "reference_reasoning_template_probe_local_repair.json")
    )
    invariance_paraphrase_probe = ReasoningTemplateProbe.model_validate(
        _load_json(
            V44D_FIXTURE_ROOT,
            "reference_reasoning_template_probe_invariance_paraphrase.json",
        )
    )
    invariance_presentation_probe = ReasoningTemplateProbe.model_validate(
        _load_json(
            V44D_FIXTURE_ROOT,
            "reference_reasoning_template_probe_invariance_presentation_shift.json",
        )
    )

    observed = build_reasoning_probe_suite(
        suite_label=expected.suite_label,
        member_specs=[
            ProbeSuiteMemberSpec(
                probe=invariance_presentation_probe,
                surface_variation_kind="presentation_shift_preserving",
                consumer_compatibility_refs=supported_consumer_compatibility_refs(
                    paired_condition_compatible=False
                ),
            ),
            ProbeSuiteMemberSpec(
                probe=condition_probes["withheld_knowledge"],
                consumer_compatibility_refs=supported_consumer_compatibility_refs(
                    paired_condition_compatible=True
                ),
                paired_condition_compatible=True,
            ),
            ProbeSuiteMemberSpec(
                probe=local_repair_probe,
                repair_locality_posture="local_only",
                consumer_compatibility_refs=supported_consumer_compatibility_refs(
                    paired_condition_compatible=False
                ),
            ),
            ProbeSuiteMemberSpec(
                probe=branching_probe,
                consumer_compatibility_refs=supported_consumer_compatibility_refs(
                    paired_condition_compatible=False
                ),
            ),
            ProbeSuiteMemberSpec(
                probe=invariance_paraphrase_probe,
                surface_variation_kind="paraphrase_preserving",
                consumer_compatibility_refs=supported_consumer_compatibility_refs(
                    paired_condition_compatible=False
                ),
            ),
            ProbeSuiteMemberSpec(
                probe=condition_probes["supplied_knowledge"],
                consumer_compatibility_refs=supported_consumer_compatibility_refs(
                    paired_condition_compatible=True
                ),
                paired_condition_compatible=True,
            ),
        ],
    )

    observed_payload = observed.model_dump(mode="json", by_alias=True, exclude_none=True)
    expected_payload = expected.model_dump(mode="json", by_alias=True, exclude_none=True)
    assert canonical_json(observed_payload) == canonical_json(expected_payload)


def test_taxonomy_compatibility_replay_matches_reference_fixture() -> None:
    payload = _load_json(V44D_FIXTURE_ROOT, "reference_v44d_taxonomy_compatibility_replay.json")
    assert isinstance(payload, dict)

    probe = ReasoningTemplateProbe.model_validate(payload["probe"])
    trace = StructuralReasoningTrace.model_validate(payload["trace"])
    expected = StructuralFailureTaxonomy.model_validate(payload["expected_taxonomy"])

    observed = normalize_trace_to_taxonomy(probe=probe, trace=trace)
    observed_payload = observed.model_dump(mode="json", by_alias=True, exclude_none=True)
    expected_payload = expected.model_dump(mode="json", by_alias=True, exclude_none=True)
    assert canonical_json(observed_payload) == canonical_json(expected_payload)


def test_differential_compatibility_replay_matches_reference_fixture() -> None:
    payload = _load_json(
        V44D_FIXTURE_ROOT,
        "reference_v44d_differential_compatibility_replay.json",
    )
    assert isinstance(payload, dict)

    condition_probes = {
        role: ReasoningTemplateProbe.model_validate(probe)
        for role, probe in payload["condition_probes"].items()
    }
    condition_traces = {
        role: StructuralReasoningTrace.model_validate(trace)
        for role, trace in payload["condition_traces"].items()
    }
    condition_taxonomies = {
        role: StructuralFailureTaxonomy.model_validate(taxonomy)
        for role, taxonomy in payload["condition_taxonomies"].items()
    }
    expected = StructuralReasoningDifferential.model_validate(payload["expected_differential"])

    observed = diagnose_condition_pair_differential(
        condition_probes=condition_probes,
        condition_traces=condition_traces,
        condition_taxonomies=condition_taxonomies,
    )
    observed_payload = observed.model_dump(mode="json", by_alias=True, exclude_none=True)
    expected_payload = expected.model_dump(mode="json", by_alias=True, exclude_none=True)
    assert canonical_json(observed_payload) == canonical_json(expected_payload)


def test_invariance_probe_missing_anchor_fails_closed() -> None:
    invalid_probe = ReasoningTemplateProbe.model_validate(
        _load_json(
            V44D_FIXTURE_ROOT,
            "reject_reasoning_template_probe_invariance_missing_anchor.json",
        )
    )

    with pytest.raises(ValueError, match="procedure_preservation_required"):
        build_reasoning_probe_suite(
            suite_label="reject_invalid_invariance_anchor",
            member_specs=[
                ProbeSuiteMemberSpec(
                    probe=invalid_probe,
                    surface_variation_kind="paraphrase_preserving",
                    consumer_compatibility_refs=supported_consumer_compatibility_refs(
                        paired_condition_compatible=False
                    ),
                )
            ],
        )


def test_non_local_repair_probe_fails_closed() -> None:
    invalid_probe = ReasoningTemplateProbe.model_validate(
        _load_json(
            V44D_FIXTURE_ROOT,
            "reject_reasoning_template_probe_non_local_repair.json",
        )
    )

    with pytest.raises(ValueError, match="no_non_local_repair|non_local_rewrite"):
        build_reasoning_probe_suite(
            suite_label="reject_non_local_repair",
            member_specs=[
                ProbeSuiteMemberSpec(
                    probe=invalid_probe,
                    repair_locality_posture="local_only",
                    consumer_compatibility_refs=supported_consumer_compatibility_refs(
                        paired_condition_compatible=False
                    ),
                )
            ],
        )


def test_suite_matrix_covers_all_classes_and_variation_kinds() -> None:
    payload = _load_json(V44D_FIXTURE_ROOT, "reference_v44d_suite_matrix.json")
    assert isinstance(payload, dict)

    rows = payload["suite_members"]
    assert isinstance(rows, list)

    seen_classes: set[str] = set()
    seen_variation_kinds: set[str] = set()
    differential_compatible_members = 0
    for row in rows:
        fixture_name = row["source_fixture_name"]
        assert (V44D_FIXTURE_ROOT / fixture_name).is_file() or (
            V44C_FIXTURE_ROOT / fixture_name
        ).is_file()
        seen_classes.add(row["template_class"])
        if row["surface_variation_kind"] is not None:
            seen_variation_kinds.add(row["surface_variation_kind"])
        compatibility_refs = row["consumer_compatibility_refs"]
        assert "adeu_structural_failure_taxonomy@1" in compatibility_refs
        if "adeu_structural_reasoning_differential@1" in compatibility_refs:
            differential_compatible_members += 1
            assert row["paired_condition_compatible"] is True

    assert seen_classes == {
        "lane_preserving_decomposition",
        "branching_under_uncertainty",
        "local_repair_continuation",
        "invariance_under_surface_variation",
    }
    assert seen_variation_kinds == {
        "paraphrase_preserving",
        "presentation_shift_preserving",
    }
    assert differential_compatible_members == 2
