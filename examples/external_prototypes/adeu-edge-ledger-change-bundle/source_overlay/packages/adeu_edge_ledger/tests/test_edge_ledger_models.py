from __future__ import annotations

import pytest
from adeu_edge_ledger.models import SymbolEdgeAdjudicationRow
from pydantic import ValidationError


EDGE_CLASS_REF = "edge_class:failure_path/rejection_fail_closed/raises_on_invalid_input"
PROBE_REF = "probe:fail_closed_rejection"
TEST_REF = "test:packages/example/tests/test_sample.py#test_rejects_invalid_input"


def test_adjudication_row_requires_supporting_test_refs_for_covered_by_existing_tests() -> None:
    with pytest.raises(ValidationError, match="covered_by_existing_tests requires supporting_test_refs"):
        SymbolEdgeAdjudicationRow.model_validate(
            {
                "edge_class_ref": EDGE_CLASS_REF,
                "source_applicability_status": "applicable",
                "adjudication_status": "covered_by_existing_tests",
                "status_posture": "observed",
                "matched_cue_tags": ["feature:raises_value_error"],
                "supporting_test_refs": [],
                "supporting_evidence_refs": [],
                "suggested_probe_template_refs": [PROBE_REF],
                "rationale": "missing supporting tests should fail",
            }
        )


def test_adjudication_row_requires_witness_summary_for_witness_found() -> None:
    with pytest.raises(ValidationError, match="witness_found requires witness_summary"):
        SymbolEdgeAdjudicationRow.model_validate(
            {
                "edge_class_ref": EDGE_CLASS_REF,
                "source_applicability_status": "applicable",
                "adjudication_status": "witness_found",
                "status_posture": "adjudicated",
                "matched_cue_tags": ["feature:raises_value_error"],
                "supporting_test_refs": [TEST_REF],
                "supporting_evidence_refs": [],
                "suggested_probe_template_refs": [PROBE_REF],
                "rationale": "missing witness summary should fail",
            }
        )


def test_adjudication_row_rejects_not_applicable_status_when_source_was_applicable() -> None:
    with pytest.raises(
        ValidationError,
        match="not_applicable adjudication_status requires source_applicability_status = not_applicable",
    ):
        SymbolEdgeAdjudicationRow.model_validate(
            {
                "edge_class_ref": EDGE_CLASS_REF,
                "source_applicability_status": "applicable",
                "adjudication_status": "not_applicable",
                "status_posture": "derived_deterministically",
                "matched_cue_tags": [],
                "supporting_test_refs": [],
                "supporting_evidence_refs": [],
                "suggested_probe_template_refs": [PROBE_REF],
                "rationale": "cannot erase applicable source posture",
            }
        )
