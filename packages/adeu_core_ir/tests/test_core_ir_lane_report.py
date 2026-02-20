from __future__ import annotations

import pytest
from adeu_core_ir import (
    AdeuCoreIR,
    AdeuLaneReport,
    build_lane_report,
    canonicalize_core_ir_payload,
    canonicalize_lane_report_payload,
)
from pydantic import ValidationError


def _valid_core_ir_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-lane-a",
        "nodes": [
            {"id": "o_concept_1", "layer": "O", "kind": "Concept", "label": "delegation"},
            {
                "id": "e_claim_1",
                "layer": "E",
                "kind": "Claim",
                "text": "AI agents can delegate tasks",
                "spans": [{"start": 0, "end": 10}],
            },
            {"id": "d_policy_1", "layer": "D", "kind": "Policy", "label": "verify-before-act"},
            {"id": "u_goal_1", "layer": "U", "kind": "Goal", "label": "maintain trust"},
        ],
        "edges": [
            {"type": "about", "from": "e_claim_1", "to": "o_concept_1"},
            {"type": "gates", "from": "d_policy_1", "to": "e_claim_1"},
            {"type": "serves_goal", "from": "d_policy_1", "to": "u_goal_1"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def test_build_lane_report_groups_nodes_and_counts_edges_by_source_lane() -> None:
    report = build_lane_report(_valid_core_ir_payload())
    assert report.schema == "adeu_lane_report@0.1"
    assert report.source_text_hash == "hash-lane-a"
    assert report.lane_nodes == {
        "O": ["o_concept_1"],
        "E": ["e_claim_1"],
        "D": ["d_policy_1"],
        "U": ["u_goal_1"],
    }
    assert report.lane_edge_counts == {
        "O": 0,
        "E": 1,
        "D": 2,
        "U": 0,
    }


def test_build_lane_report_is_deterministic_across_input_forms() -> None:
    payload = _valid_core_ir_payload()
    report_a = build_lane_report(payload)
    report_b = build_lane_report(AdeuCoreIR.model_validate(payload))
    assert canonicalize_lane_report_payload(report_a) == canonicalize_lane_report_payload(report_b)


def test_lane_report_rejects_noncanonical_lane_key_order() -> None:
    with pytest.raises(ValueError, match="lane_nodes must include lane keys in canonical order"):
        AdeuLaneReport.model_validate(
            {
                "schema": "adeu_lane_report@0.1",
                "source_text_hash": "hash-lane-a",
                "lane_nodes": {
                    "E": ["e_claim_1"],
                    "O": ["o_concept_1"],
                    "D": ["d_policy_1"],
                    "U": ["u_goal_1"],
                },
                "lane_edge_counts": {"O": 0, "E": 1, "D": 2, "U": 0},
            }
        )


def test_lane_report_rejects_unsorted_or_duplicate_nodes() -> None:
    with pytest.raises(ValueError, match="must be sorted lexicographically"):
        AdeuLaneReport.model_validate(
            {
                "schema": "adeu_lane_report@0.1",
                "source_text_hash": "hash-lane-a",
                "lane_nodes": {
                    "O": ["o_concept_2", "o_concept_1"],
                    "E": ["e_claim_1"],
                    "D": ["d_policy_1"],
                    "U": ["u_goal_1"],
                },
                "lane_edge_counts": {"O": 0, "E": 1, "D": 2, "U": 0},
            }
        )

    with pytest.raises(ValueError, match="contains duplicate node ids"):
        AdeuLaneReport.model_validate(
            {
                "schema": "adeu_lane_report@0.1",
                "source_text_hash": "hash-lane-a",
                "lane_nodes": {
                    "O": ["o_concept_1", "o_concept_1"],
                    "E": ["e_claim_1"],
                    "D": ["d_policy_1"],
                    "U": ["u_goal_1"],
                },
                "lane_edge_counts": {"O": 0, "E": 1, "D": 2, "U": 0},
            }
        )


def test_lane_report_rejects_negative_edge_counts() -> None:
    with pytest.raises(ValueError, match="lane_edge_counts\\[E\\] must be >= 0"):
        AdeuLaneReport.model_validate(
            {
                "schema": "adeu_lane_report@0.1",
                "source_text_hash": "hash-lane-a",
                "lane_nodes": {
                    "O": ["o_concept_1"],
                    "E": ["e_claim_1"],
                    "D": ["d_policy_1"],
                    "U": ["u_goal_1"],
                },
                "lane_edge_counts": {"O": 0, "E": -1, "D": 2, "U": 0},
            }
        )


def test_lane_report_requires_lane_edge_counts_field() -> None:
    with pytest.raises(ValidationError, match="lane_edge_counts"):
        AdeuLaneReport.model_validate(
            {
                "schema": "adeu_lane_report@0.1",
                "source_text_hash": "hash-lane-a",
                "lane_nodes": {
                    "O": ["o_concept_1"],
                    "E": ["e_claim_1"],
                    "D": ["d_policy_1"],
                    "U": ["u_goal_1"],
                },
            }
        )
