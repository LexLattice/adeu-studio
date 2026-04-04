from __future__ import annotations

import pytest
from adeu_odeu_sim.models import (
    EventRecord,
    EventRecordKind,
    LaneCrossingContract,
    LaneCrossingContractKind,
    LaneName,
    ScenarioConfig,
)


def test_scenario_config_rejects_invalid_share_sum() -> None:
    with pytest.raises(ValueError, match="sum exactly to 1.0"):
        ScenarioConfig(
            name="bad",
            description="bad shares",
            cooperator_share=0.5,
            opportunist_share=0.3,
            auditor_share=0.2,
            official_share=0.05,
            ai_dependent_share=0.05,
        )


def test_lane_crossing_contract_rejects_wrong_lane_pair() -> None:
    with pytest.raises(ValueError, match="frozen source/target lane pair"):
        LaneCrossingContract(
            contract_kind=LaneCrossingContractKind.O_TO_E_TRACE,
            source_lane=LaneName.E,
            target_lane=LaneName.O,
            trigger_surface="bad",
            effect_surface="bad",
            diagnostic_posture="bad",
        )


def test_event_record_requires_sorted_unique_related_ids() -> None:
    with pytest.raises(ValueError, match="sorted"):
        EventRecord(
            event_kind=EventRecordKind.DIAGNOSTIC_NOTE,
            turn=1,
            summary="note",
            related_ids=("b", "a"),
        )
