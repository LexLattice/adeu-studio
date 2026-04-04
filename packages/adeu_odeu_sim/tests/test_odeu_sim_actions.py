from __future__ import annotations

from adeu_odeu_sim.actions import (
    ACTION_CONTRACT_KINDS,
    ACTION_LIBRARY,
    FROZEN_ACTION_TYPE_ORDER,
    LANE_CROSSING_CONTRACT_LIBRARY,
    get_action_contracts,
)
from adeu_odeu_sim.models import ActionType, LaneCrossingContractKind, LaneName


def test_action_library_covers_frozen_action_order() -> None:
    assert tuple(ACTION_LIBRARY) == FROZEN_ACTION_TYPE_ORDER


def test_action_contracts_are_typed_and_explicit() -> None:
    assert set(LANE_CROSSING_CONTRACT_LIBRARY) == {
        LaneCrossingContractKind.O_TO_E_TRACE,
        LaneCrossingContractKind.E_TO_D_LEGITIMACY,
        LaneCrossingContractKind.D_TO_O_ALLOCATION,
        LaneCrossingContractKind.U_TO_D_PRESSURE,
    }
    sanction_contracts = get_action_contracts(ActionType.SANCTION)
    assert len(sanction_contracts) == 1
    assert sanction_contracts[0].source_lane == LaneName.D
    assert sanction_contracts[0].target_lane == LaneName.O
    assert ACTION_CONTRACT_KINDS[ActionType.DO_NOTHING] == ()
