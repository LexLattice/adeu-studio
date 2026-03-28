from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_arc_agi import (
    ADEU_ARC_ACTION_PROPOSAL_SCHEMA,
    ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA,
    ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA,
    ADEU_ARC_OBSERVATION_FRAME_SCHEMA,
    ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA,
    ADEU_ARC_REASONING_RUN_RECORD_SCHEMA,
    ADEU_ARC_ROLLOUT_TRACE_SCHEMA,
    ADEU_ARC_SCORECARD_MANIFEST_SCHEMA,
    ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA,
    ADEU_ARC_TASK_PACKET_SCHEMA,
)
from adeu_arc_agi.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_pairs() -> dict[str, tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return {
        ADEU_ARC_TASK_PACKET_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_task_packet.v1.json",
            root / "spec" / "adeu_arc_task_packet.schema.json",
        ),
        ADEU_ARC_OBSERVATION_FRAME_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_observation_frame.v1.json",
            root / "spec" / "adeu_arc_observation_frame.schema.json",
        ),
        ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_hypothesis_frame.v1.json",
            root / "spec" / "adeu_arc_hypothesis_frame.schema.json",
        ),
        ADEU_ARC_ACTION_PROPOSAL_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_action_proposal.v1.json",
            root / "spec" / "adeu_arc_action_proposal.schema.json",
        ),
        ADEU_ARC_ROLLOUT_TRACE_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_rollout_trace.v1.json",
            root / "spec" / "adeu_arc_rollout_trace.schema.json",
        ),
        ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_local_eval_record.v1.json",
            root / "spec" / "adeu_arc_local_eval_record.schema.json",
        ),
        ADEU_ARC_SCORECARD_MANIFEST_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_scorecard_manifest.v1.json",
            root / "spec" / "adeu_arc_scorecard_manifest.schema.json",
        ),
        ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_puzzle_input_bundle.v1.json",
            root / "spec" / "adeu_arc_puzzle_input_bundle.schema.json",
        ),
        ADEU_ARC_REASONING_RUN_RECORD_SCHEMA: (
            root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_reasoning_run_record.v1.json",
            root / "spec" / "adeu_arc_reasoning_run_record.schema.json",
        ),
        ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_submission_execution_record.v1.json",
            root / "spec" / "adeu_arc_submission_execution_record.schema.json",
        ),
    }


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for authoritative, mirror in _schema_pairs().values():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    pairs = _schema_pairs()
    before = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    export_schema_main()
    after_first = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    export_schema_main()
    after_second = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    for expected_schema, (authoritative, _mirror) in _schema_pairs().items():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_schema


def test_exported_schema_has_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()
    pair_values = _schema_pairs().values()

    def _check_node(node: object) -> None:
        if isinstance(node, dict):
            for value in node.values():
                _check_node(value)
            return
        if isinstance(node, list):
            for item in node:
                _check_node(item)
            return
        if not isinstance(node, str):
            return
        normalized = node.replace("\\", "/")
        assert root_text not in normalized
        assert not normalized.startswith("/home/")
        assert not normalized.startswith("/Users/")
        assert _WINDOWS_ABSOLUTE_PATH_RE.search(node) is None

    for authoritative, mirror in pair_values:
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
        _check_node(json.loads(mirror.read_text(encoding="utf-8")))
