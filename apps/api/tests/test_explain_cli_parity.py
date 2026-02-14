from __future__ import annotations

import json
from pathlib import Path

from adeu_api.explain_builder import build_explain_packet_payload
from adeu_api.explain_tools import main as explain_tools_main
from adeu_explain import ConceptAnalysisDelta, DiffReport, FlipExplanation


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _fixture_paths() -> list[Path]:
    fixture_dir = _repo_root() / "apps" / "api" / "tests" / "fixtures" / "explain_parity"
    return sorted(fixture_dir.glob("*_golden_v1.json"))


def test_explain_api_cli_parity_golden_fixtures(tmp_path: Path) -> None:
    fixture_paths = _fixture_paths()
    assert fixture_paths, "expected parity fixtures"

    seen_kinds: set[str] = set()
    for fixture_path in fixture_paths:
        fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
        assert fixture["schema"] == "explain.parity_fixture@1"
        input_payload = fixture["input"]
        expected_packet = fixture["expected_packet"]
        explain_kind = str(input_payload["explain_kind"])
        seen_kinds.add(explain_kind)

        api_packet = build_explain_packet_payload(
            explain_kind=explain_kind,
            diff_report=DiffReport.model_validate(input_payload["diff_report"]),
            input_artifact_refs=[str(item) for item in input_payload["input_artifact_refs"]],
            flip_explanation=(
                FlipExplanation.model_validate(input_payload["flip_explanation"])
                if "flip_explanation" in input_payload
                else None
            ),
            analysis_delta=(
                ConceptAnalysisDelta.model_validate(input_payload["analysis_delta"])
                if "analysis_delta" in input_payload
                else None
            ),
            run_ir_mismatch=input_payload.get("run_ir_mismatch"),
            left_mismatch=input_payload.get("left_mismatch"),
            right_mismatch=input_payload.get("right_mismatch"),
        )

        cli_in = tmp_path / f"{fixture_path.stem}.input.json"
        cli_out = tmp_path / f"{fixture_path.stem}.out.json"
        cli_input_json = json.dumps(input_payload, ensure_ascii=False, sort_keys=True)
        cli_in.write_text(cli_input_json, encoding="utf-8")
        exit_code = explain_tools_main(
            ["build", "--in", str(cli_in), "--out", str(cli_out)]
        )
        assert exit_code == 0
        cli_packet = json.loads(cli_out.read_text(encoding="utf-8"))

        assert api_packet == expected_packet
        assert cli_packet == expected_packet
        assert cli_packet == api_packet

    assert seen_kinds == {"semantic_diff", "concepts_diff", "puzzles_diff", "flip_explain"}
