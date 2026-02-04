from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, check


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def test_golden_fixtures_lax_mode() -> None:
    root = _repo_root_path()
    fixtures_root = root / "examples" / "fixtures"

    fixture_dirs = sorted([p for p in fixtures_root.iterdir() if p.is_dir()])
    assert fixture_dirs, f"No fixtures found under {fixtures_root}"

    for fixture_dir in fixture_dirs:
        proposals_dir = fixture_dir / "proposals"
        expected_dir = fixture_dir / "expected" / "check"
        assert proposals_dir.is_dir(), f"Missing proposals dir: {proposals_dir}"
        assert expected_dir.is_dir(), f"Missing expected dir: {expected_dir}"

        proposal_files = sorted(proposals_dir.glob("*.json"))
        assert proposal_files, f"No proposals found in {proposals_dir}"

        for proposal_path in proposal_files:
            proposal = _load_json(proposal_path)
            report = check(proposal, mode=KernelMode.LAX)

            assert isinstance(
                proposal, dict
            ), f"Fixture proposal must be an object: {proposal_path}"
            ir_id = proposal.get("ir_id")
            assert isinstance(ir_id, str) and ir_id, f"Missing ir_id in proposal: {proposal_path}"
            expected_path = expected_dir / f"{ir_id}.json"
            assert expected_path.is_file(), f"Missing expected report: {expected_path}"

            expected = _load_json(expected_path)
            actual = report.model_dump(mode="json", exclude_none=True)
            assert actual == expected, f"Mismatch for {proposal_path}"
