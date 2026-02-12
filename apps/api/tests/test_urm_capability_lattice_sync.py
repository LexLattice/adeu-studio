from __future__ import annotations

import json
from pathlib import Path


def test_repo_and_packaged_capability_lattice_are_in_sync() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    repo_policy_path = repo_root / "policy" / "urm.capability.lattice.v1.json"
    packaged_policy_path = (
        repo_root
        / "packages"
        / "urm_runtime"
        / "src"
        / "urm_runtime"
        / "policy"
        / "urm.capability.lattice.v1.json"
    )

    repo_payload = json.loads(repo_policy_path.read_text(encoding="utf-8"))
    packaged_payload = json.loads(packaged_policy_path.read_text(encoding="utf-8"))

    assert repo_payload == packaged_payload
