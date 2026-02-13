from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from adeu_api.urm_domain_conformance import DOMAIN_CONFORMANCE_SCHEMA, build_domain_conformance
from urm_runtime.hashing import canonical_json


def test_build_domain_conformance_is_deterministic_and_valid(tmp_path: Path) -> None:
    first = build_domain_conformance(events_dir=tmp_path / "first_events")
    second = build_domain_conformance(events_dir=tmp_path / "second_events")

    assert first["schema"] == DOMAIN_CONFORMANCE_SCHEMA
    assert first["valid"] is True
    assert first["issues"] == []
    assert canonical_json(first) == canonical_json(second)

    assert first["registry_order_determinism"]["valid"] is True
    assert first["import_audit"]["valid"] is True
    assert [item["domain"] for item in first["domains"]] == ["digest", "paper"]
    assert all(item["valid"] is True for item in first["domains"])
    assert all(item["event_envelope"]["valid"] is True for item in first["domains"])
    assert all(item["replay_determinism"]["valid"] is True for item in first["domains"])
    assert all(item["policy_gating"]["allow_valid"] is True for item in first["domains"])
    assert all(item["policy_gating"]["deny_valid"] is True for item in first["domains"])
    assert all(item["error_taxonomy"]["valid"] is True for item in first["domains"])


def test_build_domain_conformance_script_writes_report(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[3]
    script = repo_root / "apps" / "api" / "scripts" / "build_domain_conformance.py"
    out_json = tmp_path / "domain_conformance.json"
    events_dir = tmp_path / "events"

    completed = subprocess.run(
        [sys.executable, str(script), "--out", str(out_json), "--events-dir", str(events_dir)],
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stderr
    payload = json.loads(out_json.read_text(encoding="utf-8"))
    assert payload["schema"] == DOMAIN_CONFORMANCE_SCHEMA
    assert payload["valid"] is True
