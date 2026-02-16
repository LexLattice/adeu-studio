from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

from adeu_api.urm_domain_conformance import (
    DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELD_LIST,
    DOMAIN_CONFORMANCE_SCHEMA,
    DomainConformanceError,
    build_domain_conformance,
    domain_conformance_hash,
    validate_domain_conformance_report,
)
from urm_runtime.hashing import canonical_json


def _runtime_root() -> Path:
    repo_root = Path(__file__).resolve().parents[3]
    return (repo_root / "packages" / "urm_runtime" / "src" / "urm_runtime").resolve()


def test_build_domain_conformance_is_deterministic_and_valid(tmp_path: Path) -> None:
    runtime_root = _runtime_root()
    first = build_domain_conformance(events_dir=tmp_path / "first_events", runtime_root=runtime_root)
    second = build_domain_conformance(
        events_dir=tmp_path / "second_events",
        runtime_root=runtime_root,
    )

    assert first["schema"] == DOMAIN_CONFORMANCE_SCHEMA
    assert first["valid"] is True
    assert first["issues"] == []
    assert first["hash_excluded_fields"] == list(DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELD_LIST)
    assert first["domain_conformance_hash"] == domain_conformance_hash(first)
    assert canonical_json(first) == canonical_json(second)
    validate_domain_conformance_report(first)

    assert first["registry_order_determinism"]["valid"] is True
    assert first["import_audit"]["valid"] is True
    assert first["import_audit"]["runtime_root_path"] == str(runtime_root)
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
    runtime_root = _runtime_root()

    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            "--out",
            str(out_json),
            "--events-dir",
            str(events_dir),
            "--runtime-root",
            str(runtime_root),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stderr
    payload = json.loads(out_json.read_text(encoding="utf-8"))
    assert payload["schema"] == DOMAIN_CONFORMANCE_SCHEMA
    assert payload["valid"] is True
    assert payload["hash_excluded_fields"] == list(DOMAIN_CONFORMANCE_HASH_EXCLUDED_FIELD_LIST)
    assert payload["domain_conformance_hash"] == domain_conformance_hash(payload)
    validate_domain_conformance_report(payload)


def test_build_domain_conformance_missing_runtime_root_fails_closed(tmp_path: Path) -> None:
    missing_runtime_root = (tmp_path / "missing_runtime_root").resolve()
    report = build_domain_conformance(
        events_dir=tmp_path / "missing_runtime_root_events",
        runtime_root=missing_runtime_root,
    )

    assert report["valid"] is False
    assert report["import_audit"]["valid"] is False
    assert report["import_audit"]["runtime_root_path"] == str(missing_runtime_root)
    assert report["import_audit"]["missing_runtime_root_path"] == str(missing_runtime_root)
    assert report["domain_conformance_hash"] == domain_conformance_hash(report)
    validate_domain_conformance_report(report)

    import_issue = next(
        issue for issue in report["issues"] if issue["code"] == "RUNTIME_IMPORT_AUDIT_FAILED"
    )
    assert import_issue["urm_code"] == "URM_CONFORMANCE_RUNTIME_IMPORT_AUDIT_FAILED"


def test_validate_domain_conformance_report_fails_on_invalid_fields(tmp_path: Path) -> None:
    report = build_domain_conformance(
        events_dir=tmp_path / "validation_events",
        runtime_root=_runtime_root(),
    )

    bad_hash_fields = copy.deepcopy(report)
    bad_hash_fields["hash_excluded_fields"] = []
    with pytest.raises(DomainConformanceError, match="hash_excluded_fields"):
        validate_domain_conformance_report(bad_hash_fields)

    bad_hash = copy.deepcopy(report)
    bad_hash["domain_conformance_hash"] = "0" * 64
    with pytest.raises(DomainConformanceError, match="domain_conformance_hash mismatch"):
        validate_domain_conformance_report(bad_hash)

    bad_issue_order = copy.deepcopy(report)
    bad_issue_order["issues"] = [
        {
            "code": "ZZZ",
            "message": "later",
            "context": {},
            "urm_code": "URM_CONFORMANCE_REPORT_INVALID",
        },
        {
            "code": "AAA",
            "message": "earlier",
            "context": {},
            "urm_code": "URM_CONFORMANCE_REPORT_INVALID",
        },
    ]
    bad_issue_order["domain_conformance_hash"] = domain_conformance_hash(bad_issue_order)
    with pytest.raises(DomainConformanceError, match="issues must be canonical-sorted"):
        validate_domain_conformance_report(bad_issue_order)
