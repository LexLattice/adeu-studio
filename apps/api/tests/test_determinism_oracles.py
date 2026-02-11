from __future__ import annotations

from pathlib import Path

from adeu_api.determinism_oracles import (
    ORACLE_SCHEMA_VERSION,
    build_determinism_oracle_report,
    write_determinism_oracle_report,
)


def test_build_determinism_oracle_report_passes_locked_fixtures() -> None:
    report = build_determinism_oracle_report()

    assert report["schema"] == ORACLE_SCHEMA_VERSION
    assert report["summary"]["total"] > 0
    assert report["summary"]["failed"] == 0
    families = {item["family"] for item in report["results"]}
    domains = {item["domain"] for item in report["results"]}
    assert families == {"idempotence", "conservation", "ordering"}
    assert domains == {"bridge", "questions", "patch"}


def test_write_determinism_oracle_report_persists_json(tmp_path: Path) -> None:
    output = tmp_path / "determinism_oracles.json"
    report = write_determinism_oracle_report(output)

    assert output.is_file()
    payload = output.read_text(encoding="utf-8")
    assert '"schema": "odeu.determinism-oracles@1"' in payload
    assert report["summary"]["failed"] == 0
