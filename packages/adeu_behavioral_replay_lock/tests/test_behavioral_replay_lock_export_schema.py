from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_behavioral_replay_lock import (
    REPO_BEHAVIORAL_CANONICALIZATION_PROFILE_SCHEMA,
    REPO_BEHAVIORAL_OBSERVATION_HASH_SCHEMA,
    REPO_BEHAVIORAL_PROBE_CONTRACT_SCHEMA,
    REPO_BEHAVIORAL_REPLAY_LOCK_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    REPO_BEHAVIORAL_REPLAY_MANIFEST_SCHEMA,
    REPO_BEHAVIORAL_REPLAY_MANIFEST_VALIDATION_REPORT_SCHEMA,
)
from adeu_behavioral_replay_lock.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _schema_paths() -> list[tuple[Path, Path]]:
    root = _repo_root()
    package_schema_root = root / "packages" / "adeu_behavioral_replay_lock" / "schema"
    spec_root = root / "spec"
    return [
        (
            package_schema_root / "repo_behavioral_replay_manifest.v1.json",
            spec_root / "repo_behavioral_replay_manifest.schema.json",
        ),
        (
            package_schema_root / "repo_behavioral_probe_contract.v1.json",
            spec_root / "repo_behavioral_probe_contract.schema.json",
        ),
        (
            package_schema_root / "repo_behavioral_canonicalization_profile.v1.json",
            spec_root / "repo_behavioral_canonicalization_profile.schema.json",
        ),
        (
            package_schema_root / "repo_behavioral_observation_hash.v1.json",
            spec_root / "repo_behavioral_observation_hash.schema.json",
        ),
        (
            package_schema_root / "repo_behavioral_replay_manifest_validation_report.v1.json",
            spec_root / "repo_behavioral_replay_manifest_validation_report.schema.json",
        ),
        (
            package_schema_root / "repo_behavioral_replay_lock_non_authority_guardrail.v1.json",
            spec_root / "repo_behavioral_replay_lock_non_authority_guardrail.schema.json",
        ),
    ]


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    export_schema_main()
    for authoritative, mirror in _schema_paths():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    export_schema_main()
    before = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]
    export_schema_main()
    after = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]
    assert before == after


def test_exported_schema_has_stable_contract_markers() -> None:
    export_schema_main()
    expected_consts = {
        "repo_behavioral_replay_manifest.v1.json": REPO_BEHAVIORAL_REPLAY_MANIFEST_SCHEMA,
        "repo_behavioral_probe_contract.v1.json": REPO_BEHAVIORAL_PROBE_CONTRACT_SCHEMA,
        "repo_behavioral_canonicalization_profile.v1.json": (
            REPO_BEHAVIORAL_CANONICALIZATION_PROFILE_SCHEMA
        ),
        "repo_behavioral_observation_hash.v1.json": REPO_BEHAVIORAL_OBSERVATION_HASH_SCHEMA,
        "repo_behavioral_replay_manifest_validation_report.v1.json": (
            REPO_BEHAVIORAL_REPLAY_MANIFEST_VALIDATION_REPORT_SCHEMA
        ),
        "repo_behavioral_replay_lock_non_authority_guardrail.v1.json": (
            REPO_BEHAVIORAL_REPLAY_LOCK_NON_AUTHORITY_GUARDRAIL_SCHEMA
        ),
    }
    for authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_consts[authoritative.name]


def test_exported_schema_has_no_absolute_path_material() -> None:
    export_schema_main()
    for authoritative, mirror in _schema_paths():
        for path in (authoritative, mirror):
            text = path.read_text(encoding="utf-8")
            assert str(_repo_root()) not in text
            assert not _WINDOWS_ABSOLUTE_PATH_RE.search(text)
