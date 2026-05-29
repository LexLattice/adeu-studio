from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .brl_0a import (
    RepoBehavioralCanonicalizationProfile,
    RepoBehavioralObservationHash,
    RepoBehavioralProbeContract,
    RepoBehavioralReplayLockNonAuthorityGuardrail,
    RepoBehavioralReplayManifest,
    RepoBehavioralReplayManifestValidationReport,
)
from .brl_0b import (
    RepoBehavioralObservationRecord,
    RepoBehavioralRegressionDiff,
    RepoBehavioralReplayExecutionReport,
    RepoBehavioralSuiteRootHashReport,
)


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    package_schema_root = root / "packages" / "adeu_behavioral_replay_lock" / "schema"
    spec_root = root / "spec"
    mappings = [
        (
            RepoBehavioralReplayManifest.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_replay_manifest.v1.json",
            spec_root / "repo_behavioral_replay_manifest.schema.json",
        ),
        (
            RepoBehavioralProbeContract.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_probe_contract.v1.json",
            spec_root / "repo_behavioral_probe_contract.schema.json",
        ),
        (
            RepoBehavioralCanonicalizationProfile.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_canonicalization_profile.v1.json",
            spec_root / "repo_behavioral_canonicalization_profile.schema.json",
        ),
        (
            RepoBehavioralObservationHash.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_observation_hash.v1.json",
            spec_root / "repo_behavioral_observation_hash.schema.json",
        ),
        (
            RepoBehavioralReplayManifestValidationReport.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_replay_manifest_validation_report.v1.json",
            spec_root / "repo_behavioral_replay_manifest_validation_report.schema.json",
        ),
        (
            RepoBehavioralReplayLockNonAuthorityGuardrail.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_replay_lock_non_authority_guardrail.v1.json",
            spec_root / "repo_behavioral_replay_lock_non_authority_guardrail.schema.json",
        ),
        (
            RepoBehavioralReplayExecutionReport.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_replay_execution_report.v1.json",
            spec_root / "repo_behavioral_replay_execution_report.schema.json",
        ),
        (
            RepoBehavioralObservationRecord.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_observation_record.v1.json",
            spec_root / "repo_behavioral_observation_record.schema.json",
        ),
        (
            RepoBehavioralRegressionDiff.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_regression_diff.v1.json",
            spec_root / "repo_behavioral_regression_diff.schema.json",
        ),
        (
            RepoBehavioralSuiteRootHashReport.model_json_schema(by_alias=True),
            package_schema_root / "repo_behavioral_suite_root_hash_report.v1.json",
            spec_root / "repo_behavioral_suite_root_hash_report.schema.json",
        ),
    ]
    for schema, authoritative_path, mirror_path in mappings:
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
