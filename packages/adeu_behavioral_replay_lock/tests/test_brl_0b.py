from __future__ import annotations

import sys
from hashlib import sha256
from pathlib import Path

import pytest
from adeu_behavioral_replay_lock import (
    REPO_BEHAVIORAL_CANONICALIZATION_PROFILE_SCHEMA,
    REPO_BEHAVIORAL_OBSERVATION_HASH_SCHEMA,
    REPO_BEHAVIORAL_PROBE_CONTRACT_SCHEMA,
    CanonicalizationRuleRow,
    ExpectedObservationProvenance,
    ManifestScope,
    OwnerSurfaceRow,
    RepoBehavioralCanonicalizationProfile,
    RepoBehavioralObservationHash,
    RepoBehavioralProbeContract,
    RepoBehavioralRegressionDiff,
    RepoBehavioralReplayManifest,
    RepoBehavioralReplayManifestValidationReport,
    RepoBehavioralSuiteRootHashReport,
    SuiteRootPerProbeHashRow,
    SurfacePolicy,
    canonical_hash,
    hash_bytes,
    hash_file_tree,
    replay_manifest,
    suite_root_hash_for,
    validate_replay_manifest,
)
from pydantic import ValidationError


def _hash(label: str) -> str:
    return "sha256:" + sha256(label.encode("utf-8")).hexdigest()


def _profile(**overrides: object) -> RepoBehavioralCanonicalizationProfile:
    payload: dict[str, object] = {
        "schema": REPO_BEHAVIORAL_CANONICALIZATION_PROFILE_SCHEMA,
        "canonicalization_profile_ref": "profile:default",
        "profile_version": "v1",
        "text_rules": [],
        "structured_rules": [],
        "path_rules": [],
        "ordering_rules": [],
        "file_tree_rules": ["hash_tree"],
        "process_rules": [],
        "timing_rules": [],
        "forbidden_normalizations": ["exit_code", "stderr", "output_file_tree"],
        "rule_rows": [
            CanonicalizationRuleRow(
                rule_id="rule:stdout",
                rule_kind="text_replace",
                applies_to_surfaces=["stdout"],
                scope="stable stdout hashing",
                protected_surface_effect="preserves_protected_signal",
            )
        ],
    }
    payload.update(overrides)
    profile_without_hash = RepoBehavioralCanonicalizationProfile.model_validate(payload)
    hashed = profile_without_hash.model_dump(mode="json", exclude_none=True)
    hashed["profile_hash"] = canonical_hash(
        profile_without_hash,
        object_kind="repo_behavioral_canonicalization_profile",
        drop_keys={"profile_hash"},
    )
    return RepoBehavioralCanonicalizationProfile.model_validate(hashed)


def _surface_policy(**overrides: object) -> SurfacePolicy:
    payload: dict[str, object] = {
        "raw_observed_surfaces": [
            "exit_code",
            "stdout",
            "stderr",
            "output_file_tree",
            "timeout_status",
        ],
        "canonicalized_surfaces": [
            "stdout",
            "stderr",
            "output_file_tree",
            "timeout_status",
        ],
        "protected_surfaces": [
            "exit_code",
            "stdout",
            "stderr",
            "output_file_tree",
            "timeout_status",
        ],
        "explicitly_ignored_surfaces": [],
    }
    payload.update(overrides)
    return SurfacePolicy.model_validate(payload)


def _probe(
    *,
    profile: RepoBehavioralCanonicalizationProfile,
    cwd_ref: str,
    fixture_tree_hash_before: str,
    argv_code: str,
    expected_observation_hash_ref: str = "obs:probe",
    probe_id: str = "probe:default",
    fixture_tree_protection_kind: str = "read_only",
    workspace_write_allowlist: list[str] | None = None,
    surface_policy: SurfacePolicy | None = None,
) -> RepoBehavioralProbeContract:
    payload: dict[str, object] = {
        "schema": REPO_BEHAVIORAL_PROBE_CONTRACT_SCHEMA,
        "probe_id": probe_id,
        "probe_label": "default probe",
        "owner_surface": "output_router_renderer",
        "protected_sibling_group_ref": "siblings:renderer",
        "argv": [sys.executable, "-c", argv_code],
        "stdin_ref": None,
        "env_delta": {},
        "cwd_ref": cwd_ref,
        "fixture_tree_hash_before": fixture_tree_hash_before,
        "fixture_tree_hash_after_expected": None,
        "fixture_tree_protection_kind": fixture_tree_protection_kind,
        "workspace_write_allowlist": workspace_write_allowlist or [],
        "cleanup_policy_ref": None,
        "protected_surfaces": [
            "exit_code",
            "stdout",
            "stderr",
            "output_file_tree",
            "timeout_status",
        ],
        "surface_policy": surface_policy or _surface_policy(),
        "fixture_policy": "fixture tree policy",
        "timeout_policy_ref": "timeout:short",
        "canonicalization_profile_ref": profile.canonicalization_profile_ref,
        "canonicalization_profile_hash": profile.profile_hash,
        "expected_observation_hash_ref": expected_observation_hash_ref,
    }
    probe_without_hash = RepoBehavioralProbeContract.model_validate(payload)
    hashed = probe_without_hash.model_dump(mode="json", exclude_none=True)
    hashed["probe_contract_hash"] = canonical_hash(
        probe_without_hash,
        object_kind="repo_behavioral_probe_contract",
        canonicalization_profile_hash=profile.profile_hash,
        drop_keys={"probe_contract_hash"},
    )
    return RepoBehavioralProbeContract.model_validate(hashed)


def _provenance() -> ExpectedObservationProvenance:
    return ExpectedObservationProvenance(
        provenance_kind="locked_local_probe",
        source_ref="artifacts/replay/default.json",
        source_hash=_hash("source"),
        authority_layer="support",
        evidence_boundary_posture="local_locked_probe_delta",
        clean_first_pass_posture="clean",
        authority_posture="locked_local_probe",
    )


def _expected_observation(
    *,
    probe: RepoBehavioralProbeContract,
    stdout: bytes = b"ok",
    stderr: bytes = b"warn",
    exit_code: int = 0,
    file_tree_hash: str,
    timeout_status: str = "completed",
) -> RepoBehavioralObservationHash:
    observation_without_hash = RepoBehavioralObservationHash(
        schema=REPO_BEHAVIORAL_OBSERVATION_HASH_SCHEMA,
        observation_hash_ref=probe.expected_observation_hash_ref,
        probe_id=probe.probe_id,
        hash_algorithm="sha256",
        canonical_material_kind="exit_stdout_stderr_files_timeout",
        hash_domain="expected_reference_observation",
        exit_code=exit_code,
        stdout_hash=hash_bytes(stdout, domain="stdout"),
        stderr_hash=hash_bytes(stderr, domain="stderr"),
        output_file_tree_hash=file_tree_hash,
        process_state_hash=None,
        timeout_status=timeout_status,
        expected_observation_provenance=_provenance(),
    )
    hashed = observation_without_hash.model_dump(mode="json", exclude_none=True)
    hashed["canonical_observation_hash"] = canonical_hash(
        observation_without_hash,
        object_kind="repo_behavioral_observation_hash",
        drop_keys={"canonical_observation_hash"},
    )
    return RepoBehavioralObservationHash.model_validate(hashed)


def _manifest(
    *,
    profile: RepoBehavioralCanonicalizationProfile,
    probes: list[RepoBehavioralProbeContract],
    observations: list[RepoBehavioralObservationHash],
) -> RepoBehavioralReplayManifest:
    suite_hash = suite_root_hash_for(
        probe_contract_refs=[probe.probe_id for probe in probes],
        probe_contract_hashes=[probe.probe_contract_hash for probe in probes],
        expected_observation_hash_refs=[
            observation.observation_hash_ref for observation in observations
        ],
        expected_observation_hashes=[
            observation.canonical_observation_hash for observation in observations
        ],
        canonicalization_profile_ref=profile.canonicalization_profile_ref,
        canonicalization_profile_hash=profile.profile_hash,
    )
    payload = {
        "schema": "repo_behavioral_replay_manifest@1",
        "manifest_id": "manifest:test",
        "manifest_version": "v1",
        "manifest_authority_layer": "support",
        "manifest_lifecycle_state": "locked",
        "manifest_visibility_posture": "implementation_visible_regression",
        "manifest_scope": ManifestScope(
            bounded_claim="no observed regression over test manifest",
            certificate_use_allowed=False,
            promotion_use_allowed=False,
        ),
        "product_ref": "product:test",
        "candidate_artifact_kind": "python_script",
        "protected_owner_surfaces": ["output_router_renderer"],
        "owner_surface_rows": [
            OwnerSurfaceRow(
                owner_surface="output_router_renderer",
                patch_risk_kind="output_router_renderer",
                protected_sibling_probe_refs=[probe.probe_id for probe in probes],
                required_when_touched=True,
                coverage_posture="sentinel_required",
                taxonomy_ref="docs/support/general_program_ontology_derived_v1_7.md",
            )
        ],
        "owner_surface_map_ref": "owner-map:test",
        "owner_surface_map_hash": _hash("owner-map"),
        "owner_surface_taxonomy_version": "gpo-v1.7",
        "canonicalization_profile_ref": profile.canonicalization_profile_ref,
        "canonicalization_profile_hash": profile.profile_hash,
        "execution_environment_ref": "env:test",
        "execution_environment_hash": _hash("env"),
        "sensitive_material_policy_ref": "policy:sensitive",
        "safe_rendering_policy_ref": "policy:safe-rendering",
        "raw_material_storage_policy_ref": "policy:raw-storage",
        "redaction_profile_ref": "policy:redaction",
        "probe_contract_refs": [probe.probe_id for probe in probes],
        "probe_contract_hashes": [probe.probe_contract_hash for probe in probes],
        "expected_observation_hash_refs": [
            observation.observation_hash_ref for observation in observations
        ],
        "expected_observation_hashes": [
            observation.canonical_observation_hash for observation in observations
        ],
        "suite_root_hash": suite_hash,
    }
    manifest_without_hash = RepoBehavioralReplayManifest.model_validate(payload)
    hashed = manifest_without_hash.model_dump(mode="json", exclude_none=True)
    hashed["manifest_hash"] = canonical_hash(
        manifest_without_hash,
        object_kind="repo_behavioral_replay_manifest",
        canonicalization_profile_hash=profile.profile_hash,
        drop_keys={"manifest_hash"},
    )
    return RepoBehavioralReplayManifest.model_validate(hashed)


def _valid_bundle(
    tmp_path: Path,
    *,
    argv_code: str = "import sys; sys.stdout.write('ok'); sys.stderr.write('warn')",
    expected_stdout: bytes = b"ok",
    expected_stderr: bytes = b"warn",
    expected_exit: int = 0,
    expected_file_tree_hash: str | None = None,
    probe_overrides: dict[str, object] | None = None,
) -> tuple[
    RepoBehavioralCanonicalizationProfile,
    RepoBehavioralProbeContract,
    RepoBehavioralObservationHash,
    RepoBehavioralReplayManifest,
    RepoBehavioralReplayManifestValidationReport,
]:
    cwd_ref = "cwd:test"
    before_hash = hash_file_tree(tmp_path)
    profile = _profile()
    probe_kwargs = dict(
        profile=profile,
        cwd_ref=cwd_ref,
        fixture_tree_hash_before=before_hash,
        argv_code=argv_code,
    )
    if probe_overrides:
        probe_kwargs.update(probe_overrides)
    probe = _probe(**probe_kwargs)
    observation = _expected_observation(
        probe=probe,
        stdout=expected_stdout,
        stderr=expected_stderr,
        exit_code=expected_exit,
        file_tree_hash=expected_file_tree_hash or before_hash,
    )
    manifest = _manifest(profile=profile, probes=[probe], observations=[observation])
    validation_report = validate_replay_manifest(
        manifest=manifest,
        probe_contracts=[probe],
        canonicalization_profiles=[profile],
        expected_observation_hashes=[observation],
    )
    assert validation_report.validation_status == "valid_for_manifest_lock"
    return profile, probe, observation, manifest, validation_report


def _run(
    tmp_path: Path,
    *,
    profile: RepoBehavioralCanonicalizationProfile,
    probe: RepoBehavioralProbeContract,
    observation: RepoBehavioralObservationHash,
    manifest: RepoBehavioralReplayManifest,
    validation_report: RepoBehavioralReplayManifestValidationReport,
    timeout_seconds: float = 2,
):
    return replay_manifest(
        manifest=manifest,
        manifest_validation_report=validation_report,
        probe_contracts=[probe],
        canonicalization_profile=profile,
        expected_observation_hashes=[observation],
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
        cwd_map={"cwd:test": tmp_path},
        timeout_seconds_by_ref={"timeout:short": timeout_seconds},
        env_base={},
    )


def test_green_manifest_replays_to_matching_observation_and_suite_root(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(tmp_path)
    execution, records, diffs, suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
    )
    assert execution.execution_status == "completed"
    assert records[0].canonical_stdout_hash == observation.stdout_hash
    assert diffs[0].diff_status == "match"
    assert suite.suite_root_status == "match"
    assert suite.actual_suite_root_hash == manifest.suite_root_hash


def test_manifest_validation_failure_blocks_replay(tmp_path: Path) -> None:
    profile, probe, observation, manifest, _report = _valid_bundle(tmp_path)
    invalid_report = validate_replay_manifest(
        manifest=manifest,
        probe_contracts=[probe],
        canonicalization_profiles=[profile],
        expected_observation_hashes=[],
    )
    execution, records, diffs, suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=invalid_report,
    )
    assert execution.execution_status == "blocked_by_manifest_validation"
    assert records == []
    assert diffs[0].diff_status == "blocked_by_manifest_validation"
    assert suite.suite_root_status == "blocked_by_manifest_validation"


def test_stale_manifest_hash_blocks_replay(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(tmp_path)
    stale_report = RepoBehavioralReplayManifestValidationReport(
        schema="repo_behavioral_replay_manifest_validation_report@1",
        validation_report_ref=report.validation_report_ref,
        manifest_id=manifest.manifest_id,
        manifest_hash=_hash("stale-manifest"),
        validation_status="valid_for_manifest_lock",
        diagnostic_rows=[],
    )
    execution, _records, diffs, _suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=stale_report,
    )
    assert execution.execution_status == "blocked_by_manifest_validation"
    assert diffs[0].diff_status == "blocked_by_manifest_validation"


def test_stale_probe_contract_hash_blocks_replay(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(tmp_path)
    changed_probe = _probe(
        profile=profile,
        cwd_ref=probe.cwd_ref,
        fixture_tree_hash_before=probe.fixture_tree_hash_before,
        argv_code="import sys; sys.stdout.write('different')",
        probe_id=probe.probe_id,
    )
    execution, _records, diffs, _suite = replay_manifest(
        manifest=manifest,
        manifest_validation_report=report,
        probe_contracts=[changed_probe],
        canonicalization_profile=profile,
        expected_observation_hashes=[observation],
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
        cwd_map={"cwd:test": tmp_path},
        timeout_seconds_by_ref={"timeout:short": 2},
        env_base={},
    )
    assert execution.execution_status == "blocked_by_manifest_validation"
    assert diffs[0].diff_status == "blocked_by_manifest_validation"


def test_stale_canonicalization_profile_hash_blocks_replay(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(tmp_path)
    changed_profile = _profile(
        rule_rows=[
            CanonicalizationRuleRow(
                rule_id="rule:changed",
                rule_kind="text_replace",
                applies_to_surfaces=["stdout"],
                scope="changed",
                protected_surface_effect="preserves_protected_signal",
            )
        ]
    )
    execution, _records, diffs, _suite = replay_manifest(
        manifest=manifest,
        manifest_validation_report=report,
        probe_contracts=[probe],
        canonicalization_profile=changed_profile,
        expected_observation_hashes=[observation],
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
        cwd_map={"cwd:test": tmp_path},
        timeout_seconds_by_ref={"timeout:short": 2},
        env_base={},
    )
    assert execution.execution_status == "blocked_by_manifest_validation"
    assert diffs[0].diff_status == "blocked_by_manifest_validation"


def test_candidate_artifact_identity_is_required(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(tmp_path)
    with pytest.raises(ValueError, match="candidate_artifact_ref"):
        replay_manifest(
            manifest=manifest,
            manifest_validation_report=report,
            probe_contracts=[probe],
            canonicalization_profile=profile,
            expected_observation_hashes=[observation],
            candidate_artifact_ref="",
            candidate_artifact_hash=_hash("candidate"),
            cwd_map={"cwd:test": tmp_path},
            timeout_seconds_by_ref={"timeout:short": 2},
            env_base={},
        )


def test_missing_protected_stdout_capture_fails_closed(tmp_path: Path) -> None:
    policy = _surface_policy(raw_observed_surfaces=["exit_code", "stderr", "output_file_tree"])
    profile, probe, observation, manifest, report = _valid_bundle(
        tmp_path,
        probe_overrides={"surface_policy": policy},
    )
    execution, _records, diffs, suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
    )
    assert execution.execution_status == "capture_failed"
    assert diffs[0].diff_status == "capture_failed"
    assert suite.suite_root_status == "capture_failed"


def test_changed_stdout_emits_structured_diff(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(
        tmp_path,
        argv_code="import sys; sys.stdout.write('changed'); sys.stderr.write('warn')",
    )
    execution, _records, diffs, suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
    )
    assert execution.execution_status == "completed_with_diffs"
    assert diffs[0].changed_surfaces == ["stdout"]
    assert suite.suite_root_status == "diff"


def test_changed_stderr_emits_structured_diff(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(
        tmp_path,
        argv_code="import sys; sys.stdout.write('ok'); sys.stderr.write('changed')",
    )
    _execution, _records, diffs, _suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
    )
    assert diffs[0].changed_surfaces == ["stderr"]


def test_changed_exit_code_emits_structured_diff(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(
        tmp_path,
        argv_code="import sys; sys.stdout.write('ok'); sys.stderr.write('warn'); sys.exit(3)",
    )
    _execution, _records, diffs, _suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
    )
    assert diffs[0].changed_surfaces == ["exit_code"]


def test_changed_file_tree_hash_emits_structured_diff(tmp_path: Path) -> None:
    code = (
        "from pathlib import Path; import sys; "
        "Path('created.txt').write_text('x'); "
        "sys.stdout.write('ok'); sys.stderr.write('warn')"
    )
    profile, probe, observation, manifest, report = _valid_bundle(
        tmp_path,
        argv_code=code,
        probe_overrides={
            "fixture_tree_protection_kind": "workspace_mutation_allowed",
            "workspace_write_allowlist": ["created.txt"],
        },
    )
    _execution, _records, diffs, _suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
    )
    assert diffs[0].changed_surfaces == ["output_files"]


def test_timeout_is_reported_without_updating_expected_hashes(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(
        tmp_path,
        argv_code="import time; time.sleep(1)",
    )
    execution, _records, diffs, _suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
        timeout_seconds=0.01,
    )
    assert execution.probe_execution_rows[0].execution_status == "timeout"
    assert diffs[0].diff_status == "diff"
    assert observation.canonical_observation_hash == manifest.expected_observation_hashes[0]


def test_fixture_mutation_contrary_to_policy_fails_closed(tmp_path: Path) -> None:
    code = (
        "from pathlib import Path; import sys; "
        "Path('created.txt').write_text('x'); "
        "sys.stdout.write('ok'); sys.stderr.write('warn')"
    )
    profile, probe, observation, manifest, report = _valid_bundle(tmp_path, argv_code=code)
    execution, _records, diffs, suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
    )
    assert execution.probe_execution_rows[0].execution_status == "fixture_mutation_forbidden"
    assert diffs[0].diff_status == "capture_failed"
    assert suite.suite_root_status == "capture_failed"


def test_expected_hash_update_attempt_is_reported_as_diff(tmp_path: Path) -> None:
    profile, probe, observation, manifest, report = _valid_bundle(
        tmp_path,
        argv_code="import sys; sys.stdout.write('changed'); sys.stderr.write('warn')",
    )
    before = observation.canonical_observation_hash
    _execution, _records, diffs, _suite = _run(
        tmp_path,
        profile=profile,
        probe=probe,
        observation=observation,
        manifest=manifest,
        validation_report=report,
    )
    assert diffs[0].diff_status == "diff"
    assert observation.canonical_observation_hash == before
    assert diffs[0].expected_canonical_observation_hash == before
    assert diffs[0].actual_canonical_observation_hash != before


def test_suite_root_hash_report_is_deterministic_under_shuffled_rows() -> None:
    row_a = SuiteRootPerProbeHashRow(
        probe_id="probe:a",
        expected_observation_hash_ref="obs:a",
        expected_canonical_observation_hash=_hash("expected-a"),
        actual_canonical_observation_hash=_hash("expected-a"),
        diff_status="match",
    )
    row_b = SuiteRootPerProbeHashRow(
        probe_id="probe:b",
        expected_observation_hash_ref="obs:b",
        expected_canonical_observation_hash=_hash("expected-b"),
        actual_canonical_observation_hash=_hash("expected-b"),
        diff_status="match",
    )
    first = RepoBehavioralSuiteRootHashReport(
        schema="repo_behavioral_suite_root_hash_report@1",
        suite_root_hash_report_ref="suite:test",
        manifest_id="manifest:test",
        manifest_hash=_hash("manifest"),
        expected_suite_root_hash=_hash("suite"),
        actual_suite_root_hash=_hash("suite"),
        per_probe_hash_rows=[row_b, row_a],
        suite_root_status="match",
        authority_posture="suite_hash_report_only_not_certificate",
    )
    second = RepoBehavioralSuiteRootHashReport(
        schema="repo_behavioral_suite_root_hash_report@1",
        suite_root_hash_report_ref="suite:test",
        manifest_id="manifest:test",
        manifest_hash=_hash("manifest"),
        expected_suite_root_hash=_hash("suite"),
        actual_suite_root_hash=_hash("suite"),
        per_probe_hash_rows=[row_a, row_b],
        suite_root_status="match",
        authority_posture="suite_hash_report_only_not_certificate",
    )
    assert canonical_hash(
        first,
        object_kind="repo_behavioral_suite_root_hash_report",
        drop_keys={"canonical_output_hash"},
    ) == canonical_hash(
        second,
        object_kind="repo_behavioral_suite_root_hash_report",
        drop_keys={"canonical_output_hash"},
    )


def test_suite_root_report_cannot_claim_certificate_authority() -> None:
    row = SuiteRootPerProbeHashRow(
        probe_id="probe:a",
        expected_observation_hash_ref="obs:a",
        expected_canonical_observation_hash=_hash("expected-a"),
        actual_canonical_observation_hash=_hash("expected-a"),
        diff_status="match",
    )
    with pytest.raises(ValidationError):
        RepoBehavioralSuiteRootHashReport.model_validate(
            {
                "schema": "repo_behavioral_suite_root_hash_report@1",
                "suite_root_hash_report_ref": "suite:test",
                "manifest_id": "manifest:test",
                "manifest_hash": _hash("manifest"),
                "expected_suite_root_hash": _hash("suite"),
                "actual_suite_root_hash": _hash("suite"),
                "per_probe_hash_rows": [row],
                "suite_root_status": "match",
                "authority_posture": "no_regression_certificate",
            }
        )


def test_diff_report_cannot_claim_patch_authority() -> None:
    with pytest.raises(ValidationError):
        RepoBehavioralRegressionDiff.model_validate(
            {
                "schema": "repo_behavioral_regression_diff@1",
                "diff_ref": "diff:test",
                "probe_id": "probe:test",
                "expected_observation_hash_ref": "obs:test",
                "diff_status": "match",
                "changed_surfaces": [],
                "structured_diff_rows": [],
                "authority_posture": "patch_authority",
            }
        )
