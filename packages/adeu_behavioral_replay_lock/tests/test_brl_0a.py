from __future__ import annotations

from copy import deepcopy
from hashlib import sha256

import pytest
from adeu_behavioral_replay_lock import (
    REPO_BEHAVIORAL_CANONICALIZATION_PROFILE_SCHEMA,
    REPO_BEHAVIORAL_OBSERVATION_HASH_SCHEMA,
    REPO_BEHAVIORAL_PROBE_CONTRACT_SCHEMA,
    REPO_BEHAVIORAL_REPLAY_MANIFEST_SCHEMA,
    CanonicalizationRuleRow,
    ExpectedObservationProvenance,
    ManifestScope,
    OwnerSurfaceRow,
    RepoBehavioralCanonicalizationProfile,
    RepoBehavioralObservationHash,
    RepoBehavioralProbeContract,
    RepoBehavioralReplayLockNonAuthorityGuardrail,
    RepoBehavioralReplayManifest,
    SurfacePolicy,
    canonical_hash,
    default_non_authority_guardrail,
    suite_root_hash_for,
    validate_replay_manifest,
)
from pydantic import ValidationError


def _hash(label: str) -> str:
    return "sha256:" + sha256(label.encode("utf-8")).hexdigest()


def _profile_payload(**overrides: object) -> dict[str, object]:
    payload: dict[str, object] = {
        "schema": REPO_BEHAVIORAL_CANONICALIZATION_PROFILE_SCHEMA,
        "canonicalization_profile_ref": "profile:default",
        "profile_version": "v1",
        "text_rules": ["strip_ansi"],
        "structured_rules": [],
        "path_rules": [],
        "ordering_rules": [],
        "file_tree_rules": ["hash_tree"],
        "process_rules": [],
        "timing_rules": [],
        "forbidden_normalizations": ["exit_code", "stderr", "output_file_tree"],
        "rule_rows": [
            {
                "rule_id": "rule:stdout",
                "rule_kind": "text_replace",
                "applies_to_surfaces": ["stdout"],
                "scope": "normalize volatile temp roots",
                "protected_surface_effect": "preserves_protected_signal",
            }
        ],
    }
    payload.update(overrides)
    return payload


def _profile(**overrides: object) -> RepoBehavioralCanonicalizationProfile:
    profile_without_hash = RepoBehavioralCanonicalizationProfile.model_validate(
        _profile_payload(**overrides)
    )
    payload = profile_without_hash.model_dump(mode="json", exclude_none=True)
    payload["profile_hash"] = canonical_hash(
        profile_without_hash,
        object_kind="repo_behavioral_canonicalization_profile",
        drop_keys={"profile_hash"},
    )
    return RepoBehavioralCanonicalizationProfile.model_validate(payload)


def _surface_policy(**overrides: object) -> SurfacePolicy:
    payload: dict[str, object] = {
        "raw_observed_surfaces": ["exit_code", "stdout", "stderr", "output_file_tree"],
        "canonicalized_surfaces": ["stdout", "stderr", "output_file_tree"],
        "protected_surfaces": ["exit_code", "stdout", "stderr", "output_file_tree"],
        "explicitly_ignored_surfaces": [],
    }
    payload.update(overrides)
    return SurfacePolicy.model_validate(payload)


def _probe_payload(
    profile: RepoBehavioralCanonicalizationProfile,
    **overrides: object,
) -> dict[str, object]:
    payload: dict[str, object] = {
        "schema": REPO_BEHAVIORAL_PROBE_CONTRACT_SCHEMA,
        "probe_id": "probe:formatter-default",
        "probe_label": "formatter default",
        "owner_surface": "output_router_renderer",
        "protected_sibling_group_ref": "siblings:formatter",
        "argv": ["revive", "./..."],
        "stdin_ref": None,
        "env_delta": {},
        "cwd_ref": "fixture:repo",
        "fixture_tree_hash_before": _hash("fixture-before"),
        "fixture_tree_hash_after_expected": None,
        "fixture_tree_protection_kind": "read_only",
        "workspace_write_allowlist": [],
        "cleanup_policy_ref": None,
        "protected_surfaces": ["exit_code", "stdout", "stderr", "output_file_tree"],
        "surface_policy": _surface_policy(),
        "fixture_policy": "read-only fixture tree",
        "timeout_policy_ref": "timeout:short",
        "canonicalization_profile_ref": profile.canonicalization_profile_ref,
        "canonicalization_profile_hash": profile.profile_hash,
        "expected_observation_hash_ref": "obs:formatter-default",
    }
    payload.update(overrides)
    return payload


def _probe(
    profile: RepoBehavioralCanonicalizationProfile,
    **overrides: object,
) -> RepoBehavioralProbeContract:
    probe_without_hash = RepoBehavioralProbeContract.model_validate(
        _probe_payload(profile, **overrides)
    )
    payload = probe_without_hash.model_dump(mode="json", exclude_none=True)
    payload["probe_contract_hash"] = canonical_hash(
        probe_without_hash,
        object_kind="repo_behavioral_probe_contract",
        canonicalization_profile_hash=profile.profile_hash,
        drop_keys={"probe_contract_hash"},
    )
    return RepoBehavioralProbeContract.model_validate(payload)


def _provenance(**overrides: object) -> ExpectedObservationProvenance:
    payload: dict[str, object] = {
        "provenance_kind": "locked_local_probe",
        "source_ref": "artifacts/replay/formatter-default.json",
        "source_hash": _hash("source"),
        "authority_layer": "support",
        "evidence_boundary_posture": "local_locked_probe_delta",
        "clean_first_pass_posture": "clean",
        "authority_posture": "locked_local_probe",
    }
    payload.update(overrides)
    return ExpectedObservationProvenance.model_validate(payload)


def _observation_payload(
    probe: RepoBehavioralProbeContract,
    **overrides: object,
) -> dict[str, object]:
    payload: dict[str, object] = {
        "schema": REPO_BEHAVIORAL_OBSERVATION_HASH_SCHEMA,
        "observation_hash_ref": probe.expected_observation_hash_ref,
        "probe_id": probe.probe_id,
        "hash_algorithm": "sha256",
        "canonical_material_kind": "exit_stdout_stderr_files",
        "hash_domain": "expected_reference_observation",
        "exit_code": 0,
        "stdout_hash": _hash("stdout"),
        "stderr_hash": _hash("stderr"),
        "output_file_tree_hash": _hash("files"),
        "process_state_hash": None,
        "timeout_status": "completed",
        "expected_observation_provenance": _provenance(),
    }
    payload.update(overrides)
    return payload


def _observation(
    probe: RepoBehavioralProbeContract,
    **overrides: object,
) -> RepoBehavioralObservationHash:
    observation_without_hash = RepoBehavioralObservationHash.model_validate(
        _observation_payload(probe, **overrides)
    )
    payload = observation_without_hash.model_dump(mode="json", exclude_none=True)
    payload["canonical_observation_hash"] = canonical_hash(
        observation_without_hash,
        object_kind="repo_behavioral_observation_hash",
        drop_keys={"canonical_observation_hash"},
    )
    return RepoBehavioralObservationHash.model_validate(payload)


def _owner_rows(probe: RepoBehavioralProbeContract) -> list[OwnerSurfaceRow]:
    return [
        OwnerSurfaceRow(
            owner_surface=probe.owner_surface,
            patch_risk_kind="output_router_renderer",
            protected_sibling_probe_refs=[probe.probe_id],
            required_when_touched=True,
            coverage_posture="sentinel_required",
            local_extension_posture="none",
            taxonomy_ref="docs/support/general_program_ontology_derived_v1_7.md",
        )
    ]


def _manifest_payload(
    profile: RepoBehavioralCanonicalizationProfile,
    probe: RepoBehavioralProbeContract,
    observation: RepoBehavioralObservationHash,
    **overrides: object,
) -> dict[str, object]:
    suite_root_hash = suite_root_hash_for(
        probe_contract_refs=[probe.probe_id],
        expected_observation_hash_refs=[observation.observation_hash_ref],
        canonicalization_profile_ref=profile.canonicalization_profile_ref,
        canonicalization_profile_hash=profile.profile_hash,
    )
    payload: dict[str, object] = {
        "schema": REPO_BEHAVIORAL_REPLAY_MANIFEST_SCHEMA,
        "manifest_id": "revive-tail-lock",
        "manifest_version": "v1",
        "manifest_authority_layer": "support",
        "manifest_lifecycle_state": "locked",
        "manifest_visibility_posture": "implementation_visible_regression",
        "manifest_scope": ManifestScope(
            bounded_claim="no observed regression over revive tail manifest",
            certificate_use_allowed=False,
            promotion_use_allowed=False,
        ),
        "product_ref": "programbench/revive",
        "candidate_artifact_kind": "python_package",
        "protected_owner_surfaces": [probe.owner_surface],
        "owner_surface_rows": _owner_rows(probe),
        "owner_surface_map_ref": "owner-map:revive-tail",
        "owner_surface_map_hash": _hash("owner-map"),
        "owner_surface_taxonomy_version": "gpo-v1.7",
        "canonicalization_profile_ref": profile.canonicalization_profile_ref,
        "canonicalization_profile_hash": profile.profile_hash,
        "execution_environment_ref": "env:local",
        "execution_environment_hash": _hash("env"),
        "sensitive_material_policy_ref": "policy:sensitive",
        "safe_rendering_policy_ref": "policy:safe-rendering",
        "raw_material_storage_policy_ref": "policy:raw-storage",
        "redaction_profile_ref": "policy:redaction",
        "probe_contract_refs": [probe.probe_id],
        "expected_observation_hash_refs": [observation.observation_hash_ref],
        "suite_root_hash": suite_root_hash,
    }
    payload.update(overrides)
    return payload


def _manifest(
    profile: RepoBehavioralCanonicalizationProfile,
    probe: RepoBehavioralProbeContract,
    observation: RepoBehavioralObservationHash,
    **overrides: object,
) -> RepoBehavioralReplayManifest:
    manifest_without_hash = RepoBehavioralReplayManifest.model_validate(
        _manifest_payload(profile, probe, observation, **overrides)
    )
    payload = manifest_without_hash.model_dump(mode="json", exclude_none=True)
    payload["manifest_hash"] = canonical_hash(
        manifest_without_hash,
        object_kind="repo_behavioral_replay_manifest",
        canonicalization_profile_hash=profile.profile_hash,
        drop_keys={"manifest_hash"},
    )
    return RepoBehavioralReplayManifest.model_validate(payload)


def _valid_bundle() -> tuple[
    RepoBehavioralCanonicalizationProfile,
    RepoBehavioralProbeContract,
    RepoBehavioralObservationHash,
    RepoBehavioralReplayManifest,
]:
    profile = _profile()
    probe = _probe(profile)
    observation = _observation(probe)
    manifest = _manifest(profile, probe, observation)
    return profile, probe, observation, manifest


def test_valid_manifest_validates() -> None:
    profile, probe, observation, manifest = _valid_bundle()
    report = validate_replay_manifest(
        manifest=manifest,
        probe_contracts=[probe],
        canonicalization_profiles=[profile],
        expected_observation_hashes=[observation],
    )
    assert report.validation_status == "valid_for_manifest_lock"
    assert report.diagnostic_rows == []
    assert report.canonical_output_hash is not None


def test_shuffled_owner_rows_keep_manifest_hash_stable() -> None:
    profile = _profile()
    probe_a = _probe(profile)
    probe_b = _probe(
        profile,
        probe_id="probe:diagnostic-default",
        probe_label="diagnostic default",
        owner_surface="diagnostic_exit_channel",
        protected_sibling_group_ref="siblings:diagnostic",
        expected_observation_hash_ref="obs:diagnostic-default",
    )
    observation_a = _observation(probe_a)
    observation_b = _observation(probe_b)
    rows = _owner_rows(probe_a) + [
        OwnerSurfaceRow(
            owner_surface=probe_b.owner_surface,
            patch_risk_kind="diagnostic_exit_channel",
            protected_sibling_probe_refs=[probe_b.probe_id],
            required_when_touched=True,
            coverage_posture="sentinel_required",
            taxonomy_ref="docs/support/general_program_ontology_derived_v1_7.md",
        )
    ]
    suite_hash = suite_root_hash_for(
        probe_contract_refs=[probe_b.probe_id, probe_a.probe_id],
        expected_observation_hash_refs=[
            observation_b.observation_hash_ref,
            observation_a.observation_hash_ref,
        ],
        canonicalization_profile_ref=profile.canonicalization_profile_ref,
        canonicalization_profile_hash=profile.profile_hash,
    )
    base_payload = _manifest_payload(
        profile,
        probe_a,
        observation_a,
        protected_owner_surfaces=[probe_b.owner_surface, probe_a.owner_surface],
        owner_surface_rows=list(reversed(rows)),
        probe_contract_refs=[probe_b.probe_id, probe_a.probe_id],
        expected_observation_hash_refs=[
            observation_b.observation_hash_ref,
            observation_a.observation_hash_ref,
        ],
        suite_root_hash=suite_hash,
    )
    first = RepoBehavioralReplayManifest.model_validate(base_payload)
    second_payload = deepcopy(base_payload)
    second_payload["owner_surface_rows"] = rows
    second_payload["probe_contract_refs"] = [probe_a.probe_id, probe_b.probe_id]
    second_payload["expected_observation_hash_refs"] = [
        observation_a.observation_hash_ref,
        observation_b.observation_hash_ref,
    ]
    second = RepoBehavioralReplayManifest.model_validate(second_payload)
    assert canonical_hash(
        first,
        object_kind="repo_behavioral_replay_manifest",
        canonicalization_profile_hash=profile.profile_hash,
        drop_keys={"manifest_hash"},
    ) == canonical_hash(
        second,
        object_kind="repo_behavioral_replay_manifest",
        canonicalization_profile_hash=profile.profile_hash,
        drop_keys={"manifest_hash"},
    )


def test_duplicate_probe_ids_fail_validation_report() -> None:
    profile, probe, observation, manifest = _valid_bundle()
    report = validate_replay_manifest(
        manifest=manifest,
        probe_contracts=[probe, probe],
        canonicalization_profiles=[profile],
        expected_observation_hashes=[observation],
    )
    assert report.validation_status == "invalid"
    assert report.diagnostic_rows[0].diagnostic_code == "duplicate_probe_id"


def test_missing_expected_observation_hash_fails_report() -> None:
    profile, probe, _observation, manifest = _valid_bundle()
    report = validate_replay_manifest(
        manifest=manifest,
        probe_contracts=[probe],
        canonicalization_profiles=[profile],
        expected_observation_hashes=[],
    )
    assert report.validation_status == "invalid"
    assert {
        row.diagnostic_code for row in report.diagnostic_rows
    } == {"missing_expected_observation_hash"}


def test_unknown_canonicalization_rule_kind_fails() -> None:
    payload = _profile_payload()
    payload["rule_rows"] = [
        {
            "rule_id": "rule:bad",
            "rule_kind": "drop_everything",
            "applies_to_surfaces": ["stdout"],
            "scope": "bad",
            "protected_surface_effect": "preserves_protected_signal",
        }
    ]
    with pytest.raises(ValidationError):
        RepoBehavioralCanonicalizationProfile.model_validate(payload)


def test_empty_protected_surface_set_fails() -> None:
    profile = _profile()
    with pytest.raises(ValidationError, match="protected surfaces must not be empty"):
        _probe(
            profile,
            protected_surfaces=[],
            surface_policy=_surface_policy(protected_surfaces=[]),
        )


def test_file_tree_protection_without_fixture_hash_fails() -> None:
    profile = _profile()
    with pytest.raises(ValidationError, match="output_file_tree protection requires"):
        _probe(profile, fixture_tree_hash_before=None)


def test_suite_root_mismatch_fails() -> None:
    profile, probe, observation, _manifest_obj = _valid_bundle()
    with pytest.raises(ValidationError, match="suite_root_hash must match"):
        _manifest(profile, probe, observation, suite_root_hash=_hash("wrong-suite-root"))


def test_manifest_hash_mismatch_fails() -> None:
    profile, probe, observation, _manifest_obj = _valid_bundle()
    payload = _manifest_payload(profile, probe, observation)
    payload["manifest_hash"] = _hash("wrong-manifest")
    with pytest.raises(ValidationError, match="manifest_hash must match"):
        RepoBehavioralReplayManifest.model_validate(payload)


def test_non_authority_guardrail_denies_forbidden_authorities() -> None:
    guardrail = default_non_authority_guardrail()
    assert guardrail.candidate_replay_execution_authority_granted is False
    payload = guardrail.model_dump(mode="json")
    payload["candidate_replay_execution_authority_granted"] = True
    with pytest.raises(ValidationError, match="cannot grant authority"):
        RepoBehavioralReplayLockNonAuthorityGuardrail.model_validate(payload)


def test_owner_surface_required_sentinel_fails_when_missing() -> None:
    with pytest.raises(ValidationError, match="protected sibling probes"):
        OwnerSurfaceRow(
            owner_surface="output_router_renderer",
            patch_risk_kind="output_router_renderer",
            protected_sibling_probe_refs=[],
            required_when_touched=True,
            coverage_posture="sentinel_required",
            taxonomy_ref="docs/support/general_program_ontology_derived_v1_7.md",
        )


def test_expected_hash_provenance_is_required() -> None:
    profile = _profile()
    probe = _probe(profile)
    payload = _observation_payload(probe)
    payload.pop("expected_observation_provenance")
    with pytest.raises(ValidationError):
        RepoBehavioralObservationHash.model_validate(payload)


def test_same_payload_hashes_differ_by_object_kind() -> None:
    payload = {"schema": "same@1", "value": "x"}
    assert canonical_hash(payload, object_kind="alpha") != canonical_hash(
        payload,
        object_kind="beta",
    )


def test_replayable_manifest_requires_execution_environment_profile() -> None:
    profile, probe, observation, _manifest_obj = _valid_bundle()
    with pytest.raises(ValidationError, match="execution_environment_ref"):
        _manifest(profile, probe, observation, execution_environment_ref="")


def test_protected_ignored_surface_contradiction_fails() -> None:
    with pytest.raises(ValidationError, match="protected surfaces cannot be explicitly ignored"):
        _surface_policy(explicitly_ignored_surfaces=["stderr"])


def test_canonicalization_hiding_protected_surface_fails() -> None:
    with pytest.raises(ValidationError, match="cannot hide protected behavioral surfaces"):
        _profile(
            rule_rows=[
                CanonicalizationRuleRow(
                    rule_id="rule:hide-stderr",
                    rule_kind="text_replace",
                    applies_to_surfaces=["stderr"],
                    scope="bad",
                    protected_surface_effect="hides_protected_change",
                )
            ]
        )


def test_mutating_probe_requires_after_hash_or_mutation_policy() -> None:
    profile = _profile()
    with pytest.raises(ValidationError, match="mutating probes require"):
        _probe(
            profile,
            fixture_tree_protection_kind="mutating_expected",
            fixture_tree_hash_after_expected=None,
            workspace_write_allowlist=[],
        )


def test_secret_like_env_requires_safe_policy_refs() -> None:
    profile = _profile()
    probe = _probe(profile, env_delta={"API_TOKEN": "secret-ref:test"})
    observation = _observation(probe)
    with pytest.raises(ValidationError, match="safe_rendering_policy_ref"):
        _manifest(profile, probe, observation, safe_rendering_policy_ref="")


def test_lifecycle_state_blocks_promotion_claims() -> None:
    profile, probe, observation, _manifest_obj = _valid_bundle()
    with pytest.raises(ValidationError, match="unpromotable manifest lifecycle"):
        _manifest(
            profile,
            probe,
            observation,
            manifest_lifecycle_state="draft",
            manifest_scope=ManifestScope(
                bounded_claim="no regression",
                certificate_use_allowed=True,
                promotion_use_allowed=False,
            ),
        )


def test_unknown_owner_label_requires_local_extension() -> None:
    with pytest.raises(ValidationError, match="unknown owner_surface"):
        OwnerSurfaceRow(
            owner_surface="new-owner",
            patch_risk_kind="other",
            protected_sibling_probe_refs=["probe:x"],
            required_when_touched=True,
            coverage_posture="sentinel_required",
        )
    row = OwnerSurfaceRow(
        owner_surface="new-owner",
        patch_risk_kind="other",
        protected_sibling_probe_refs=["probe:x"],
        required_when_touched=True,
        coverage_posture="sentinel_required",
        local_extension_posture="declared_local_extension",
        taxonomy_ref="docs/support/local.md",
    )
    assert row.owner_surface == "new-owner"


def test_canonicalization_profile_hash_change_changes_manifest_hash() -> None:
    profile, probe, observation, manifest = _valid_bundle()
    changed_profile_hash = _hash("changed-profile")
    changed_suite_root = suite_root_hash_for(
        probe_contract_refs=[probe.probe_id],
        expected_observation_hash_refs=[observation.observation_hash_ref],
        canonicalization_profile_ref=profile.canonicalization_profile_ref,
        canonicalization_profile_hash=changed_profile_hash,
    )
    payload = manifest.model_dump(mode="json", exclude_none=True)
    payload["canonicalization_profile_hash"] = changed_profile_hash
    payload["suite_root_hash"] = changed_suite_root
    payload.pop("manifest_hash")
    changed_manifest = RepoBehavioralReplayManifest.model_validate(payload)
    assert canonical_hash(
        manifest,
        object_kind="repo_behavioral_replay_manifest",
        canonicalization_profile_hash=profile.profile_hash,
        drop_keys={"manifest_hash"},
    ) != canonical_hash(
        changed_manifest,
        object_kind="repo_behavioral_replay_manifest",
        canonicalization_profile_hash=changed_profile_hash,
        drop_keys={"manifest_hash"},
    )
