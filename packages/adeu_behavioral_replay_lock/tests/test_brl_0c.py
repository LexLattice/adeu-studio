from __future__ import annotations

from hashlib import sha256

import pytest
from adeu_behavioral_replay_lock import (
    REPO_BEHAVIORAL_LOCK_STALENESS_REPORT_SCHEMA,
    REPO_BEHAVIORAL_NO_REGRESSION_CERTIFICATE_SCHEMA,
    OwnerSurfaceRow,
    ProbeExecutionRow,
    RepoBehavioralLockStalenessReport,
    RepoBehavioralNoRegressionCertificate,
    RepoBehavioralRegressionDiff,
    RepoBehavioralReplayExecutionReport,
    RepoBehavioralReplayIntegrationHandoff,
    RepoBehavioralReplayManifest,
    RepoBehavioralSuiteRootHashReport,
    StructuredDiffRow,
    SuiteRootPerProbeHashRow,
    build_lock_staleness_report,
    build_no_regression_certificate,
    build_replay_integration_handoff,
    canonical_hash,
    select_impact_cone,
    suite_root_hash_for,
)
from pydantic import BaseModel, ValidationError


def _hash(label: str) -> str:
    return "sha256:" + sha256(label.encode("utf-8")).hexdigest()


def _with_hash(model: BaseModel, *, object_kind: str, hash_field: str) -> object:
    payload = model.model_dump(mode="json", exclude_none=True)
    payload[hash_field] = canonical_hash(
        model,
        object_kind=object_kind,
        drop_keys={hash_field},
    )
    return type(model).model_validate(payload)


def _manifest() -> RepoBehavioralReplayManifest:
    probe_refs = ["probe:a", "probe:b"]
    probe_hashes = [_hash("probe:a"), _hash("probe:b")]
    expected_refs = ["obs:a", "obs:b"]
    expected_hashes = [_hash("obs:a"), _hash("obs:b")]
    profile_hash = _hash("profile")
    suite_root_hash = suite_root_hash_for(
        probe_contract_refs=probe_refs,
        probe_contract_hashes=probe_hashes,
        expected_observation_hash_refs=expected_refs,
        expected_observation_hashes=expected_hashes,
        canonicalization_profile_ref="profile:default",
        canonicalization_profile_hash=profile_hash,
    )
    manifest_without_hash = RepoBehavioralReplayManifest(
        schema="repo_behavioral_replay_manifest@1",
        manifest_id="manifest:test",
        manifest_version="v1",
        manifest_authority_layer="support",
        manifest_lifecycle_state="locked",
        manifest_visibility_posture="implementation_visible_regression",
        manifest_scope={
            "bounded_claim": "no observed regression over test manifest",
            "certificate_use_allowed": False,
            "promotion_use_allowed": False,
        },
        product_ref="product:test",
        candidate_artifact_kind="python_script",
        protected_owner_surfaces=["diagnostic_exit_channel", "output_router_renderer"],
        owner_surface_rows=[
            OwnerSurfaceRow(
                owner_surface="diagnostic_exit_channel",
                patch_risk_kind="diagnostic_exit_channel",
                protected_sibling_probe_refs=["probe:b"],
                required_when_touched=True,
                coverage_posture="sentinel_required",
                taxonomy_ref="docs/support/general_program_ontology_derived_v1_7.md",
            ),
            OwnerSurfaceRow(
                owner_surface="output_router_renderer",
                patch_risk_kind="output_router_renderer",
                protected_sibling_probe_refs=["probe:a"],
                required_when_touched=True,
                coverage_posture="sentinel_required",
                taxonomy_ref="docs/support/general_program_ontology_derived_v1_7.md",
            ),
        ],
        owner_surface_map_ref="owner-map:test",
        owner_surface_map_hash=_hash("owner-map"),
        owner_surface_taxonomy_version="gpo-v1.7",
        canonicalization_profile_ref="profile:default",
        canonicalization_profile_hash=profile_hash,
        execution_environment_ref="env:test",
        execution_environment_hash=_hash("env"),
        sensitive_material_policy_ref="policy:sensitive",
        safe_rendering_policy_ref="policy:safe-rendering",
        raw_material_storage_policy_ref="policy:raw-storage",
        redaction_profile_ref="policy:redaction",
        probe_contract_refs=probe_refs,
        probe_contract_hashes=probe_hashes,
        expected_observation_hash_refs=expected_refs,
        expected_observation_hashes=expected_hashes,
        suite_root_hash=suite_root_hash,
    )
    payload = manifest_without_hash.model_dump(mode="json", exclude_none=True)
    payload["manifest_hash"] = canonical_hash(
        manifest_without_hash,
        object_kind="repo_behavioral_replay_manifest",
        canonicalization_profile_hash=profile_hash,
        drop_keys={"manifest_hash"},
    )
    return RepoBehavioralReplayManifest.model_validate(payload)


def _execution(
    manifest: RepoBehavioralReplayManifest,
    *,
    probe_refs: list[str] | None = None,
    status_by_probe: dict[str, str] | None = None,
) -> RepoBehavioralReplayExecutionReport:
    selected_probe_refs = probe_refs if probe_refs is not None else manifest.probe_contract_refs
    statuses = status_by_probe or {}
    probe_hash_by_ref = dict(zip(manifest.probe_contract_refs, manifest.probe_contract_hashes))
    rows = [
        ProbeExecutionRow(
            probe_id=probe_ref,
            probe_contract_hash=probe_hash_by_ref[probe_ref],
            execution_status=statuses.get(probe_ref, "completed"),
            argv=["python", "-c", "print('ok')"],
            cwd_ref="cwd:test",
            env_delta_hash=_hash("env-delta"),
            timeout_policy_ref="timeout:short",
            fixture_tree_hash_before=_hash("fixture-before"),
            fixture_tree_hash_after_actual=_hash("fixture-after"),
            observation_record_ref=f"observation:{probe_ref}",
            diff_ref=f"diff:{probe_ref}",
        )
        for probe_ref in selected_probe_refs
    ]
    execution_without_hash = RepoBehavioralReplayExecutionReport(
        schema="repo_behavioral_replay_execution_report@1",
        execution_report_ref="execution:test",
        manifest_id=manifest.manifest_id,
        manifest_hash=manifest.manifest_hash,
        manifest_validation_report_ref="validation:test",
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
        execution_environment_ref=manifest.execution_environment_ref,
        execution_environment_hash=manifest.execution_environment_hash,
        probe_execution_rows=rows,
        observation_record_refs=[f"observation:{probe_ref}" for probe_ref in selected_probe_refs],
        diff_refs=[f"diff:{probe_ref}" for probe_ref in selected_probe_refs],
        suite_root_hash_report_ref="suite:test",
        execution_status=(
            "completed"
            if all(row.execution_status == "completed" for row in rows)
            else "completed_with_diffs"
        ),
        authority_posture="replay_report_only_not_product_authority",
    )
    return _with_hash(
        execution_without_hash,
        object_kind="repo_behavioral_replay_execution_report",
        hash_field="canonical_output_hash",
    )


def _diffs(
    manifest: RepoBehavioralReplayManifest,
    *,
    status_by_probe: dict[str, str] | None = None,
) -> list[RepoBehavioralRegressionDiff]:
    statuses = status_by_probe or {}
    expected_by_probe = dict(
        zip(manifest.probe_contract_refs, manifest.expected_observation_hashes)
    )
    result = []
    for probe_ref in manifest.probe_contract_refs:
        status = statuses.get(probe_ref, "match")
        rows = []
        changed_surfaces = []
        if status == "diff":
            changed_surfaces = ["stdout"]
            rows = [
                StructuredDiffRow(
                    surface="stdout",
                    expected_value="sha256:expected",
                    actual_value="sha256:actual",
                    summary=f"stdout changed for {probe_ref}",
                )
            ]
        diff_without_hash = RepoBehavioralRegressionDiff(
            schema="repo_behavioral_regression_diff@1",
            diff_ref=f"diff:{probe_ref}",
            probe_id=probe_ref,
            expected_observation_hash_ref=f"obs:{probe_ref.rsplit(':', maxsplit=1)[-1]}",
            expected_canonical_observation_hash=expected_by_probe[probe_ref],
            actual_observation_record_ref=f"observation:{probe_ref}",
            actual_canonical_observation_hash=(
                expected_by_probe[probe_ref] if status == "match" else _hash(f"actual:{probe_ref}")
            ),
            diff_status=status,
            changed_surfaces=changed_surfaces,
            structured_diff_rows=rows,
            authority_posture="diff_report_only_not_patch_authority",
        )
        result.append(
            _with_hash(
                diff_without_hash,
                object_kind="repo_behavioral_regression_diff",
                hash_field="canonical_output_hash",
            )
        )
    return result


def _suite(
    manifest: RepoBehavioralReplayManifest,
    *,
    status: str = "match",
) -> RepoBehavioralSuiteRootHashReport:
    rows = [
        SuiteRootPerProbeHashRow(
            probe_id=probe_ref,
            expected_observation_hash_ref=expected_ref,
            expected_canonical_observation_hash=expected_hash,
            actual_canonical_observation_hash=expected_hash if status == "match" else _hash("diff"),
            diff_status="match" if status == "match" else "diff",
        )
        for probe_ref, expected_ref, expected_hash in zip(
            manifest.probe_contract_refs,
            manifest.expected_observation_hash_refs,
            manifest.expected_observation_hashes,
        )
    ]
    suite_without_hash = RepoBehavioralSuiteRootHashReport(
        schema="repo_behavioral_suite_root_hash_report@1",
        suite_root_hash_report_ref="suite:test",
        manifest_id=manifest.manifest_id,
        manifest_hash=manifest.manifest_hash,
        expected_suite_root_hash=manifest.suite_root_hash,
        actual_suite_root_hash=manifest.suite_root_hash if status == "match" else _hash("suite"),
        per_probe_hash_rows=rows,
        suite_root_status=status,
        authority_posture="suite_hash_report_only_not_certificate",
    )
    return _with_hash(
        suite_without_hash,
        object_kind="repo_behavioral_suite_root_hash_report",
        hash_field="canonical_output_hash",
    )


def _fresh(manifest: RepoBehavioralReplayManifest) -> RepoBehavioralLockStalenessReport:
    return build_lock_staleness_report(manifest=manifest)


def test_full_manifest_replay_match_emits_bounded_certificate() -> None:
    manifest = _manifest()
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:test",
        full_manifest_scope=True,
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest),
        suite_root_report=_suite(manifest),
        diffs=_diffs(manifest),
        impact_cone_report=impact,
        staleness_report=_fresh(manifest),
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    assert certificate.certificate_posture == "full_manifest_no_observed_regression"
    assert certificate.covered_probe_refs == ["probe:a", "probe:b"]
    assert certificate.known_gaps == []


def test_touched_owner_surfaces_select_only_required_sentinels() -> None:
    manifest = _manifest()
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:renderer",
        touched_owner_surfaces=["output_router_renderer"],
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest),
        suite_root_report=_suite(manifest),
        diffs=_diffs(manifest),
        impact_cone_report=impact,
        staleness_report=_fresh(manifest),
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    assert impact.required_probe_refs == ["probe:a"]
    assert impact.selected_probe_refs == ["probe:a"]
    assert [row.omitted_probe_ref for row in impact.omitted_probe_rows] == ["probe:b"]
    assert certificate.certificate_posture == "impact_cone_no_observed_regression"
    assert certificate.covered_owner_surfaces == ["output_router_renderer"]


def test_missing_sentinel_coverage_blocks_certificate() -> None:
    manifest = _manifest()
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:missing",
        touched_owner_surfaces=["config_policy_activation"],
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest),
        suite_root_report=_suite(manifest),
        diffs=_diffs(manifest),
        impact_cone_report=impact,
        staleness_report=_fresh(manifest),
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    assert impact.selection_status == "blocked_by_missing_sentinel"
    assert certificate.certificate_posture == "blocked_by_missing_sentinel"
    assert certificate.known_gaps


def test_unreplayed_selected_sentinel_blocks_certificate() -> None:
    manifest = _manifest()
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:renderer",
        touched_owner_surfaces=["output_router_renderer"],
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest, probe_refs=[]),
        suite_root_report=_suite(manifest),
        diffs=[],
        impact_cone_report=impact,
        staleness_report=_fresh(manifest),
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    assert certificate.certificate_posture == "blocked_by_unreplayed_required_sentinel"
    assert certificate.known_gaps == ["selected sentinel not replayed: probe:a"]


def test_replay_diff_blocks_certificate() -> None:
    manifest = _manifest()
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:renderer",
        touched_owner_surfaces=["output_router_renderer"],
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest),
        suite_root_report=_suite(manifest, status="diff"),
        diffs=_diffs(manifest, status_by_probe={"probe:a": "diff"}),
        impact_cone_report=impact,
        staleness_report=_fresh(manifest),
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    assert certificate.certificate_posture == "blocked_by_replay_diff"
    assert "selected sentinel diff not match: probe:a" in certificate.known_gaps


def test_stale_manifest_hash_blocks_certificate() -> None:
    manifest = _manifest()
    stale = build_lock_staleness_report(
        manifest=manifest,
        actual_manifest_hash=_hash("stale-manifest"),
    )
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:test",
        full_manifest_scope=True,
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest),
        suite_root_report=_suite(manifest),
        diffs=_diffs(manifest),
        impact_cone_report=impact,
        staleness_report=stale,
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    assert stale.staleness_status == "stale"
    assert certificate.certificate_posture == "blocked_by_stale_manifest"


def test_stale_owner_surface_map_blocks_with_specific_posture() -> None:
    manifest = _manifest()
    stale = build_lock_staleness_report(
        manifest=manifest,
        actual_owner_surface_map_hash=_hash("stale-owner-map"),
    )
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:test",
        full_manifest_scope=True,
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest),
        suite_root_report=_suite(manifest),
        diffs=_diffs(manifest),
        impact_cone_report=impact,
        staleness_report=stale,
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    assert certificate.certificate_posture == "blocked_by_stale_owner_surface_map"


def test_stale_canonicalization_profile_blocks_certificate() -> None:
    manifest = _manifest()
    stale = build_lock_staleness_report(
        manifest=manifest,
        actual_canonicalization_profile_hash=_hash("stale-profile"),
    )
    assert [row.stale_reason_kind for row in stale.stale_reason_rows] == [
        "canonicalization_profile_hash_changed"
    ]


def test_stale_expected_observation_hash_blocks_certificate() -> None:
    manifest = _manifest()
    stale = build_lock_staleness_report(
        manifest=manifest,
        actual_suite_root_hash=_hash("stale-suite"),
    )
    assert [row.stale_reason_kind for row in stale.stale_reason_rows] == [
        "expected_observation_hash_changed"
    ]


def test_stale_hob_otb_handoff_hash_emits_staleness_report() -> None:
    manifest = _manifest()
    stale = build_lock_staleness_report(
        manifest=manifest,
        expected_hob_otb_handoff_hash=_hash("handoff-old"),
        actual_hob_otb_handoff_hash=_hash("handoff-new"),
    )
    assert stale.staleness_status == "stale"
    assert stale.stale_reason_rows[0].stale_reason_kind == "hob_otb_handoff_hash_changed"
    assert (
        stale.required_refresh_rows[0].stale_reason_ref
        == stale.stale_reason_rows[0].stale_reason_ref
    )


def test_certificate_bounded_claim_does_not_exceed_selected_scope() -> None:
    manifest = _manifest()
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:renderer",
        touched_owner_surfaces=["output_router_renderer"],
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest),
        suite_root_report=_suite(manifest),
        diffs=_diffs(manifest),
        impact_cone_report=impact,
        staleness_report=_fresh(manifest),
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    assert certificate.certificate_posture == "impact_cone_no_observed_regression"
    assert "selected impact-cone sentinels" in certificate.bounded_claim


def test_integration_handoff_constrains_without_transition_authority() -> None:
    manifest = _manifest()
    impact = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:test",
        full_manifest_scope=True,
    )
    certificate = build_no_regression_certificate(
        manifest=manifest,
        execution_report=_execution(manifest),
        suite_root_report=_suite(manifest),
        diffs=_diffs(manifest),
        impact_cone_report=impact,
        staleness_report=_fresh(manifest),
        candidate_artifact_ref="candidate:test",
        candidate_artifact_hash=_hash("candidate"),
    )
    handoff = build_replay_integration_handoff(
        source_family="BRL-0",
        target_family="OTB",
        certificates=[certificate],
    )
    assert handoff.handoff_status == "handoff_ready"
    assert handoff.authority_posture == "handoff_constraint_only_not_transition_authority"
    assert set(handoff.forbidden_promotions) == {
        "hob_closure",
        "official_eval_readiness",
        "otb_transition_legality",
        "product_truth",
    }


def test_deterministic_ordering_for_selection_and_staleness_rows() -> None:
    manifest = _manifest()
    impact_a = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:test",
        touched_owner_surfaces=["output_router_renderer", "diagnostic_exit_channel"],
    )
    impact_b = select_impact_cone(
        manifest=manifest,
        candidate_change_ref="change:test",
        touched_owner_surfaces=["diagnostic_exit_channel", "output_router_renderer"],
    )
    stale = build_lock_staleness_report(
        manifest=manifest,
        actual_owner_surface_map_hash=_hash("stale-owner-map"),
        actual_canonicalization_profile_hash=_hash("stale-profile"),
    )
    assert impact_a.canonical_output_hash == impact_b.canonical_output_hash
    assert [row.stale_reason_ref for row in stale.stale_reason_rows] == sorted(
        row.stale_reason_ref for row in stale.stale_reason_rows
    )


def test_unknown_or_overreaching_vocabulary_fails_closed() -> None:
    with pytest.raises(ValidationError):
        RepoBehavioralNoRegressionCertificate.model_validate(
            {
                "schema": REPO_BEHAVIORAL_NO_REGRESSION_CERTIFICATE_SCHEMA,
                "certificate_ref": "certificate:test",
                "manifest_id": "manifest:test",
                "manifest_hash": _hash("manifest"),
                "candidate_artifact_ref": "candidate:test",
                "candidate_artifact_hash": _hash("candidate"),
                "execution_report_ref": "execution:test",
                "impact_cone_report_ref": "impact:test",
                "certificate_posture": "full_manifest_no_observed_regression",
                "bounded_claim": "bad product claim",
                "covered_probe_refs": ["probe:a"],
                "covered_owner_surfaces": ["output_router_renderer"],
                "known_gaps": [],
                "authority_posture": "product_truth",
            }
        )
    with pytest.raises(ValidationError):
        RepoBehavioralReplayIntegrationHandoff.model_validate(
            {
                "schema": "repo_behavioral_replay_integration_handoff@1",
                "handoff_ref": "handoff:test",
                "source_family": "BRL-0",
                "target_family": "OTB",
                "certificate_refs": ["certificate:test"],
                "blocker_refs": [],
                "bounded_use": "bad transition claim",
                "forbidden_promotions": ["product_truth"],
                "handoff_status": "handoff_ready",
                "authority_posture": "transition_authority",
            }
        )
    with pytest.raises(ValidationError):
        RepoBehavioralLockStalenessReport.model_validate(
            {
                "schema": REPO_BEHAVIORAL_LOCK_STALENESS_REPORT_SCHEMA,
                "staleness_report_ref": "stale:test",
                "manifest_id": "manifest:test",
                "staleness_status": "fresh",
                "stale_reason_rows": [],
                "required_refresh_rows": [],
                "authority_posture": "refresh_authority",
            }
        )
