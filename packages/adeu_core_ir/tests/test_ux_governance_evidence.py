from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_core_ir import (
    DEFAULT_APPROVED_PROFILE_TABLE_PATH,
    DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
    DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH,
    DEFAULT_UX_CONFORMANCE_REPORT_SCHEMA_PATH,
    DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
    DEFAULT_UX_DOMAIN_PACKET_SCHEMA_PATH,
    DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH,
    DEFAULT_UX_INTERACTION_CONTRACT_SCHEMA_PATH,
    DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH,
    DEFAULT_UX_MORPH_DIAGNOSTICS_SCHEMA_PATH,
    DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
    DEFAULT_UX_MORPH_IR_SCHEMA_PATH,
    DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH,
    DEFAULT_UX_SURFACE_PROJECTION_SCHEMA_PATH,
    DEFAULT_V36C_IMPLEMENTATION_BINDING_MANIFEST_PATH,
    DEFAULT_V36C_REFERENCE_SURFACE_EVIDENCE_PATH,
    DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH,
    DEFAULT_V36C_RENDERED_SURFACE_SNAPSHOT_PATH,
    DEFAULT_V60_BASELINE_METRICS_PATH,
    DEFAULT_V61_BASELINE_METRICS_PATH,
    DEFAULT_V62_BASELINE_METRICS_PATH,
    DEFAULT_V63_BASELINE_METRICS_PATH,
    build_v36b_stable_binding_id,
    build_v36b_stable_provenance_hook_id,
    materialize_v36a_ux_domain_morph_ir_evidence,
    materialize_v36b_surface_projection_interaction_evidence,
    materialize_v36c_artifact_inspector_reference_surface_evidence,
    materialize_v36d_morph_diagnostics_conformance_evidence,
)
from adeu_core_ir.ux_governance_evidence import UXGovernanceEvidenceError
from adeu_ir.repo import repo_root


def _source_repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _canonical_pretty_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_canonical_pretty_json(payload), encoding="utf-8")


def _write_stop_gate_metrics_fixture(
    *,
    repo_root: Path,
    baseline_rel: str = DEFAULT_V60_BASELINE_METRICS_PATH,
    current_rel: str = "artifacts/stop_gate/metrics_v61_closeout.json",
) -> tuple[str, str]:
    metric_keys = [f"metric_{index:02d}" for index in range(80)]
    payload = {
        "schema": "stop_gate_metrics@1",
        "metrics": {key: 100.0 for key in metric_keys},
        "runtime_observability": {
            "elapsed_ms": 61,
            "total_fixtures": 6,
            "total_replays": 6,
        },
    }
    for relative_path in (baseline_rel, current_rel):
        _write_json(repo_root / relative_path, payload)
    return baseline_rel, current_rel


def _copy_repo_relative_file(*, source_root: Path, target_root: Path, relative_path: str) -> None:
    source = source_root / relative_path
    target = target_root / relative_path
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)


def _build_temp_repo_fixture_tree(tmp_path: Path) -> Path:
    source_root = _source_repo_root()
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    for relative_path in (
        DEFAULT_UX_DOMAIN_PACKET_SCHEMA_PATH,
        DEFAULT_UX_MORPH_IR_SCHEMA_PATH,
        DEFAULT_UX_SURFACE_PROJECTION_SCHEMA_PATH,
        DEFAULT_UX_INTERACTION_CONTRACT_SCHEMA_PATH,
        DEFAULT_UX_MORPH_DIAGNOSTICS_SCHEMA_PATH,
        DEFAULT_UX_CONFORMANCE_REPORT_SCHEMA_PATH,
        DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
        DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
        DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH,
        DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH,
        DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH,
        DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH,
        DEFAULT_APPROVED_PROFILE_TABLE_PATH,
        DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
        DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH,
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md",
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md",
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md",
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md",
    ):
        _copy_repo_relative_file(
            source_root=source_root,
            target_root=repo_root,
            relative_path=relative_path,
        )
    return repo_root


def _load_json(repo_root: Path, relative_path: str) -> dict[str, object]:
    return json.loads((repo_root / relative_path).read_text(encoding="utf-8"))


def _materialize_v36a_evidence(*, repo_root: Path) -> dict[str, object]:
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    evidence = materialize_v36a_ux_domain_morph_ir_evidence(
        repo_root=repo_root,
        output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v36b_evidence(*, repo_root: Path) -> dict[str, object]:
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    evidence = materialize_v36b_surface_projection_interaction_evidence(
        repo_root=repo_root,
        output_path=(
            "artifacts/agent_harness/v62/evidence_inputs/"
            "v36b_surface_projection_interaction_evidence_v62.json"
        ),
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v36c_evidence(*, repo_root: Path) -> dict[str, object]:
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    evidence = materialize_v36c_artifact_inspector_reference_surface_evidence(
        repo_root=repo_root,
        output_path=(
            "artifacts/agent_harness/v63/evidence_inputs/"
            "v36c_artifact_inspector_reference_surface_evidence_v63.json"
        ),
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
        "snapshot": _load_json(repo_root, DEFAULT_V36C_RENDERED_SURFACE_SNAPSHOT_PATH),
        "binding_manifest": _load_json(
            repo_root, DEFAULT_V36C_IMPLEMENTATION_BINDING_MANIFEST_PATH
        ),
    }


def _materialize_v36d_evidence(*, repo_root: Path) -> dict[str, object]:
    _materialize_v36c_evidence(repo_root=repo_root)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V63_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )
    evidence = materialize_v36d_morph_diagnostics_conformance_evidence(
        repo_root=repo_root,
        output_path=(
            "artifacts/agent_harness/v64/evidence_inputs/"
            "v36d_morph_diagnostics_conformance_evidence_v64.json"
        ),
        baseline_metrics_path=baseline_rel,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root / evidence.path).read_text(encoding="utf-8")),
    }


def _inject_v36d_finding_fixture(
    repo_root: Path,
    *,
    finding_id: str = "finding-001",
    violation_family: str = "destructive_action_lacks_adequate_confirmation",
    severity: str = "error",
) -> None:
    binding_manifest = _load_json(repo_root, DEFAULT_V36C_IMPLEMENTATION_BINDING_MANIFEST_PATH)
    target_ref = binding_manifest["target_manifest"][0]["target_ref"]  # type: ignore[index]
    rendered_input = "v36c_rendered_reference_surface_contract@1"
    conformance_impact = {
        "error": "blocks_pass",
        "warning": "needs_review",
        "advisory": "advisory_only",
    }[severity]

    diagnostics = _load_json(repo_root, DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH)
    diagnostics["findings"] = [  # type: ignore[index]
        {
            "finding_id": finding_id,
            "violation_family": violation_family,
            "severity": severity,
            "provenance_pointers": [
                {
                    "source_schema": rendered_input,
                    "source_path": DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH,
                    "target_ref": target_ref,
                }
            ],
            "rendered_surface_assertion_inputs_used": [rendered_input],
            "supporting_evidence_refs": [DEFAULT_V36C_REFERENCE_SURFACE_EVIDENCE_PATH],
            "conformance_impact": conformance_impact,
        }
    ]
    _write_json(repo_root / DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH, diagnostics)

    conformance = _load_json(repo_root, DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH)
    conformance["supporting_finding_ids"] = [finding_id]  # type: ignore[index]
    conformance["severity_counts"] = {  # type: ignore[index]
        "error": 1 if severity == "error" else 0,
        "warning": 1 if severity == "warning" else 0,
        "advisory": 1 if severity == "advisory" else 0,
    }
    conformance["overall_judgment"] = {
        "error": "fail",
        "warning": "needs_review",
        "advisory": "pass",
    }[severity]
    conformance["failed_rule_families"] = [violation_family] if severity == "error" else []  # type: ignore[index]
    conformance["warning_rule_families"] = [violation_family] if severity == "warning" else []  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH, conformance)


def test_materialize_v36a_ux_domain_morph_ir_evidence_is_deterministic(tmp_path: Path) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v36a_evidence(repo_root=repo_root)
    second = _materialize_v36a_evidence(repo_root=repo_root)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["payload"]["schema"] == "v36a_ux_domain_morph_ir_evidence@1"


def test_materialize_v36a_evidence_fails_closed_on_missing_reference_instance(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    (repo_root / DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH).unlink()

    with pytest.raises(
        UXGovernanceEvidenceError, match="ux_domain_packet_reference_path does not exist"
    ):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_reference_binding_mismatch(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    payload = _load_json(repo_root, DEFAULT_UX_MORPH_IR_REFERENCE_PATH)
    payload["reference_instance_id"] = "artifact_inspector_reference_other"
    _write_json(repo_root / DEFAULT_UX_MORPH_IR_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="reference instance binding mismatch for reference_instance_id",
    ):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_missing_adeu_split(tmp_path: Path) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    payload = _load_json(repo_root, DEFAULT_UX_MORPH_IR_REFERENCE_PATH)
    del payload["utility"]
    _write_json(repo_root / DEFAULT_UX_MORPH_IR_REFERENCE_PATH, payload)

    with pytest.raises(UXGovernanceEvidenceError, match="ux_morph_ir_reference_path is invalid"):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_approved_profile_table_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    payload = _load_json(repo_root, DEFAULT_APPROVED_PROFILE_TABLE_PATH)
    payload["profiles"] = payload["profiles"][:1]  # type: ignore[index]
    _write_json(repo_root / DEFAULT_APPROVED_PROFILE_TABLE_PATH, payload)

    with pytest.raises(UXGovernanceEvidenceError, match="approved_profile_table_path is invalid"):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_invalid_profile_combination(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    payload = _load_json(repo_root, DEFAULT_UX_MORPH_IR_REFERENCE_PATH)
    payload["morph_axes"]["density"] = "medium"  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_MORPH_IR_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError, match="approved profile binding mismatch for morph axes"
    ):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_same_context_glossary_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    payload = _load_json(repo_root, DEFAULT_SAME_CONTEXT_GLOSSARY_PATH)
    payload["same_context_reachable"] = [  # type: ignore[index]
        "bounded_workbench_position_shift",
        "bounded_workbench_focus_shift",
        "bounded_workbench_state_reveal",
    ]
    _write_json(repo_root / DEFAULT_SAME_CONTEXT_GLOSSARY_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError, match="same_context_reachability_glossary_path is invalid"
    ):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_free_form_codegen_bypass(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    payload = _load_json(repo_root, DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH)
    payload["authority_boundary_policy"]["no_free_form_ui_codegen_without_ir"] = False  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH, payload)

    with pytest.raises(UXGovernanceEvidenceError, match="free-form UI codegen bypass detected"):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_authority_minting_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    payload = _load_json(repo_root, DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH)
    payload["authority_boundary_policy"]["ui_artifacts_may_express_but_may_not_mint_authority"] = (  # type: ignore[index]
        False
    )
    _write_json(repo_root / DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH, payload)

    with pytest.raises(UXGovernanceEvidenceError, match="authority-minting drift detected"):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_metric_key_continuity_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(repo_root=repo_root)
    payload = _load_json(repo_root, current_rel)
    payload["metrics"].pop("metric_79")  # type: ignore[index]
    _write_json(repo_root / current_rel, payload)

    with pytest.raises(
        UXGovernanceEvidenceError, match="metric key cardinality must remain frozen at 80"
    ):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36a_evidence_fails_closed_on_non_v60_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel="artifacts/stop_gate/metrics_other_closeout.json",
    )

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="baseline_metrics_path must point to the frozen v60 closeout metrics artifact",
    ):
        materialize_v36a_ux_domain_morph_ir_evidence(
            repo_root=repo_root,
            output_path="artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json",
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_surface_projection_interaction_evidence_is_deterministic(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v36b_evidence(repo_root=repo_root)
    second = _materialize_v36b_evidence(repo_root=repo_root)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["payload"]["schema"] == "v36b_surface_projection_interaction_evidence@1"


def test_materialize_v36b_evidence_fails_closed_on_missing_projection_reference(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    (repo_root / DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH).unlink()

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="ux_surface_projection_reference_path does not exist",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_projection_interaction_binding_mismatch(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH)
    new_reference_instance_id = "artifact_inspector_reference_other"
    payload["reference_instance_id"] = new_reference_instance_id
    for hook in payload["stable_provenance_hooks"]:  # type: ignore[index]
        _old_reference_instance_id, suffix = hook["target_ref"].split(":", 1)
        hook["target_ref"] = f"{new_reference_instance_id}:{suffix}"
        hook["hook_id"] = build_v36b_stable_provenance_hook_id(
            reference_instance_id=new_reference_instance_id,
            target_kind=hook["target_kind"],
            target_ref=hook["target_ref"],
        )
    for binding in payload["implementation_observable_bindings"]:  # type: ignore[index]
        _old_reference_instance_id, suffix = binding["target_ref"].split(":", 1)
        binding["target_ref"] = f"{new_reference_instance_id}:{suffix}"
        binding["binding_id"] = build_v36b_stable_binding_id(
            reference_instance_id=new_reference_instance_id,
            target_kind=binding["target_kind"],
            target_ref=binding["target_ref"],
        )
    _write_json(repo_root / DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="projection/interaction binding mismatch for reference_instance_id",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_hash_changes_when_consumed_v36a_substrate_changes(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    first = _materialize_v36b_evidence(repo_root=repo_root)

    domain_payload = _load_json(repo_root, DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH)
    morph_payload = _load_json(repo_root, DEFAULT_UX_MORPH_IR_REFERENCE_PATH)
    updated_ranking = [
        "error_prevention",
        "trust_calibration",
        "operator_speed",
    ]
    domain_payload["utility_ranking"] = updated_ranking
    morph_payload["utility"]["priority_order"] = updated_ranking  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH, domain_payload)
    _write_json(repo_root / DEFAULT_UX_MORPH_IR_REFERENCE_PATH, morph_payload)

    second = _materialize_v36b_evidence(repo_root=repo_root)

    assert first["artifact"].hash != second["artifact"].hash
    assert first["payload"]["notes"] != second["payload"]["notes"]


def test_materialize_v36b_evidence_fails_closed_on_forbidden_gate_source(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH)
    payload["interaction_entries"][1]["authoritative_gate_source"]["source_kind"] = (  # type: ignore[index]
        "page_local_constants"
    )
    _write_json(repo_root / DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError, match="forbidden authoritative gate source detected"
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_missing_gate_source_anchor(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH)
    payload["interaction_entries"][1]["authoritative_gate_source"]["source_ref"] = (  # type: ignore[index]
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md#missing_anchor"
    )
    _write_json(repo_root / DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="authoritative_gate_source source_ref must resolve to a committed docs anchor",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_missing_minimum_provenance_hook_coverage(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH)
    payload["stable_provenance_hooks"] = [
        hook
        for hook in payload["stable_provenance_hooks"]  # type: ignore[index]
        if hook["target_kind"] != "authority_bearing_control"
    ]
    _write_json(repo_root / DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="stable_provenance_hooks missing required target kinds",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_missing_minimum_binding_coverage(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH)
    payload["implementation_observable_bindings"] = [
        binding
        for binding in payload["implementation_observable_bindings"]  # type: ignore[index]
        if binding["target_kind"] != "diagnostic_surface"
    ]
    _write_json(repo_root / DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="implementation_observable_bindings missing required target kinds",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_binding_identifier_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH)
    payload["stable_provenance_hooks"][0]["hook_id"] = "v36b.prov:drifted"  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="stable provenance hook id must match the frozen deterministic format",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_glossary_shadowing(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH)
    payload["evidence_before_commit"]["same_context_reachability_glossary"]["context_break"] = [  # type: ignore[index]
        "route_transition",
        "bounded_workbench_replacement",
        "detached_surface_replacement",
        "local_tab_switch",
    ]
    _write_json(repo_root / DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="projection must consume the released v36a same-context glossary without shadowing",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_runtime_truth_overstatement(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH)
    payload["interaction_entries"][3]["runtime_visible_consequence"] = {  # type: ignore[index]
        "outcome_kind": "bounded_context_focus_visible",
        "truth_posture": "request_only",
    }
    _write_json(repo_root / DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="runtime_visible_consequence must remain epistemic and must not overstate success",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_visual_authority_inflation_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH)
    payload["authority_boundary_policy"]["no_visual_authority_inflation"] = False  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError, match="visual authority inflation drift detected"
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_metric_key_continuity_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V61_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )
    payload = _load_json(repo_root, current_rel)
    payload["metrics"].pop("metric_79")  # type: ignore[index]
    _write_json(repo_root / current_rel, payload)

    with pytest.raises(
        UXGovernanceEvidenceError, match="metric key cardinality must remain frozen at 80"
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36b_evidence_fails_closed_on_non_v61_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel="artifacts/stop_gate/metrics_other_closeout.json",
        current_rel="artifacts/stop_gate/metrics_v62_closeout.json",
    )

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="baseline_metrics_path must point to the frozen v61 closeout metrics artifact",
    ):
        materialize_v36b_surface_projection_interaction_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v62/evidence_inputs/"
                "v36b_surface_projection_interaction_evidence_v62.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_reference_surface_evidence_is_deterministic(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v36c_evidence(repo_root=repo_root)
    second = _materialize_v36c_evidence(repo_root=repo_root)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["snapshot"] == second["snapshot"]
    assert first["binding_manifest"] == second["binding_manifest"]
    assert first["payload"]["schema"] == "v36c_artifact_inspector_reference_surface_evidence@1"
    assert first["snapshot"]["schema"] == "v36c_rendered_reference_surface_semantic_snapshot@1"
    assert (
        first["binding_manifest"]["schema"] == "v36c_rendered_reference_surface_binding_manifest@1"
    )


def test_materialize_v36c_evidence_fails_closed_on_missing_route_contract(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    (repo_root / DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH).unlink()

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="rendered_reference_surface_contract_path does not exist",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_route_path_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH)
    payload["route_path"] = "/copilot"
    _write_json(repo_root / DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="rendered surface contract route_path drift detected",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_lane_cluster_mapping_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH)
    payload["lane_cluster_rendering"][1]["cluster_ids"] = ["commit-actions"]  # type: ignore[index]
    _write_json(repo_root / DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="rendered lane cluster mapping drift detected",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_missing_lane_cluster_coverage(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH)
    payload["lane_cluster_rendering"] = payload["lane_cluster_rendering"][:1]  # type: ignore[index]
    _write_json(repo_root / DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="rendered lane cluster coverage drift detected",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_missing_binding_exposure_target(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH)
    del payload["rendered_binding_exposures"]["required_evidence_reachability_anchors"]  # type: ignore[index]
    _write_json(repo_root / DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="rendered binding exposure targets is missing required target",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_diagnostics_placeholder_widening(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH)
    payload["diagnostics_lane_read_only_notice"] = "Diagnostics lane now produces local severity."
    _write_json(repo_root / DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="diagnostics placeholder widening detected",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_truth_label_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH)
    payload["truth_source_notice"] = "Worker summaries may be treated as accepted truth here."
    _write_json(repo_root / DEFAULT_V36C_RENDERED_REFERENCE_SURFACE_CONTRACT_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="non-authoritative event or worker content truth labeling drift detected",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_route_change_requirement_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH)
    payload["evidence_before_commit"]["route_change_required"] = True  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="rendered surface cannot require a route change before required evidence",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_metric_key_continuity_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V62_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )
    payload = _load_json(repo_root, current_rel)
    payload["metrics"].pop("metric_79")  # type: ignore[index]
    _write_json(repo_root / current_rel, payload)

    with pytest.raises(
        UXGovernanceEvidenceError, match="metric key cardinality must remain frozen at 80"
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36c_evidence_fails_closed_on_non_v62_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel="artifacts/stop_gate/metrics_other_closeout.json",
        current_rel="artifacts/stop_gate/metrics_v63_closeout.json",
    )

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="baseline_metrics_path must point to the frozen v62 closeout metrics artifact",
    ):
        materialize_v36c_artifact_inspector_reference_surface_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_evidence_v63.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36d_morph_diagnostics_conformance_evidence_is_deterministic(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v36d_evidence(repo_root=repo_root)
    second = _materialize_v36d_evidence(repo_root=repo_root)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["payload"]["schema"] == "v36d_morph_diagnostics_conformance_evidence@1"


def test_materialize_v36d_evidence_fails_closed_on_missing_diagnostics_reference(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v36c_evidence(repo_root=repo_root)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V63_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )
    (repo_root / DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH).unlink()

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="ux_morph_diagnostics_reference_path does not exist",
    ):
        materialize_v36d_morph_diagnostics_conformance_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v64/evidence_inputs/"
                "v36d_morph_diagnostics_conformance_evidence_v64.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36d_evidence_fails_closed_on_reference_binding_mismatch(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v36c_evidence(repo_root=repo_root)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V63_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH)
    payload["approved_profile_id"] = "artifact_inspector_alternate"
    _write_json(repo_root / DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="conformance report mismatch for approved_profile_id",
    ):
        materialize_v36d_morph_diagnostics_conformance_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v64/evidence_inputs/"
                "v36d_morph_diagnostics_conformance_evidence_v64.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36d_evidence_fails_closed_on_seeded_violation_family_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v36c_evidence(repo_root=repo_root)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V63_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH)
    payload["seeded_violation_families"] = payload["seeded_violation_families"][:-1]  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="seeded violation family coverage drift detected",
    ):
        materialize_v36d_morph_diagnostics_conformance_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v64/evidence_inputs/"
                "v36d_morph_diagnostics_conformance_evidence_v64.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36d_evidence_fails_closed_on_provenance_resolution_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v36c_evidence(repo_root=repo_root)
    _inject_v36d_finding_fixture(repo_root)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V63_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH)
    payload["findings"][0]["provenance_pointers"][0]["source_path"] = (  # type: ignore[index]
        DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH
    )
    _write_json(repo_root / DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="diagnostics provenance pointers must resolve to the consumed canonical artifacts",
    ):
        materialize_v36d_morph_diagnostics_conformance_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v64/evidence_inputs/"
                "v36d_morph_diagnostics_conformance_evidence_v64.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36d_evidence_fails_closed_on_diagnostic_truth_substitution(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v36c_evidence(repo_root=repo_root)
    _inject_v36d_finding_fixture(repo_root)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V63_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH)
    payload["findings"][0]["supporting_evidence_refs"] = [  # type: ignore[index]
        "artifacts/agent_harness/v63/runtime/evidence/codex/copilot/v63-closeout-main-1/urm_events.ndjson"
    ]
    _write_json(repo_root / DEFAULT_UX_MORPH_DIAGNOSTICS_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="diagnostic truth substitution detected",
    ):
        materialize_v36d_morph_diagnostics_conformance_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v64/evidence_inputs/"
                "v36d_morph_diagnostics_conformance_evidence_v64.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36d_evidence_fails_closed_on_fresh_route_heuristics_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v36c_evidence(repo_root=repo_root)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V63_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH)
    payload["derivation_metadata"]["fresh_route_local_heuristics_introduced"] = True  # type: ignore[index]
    _write_json(repo_root / DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="rendered surface assertion bridge introduced fresh route-local heuristics",
    ):
        materialize_v36d_morph_diagnostics_conformance_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v64/evidence_inputs/"
                "v36d_morph_diagnostics_conformance_evidence_v64.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36d_evidence_fails_closed_on_conformance_aggregation_drift(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v36c_evidence(repo_root=repo_root)
    _inject_v36d_finding_fixture(
        repo_root,
        violation_family="competing_primary_actions_in_one_region",
        severity="warning",
    )
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel=DEFAULT_V63_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )
    payload = _load_json(repo_root, DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH)
    payload["overall_judgment"] = "pass"
    _write_json(repo_root / DEFAULT_UX_CONFORMANCE_REPORT_REFERENCE_PATH, payload)

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="conformance report overall judgment must follow the frozen aggregation rule",
    ):
        materialize_v36d_morph_diagnostics_conformance_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v64/evidence_inputs/"
                "v36d_morph_diagnostics_conformance_evidence_v64.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )


def test_materialize_v36d_evidence_fails_closed_on_non_v63_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v36c_evidence(repo_root=repo_root)
    baseline_rel, current_rel = _write_stop_gate_metrics_fixture(
        repo_root=repo_root,
        baseline_rel="artifacts/stop_gate/metrics_other_closeout.json",
        current_rel="artifacts/stop_gate/metrics_v64_closeout.json",
    )

    with pytest.raises(
        UXGovernanceEvidenceError,
        match="baseline_metrics_path must point to the frozen v63 closeout metrics artifact",
    ):
        materialize_v36d_morph_diagnostics_conformance_evidence(
            repo_root=repo_root,
            output_path=(
                "artifacts/agent_harness/v64/evidence_inputs/"
                "v36d_morph_diagnostics_conformance_evidence_v64.json"
            ),
            baseline_metrics_path=baseline_rel,
            current_metrics_path=current_rel,
        )
