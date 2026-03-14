from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_core_ir import (
    DEFAULT_APPROVED_PROFILE_TABLE_PATH,
    DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
    DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
    DEFAULT_UX_DOMAIN_PACKET_SCHEMA_PATH,
    DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH,
    DEFAULT_UX_INTERACTION_CONTRACT_SCHEMA_PATH,
    DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
    DEFAULT_UX_MORPH_IR_SCHEMA_PATH,
    DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH,
    DEFAULT_UX_SURFACE_PROJECTION_SCHEMA_PATH,
    DEFAULT_V60_BASELINE_METRICS_PATH,
    DEFAULT_V61_BASELINE_METRICS_PATH,
    build_v36b_stable_binding_id,
    build_v36b_stable_provenance_hook_id,
    materialize_v36a_ux_domain_morph_ir_evidence,
    materialize_v36b_surface_projection_interaction_evidence,
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
        DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
        DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
        DEFAULT_UX_SURFACE_PROJECTION_REFERENCE_PATH,
        DEFAULT_UX_INTERACTION_CONTRACT_REFERENCE_PATH,
        DEFAULT_APPROVED_PROFILE_TABLE_PATH,
        DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md",
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md",
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


def _rewrite_v36b_reference_instance(
    payload: dict[str, object],
    *,
    new_reference_instance_id: str,
    hooks_field: str = "stable_provenance_hooks",
    bindings_field: str = "implementation_observable_bindings",
) -> None:
    payload["reference_instance_id"] = new_reference_instance_id
    for hook in payload[hooks_field]:  # type: ignore[index]
        _old_reference_instance_id, suffix = hook["target_ref"].split(":", 1)
        hook["target_ref"] = f"{new_reference_instance_id}:{suffix}"
        hook["hook_id"] = build_v36b_stable_provenance_hook_id(
            reference_instance_id=new_reference_instance_id,
            target_kind=hook["target_kind"],
            target_ref=hook["target_ref"],
        )
    for binding in payload[bindings_field]:  # type: ignore[index]
        _old_reference_instance_id, suffix = binding["target_ref"].split(":", 1)
        binding["target_ref"] = f"{new_reference_instance_id}:{suffix}"
        binding["binding_id"] = build_v36b_stable_binding_id(
            reference_instance_id=new_reference_instance_id,
            target_kind=binding["target_kind"],
            target_ref=binding["target_ref"],
        )


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
    _rewrite_v36b_reference_instance(
        payload,
        new_reference_instance_id="artifact_inspector_reference_other",
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
