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
    DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
    DEFAULT_UX_MORPH_IR_SCHEMA_PATH,
    DEFAULT_V60_BASELINE_METRICS_PATH,
    materialize_v36a_ux_domain_morph_ir_evidence,
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
        DEFAULT_UX_DOMAIN_PACKET_REFERENCE_PATH,
        DEFAULT_UX_MORPH_IR_REFERENCE_PATH,
        DEFAULT_APPROVED_PROFILE_TABLE_PATH,
        DEFAULT_SAME_CONTEXT_GLOSSARY_PATH,
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
