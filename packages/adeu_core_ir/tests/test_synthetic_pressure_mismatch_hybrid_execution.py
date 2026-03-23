from __future__ import annotations

import hashlib
import json
import shutil
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_core_ir import (
    DEFAULT_V39E_FIX_PLAN_REFERENCE_FIXTURE_PATH,
    DEFAULT_V39E_LOCAL_HYBRID_HUMAN_FIXTURE_PATH,
    DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH,
    SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_SCHEMA,
    SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_SCHEMA,
    SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_SCHEMA,
    SyntheticPressureMismatchCheckpointTrace,
    SyntheticPressureMismatchOracleRequest,
    SyntheticPressureMismatchOracleResolution,
    canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload,
    canonicalize_synthetic_pressure_mismatch_oracle_request_payload,
    canonicalize_synthetic_pressure_mismatch_oracle_resolution_payload,
    derive_v39e_checkpoint_trace,
    derive_v39e_oracle_request,
    derive_v39e_oracle_resolution,
)
from adeu_core_ir.synthetic_pressure_mismatch_hybrid_execution import (
    _checkpoint_id,
    _oracle_request_id,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixtures_root() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "synthetic_pressure_mismatch"
        / "vnext_plus76"
    )


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def _load_exported_schema(name: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / name
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256_text(value: str) -> str:
    return _sha256_bytes(value.encode("utf-8"))


def _sha256_path(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _canonical_json_hash(payload: dict[str, object]) -> str:
    return hashlib.sha256(
        json.dumps(
            payload,
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        ).encode("utf-8")
    ).hexdigest()


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def test_v39e_oracle_request_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_oracle_request_v76_reference.json")
    request = SyntheticPressureMismatchOracleRequest.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert request.schema == SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_SCHEMA
    assert request.source_kind == "local_hybrid_fixture"
    assert request.resolution_route == "oracle_assisted"

    derived = derive_v39e_oracle_request(
        DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH,
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_oracle_request_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_oracle_request_requires_full_policy_source_set() -> None:
    payload = deepcopy(_load_json("synthetic_pressure_mismatch_oracle_request_v76_reference.json"))
    replay_identity = payload["replay_identity"]
    assert isinstance(replay_identity, dict)
    replay_identity["policy_sources"] = replay_identity["policy_sources"][:-1]

    with pytest.raises(
        ValidationError,
        match="full V39-E policy source set",
    ):
        SyntheticPressureMismatchOracleRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39e_oracle_request_rejects_bounded_context_drift() -> None:
    payload = deepcopy(_load_json("synthetic_pressure_mismatch_oracle_request_v76_reference.json"))
    payload["bounded_context"] = "Narrates an unrelated checkpoint context."
    replay_identity = payload["replay_identity"]
    assert isinstance(replay_identity, dict)
    payload["oracle_request_id"] = _oracle_request_id(
        checkpoint_id=str(payload["checkpoint_id"]),
        replay_identity=replay_identity,
        interpretation_prompt=str(payload["interpretation_prompt"]),
        bounded_context=str(payload["bounded_context"]),
    )

    with pytest.raises(
        ValidationError,
        match="bounded_context must match the referenced local hybrid fixture content",
    ):
        SyntheticPressureMismatchOracleRequest.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39e_oracle_resolution_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_oracle_resolution_v76_reference.json")
    resolution = SyntheticPressureMismatchOracleResolution.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert resolution.schema == SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_SCHEMA
    assert resolution.resolution_disposition == "advisory_support"

    derived = derive_v39e_oracle_resolution(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
        "synthetic_pressure_mismatch_oracle_request_v76_reference.json",
        resolution_disposition="advisory_support",
        advisory_summary=(
            "The anchored comment repeats behavior already visible from the local return "
            "logic and adds no hidden invariant."
        ),
        raw_output_text=(
            "advisory_support: the anchored comment narrates code that is already "
            "evident from the local return path."
        ),
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_oracle_resolution_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_deterministic_trace_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_deterministic.json")
    trace = SyntheticPressureMismatchCheckpointTrace.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert trace.schema == SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_SCHEMA
    assert trace.source_kind == "released_fix_plan_projection"
    assert len(trace.checkpoints) == 2
    assert all(
        checkpoint.checkpoint_class == "deterministic_fail"
        for checkpoint in trace.checkpoints
    )

    derived = derive_v39e_checkpoint_trace(
        fix_plan_reference_fixture=DEFAULT_V39E_FIX_PLAN_REFERENCE_FIXTURE_PATH,
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_oracle_trace_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_oracle.json")
    trace = SyntheticPressureMismatchCheckpointTrace.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert trace.source_kind == "local_hybrid_fixture"
    assert len(trace.checkpoints) == 1
    assert trace.checkpoints[0].checkpoint_class == "oracle_needed"
    assert trace.checkpoints[0].final_adjudication == "resolved_fail"

    derived = derive_v39e_checkpoint_trace(
        local_hybrid_fixture_reference=DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH,
        oracle_request_reference_fixture=(
            "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
            "synthetic_pressure_mismatch_oracle_request_v76_reference.json"
        ),
        oracle_resolution_reference_fixture=(
            "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
            "synthetic_pressure_mismatch_oracle_resolution_v76_reference.json"
        ),
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_human_trace_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_human.json")
    trace = SyntheticPressureMismatchCheckpointTrace.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert trace.source_kind == "local_hybrid_fixture"
    assert trace.checkpoints[0].checkpoint_class == "human_needed"
    assert trace.checkpoints[0].final_adjudication == "escalated_human"

    derived = derive_v39e_checkpoint_trace(
        local_hybrid_fixture_reference=DEFAULT_V39E_LOCAL_HYBRID_HUMAN_FIXTURE_PATH,
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_oracle_trace_fails_closed_for_invalid_replay_identity_fixture() -> None:
    payload = _load_json(
        "synthetic_pressure_mismatch_oracle_resolution_v76_invalid_replay_identity.json"
    )

    with pytest.raises(
        ValidationError,
        match=(
            "request_replay_identity_sha256 must match the referenced request replay identity"
        ),
    ):
        SyntheticPressureMismatchOracleResolution.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39e_contradictory_resolution_escalates_human() -> None:
    contradictory_resolution = derive_v39e_oracle_resolution(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
        "synthetic_pressure_mismatch_oracle_request_v76_reference.json",
        resolution_disposition="contradictory",
        advisory_summary=(
            "The advisory output contradicts itself and cannot support a stable "
            "checkpoint disposition."
        ),
        raw_output_text=(
            "contradictory: the comment is both necessary domain context and also mere "
            "narration."
        ),
        repository_root=_repo_root(),
    )

    assert contradictory_resolution.resolution_disposition == "contradictory"
    assert contradictory_resolution.request_replay_identity_sha256


def test_v39e_can_bind_directly_to_released_conformance_findings() -> None:
    trace = derive_v39e_checkpoint_trace(
        conformance_report_reference_fixture=(
            "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
            "synthetic_pressure_mismatch_conformance_report_v74_reference.json"
        ),
        repository_root=_repo_root(),
    )

    assert trace.source_kind == "released_conformance_finding"
    assert len(trace.checkpoints) == 1
    assert trace.checkpoints[0].source_finding_id is not None


def test_v39e_can_bind_oracle_assisted_released_conformance_findings(
    tmp_path: Path,
) -> None:
    repo = tmp_path / "repo"
    registry_rel = Path(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/"
        "synthetic_pressure_mismatch_rule_registry_v73_reference.json"
    )
    registry_path = repo / registry_rel
    registry_path.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(_repo_root() / registry_rel, registry_path)

    (repo / "docs").mkdir(parents=True, exist_ok=True)
    (repo / "AGENTS.md").write_text("temporary agents policy\n", encoding="utf-8")
    (
        repo / "docs" / "DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md"
    ).write_text("temporary drift policy\n", encoding="utf-8")
    (
        repo / "docs" / "LOCKED_CONTINUATION_vNEXT_PLUS76.md"
    ).write_text("temporary v76 lock\n", encoding="utf-8")

    registry_payload = json.loads(registry_path.read_text(encoding="utf-8"))
    registry_id = registry_payload["registry_id"]
    registry_sha = _sha256_path(registry_path)

    subject_rel = Path(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
        "subject_comment_block_oracle_v74.json"
    )
    subject_payload = {
        "subject_id": "v39c_v74_subject_oracle_comment",
        "subject_kind": "comment_block",
        "language": "python",
        "content": "# Returns the final label chosen above.\n# This comment narrates the code.\n",
    }
    _write_json(repo / subject_rel, subject_payload)

    observation_packet_id = "v39c_v74_obs_oracle_comment"
    observation_rel = Path(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
        "synthetic_pressure_mismatch_observation_packet_v74_oracle_comment.json"
    )
    observation_payload = {
        "schema": "synthetic_pressure_mismatch_observation_packet@1",
        "target_arc": "vNext+74",
        "target_path": "V39-C",
        "contract_source": (
            "docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md"
            "#v39c_synthetic_pressure_mismatch_observation_contract@1"
        ),
        "observation_packet_id": observation_packet_id,
        "registry_schema": "synthetic_pressure_mismatch_rule_registry@1",
        "registry_id": registry_id,
        "registry_reference_fixture": registry_rel.as_posix(),
        "subject_kind": "comment_block",
        "subject_ref": subject_rel.as_posix(),
        "subject_content_sha256": _sha256_text(subject_payload["content"]),
        "findings": [],
        "derivation_metadata": {
            "evaluator_id": (
                "adeu_core_ir.synthetic_pressure_mismatch_observation"
                ".derive_v39c_observation_packet@1"
            ),
            "evaluator_version": "1",
            "registry_reference_fixture_sha256": registry_sha,
            "executed_rule_ids": [],
            "canonical_local_subject_only": True,
            "deterministic_local_execution_only": True,
        },
    }
    _write_json(repo / observation_rel, observation_payload)
    observation_hash = _canonical_json_hash(observation_payload)

    local_locator = "comment:block:render_title:line:1-2"
    source_finding_id = (
        f"{observation_packet_id}::semantic_communication_narrative_comment::{local_locator}"
    )
    report_rel = Path(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
        "synthetic_pressure_mismatch_conformance_report_v74_oracle_comment.json"
    )
    report_payload = {
        "schema": "synthetic_pressure_mismatch_conformance_report@1",
        "target_arc": "vNext+74",
        "target_path": "V39-C",
        "contract_source": (
            "docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md"
            "#v39c_synthetic_pressure_mismatch_observation_contract@1"
        ),
        "report_id": "v39c_v74_report_oracle_comment",
        "registry_schema": "synthetic_pressure_mismatch_rule_registry@1",
        "registry_id": registry_id,
        "registry_reference_fixture": registry_rel.as_posix(),
        "aggregated_observation_packet_ids": [observation_packet_id],
        "aggregated_observation_packet_hashes": [observation_hash],
        "aggregated_subject_refs": [subject_rel.as_posix()],
        "observation_count": 1,
        "finding_count": 1,
        "findings_by_evidence_regime": [
            {
                "evidence_regime": "semantic_ambiguous",
                "finding_count": 1,
            }
        ],
        "findings_by_allowed_action": [
            {
                "allowed_action": "review_only_finding",
                "finding_count": 1,
            }
        ],
        "safe_autofix_candidates": [],
        "deterministic_high_severity_findings": [],
        "review_only_findings": [
            {
                "observation_packet_id": observation_packet_id,
                "rule_id": "semantic_communication_narrative_comment",
                "local_observation_locator": local_locator,
            }
        ],
        "meta_governance_findings": [],
        "overall_pressure_mismatch_posture": "review_only_or_meta_findings_present",
        "derivation_metadata": {
            "evaluator_id": (
                "adeu_core_ir.synthetic_pressure_mismatch_observation"
                ".derive_v39c_conformance_report@1"
            ),
            "evaluator_version": "1",
            "observation_packet_hashes": [observation_hash],
            "registry_reference_fixture_sha256": registry_sha,
            "canonical_local_subject_only": True,
            "count_based_aggregation_only": True,
            "weighted_rollup_forbidden": True,
        },
    }
    _write_json(repo / report_rel, report_payload)
    report_sha = _sha256_path(repo / report_rel)

    policy_paths = [
        "AGENTS.md",
        "docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md",
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md",
    ]
    policy_sources = [
        {
            "path": path_text,
            "sha256": _sha256_path(repo / path_text),
        }
        for path_text in sorted(policy_paths)
    ]
    checkpoint_id = _checkpoint_id(
        source_kind="released_conformance_finding",
        source_binding_id=source_finding_id,
        rule_id="semantic_communication_narrative_comment",
        subject_ref=subject_rel.as_posix(),
        local_subject_anchor=local_locator,
    )
    replay_identity = {
        "source_kind": "released_conformance_finding",
        "source_binding_id": source_finding_id,
        "source_fixture_path": report_rel.as_posix(),
        "source_fixture_sha256": report_sha,
        "policy_sources": policy_sources,
        "model_id": "gpt-5.4",
        "model_version": "2026-03-01",
        "reasoning_effort": "xhigh",
        "evaluator_version": "1",
    }
    request_payload = {
        "schema": "synthetic_pressure_mismatch_oracle_request@1",
        "target_arc": "vNext+76",
        "target_path": "V39-E",
        "contract_source": (
            "docs/LOCKED_CONTINUATION_vNEXT_PLUS76.md"
            "#v39e_synthetic_pressure_mismatch_hybrid_execution_contract@1"
        ),
        "oracle_request_id": _oracle_request_id(
            checkpoint_id=checkpoint_id,
            replay_identity=replay_identity,
            interpretation_prompt=(
                "Interpret whether the anchored comment is narration without new "
                "semantics."
            ),
            bounded_context=subject_payload["content"],
        ),
        "checkpoint_id": checkpoint_id,
        "registry_schema": "synthetic_pressure_mismatch_rule_registry@1",
        "registry_id": registry_id,
        "registry_reference_fixture": registry_rel.as_posix(),
        "source_kind": "released_conformance_finding",
        "conformance_report_schema": "synthetic_pressure_mismatch_conformance_report@1",
        "conformance_report_reference_fixture": report_rel.as_posix(),
        "source_finding_id": source_finding_id,
        "rule_id": "semantic_communication_narrative_comment",
        "signal_kind": "semantic_communication_drift",
        "harm_kind": "semantic_density_loss",
        "evidence_regime": "semantic_ambiguous",
        "allowed_action": "review_only_finding",
        "resolution_route": "oracle_assisted",
        "subject_kind": "comment_block",
        "subject_ref": subject_rel.as_posix(),
        "local_subject_anchor": local_locator,
        "interpretation_prompt": (
            "Interpret whether the anchored comment is narration without new semantics."
        ),
        "bounded_context": subject_payload["content"],
        "replay_identity": replay_identity,
    }
    request = SyntheticPressureMismatchOracleRequest.model_validate(
        request_payload,
        context={"repository_root": repo},
    )
    request_rel = Path(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
        "synthetic_pressure_mismatch_oracle_request_v76_conformance_oracle.json"
    )
    _write_json(
        repo / request_rel,
        request.model_dump(mode="json", exclude_none=True),
    )

    resolution = derive_v39e_oracle_resolution(
        request_rel.as_posix(),
        resolution_disposition="advisory_support",
        advisory_summary=(
            "The anchored comment only restates logic already visible in the local code."
        ),
        raw_output_text=(
            "advisory_support: the comment narrates code without introducing a new "
            "invariant."
        ),
        repository_root=repo,
    )
    resolution_rel = Path(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
        "synthetic_pressure_mismatch_oracle_resolution_v76_conformance_oracle.json"
    )
    _write_json(
        repo / resolution_rel,
        resolution.model_dump(mode="json", exclude_none=True),
    )

    trace = derive_v39e_checkpoint_trace(
        conformance_report_reference_fixture=report_rel.as_posix(),
        oracle_request_reference_fixture=request_rel.as_posix(),
        oracle_resolution_reference_fixture=resolution_rel.as_posix(),
        repository_root=repo,
    )

    assert trace.source_kind == "released_conformance_finding"
    assert len(trace.checkpoints) == 1
    assert trace.checkpoints[0].checkpoint_class == "oracle_needed"
    assert trace.checkpoints[0].source_finding_id == source_finding_id
    assert trace.checkpoints[0].oracle_request_id == request.oracle_request_id
    assert trace.checkpoints[0].oracle_resolution_id == resolution.oracle_resolution_id
    assert trace.checkpoints[0].final_adjudication == "resolved_fail"


def test_v39e_exported_schemas_accept_reference_fixtures_and_reject_bad_transition() -> None:
    request_validator = _load_exported_schema("synthetic_pressure_mismatch_oracle_request.v1.json")
    resolution_validator = _load_exported_schema(
        "synthetic_pressure_mismatch_oracle_resolution.v1.json"
    )
    trace_validator = _load_exported_schema("synthetic_pressure_mismatch_checkpoint_trace.v1.json")

    request = _load_json("synthetic_pressure_mismatch_oracle_request_v76_reference.json")
    resolution = _load_json("synthetic_pressure_mismatch_oracle_resolution_v76_reference.json")
    deterministic_trace = _load_json(
        "synthetic_pressure_mismatch_checkpoint_trace_v76_deterministic.json"
    )
    oracle_trace = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_oracle.json")
    human_trace = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_human.json")

    assert request_validator.is_valid(request)
    assert resolution_validator.is_valid(resolution)
    assert trace_validator.is_valid(deterministic_trace)
    assert trace_validator.is_valid(oracle_trace)
    assert trace_validator.is_valid(human_trace)

    bad_transition = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_human.json")
    bad_transition["checkpoints"][0]["final_adjudication"] = "resolved_fail"  # type: ignore[index]
    assert not trace_validator.is_valid(bad_transition)
