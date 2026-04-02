from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_commitments_ir import (
    ADEU_COMMITMENTS_IR_SCHEMA,
    ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA,
    ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA,
    ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA,
    CHECKER_FACT_BUNDLE_SCHEMA,
    D1_NORMALIZED_IR_SCHEMA,
    POLICY_EVALUATION_RESULT_SET_SCHEMA,
    POLICY_OBLIGATION_LEDGER_SCHEMA,
    PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA,
)
from adeu_commitments_ir.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            ADEU_COMMITMENTS_IR_SCHEMA,
            root / "packages" / "adeu_commitments_ir" / "schema" / "adeu_commitments_ir.v0_1.json",
            root / "spec" / "adeu_commitments_ir.schema.json",
        ),
        (
            D1_NORMALIZED_IR_SCHEMA,
            root / "packages" / "adeu_commitments_ir" / "schema" / "d1_normalized_ir.v1.json",
            root / "spec" / "d1_normalized_ir.schema.json",
        ),
        (
            PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "predicate_contracts_bootstrap.v1.json",
            root / "spec" / "predicate_contracts_bootstrap.schema.json",
        ),
        (
            CHECKER_FACT_BUNDLE_SCHEMA,
            root / "packages" / "adeu_commitments_ir" / "schema" / "checker_fact_bundle.v1.json",
            root / "spec" / "checker_fact_bundle.schema.json",
        ),
        (
            POLICY_EVALUATION_RESULT_SET_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "policy_evaluation_result_set.v1.json",
            root / "spec" / "policy_evaluation_result_set.schema.json",
        ),
        (
            POLICY_OBLIGATION_LEDGER_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "policy_obligation_ledger.v1.json",
            root / "spec" / "policy_obligation_ledger.schema.json",
        ),
        (
            ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_markdown_coexistence_profile.v1.json",
            root / "spec" / "anm_markdown_coexistence_profile.schema.json",
        ),
        (
            ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_selector_predicate_ownership_profile.v1.json",
            root / "spec" / "anm_selector_predicate_ownership_profile.schema.json",
        ),
        (
            ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_policy_consumer_binding_profile.v1.json",
            root / "spec" / "anm_policy_consumer_binding_profile.schema.json",
        ),
    ]


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for _, authoritative, mirror in _schema_pairs():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    before = {
        authoritative: authoritative.read_bytes()
        for _, authoritative, _ in _schema_pairs()
    }
    before.update(
        {
            mirror: mirror.read_bytes()
            for _, _, mirror in _schema_pairs()
        }
    )

    export_schema_main()
    after_first = {path: path.read_bytes() for path in before}

    export_schema_main()
    after_second = {path: path.read_bytes() for path in before}

    assert before == after_first == after_second


def test_exported_schema_uses_frozen_writer_profile() -> None:
    for _, authoritative, mirror in _schema_pairs():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))

        expected_authoritative = json.dumps(authoritative_payload, indent=2, sort_keys=True) + "\n"
        expected_mirror = json.dumps(mirror_payload, indent=2, sort_keys=True) + "\n"
        assert authoritative.read_text(encoding="utf-8") == expected_authoritative
        assert mirror.read_text(encoding="utf-8") == expected_mirror


def test_exported_schema_has_stable_contract_markers() -> None:
    schema_payloads = {
        schema_label: json.loads(authoritative.read_text(encoding="utf-8"))
        for schema_label, authoritative, _ in _schema_pairs()
    }

    commitments_schema = schema_payloads[ADEU_COMMITMENTS_IR_SCHEMA]
    assert commitments_schema["properties"]["schema"]["const"] == ADEU_COMMITMENTS_IR_SCHEMA
    discriminator = commitments_schema["properties"]["modules"]["items"]["discriminator"]
    assert discriminator["propertyName"] == "module_kind"
    assert sorted(discriminator["mapping"].keys()) == ["arc_lock", "slice_spec", "stop_gate"]
    assert (
        schema_payloads[D1_NORMALIZED_IR_SCHEMA]["properties"]["schema"]["const"]
        == D1_NORMALIZED_IR_SCHEMA
    )
    assert (
        schema_payloads[PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA]["properties"]["schema"]["const"]
        == PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA
    )
    assert (
        schema_payloads[CHECKER_FACT_BUNDLE_SCHEMA]["properties"]["schema"]["const"]
        == CHECKER_FACT_BUNDLE_SCHEMA
    )
    assert (
        schema_payloads[POLICY_EVALUATION_RESULT_SET_SCHEMA]["properties"]["schema"]["const"]
        == POLICY_EVALUATION_RESULT_SET_SCHEMA
    )
    assert (
        schema_payloads[POLICY_OBLIGATION_LEDGER_SCHEMA]["properties"]["schema"]["const"]
        == POLICY_OBLIGATION_LEDGER_SCHEMA
    )
    assert (
        schema_payloads[ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA]["properties"]["schema"]["const"]
        == ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA
    )
    assert (
        schema_payloads[ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA]["properties"][
            "schema"
        ]["const"]
        == ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA
    )
    assert (
        schema_payloads[ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA]["properties"]["schema"][
            "const"
        ]
        == ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA
    )
    checker_fact_row_defs = schema_payloads[CHECKER_FACT_BUNDLE_SCHEMA]["$defs"]
    value_type_fact = checker_fact_row_defs["ValueTypeObservationFact"]
    assert value_type_fact["properties"]["fact_type"]["const"] == "value_type_observation"
    provenance_mode = checker_fact_row_defs["FactProvenance"]["properties"]["mode"]["enum"]
    assert provenance_mode == ["direct", "derived", "indirect", "absent", "inconclusive"]
    coexistence_defs = schema_payloads[ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA]["$defs"]
    embedding_posture = coexistence_defs["AnmCoexistenceSourceRow"]["properties"][
        "companion_embedding_posture"
    ]["enum"]
    assert embedding_posture == [
        "not_applicable",
        "embedded_in_host_markdown",
        "adjacent_companion_document",
    ]
    assert (
        schema_payloads[ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA]["properties"][
            "released_stack_refs"
        ]["uniqueItems"]
        is True
    )
    assert (
        coexistence_defs["MigrationDiscipline"]["properties"]["compatible_local_source_scopes"][
            "uniqueItems"
        ]
        is True
    )
    assert (
        coexistence_defs["MigrationDiscipline"]["properties"]["preferred_source_postures"][
            "uniqueItems"
        ]
        is True
    )
    assert (
        coexistence_defs["AnmCoexistenceSourceRow"]["properties"][
            "allowed_constrain_actions"
        ]["uniqueItems"]
        is True
    )
    for field_name in (
        "allowed_now_actions",
        "later_lock_required_actions",
        "forbidden_actions",
    ):
        assert coexistence_defs["AnmAdoptionBoundaryRow"]["properties"][field_name][
            "uniqueItems"
        ] is True
    ownership_defs = schema_payloads[ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA]["$defs"]
    assert (
        schema_payloads[ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA]["properties"][
            "released_stack_refs"
        ]["uniqueItems"]
        is True
    )
    selector_owner_layer = ownership_defs["SelectorOwnershipRow"]["properties"][
        "selector_owner_layer"
    ]["enum"]
    assert selector_owner_layer == ["bootstrap", "o_owned"]
    predicate_owner_layer = ownership_defs["PredicateOwnershipRow"]["properties"][
        "predicate_owner_layer"
    ]["enum"]
    assert predicate_owner_layer == ["bootstrap", "e_owned"]
    compatibility_posture = ownership_defs["OwnershipCompatibilityRule"]["properties"][
        "compatibility_posture"
    ]["enum"]
    assert compatibility_posture == [
        "bootstrap_only",
        "bootstrap_compatible_with_owned_successor",
        "owned_preferred_bootstrap_still_allowed",
        "mixed_ownership_forbidden",
    ]
    consumer_defs = schema_payloads[ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA]["$defs"]
    assert (
        schema_payloads[ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA]["properties"][
            "released_stack_refs"
        ]["uniqueItems"]
        is True
    )
    consumer_world_kind = consumer_defs["AnmPolicyConsumerRow"]["properties"][
        "consumer_world_kind"
    ]["enum"]
    assert consumer_world_kind == [
        "released_v45_descriptive_artifact_world",
        "released_runtime_event_artifact_world",
    ]
    consumer_ref_kind = consumer_defs["AnmPolicyConsumerRow"]["properties"][
        "consumer_ref_kind"
    ]["enum"]
    assert consumer_ref_kind == [
        "released_v45_artifact_ref",
        "released_runtime_event_stream_ref",
    ]
    consumer_authority_relation = consumer_defs["AnmPolicyConsumerRow"]["properties"][
        "current_consumer_authority_relation"
    ]["enum"]
    assert consumer_authority_relation == [
        "constrain_only_non_executive",
        "later_lock_required_for_effective_action",
    ]
    for field_name in (
        "supporting_result_refs",
        "supporting_ledger_refs",
        "allowed_now_actions",
        "later_lock_required_actions",
        "forbidden_actions",
    ):
        assert consumer_defs["AnmPolicyConsumerRow"]["properties"][field_name][
            "uniqueItems"
        ] is True


def test_exported_schema_has_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()

    def _check_node(node: object) -> None:
        if isinstance(node, dict):
            for key in sorted(node):
                _check_node(node[key])
            return
        if isinstance(node, list):
            for item in node:
                _check_node(item)
            return
        if not isinstance(node, str):
            return

        normalized = node.replace("\\", "/")
        assert root_text not in normalized
        assert not normalized.startswith("/home/")
        assert not normalized.startswith("/Users/")
        assert _WINDOWS_ABSOLUTE_PATH_RE.search(node) is None

    for _, authoritative, mirror in _schema_pairs():
        for path in (authoritative, mirror):
            payload = json.loads(path.read_text(encoding="utf-8"))
            _check_node(payload)
