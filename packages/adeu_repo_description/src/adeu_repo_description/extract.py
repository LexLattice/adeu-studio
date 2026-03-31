from __future__ import annotations

import json
import re
from copy import deepcopy
from pathlib import Path, PurePosixPath
from typing import Any

from adeu_ir.repo import repo_root
from urm_runtime.hashing import sha256_canonical_json

from .models import (
    SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE,
    V45A_CLASSIFICATION_POLICY_REF,
    V45C_DEPENDENCY_POLICY_REF,
    RepoDescriptionEvidenceRef,
    RepoSchemaFamilyRegistry,
    compute_v45a_classification_policy_hash,
    compute_v45c_dependency_policy_hash,
    materialize_repo_arc_dependency_register_payload,
    materialize_repo_entity_catalog_payload,
    materialize_repo_schema_family_registry_payload,
    representative_schema_keys,
)

_DEFAULT_SOURCE_PATHS: tuple[str, ...] = (
    "packages/adeu_arc_agi/schema/adeu_arc_task_packet.v1.json",
    "packages/adeu_architecture_ir/schema/adeu_architecture_analysis_request.v1.json",
    "packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json",
    "packages/adeu_core_ir/schema/ux_interaction_contract.v1.json",
    "packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json",
    "spec/policy_registry.schema.json",
    "packages/adeu_ir/schema/adeu.validator_result.v0.json",
)
_DEFAULT_V45C_SOURCE_PATHS: tuple[str, ...] = (
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md",
)
_DEFAULT_V45C_V100_SOURCE_PATHS: tuple[str, ...] = (
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md",
)


def _assert_repo_rel_path(value: str, *, field_name: str) -> str:
    normalized = value.strip().replace("\\", "/")
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    if normalized.startswith("/"):
        raise ValueError(f"{field_name} must be repository-relative")
    if ".." in PurePosixPath(normalized).parts:
        raise ValueError(f"{field_name} must not contain parent traversal")
    return str(PurePosixPath(normalized))


def _schema_discriminator(payload: dict[str, Any], *, fallback_path: str) -> str:
    schema_properties = payload.get("properties")
    if isinstance(schema_properties, dict):
        schema_field = schema_properties.get("schema")
        if isinstance(schema_field, dict):
            schema_const = schema_field.get("const")
            if isinstance(schema_const, str) and schema_const:
                return schema_const
    return f"missing_schema_discriminator:{fallback_path}"


def _schema_key(schema_discriminator: str, *, schema_path: str) -> str:
    if "@" in schema_discriminator:
        return schema_discriminator.split("@", 1)[0]
    filename = Path(schema_path).name
    if filename.endswith(".schema.json"):
        stem = filename[: -len(".schema.json")]
    elif filename.endswith(".json"):
        stem = filename[: -len(".json")]
    else:
        stem = filename
    # Drop trailing version suffixes like ".v1", ".v0_1", ".v10".
    stem = re.sub(r"\.v[0-9][0-9_]*$", "", stem)
    return stem


def _family_cluster(schema_key: str) -> str:
    if schema_key.startswith("adeu_arc_"):
        return "adeu_arc"
    if schema_key.startswith("adeu_architecture_"):
        return "adeu_architecture"
    if schema_key.startswith("meta_"):
        return "meta"
    if schema_key.startswith("ux_"):
        return "ux"
    if schema_key.startswith("policy_"):
        return "policy"
    if schema_key.startswith("adeu_core_ir"):
        return "adeu_core_ir"
    if schema_key.startswith("adeu.validator"):
        return "adeu_validator"
    if schema_key.startswith("adeu_"):
        return "adeu_generic"
    return "residual"


def _lineage_overlay(family_cluster: str) -> str:
    return {
        "adeu_arc": "arc_agi_lineage",
        "adeu_architecture": "architecture_lineage",
        "meta": "meta_control_lineage",
        "ux": "ux_governance_lineage",
        "policy": "policy_lineage",
        "adeu_core_ir": "core_ir_lineage",
        "adeu_validator": "validator_lineage",
        "adeu_generic": "adeu_generic_lineage",
        "residual": "residual_lineage",
    }[family_cluster]


def _primary_carrier_class(schema_key: str) -> str:
    key = schema_key.lower().replace(".", "_")
    if any(token in key for token in ("contract", "policy", "rule", "gate")):
        return "ContractGate"
    if any(token in key for token in ("trace", "checkpoint", "log")):
        return "TraceRecord"
    if any(token in key for token in ("manifest", "registry", "catalog", "table", "snapshot")):
        return "CuratedSet"
    if any(token in key for token in ("report", "diagnostic", "resolution", "evidence", "result")):
        return "Adjudication"
    if any(token in key for token in ("ir", "model", "projection", "delta", "payload")):
        return "StructuralModel"
    return "IntakeFrame"


def _secondary_role_form_tags(schema_key: str) -> list[str]:
    key = schema_key.lower().replace(".", "_")
    tags: list[str] = []
    token_map = (
        ("packet", "packet"),
        ("frame", "frame"),
        ("request", "request"),
        ("candidate", "candidate"),
        ("trace", "trace"),
        ("manifest", "manifest"),
        ("registry", "registry"),
        ("catalog", "catalog"),
        ("report", "report"),
        ("diagnostic", "diagnostics"),
        ("result", "result"),
        ("contract", "contract"),
        ("policy", "policy"),
        ("ir", "ir"),
        ("projection", "projection"),
        ("payload", "payload"),
        ("delta", "delta"),
    )
    for token, tag in token_map:
        if token in key:
            tags.append(tag)
    if not tags:
        tags.append("plan")
    return sorted(set(tags))


def _core_envelope_features(payload: dict[str, Any]) -> list[str]:
    features: list[str] = []
    schema_properties = payload.get("properties")
    has_schema_const = False
    if isinstance(schema_properties, dict):
        schema_field = schema_properties.get("schema")
        if isinstance(schema_field, dict):
            has_schema_const = isinstance(schema_field.get("const"), str)
    if has_schema_const:
        features.append("has_schema_const")
    else:
        features.append("missing_schema_const")
    if payload.get("additionalProperties") is False:
        features.append("closed_root")
    if "$defs" in payload:
        features.append("has_defs")
    return sorted(features)


def _residual_flags(payload: dict[str, Any]) -> list[str]:
    flags: list[str] = []
    schema_properties = payload.get("properties")
    has_schema_const = False
    if isinstance(schema_properties, dict):
        schema_field = schema_properties.get("schema")
        if isinstance(schema_field, dict):
            has_schema_const = isinstance(schema_field.get("const"), str)
    if not has_schema_const:
        flags.append("missing_schema_const")
    additional = payload.get("additionalProperties")
    if additional is True:
        flags.append("open_root_map")
    return sorted(flags)


def _classification_method(payload: dict[str, Any], *, schema_discriminator: str) -> str:
    if schema_discriminator.startswith("missing_schema_discriminator:"):
        return "lexical_naming"
    schema_properties = payload.get("properties")
    if isinstance(schema_properties, dict):
        schema_field = schema_properties.get("schema")
        if isinstance(schema_field, dict) and isinstance(schema_field.get("const"), str):
            return "structural_signature"
    return "lexical_naming"


def _classification_posture(classification_method: str) -> str:
    if classification_method == "lexical_naming":
        return "inferred_heuristically"
    return "derived_deterministically"


def _semantic_role_for_carrier(carrier: str) -> str:
    return {
        "IntakeFrame": "intake_surface",
        "TraceRecord": "trace_surface",
        "CuratedSet": "curated_set_surface",
        "Adjudication": "adjudication_surface",
        "ContractGate": "contract_surface",
        "StructuralModel": "structural_model_surface",
    }[carrier]


def _as_repo_rel(path: Path, *, root: Path) -> str:
    return path.relative_to(root).as_posix()


def _default_source_paths() -> list[str]:
    return list(_DEFAULT_SOURCE_PATHS)


def _extract_json_blocks(text: str) -> list[dict[str, Any]]:
    blocks: list[dict[str, Any]] = []
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        if lines[index].strip() != "```json":
            index += 1
            continue
        index += 1
        block_lines: list[str] = []
        while index < len(lines) and lines[index].strip() != "```":
            block_lines.append(lines[index])
            index += 1
        if index < len(lines):
            index += 1
        try:
            payload = json.loads("\n".join(block_lines))
        except json.JSONDecodeError:
            continue
        if isinstance(payload, dict):
            blocks.append(payload)
    return blocks


def _extract_lock_contract(*, text: str, target_arc: str, target_path: str) -> dict[str, Any]:
    for payload in _extract_json_blocks(text):
        if payload.get("target_arc") == target_arc and payload.get("target_path") == target_path:
            return payload
    raise ValueError(f"{target_arc} lock contract block is missing from source set")


def _extract_v45_path_rows(*, text: str) -> dict[str, str]:
    rows: dict[str, str] = {}
    lines = text.splitlines()
    table_header = "| Path | Theme | Primary output | Status |"
    in_table = False
    for line in lines:
        if line.strip() == table_header:
            in_table = True
            continue
        if not in_table:
            continue
        stripped = line.strip()
        if not stripped.startswith("|"):
            break
        if stripped.startswith("|---"):
            continue
        cells = [cell.strip() for cell in stripped.strip("|").split("|")]
        if len(cells) != 4:
            continue
        path = cells[0].strip("`")
        status = cells[3]
        if path.startswith("V45-"):
            rows[path] = status
    if not rows:
        raise ValueError("V45 path ladder rows are missing from planning source")
    return rows


def _extract_selected_v45_path(*, text: str) -> str:
    candidates: set[str] = set()

    phrase_match = re.search(
        r"select\s+`(?P<path>V45-[A-Z])`\s+as the next default candidate",
        text,
    )
    if phrase_match is not None:
        candidates.add(phrase_match.group("path"))

    branch_path_match = re.search(
        r"Recommended next path for this branch:\s*\n\s*-\s*`(?P<path>V45-[A-Z])`",
        text,
    )
    if branch_path_match is not None:
        candidates.add(branch_path_match.group("path"))

    section_match = re.search(
        r"^## Recommended Next Path \(`(?P<path>V45-[A-Z])`\)$",
        text,
        flags=re.MULTILINE,
    )
    if section_match is not None:
        candidates.add(section_match.group("path"))

    try:
        path_rows = _extract_v45_path_rows(text=text)
    except ValueError:
        path_rows = {}
    selected_table_paths = sorted(
        path for path, status in path_rows.items() if status == "selected_next_branch_local"
    )
    candidates.update(selected_table_paths)

    if not candidates:
        raise ValueError("branch-local V45 default selection markers are missing")
    if len(candidates) != 1:
        raise ValueError(
            "branch-local V45 default selection markers must agree on one selected path"
        )
    return next(iter(candidates))


def derive_v45a_repo_schema_family_registry(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    normalized_source_paths = source_paths if source_paths is not None else _default_source_paths()
    normalized_source_paths = sorted(
        {_assert_repo_rel_path(path, field_name="source_paths") for path in normalized_source_paths}
    )
    if not normalized_source_paths:
        raise ValueError("source_paths must not be empty")

    source_files: list[dict[str, Any]] = []
    schema_entries: list[dict[str, Any]] = []
    evidence_refs_by_id: dict[str, RepoDescriptionEvidenceRef] = {}
    schema_by_key: dict[str, dict[str, Any]] = {}

    for source_path in normalized_source_paths:
        absolute_path = root / source_path
        if not absolute_path.is_file():
            raise FileNotFoundError(f"source path does not exist: {source_path}")
        raw_payload = json.loads(absolute_path.read_text(encoding="utf-8"))
        if not isinstance(raw_payload, dict):
            raise ValueError(f"source schema must be a json object: {source_path}")
        source_hash = sha256_canonical_json(raw_payload)
        source_files.append({"source_path": source_path, "source_hash": source_hash})

        schema_discriminator = _schema_discriminator(raw_payload, fallback_path=source_path)
        schema_key = _schema_key(schema_discriminator, schema_path=source_path)
        if schema_key in schema_by_key:
            raise ValueError(f"duplicate schema_key in source set: {schema_key}")
        schema_by_key[schema_key] = raw_payload

        family_cluster = _family_cluster(schema_key)
        primary_carrier_class = _primary_carrier_class(schema_key)
        lineage_overlay = _lineage_overlay(family_cluster)
        classification_method = _classification_method(
            raw_payload, schema_discriminator=schema_discriminator
        )
        classification_posture = _classification_posture(classification_method)

        base_evidence_id = f"evidence:{schema_key}"
        row_evidence: list[RepoDescriptionEvidenceRef] = [
            RepoDescriptionEvidenceRef(
                evidence_ref=f"{base_evidence_id}:anchor",
                evidence_kind="observed_anchor_tuple_evidence",
            ),
            RepoDescriptionEvidenceRef(
                evidence_ref=f"{base_evidence_id}:lexical",
                evidence_kind="lexical_cue_evidence",
            ),
        ]
        if classification_method == "structural_signature":
            row_evidence.append(
                RepoDescriptionEvidenceRef(
                    evidence_ref=f"{base_evidence_id}:structural",
                    evidence_kind="structural_signature_evidence",
                )
            )
        if classification_method != "lexical_naming" and any(
            token in schema_key for token in ("request", "report", "result", "registry")
        ):
            row_evidence.append(
                RepoDescriptionEvidenceRef(
                    evidence_ref=f"{base_evidence_id}:semantic",
                    evidence_kind="semantic_function_cue_evidence",
                )
            )
        if classification_method != "lexical_naming" and any(
            token in schema_key for token in ("contract", "policy")
        ):
            row_evidence.append(
                RepoDescriptionEvidenceRef(
                    evidence_ref=f"{base_evidence_id}:governance",
                    evidence_kind="governance_cue_evidence",
                )
            )
        for evidence in row_evidence:
            evidence_refs_by_id[evidence.evidence_ref] = evidence

        schema_entries.append(
            {
                "schema_key": schema_key,
                "schema_path": source_path,
                "schema_discriminator": schema_discriminator,
                "family_cluster": family_cluster,
                "primary_carrier_class": primary_carrier_class,
                "secondary_role_form_tags": _secondary_role_form_tags(schema_key),
                "lineage_overlay": lineage_overlay,
                "core_envelope_features": _core_envelope_features(raw_payload),
                "residual_flags": _residual_flags(raw_payload),
                "classification_posture": classification_posture,
                "classification_method": classification_method,
                "adjudicator_ref": None,
                "supporting_evidence_refs": sorted(
                    evidence.evidence_ref for evidence in row_evidence
                ),
            }
        )

    source_set_hash = sha256_canonical_json(
        {
            "source_paths": [
                entry["source_path"]
                for entry in sorted(source_files, key=lambda row: row["source_path"])
            ],
            "source_hashes": {
                entry["source_path"]: entry["source_hash"]
                for entry in sorted(source_files, key=lambda row: row["source_path"])
            },
        }
    )
    repo_snapshot_hash = source_set_hash
    repo_snapshot_id = f"repo_snapshot_{repo_snapshot_hash[:24]}"

    reconstruction_subset: list[dict[str, Any]] = []
    for schema_key in representative_schema_keys():
        payload = schema_by_key.get(schema_key)
        if payload is None:
            raise ValueError(
                f"representative reconstruction schema is missing from source set: {schema_key}"
            )
        reconstruction_evidence_ref = f"evidence:{schema_key}:reconstruction"
        evidence_refs_by_id[reconstruction_evidence_ref] = RepoDescriptionEvidenceRef(
            evidence_ref=reconstruction_evidence_ref,
            evidence_kind="reconstruction_subset_evidence",
        )
        reconstruction_subset.append(
            {
                "schema_key": schema_key,
                "source_schema_definition": payload,
                "reconstructed_schema_definition": deepcopy(payload),
                "evidence_refs": sorted(
                    {
                        reconstruction_evidence_ref,
                        f"evidence:{schema_key}:anchor",
                    }
                ),
            }
        )

    payload_without_registry_id = {
        "schema": "repo_schema_family_registry@1",
        "repo_snapshot_id": repo_snapshot_id,
        "repo_snapshot_hash": repo_snapshot_hash,
        "snapshot_validity_posture": snapshot_validity_posture,
        "source_set": {
            "source_paths": normalized_source_paths,
            "source_set_hash": source_set_hash,
        },
        "classification_policy_ref": V45A_CLASSIFICATION_POLICY_REF,
        "classification_policy_hash": compute_v45a_classification_policy_hash(),
        "reconstruction_equivalence_mode": "canonical_normalized_semantic_equivalence",
        "schema_entries": sorted(schema_entries, key=lambda row: row["schema_key"]),
        "reconstruction_subset": sorted(reconstruction_subset, key=lambda row: row["schema_key"]),
        "evidence_refs": [
            evidence_refs_by_id[key].model_dump(mode="json") for key in sorted(evidence_refs_by_id)
        ],
    }
    return materialize_repo_schema_family_registry_payload(payload_without_registry_id)


def derive_v45a_repo_entity_catalog(
    *,
    schema_family_registry: dict[str, Any],
) -> dict[str, Any]:
    registry = RepoSchemaFamilyRegistry.model_validate(schema_family_registry)
    evidence_refs = [
        RepoDescriptionEvidenceRef.model_validate(entry).model_dump(mode="json")
        for entry in registry.evidence_refs
    ]
    entries = []
    derivation_posture_map = {
        "observed": "observed",
        "derived_deterministically": "derived",
        "inferred_heuristically": "inferred",
        "adjudicated": "adjudicated",
        "settled": "settled",
    }
    for schema_entry in registry.schema_entries:
        entries.append(
            {
                "entity_ref": f"schema:{schema_entry.schema_key}",
                "surface_kind": "schema",
                "semantic_role": _semantic_role_for_carrier(schema_entry.primary_carrier_class),
                "governance_posture": "descriptive_registry_row",
                "derivation_posture": derivation_posture_map[schema_entry.classification_posture],
                "mutation_posture": "read_only_descriptive",
                "classification_posture": schema_entry.classification_posture,
                "classification_method": schema_entry.classification_method,
                "adjudicator_ref": schema_entry.adjudicator_ref,
                "supporting_evidence_refs": schema_entry.supporting_evidence_refs,
            }
        )
    payload_without_catalog_id = {
        "schema": "repo_entity_catalog@1",
        "repo_snapshot_id": registry.repo_snapshot_id,
        "repo_snapshot_hash": registry.repo_snapshot_hash,
        "snapshot_validity_posture": registry.snapshot_validity_posture,
        "catalog_scope": "schema-visible-entity-catalog-over-bounded-repo-snapshot",
        "entity_coverage_mode": SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE,
        "classification_policy_ref": registry.classification_policy_ref,
        "classification_policy_hash": registry.classification_policy_hash,
        "entities": sorted(entries, key=lambda row: row["entity_ref"]),
        "evidence_refs": evidence_refs,
    }
    return materialize_repo_entity_catalog_payload(payload_without_catalog_id)


def derive_v45a_repo_description_bundle(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> tuple[dict[str, Any], dict[str, Any]]:
    registry = derive_v45a_repo_schema_family_registry(
        source_paths=source_paths,
        snapshot_validity_posture=snapshot_validity_posture,
    )
    catalog = derive_v45a_repo_entity_catalog(schema_family_registry=registry)
    return registry, catalog


def derive_v45c_repo_arc_dependency_register(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    normalized_source_paths = (
        source_paths if source_paths is not None else list(_DEFAULT_V45C_SOURCE_PATHS)
    )
    normalized_source_paths = sorted(
        {_assert_repo_rel_path(path, field_name="source_paths") for path in normalized_source_paths}
    )
    if not normalized_source_paths:
        raise ValueError("source_paths must not be empty")

    source_hashes: dict[str, str] = {}
    options_text: str | None = None
    lock_text: str | None = None
    lock102_text: str | None = None
    for source_path in normalized_source_paths:
        absolute_path = root / source_path
        if not absolute_path.is_file():
            raise FileNotFoundError(f"source path does not exist: {source_path}")
        text = absolute_path.read_text(encoding="utf-8")
        source_hashes[source_path] = sha256_canonical_json({"text": text})
        filename = Path(source_path).name
        if filename == "DRAFT_NEXT_ARC_OPTIONS_v28.md":
            options_text = text
        elif filename == "LOCKED_CONTINUATION_vNEXT_PLUS100.md":
            if lock_text is not None:
                raise ValueError("duplicate v100 lock source provided")
            lock_text = text
        elif filename == "LOCKED_CONTINUATION_vNEXT_PLUS102.md":
            if lock102_text is not None:
                raise ValueError("duplicate v102 lock source provided")
            lock102_text = text

    if options_text is None:
        raise ValueError("source_paths must include docs/DRAFT_NEXT_ARC_OPTIONS_v28.md")
    if lock_text is None:
        raise ValueError("source_paths must include docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md")
    if lock102_text is None:
        raise ValueError("source_paths must include docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md")

    if "select `V45-C` as the next default candidate for" not in options_text:
        raise ValueError("planning source must include the bounded V45-C corrective follow-up note")

    path_rows = _extract_v45_path_rows(text=options_text)
    lock_contract_v100 = _extract_lock_contract(
        text=lock_text,
        target_arc="vNext+100",
        target_path="V45-C",
    )
    lock_contract_v102 = _extract_lock_contract(
        text=lock102_text,
        target_arc="vNext+102",
        target_path="V45-C",
    )
    selected_path = lock_contract_v102["target_path"]

    source_set_hash = sha256_canonical_json(
        {
            "source_paths": normalized_source_paths,
            "source_hashes": {path: source_hashes[path] for path in normalized_source_paths},
        }
    )
    repo_snapshot_hash = source_set_hash
    repo_snapshot_id = f"repo_snapshot_{repo_snapshot_hash[:24]}"

    evidence_refs_by_id: dict[str, RepoDescriptionEvidenceRef] = {}
    for path in sorted(path_rows):
        evidence_ref = f"evidence:planning:v28:row:{path}"
        evidence_refs_by_id[evidence_ref] = RepoDescriptionEvidenceRef(
            evidence_ref=evidence_ref,
            evidence_kind="planning_table_row_evidence",
        )
    evidence_refs_by_id["evidence:planning:v28:corrective_selection"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:planning:v28:corrective_selection",
        evidence_kind="planning_selection_evidence",
    )
    evidence_refs_by_id["evidence:lock:v100:contract"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:lock:v100:contract",
        evidence_kind="lock_contract_evidence",
    )
    evidence_refs_by_id["evidence:policy:v45c"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:policy:v45c",
        evidence_kind="dependency_policy_evidence",
    )
    evidence_refs_by_id["evidence:lock:v102:contract"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:lock:v102:contract",
        evidence_kind="lock_contract_evidence",
    )

    dependency_map: dict[str, list[str]] = {
        "V45-F": ["V45-B", "V45-C", "V45-D", "V45-E"],
    }
    tracked_paths = ("V45-B", "V45-C", "V45-D", "V45-E", "V45-F")
    missing_paths = [path for path in tracked_paths if path not in path_rows]
    if missing_paths:
        raise ValueError(f"planning source is missing tracked V45 paths: {missing_paths}")

    open_arc_entries: list[dict[str, Any]] = []
    for path in tracked_paths:
        blocked_by = sorted(dependency_map.get(path, []))
        if path == selected_path:
            phase_status = "locked_start_bundle"
            authority_layer = "lock"
        else:
            phase_status = path_rows[path]
            authority_layer = "planning"
        open_arc_entries.append(
            {
                "arc_id": path,
                "family_path": path,
                "phase_status": phase_status,
                "authority_layer": authority_layer,
                "readiness_posture": "blocked" if blocked_by else "ready",
                "blocker_arc_ids": blocked_by,
                "blocked_by_arc_ids": blocked_by,
                "derivation_posture": "derived_deterministically",
                "derivation_method": "deterministic_projection",
                "source_artifact_refs": sorted(
                    {
                        "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
                        *(
                            {
                                "docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md",
                                "docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md",
                            }
                            if path == selected_path
                            else set()
                        ),
                    }
                ),
                "supporting_evidence_refs": sorted(
                    {
                        f"evidence:planning:v28:row:{path}",
                        (
                            "evidence:planning:v28:corrective_selection"
                            if path == selected_path
                            else f"evidence:planning:v28:row:{path}"
                        ),
                        (
                            "evidence:lock:v102:contract"
                            if path == selected_path
                            else f"evidence:planning:v28:row:{path}"
                        ),
                        (
                            "evidence:lock:v100:contract"
                            if path == selected_path
                            else f"evidence:planning:v28:row:{path}"
                        ),
                    }
                ),
            }
        )

    dependency_edges: list[dict[str, Any]] = []
    for to_arc_id, from_arc_ids in sorted(dependency_map.items()):
        for from_arc_id in sorted(from_arc_ids):
            dependency_edges.append(
                {
                    "edge_id": f"edge:{from_arc_id.lower()}-to-{to_arc_id.lower()}",
                    "from_arc_id": from_arc_id,
                    "to_arc_id": to_arc_id,
                    "dependency_kind": "descriptive_prerequisite"
                    if to_arc_id == "V45-F"
                    else "family_progression",
                    "dependency_strength": "hard",
                    "dependency_status": "unresolved",
                    "derivation_posture": "derived_deterministically",
                    "derivation_method": "deterministic_projection",
                    "source_artifact_refs": ["docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"],
                    "supporting_evidence_refs": sorted(
                        {
                            f"evidence:planning:v28:row:{from_arc_id}",
                            f"evidence:planning:v28:row:{to_arc_id}",
                            "evidence:policy:v45c",
                        }
                    ),
                }
            )

    payload_without_register_id = {
        "schema": "repo_arc_dependency_register@2",
        "repo_snapshot_id": repo_snapshot_id,
        "repo_snapshot_hash": repo_snapshot_hash,
        "snapshot_validity_posture": snapshot_validity_posture,
        "source_set": normalized_source_paths,
        "source_set_hash": source_set_hash,
        "register_scope": (
            "v45-open-arc-dependency-register-corrective-hardening-over-"
            "branch-local-selection"
        ),
        "pending_list_posture": "machine_enforced_open_arc_register",
        "cycle_posture": "cycles_forbidden",
        "cycle_detection_scope": "all_declared_edges",
        "dependency_policy_ref": V45C_DEPENDENCY_POLICY_REF,
        "dependency_policy_hash": compute_v45c_dependency_policy_hash(),
        "extraction_posture": "derived_deterministically",
        "extraction_method": "deterministic_projection",
        "open_arc_entries": sorted(open_arc_entries, key=lambda row: row["arc_id"]),
        "dependency_edges": sorted(dependency_edges, key=lambda row: row["edge_id"]),
        "evidence_refs": [
            evidence_refs_by_id[key].model_dump(mode="json") for key in sorted(evidence_refs_by_id)
        ],
    }
    if lock_contract_v100.get("target_path") != selected_path:
        raise ValueError("released v100 and corrective v102 lock target paths must agree")
    return materialize_repo_arc_dependency_register_payload(payload_without_register_id)


def default_v45a_source_paths() -> list[str]:
    return list(_DEFAULT_SOURCE_PATHS)


def default_v45c_source_paths() -> list[str]:
    return list(_DEFAULT_V45C_SOURCE_PATHS)
