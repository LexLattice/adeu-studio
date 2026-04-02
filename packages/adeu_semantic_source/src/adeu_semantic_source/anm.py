from __future__ import annotations

import json
import re
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from typing import Any

from adeu_commitments_ir import (
    AnmAdoptionBoundaryRow,
    AnmBenchmarkPolicyConsumerBindingProfile,
    AnmBenchmarkPolicyConsumerRow,
    AnmCoexistenceSourceRow,
    AnmMarkdownCoexistenceProfile,
    AnmPolicyConsumerBindingProfile,
    AnmPolicyConsumerRow,
    AnmSelectorPredicateOwnershipProfile,
    CheckerFactBundle,
    ClauseScopeBlockerResultRow,
    D1Clause,
    D1NormalizedIR,
    D1Qualifier,
    D1SelectorRef,
    EvaluationNotice,
    MigrationDiscipline,
    OwnershipCompatibilityRule,
    PolicyEvaluationResultSet,
    PolicyObligationLedger,
    PolicyObligationLedgerRow,
    PredicateArgumentSpec,
    PredicateContract,
    PredicateContractsBootstrap,
    PredicateOwnershipRow,
    SelectorOwnershipRow,
    SubjectScopedResultRow,
    stable_payload_hash,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError

_D1_BLOCK_HEADER_RE = re.compile(r"^:::D@1(?:\s+id=(?P<block_id>[A-Za-z0-9_.-]+))\s*$")
_CLAUSE_RE = re.compile(r"^@(?P<label>[A-Za-z0-9_.-]+)\s+(?P<modal>MUST|MUST_NOT)\s+(?P<rest>.+)$")
_PREDICATE_CALL_RE = re.compile(
    r"^(?P<name>[A-Za-z_][A-Za-z0-9_]*)\((?P<args>.*)\)$"
)
_QUALIFIER_SEGMENT_RE = re.compile(
    r"(ONLY_IF|UNLESS)\s+(.+?)(?=(?:\s+(?:ONLY_IF|UNLESS)\s+)|$)"
)


class AnmCompileError(ValueError):
    """Fail-closed bounded ANM / D@1 compilation error."""


@dataclass(frozen=True)
class _ParsedBlock:
    block_id: str
    selector_source_text: str
    clause_lines: list[str]


def _normalize_text(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")


def _sha256_text(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def _require_non_empty_text(value: Any, *, field_name: str) -> str:
    if not isinstance(value, str):
        raise AnmCompileError(f"{field_name} must be a string")
    normalized = value.strip()
    if not normalized:
        raise AnmCompileError(f"{field_name} must not be empty")
    return normalized


def _require_mapping(value: Any, *, field_name: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise AnmCompileError(f"{field_name} must be a mapping")
    return value


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json_artifact_ref(
    ref: str,
    *,
    field_name: str,
    expected_schema: str,
) -> dict[str, Any]:
    repo_root_path = _repo_root_path().resolve()
    ref_path = Path(ref)
    if ref_path.is_absolute():
        raise AnmCompileError(f"{field_name} {ref} must remain within the repo root")
    candidate_path = (repo_root_path / ref_path).resolve()
    if candidate_path != repo_root_path and repo_root_path not in candidate_path.parents:
        raise AnmCompileError(f"{field_name} {ref} must remain within the repo root")
    try:
        payload = json.loads(candidate_path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise AnmCompileError(f"{field_name} {ref} is unresolved") from error
    except OSError as error:
        raise AnmCompileError(f"{field_name} {ref} must be a readable JSON file") from error
    except json.JSONDecodeError as error:
        raise AnmCompileError(f"{field_name} {ref} must be valid JSON") from error
    payload = _require_mapping(payload, field_name=field_name)
    schema = _require_non_empty_text(
        _require_mapping_value(payload, "schema", field_name=field_name),
        field_name=f"{field_name}.schema",
    )
    if schema != expected_schema:
        raise AnmCompileError(f"{field_name} {ref} must use schema {expected_schema}")
    return payload


def _require_mapping_value(mapping: dict[str, Any], key: str, *, field_name: str) -> Any:
    try:
        return mapping[key]
    except KeyError as error:
        raise AnmCompileError(f"{field_name} missing required field {key}") from error


def _json_scalar_from_text(value_text: str) -> str | int | bool | None:
    normalized = value_text.strip()
    if normalized == "true":
        return True
    if normalized == "false":
        return False
    if normalized == "null":
        return None
    if re.fullmatch(r"-?[0-9]+", normalized):
        return int(normalized)
    if (
        len(normalized) >= 2
        and normalized[0] == '"'
        and normalized[-1] == '"'
    ):
        return normalized[1:-1]
    return normalized


def _split_args(args_text: str) -> list[str]:
    if not args_text.strip():
        return []
    return [part.strip() for part in args_text.split(",")]


def _parse_condition(condition_text: str) -> D1Qualifier:
    normalized = condition_text.strip()
    predicate_match = _PREDICATE_CALL_RE.match(normalized)
    if predicate_match is not None:
        name = predicate_match.group("name")
        args = _split_args(predicate_match.group("args"))
        if name in {"present", "explicit", "bind_to"} and len(args) == 1:
            return D1Qualifier(
                qualifier_kind="only_if",
                normalized_predicate_id=name,
                target_path=args[0],
            )
        if name == "cardinality_eq" and len(args) == 2:
            return D1Qualifier(
                qualifier_kind="only_if",
                normalized_predicate_id="cardinality_eq",
                target_path=args[0],
                expected_count=int(args[1]),
            )
        raise AnmCompileError(f"unsupported qualifier predicate call: {condition_text}")

    if "==" in normalized:
        target_path, expected = normalized.split("==", 1)
        return D1Qualifier(
            qualifier_kind="only_if",
            normalized_predicate_id="eq",
            target_path=target_path.strip(),
            expected_scalar=_json_scalar_from_text(expected),
        )

    raise AnmCompileError(f"unsupported qualifier condition: {condition_text}")


def _parse_assertion(assertion_text: str, *, modal: str) -> dict[str, Any]:
    normalized = assertion_text.strip()
    if " AND " in normalized or " OR " in normalized:
        raise AnmCompileError("boolean composition is forbidden in V47-A")
    if normalized.startswith("DEFERRED "):
        raise AnmCompileError("source-level DEFERRED is forbidden in V47-A")

    for prefix, kind, predicate_id in (
        ("REQUIRED ", "required", "present"),
        ("EXPLICIT ", "explicit", "explicit"),
        ("EXACTLY_ONE ", "exactly_one", "cardinality_eq"),
    ):
        if normalized.startswith(prefix):
            target_path = normalized[len(prefix) :].strip()
            payload: dict[str, Any] = {
                "assertion_kind": kind,
                "normalized_predicate_id": predicate_id,
                "target_path": target_path,
            }
            if kind == "exactly_one":
                payload["expected_count"] = 1
            return payload

    predicate_match = _PREDICATE_CALL_RE.match(normalized)
    if predicate_match is not None:
        name = predicate_match.group("name")
        args = _split_args(predicate_match.group("args"))
        if modal == "MUST_NOT":
            raise AnmCompileError("MUST_NOT predicate calls are forbidden in V47-A")
        if name in {"present", "explicit", "bind_to"} and len(args) == 1:
            return {
                "assertion_kind": "predicate_call",
                "normalized_predicate_id": name,
                "target_path": args[0],
            }
        if name == "cardinality_eq" and len(args) == 2:
            return {
                "assertion_kind": "predicate_call",
                "normalized_predicate_id": "cardinality_eq",
                "target_path": args[0],
                "expected_count": int(args[1]),
            }
        raise AnmCompileError(f"unsupported predicate call: {assertion_text}")

    if "==" in normalized:
        target_path, expected = normalized.split("==", 1)
        return {
            "assertion_kind": "comparison",
            "normalized_predicate_id": "eq",
            "target_path": target_path.strip(),
            "expected_scalar": _json_scalar_from_text(expected),
        }

    raise AnmCompileError(f"unsupported assertion form: {assertion_text}")


def _extract_blocks(source_text: str) -> list[_ParsedBlock]:
    lines = _normalize_text(source_text).split("\n")
    blocks: list[_ParsedBlock] = []
    current_block_id: str | None = None
    current_selector: str | None = None
    current_clauses: list[str] = []

    for line in lines:
        header_match = _D1_BLOCK_HEADER_RE.match(line.strip())
        if header_match is not None:
            if current_block_id is not None:
                raise AnmCompileError("nested D@1 blocks are forbidden")
            block_id = header_match.group("block_id")
            if block_id is None:
                raise AnmCompileError("D@1 block id is required")
            current_block_id = block_id
            current_selector = None
            current_clauses = []
            continue

        if current_block_id is None:
            continue

        if line.strip() == ":::":
            if current_selector is None:
                raise AnmCompileError(f"D@1 block {current_block_id} is missing ON selector")
            if not current_clauses:
                raise AnmCompileError(f"D@1 block {current_block_id} contains no clauses")
            blocks.append(
                _ParsedBlock(
                    block_id=current_block_id,
                    selector_source_text=current_selector,
                    clause_lines=list(current_clauses),
                )
            )
            current_block_id = None
            current_selector = None
            current_clauses = []
            continue

        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("NOTE "):
            continue
        if stripped.startswith("ON "):
            if current_selector is not None:
                raise AnmCompileError(f"D@1 block {current_block_id} declares multiple selectors")
            current_selector = stripped[3:].strip()
            continue
        if stripped.startswith("@"):
            current_clauses.append(stripped)
            continue

        raise AnmCompileError(f"unsupported line inside D@1 block {current_block_id}: {stripped}")

    if current_block_id is not None:
        raise AnmCompileError(f"D@1 block {current_block_id} was not closed")
    if not blocks:
        raise AnmCompileError("no D@1 blocks found; prose inference is forbidden")
    return blocks


def _infer_source_posture(*, source_ref: str, source_text: str) -> str:
    _extract_blocks(source_text)
    return "standalone_anm" if source_ref.endswith(".adeu.md") else "companion_anm"


def build_v47c_coexistence_profile(
    *,
    snapshot_id: str,
    source_scope_profile: str,
    released_stack_refs: list[str],
    source_docs: dict[str, str],
    source_row_specs: list[dict[str, Any]],
    migration_discipline: dict[str, Any],
    adoption_boundary_rows: list[dict[str, Any]],
    host_registry: list[dict[str, Any]] | None = None,
) -> AnmMarkdownCoexistenceProfile:
    snapshot_id = _require_non_empty_text(snapshot_id, field_name="snapshot_id")
    source_scope_profile = _require_non_empty_text(
        source_scope_profile,
        field_name="source_scope_profile",
    )
    if not source_docs:
        raise AnmCompileError("source_docs must not be empty")

    try:
        migration = MigrationDiscipline.model_validate(migration_discipline)
    except ValidationError as error:
        raise AnmCompileError(str(error)) from error
    compatible_scopes = set(migration.compatible_local_source_scopes)

    normalized_source_docs: dict[str, str] = {}
    for source_ref, source_text in sorted(source_docs.items()):
        normalized_ref = _require_non_empty_text(source_ref, field_name="source_ref")
        normalized_source_docs[normalized_ref] = _normalize_text(source_text)
        _infer_source_posture(
            source_ref=normalized_ref,
            source_text=normalized_source_docs[normalized_ref],
        )

    row_specs_by_ref: dict[str, dict[str, Any]] = {}
    row_spec_labels_by_ref: dict[str, str] = {}
    local_scope_by_source_ref: dict[str, str] = {}
    for index, payload in enumerate(source_row_specs):
        spec_label = f"source_row_specs[{index}]"
        spec = _require_mapping(payload, field_name=spec_label)
        source_ref = _require_non_empty_text(
            _require_mapping_value(spec, "source_ref", field_name=spec_label),
            field_name="source_ref",
        )
        local_source_scope = _require_non_empty_text(
            _require_mapping_value(spec, "local_source_scope", field_name=spec_label),
            field_name="local_source_scope",
        )
        if source_ref in row_specs_by_ref:
            raise AnmCompileError(f"duplicate source_row_specs entry for {source_ref}")
        row_specs_by_ref[source_ref] = spec
        row_spec_labels_by_ref[source_ref] = spec_label
        local_scope_by_source_ref[source_ref] = local_source_scope

    if sorted(row_specs_by_ref) != sorted(normalized_source_docs):
        raise AnmCompileError("source_row_specs must exactly cover source_docs")

    host_registry_index: dict[str, dict[str, Any]] = {}
    for index, payload in enumerate(host_registry or []):
        entry_label = f"host_registry[{index}]"
        entry = _require_mapping(payload, field_name=entry_label)
        host_ref = _require_non_empty_text(
            _require_mapping_value(entry, "host_ref", field_name=entry_label),
            field_name="host_ref",
        )
        if host_ref in host_registry_index:
            raise AnmCompileError(f"duplicate host_registry entry for {host_ref}")
        host_registry_index[host_ref] = entry

    built_rows: list[AnmCoexistenceSourceRow] = []
    for source_ref in sorted(row_specs_by_ref):
        spec = row_specs_by_ref[source_ref]
        spec_label = row_spec_labels_by_ref[source_ref]
        local_source_scope = local_scope_by_source_ref[source_ref]
        if local_source_scope not in compatible_scopes:
            raise AnmCompileError(
                f"source {source_ref} local_source_scope {local_source_scope} is not compatible"
            )
        source_posture = _infer_source_posture(
            source_ref=source_ref,
            source_text=normalized_source_docs[source_ref],
        )
        try:
            row = AnmCoexistenceSourceRow.model_validate(
                {
                    "source_ref": source_ref,
                    "source_posture": source_posture,
                    "current_markdown_authority_relation": _require_mapping_value(
                        spec,
                        "current_markdown_authority_relation",
                        field_name=spec_label,
                    ),
                    "host_or_companion_ref": spec.get("host_or_companion_ref"),
                    "companion_embedding_posture": spec.get(
                        "companion_embedding_posture",
                        "not_applicable",
                    ),
                    "non_override_rule": spec.get(
                        "non_override_rule",
                        "current_markdown_not_overridden",
                    ),
                    "allowed_constrain_actions": spec.get("allowed_constrain_actions", []),
                    "migration_posture": _require_mapping_value(
                        spec,
                        "migration_posture",
                        field_name=spec_label,
                    ),
                    "requires_later_lock_for_supersession": _require_mapping_value(
                        spec,
                        "requires_later_lock_for_supersession",
                        field_name=spec_label,
                    ),
                }
            )
        except ValidationError as error:
            raise AnmCompileError(str(error)) from error
        if row.source_posture == "standalone_anm" and not migration.standalone_posture_allowed:
            raise AnmCompileError(
                f"source {source_ref} standalone_anm posture is forbidden by migration_discipline"
            )
        if row.source_posture == "companion_anm" and not migration.companion_posture_allowed:
            raise AnmCompileError(
                f"source {source_ref} companion_anm posture is forbidden by migration_discipline"
            )
        if row.source_posture == "companion_anm":
            host_ref = row.host_or_companion_ref
            assert host_ref is not None
            if host_ref in normalized_source_docs:
                linked_scope = local_scope_by_source_ref.get(host_ref)
                if linked_scope is None:
                    raise AnmCompileError(f"host_or_companion_ref {host_ref} is orphaned")
                if linked_scope not in compatible_scopes:
                    raise AnmCompileError(
                        f"host_or_companion_ref {host_ref} has incompatible source scope"
                    )
            else:
                host_entry = host_registry_index.get(host_ref)
                if host_entry is None:
                    raise AnmCompileError(f"host_or_companion_ref {host_ref} is orphaned")
                if host_entry.get("snapshot_id") != snapshot_id:
                    raise AnmCompileError(
                        f"host_or_companion_ref {host_ref} is stale for snapshot {snapshot_id}"
                    )
                host_scope = _require_non_empty_text(
                    _require_mapping_value(
                        host_entry,
                        "local_source_scope",
                        field_name=f"host_registry[{host_ref}]",
                    ),
                    field_name="host_registry.local_source_scope",
                )
                if host_scope not in compatible_scopes:
                    raise AnmCompileError(
                        f"host_or_companion_ref {host_ref} has incompatible source scope"
                    )
                authority_surface_kind = host_entry.get(
                    "authority_surface_kind",
                    "current_markdown_authority",
                )
                if authority_surface_kind != "current_markdown_authority":
                    raise AnmCompileError(
                        f"host_or_companion_ref {host_ref} implies incompatible authority posture"
                    )
        built_rows.append(row)

    try:
        boundary_rows = [
            AnmAdoptionBoundaryRow.model_validate(payload)
            for payload in adoption_boundary_rows
        ]
    except ValidationError as error:
        raise AnmCompileError(str(error)) from error
    released_stack_refs = sorted(
        {
            _require_non_empty_text(item, field_name="released_stack_refs")
            for item in released_stack_refs
        }
    )
    snapshot_sha256 = stable_payload_hash(
        {
            "snapshot_id": snapshot_id,
            "source_scope_profile": source_scope_profile,
            "source_docs": [
                {
                    "source_ref": source_ref,
                    "sha256": _sha256_text(source_text),
                }
                for source_ref, source_text in sorted(normalized_source_docs.items())
            ],
            "host_registry": [
                {
                    "host_ref": host_ref,
                    "snapshot_id": host_entry["snapshot_id"],
                    "local_source_scope": host_entry["local_source_scope"],
                    "authority_surface_kind": host_entry.get(
                        "authority_surface_kind",
                        "current_markdown_authority",
                    ),
                }
                for host_ref, host_entry in sorted(host_registry_index.items())
            ],
        }
    )
    semantic_hash = stable_payload_hash(
        {
            "snapshot_id": snapshot_id,
            "snapshot_sha256": snapshot_sha256,
            "source_scope_profile": source_scope_profile,
            "released_stack_refs": released_stack_refs,
            "source_rows": [
                row.model_dump(mode="json", exclude_none=True) for row in built_rows
            ],
            "migration_discipline": migration.model_dump(mode="json", exclude_none=True),
            "adoption_boundary_rows": [
                row.model_dump(mode="json", exclude_none=True) for row in boundary_rows
            ],
        }
    )
    return AnmMarkdownCoexistenceProfile(
        coexistence_profile_id=f"anm-coexistence:{semantic_hash[:12]}",
        snapshot_id=snapshot_id,
        snapshot_sha256=snapshot_sha256,
        source_scope_profile=source_scope_profile,
        released_stack_refs=released_stack_refs,
        source_rows=built_rows,
        migration_discipline=migration,
        adoption_boundary_rows=boundary_rows,
        semantic_hash=semantic_hash,
    )


def _indexed_imported_registry(
    *,
    registry_payloads: list[dict[str, Any]] | None,
    ref_field: str,
    identity_field: str,
    version_field: str,
    entry_label: str,
) -> dict[str, dict[str, str]]:
    index: dict[str, dict[str, str]] = {}
    for position, payload in enumerate(registry_payloads or []):
        label = f"{entry_label}[{position}]"
        entry = _require_mapping(payload, field_name=label)
        ref = _require_non_empty_text(
            _require_mapping_value(entry, ref_field, field_name=label),
            field_name=ref_field,
        )
        if ref in index:
            raise AnmCompileError(f"duplicate {entry_label} entry for {ref}")
        index[ref] = {
            ref_field: ref,
            "snapshot_id": _require_non_empty_text(
                _require_mapping_value(entry, "snapshot_id", field_name=label),
                field_name=f"{entry_label}.snapshot_id",
            ),
            "source_scope_profile": _require_non_empty_text(
                _require_mapping_value(entry, "source_scope_profile", field_name=label),
                field_name=f"{entry_label}.source_scope_profile",
            ),
            identity_field: _require_non_empty_text(
                _require_mapping_value(entry, identity_field, field_name=label),
                field_name=identity_field,
            ),
            version_field: _require_non_empty_text(
                _require_mapping_value(entry, version_field, field_name=label),
                field_name=version_field,
            ),
        }
    return index


def _indexed_consumer_registry(
    *,
    registry_payloads: list[dict[str, Any]] | None,
    ref_field: str,
    entry_label: str,
) -> dict[str, dict[str, str]]:
    index: dict[str, dict[str, str]] = {}
    optional_fields = (
        "required_coexistence_source_ref",
        "required_selector_ref",
        "required_predicate_ref",
    )
    for position, payload in enumerate(registry_payloads or []):
        label = f"{entry_label}[{position}]"
        entry = _require_mapping(payload, field_name=label)
        ref = _require_non_empty_text(
            _require_mapping_value(entry, ref_field, field_name=label),
            field_name=ref_field,
        )
        if ref in index:
            raise AnmCompileError(f"duplicate {entry_label} entry for {ref}")
        normalized_entry: dict[str, str] = {
            ref_field: ref,
            "snapshot_id": _require_non_empty_text(
                _require_mapping_value(entry, "snapshot_id", field_name=label),
                field_name=f"{entry_label}.snapshot_id",
            ),
            "source_scope_profile": _require_non_empty_text(
                _require_mapping_value(entry, "source_scope_profile", field_name=label),
                field_name=f"{entry_label}.source_scope_profile",
            ),
        }
        for field_name in optional_fields:
            if field_name not in entry or entry[field_name] is None:
                continue
            normalized_entry[field_name] = _require_non_empty_text(
                entry[field_name],
                field_name=field_name,
            )
        index[ref] = normalized_entry
    return index


def _indexed_benchmark_registry(
    *,
    registry_payloads: list[dict[str, Any]] | None,
    ref_field: str,
    entry_label: str,
) -> dict[str, dict[str, str]]:
    index: dict[str, dict[str, str]] = {}
    optional_fields = (
        "required_coexistence_source_ref",
        "required_selector_ref",
        "required_predicate_ref",
        "required_support_subject_ref",
    )
    for position, payload in enumerate(registry_payloads or []):
        label = f"{entry_label}[{position}]"
        entry = _require_mapping(payload, field_name=label)
        ref = _require_non_empty_text(
            _require_mapping_value(entry, ref_field, field_name=label),
            field_name=ref_field,
        )
        if ref in index:
            raise AnmCompileError(f"duplicate {entry_label} entry for {ref}")
        normalized_entry: dict[str, str] = {
            ref_field: ref,
            "snapshot_id": _require_non_empty_text(
                _require_mapping_value(entry, "snapshot_id", field_name=label),
                field_name=f"{entry_label}.snapshot_id",
            ),
            "source_scope_profile": _require_non_empty_text(
                _require_mapping_value(entry, "source_scope_profile", field_name=label),
                field_name=f"{entry_label}.source_scope_profile",
            ),
        }
        for field_name in optional_fields:
            if field_name not in entry or entry[field_name] is None:
                continue
            normalized_entry[field_name] = _require_non_empty_text(
                entry[field_name],
                field_name=field_name,
            )
        index[ref] = normalized_entry
    return index


def build_v47d_selector_predicate_ownership_profile(
    *,
    snapshot_id: str,
    source_scope_profile: str,
    released_stack_refs: list[str],
    d1_ir: D1NormalizedIR,
    predicate_contracts: PredicateContractsBootstrap,
    coexistence_profile: AnmMarkdownCoexistenceProfile,
    selector_row_specs: list[dict[str, Any]],
    predicate_row_specs: list[dict[str, Any]],
    compatibility_rule_specs: list[dict[str, Any]],
    imported_selector_registry: list[dict[str, Any]] | None = None,
    imported_predicate_registry: list[dict[str, Any]] | None = None,
) -> AnmSelectorPredicateOwnershipProfile:
    snapshot_id = _require_non_empty_text(snapshot_id, field_name="snapshot_id")
    source_scope_profile = _require_non_empty_text(
        source_scope_profile,
        field_name="source_scope_profile",
    )
    if coexistence_profile.snapshot_id != snapshot_id:
        raise AnmCompileError("coexistence_profile snapshot_id must match requested snapshot_id")
    if coexistence_profile.source_scope_profile != source_scope_profile:
        raise AnmCompileError(
            "coexistence_profile source_scope_profile must match requested source_scope_profile"
        )

    compatible_source_refs = {row.source_ref for row in coexistence_profile.source_rows}
    if d1_ir.source_doc_ref not in compatible_source_refs:
        raise AnmCompileError(
            f"d1_ir source_doc_ref {d1_ir.source_doc_ref} is not covered by coexistence_profile"
        )

    released_stack_refs = sorted(
        {
            _require_non_empty_text(item, field_name="released_stack_refs")
            for item in released_stack_refs
        }
    )

    bootstrap_selector_refs = sorted(item.selector_ref for item in d1_ir.selector_refs)
    bootstrap_selector_ref_set = set(bootstrap_selector_refs)
    bootstrap_predicate_contracts = {
        contract.predicate_id: contract for contract in predicate_contracts.contracts
    }
    imported_selector_index = _indexed_imported_registry(
        registry_payloads=imported_selector_registry,
        ref_field="imported_selector_handle_ref",
        identity_field="imported_selector_identity",
        version_field="imported_selector_version",
        entry_label="imported_selector_registry",
    )
    imported_predicate_index = _indexed_imported_registry(
        registry_payloads=imported_predicate_registry,
        ref_field="imported_predicate_registry_ref",
        identity_field="imported_predicate_identity",
        version_field="imported_predicate_version",
        entry_label="imported_predicate_registry",
    )

    try:
        selector_rows = [
            SelectorOwnershipRow.model_validate(payload)
            for payload in selector_row_specs
        ]
    except ValidationError as error:
        raise AnmCompileError(str(error)) from error
    selector_rows = sorted(selector_rows, key=lambda item: item.selector_ref)
    selector_bootstrap_refs: set[str] = set()
    for row in selector_rows:
        if row.selector_ref_kind == "bootstrap_string_selector":
            bootstrap_ref = row.bootstrap_selector_source_ref
            assert bootstrap_ref is not None
            if row.selector_ref != bootstrap_ref:
                raise AnmCompileError(
                    "bootstrap selector rows must use selector_ref identical to "
                    "bootstrap_selector_source_ref"
                )
            if bootstrap_ref not in bootstrap_selector_ref_set:
                raise AnmCompileError(
                    f"bootstrap selector row {bootstrap_ref} does not resolve against d1_ir"
                )
            selector_bootstrap_refs.add(bootstrap_ref)
            continue
        imported_ref = row.imported_selector_handle_ref
        assert imported_ref is not None
        if row.selector_ref != imported_ref:
            raise AnmCompileError(
                "owned selector rows must use selector_ref identical to "
                "imported_selector_handle_ref"
            )
        imported_entry = imported_selector_index.get(imported_ref)
        if imported_entry is None:
            raise AnmCompileError(f"imported selector handle {imported_ref} is dangling")
        if imported_entry["snapshot_id"] != snapshot_id:
            raise AnmCompileError(f"imported selector handle {imported_ref} is stale")
        if imported_entry["source_scope_profile"] != source_scope_profile:
            raise AnmCompileError(
                f"imported selector handle {imported_ref} has incompatible source scope"
            )
        if imported_entry["imported_selector_identity"] != row.imported_selector_identity:
            raise AnmCompileError(
                f"imported selector handle {imported_ref} has incompatible declared identity"
            )
        if imported_entry["imported_selector_version"] != row.imported_selector_version:
            raise AnmCompileError(
                f"imported selector handle {imported_ref} has incompatible declared version"
            )
    if selector_bootstrap_refs != bootstrap_selector_ref_set:
        missing = sorted(bootstrap_selector_ref_set - selector_bootstrap_refs)
        raise AnmCompileError(
            "bootstrap selector replay rows must exactly cover d1_ir selectors; missing "
            + ", ".join(missing)
        )

    try:
        predicate_rows = [
            PredicateOwnershipRow.model_validate(payload)
            for payload in predicate_row_specs
        ]
    except ValidationError as error:
        raise AnmCompileError(str(error)) from error
    predicate_rows = sorted(predicate_rows, key=lambda item: item.predicate_ref)
    predicate_bootstrap_refs: set[str] = set()
    for row in predicate_rows:
        if row.predicate_ref_kind == "bootstrap_predicate_contract":
            bootstrap_ref = row.bootstrap_predicate_contract_ref
            assert bootstrap_ref is not None
            if row.predicate_ref != bootstrap_ref:
                raise AnmCompileError(
                    "bootstrap predicate rows must use predicate_ref identical to "
                    "bootstrap_predicate_contract_ref"
                )
            if bootstrap_ref not in bootstrap_predicate_contracts:
                raise AnmCompileError(
                    f"bootstrap predicate row {bootstrap_ref} does not resolve against "
                    "predicate_contracts"
                )
            predicate_bootstrap_refs.add(bootstrap_ref)
            continue
        imported_ref = row.imported_predicate_registry_ref
        assert imported_ref is not None
        if row.predicate_ref != imported_ref:
            raise AnmCompileError(
                "owned predicate rows must use predicate_ref identical to "
                "imported_predicate_registry_ref"
            )
        imported_entry = imported_predicate_index.get(imported_ref)
        if imported_entry is None:
            raise AnmCompileError(f"imported predicate registry ref {imported_ref} is dangling")
        if imported_entry["snapshot_id"] != snapshot_id:
            raise AnmCompileError(f"imported predicate registry ref {imported_ref} is stale")
        if imported_entry["source_scope_profile"] != source_scope_profile:
            raise AnmCompileError(
                f"imported predicate registry ref {imported_ref} has incompatible source scope"
            )
        if imported_entry["imported_predicate_identity"] != row.imported_predicate_identity:
            raise AnmCompileError(
                f"imported predicate registry ref {imported_ref} has incompatible declared "
                "identity"
            )
        if imported_entry["imported_predicate_version"] != row.imported_predicate_version:
            raise AnmCompileError(
                f"imported predicate registry ref {imported_ref} has incompatible declared "
                "version"
            )
    if predicate_bootstrap_refs != set(bootstrap_predicate_contracts):
        missing = sorted(set(bootstrap_predicate_contracts) - predicate_bootstrap_refs)
        raise AnmCompileError(
            "bootstrap predicate replay rows must exactly cover predicate_contracts; missing "
            + ", ".join(missing)
        )

    try:
        compatibility_rules = [
            OwnershipCompatibilityRule.model_validate(payload)
            for payload in compatibility_rule_specs
        ]
    except ValidationError as error:
        raise AnmCompileError(str(error)) from error
    compatibility_rules = sorted(
        compatibility_rules,
        key=lambda item: (item.selector_ref_kind, item.predicate_ref_kind),
    )
    present_selector_kinds = {row.selector_ref_kind for row in selector_rows}
    present_predicate_kinds = {row.predicate_ref_kind for row in predicate_rows}
    compatibility_index = {
        (row.selector_ref_kind, row.predicate_ref_kind): row
        for row in compatibility_rules
    }
    for selector_kind in present_selector_kinds:
        for predicate_kind in present_predicate_kinds:
            rule = compatibility_index.get((selector_kind, predicate_kind))
            if rule is None:
                raise AnmCompileError(
                    "compatibility_rules must explicitly cover present ownership combination "
                    f"{selector_kind} + {predicate_kind}"
                )
            if not rule.combination_allowed:
                raise AnmCompileError(
                    "contradictory mixed ownership posture forbids present combination "
                    f"{selector_kind} + {predicate_kind}"
                )

    snapshot_sha256 = stable_payload_hash(
        {
            "snapshot_id": snapshot_id,
            "source_scope_profile": source_scope_profile,
            "d1_ir_ref": d1_ir.d1_ir_id,
            "d1_ir_sha256": d1_ir.source_doc_sha256,
            "predicate_contract_bundle_id": predicate_contracts.predicate_contract_bundle_id,
            "predicate_contract_versions": [
                {
                    "predicate_id": contract.predicate_id,
                    "owner_layer": contract.owner_layer,
                    "version": contract.version,
                }
                for contract in predicate_contracts.contracts
            ],
            "coexistence_profile_id": coexistence_profile.coexistence_profile_id,
            "coexistence_snapshot_sha256": coexistence_profile.snapshot_sha256,
            "imported_selector_registry": [
                imported_selector_index[ref]
                for ref in sorted(imported_selector_index)
            ],
            "imported_predicate_registry": [
                imported_predicate_index[ref]
                for ref in sorted(imported_predicate_index)
            ],
        }
    )
    semantic_hash = stable_payload_hash(
        {
            "snapshot_id": snapshot_id,
            "snapshot_sha256": snapshot_sha256,
            "source_scope_profile": source_scope_profile,
            "released_stack_refs": released_stack_refs,
            "selector_rows": [
                row.model_dump(mode="json", exclude_none=True) for row in selector_rows
            ],
            "predicate_rows": [
                row.model_dump(mode="json", exclude_none=True) for row in predicate_rows
            ],
            "compatibility_rules": [
                row.model_dump(mode="json", exclude_none=True) for row in compatibility_rules
            ],
        }
    )
    return AnmSelectorPredicateOwnershipProfile(
        ownership_profile_id=f"anm-ownership:{semantic_hash[:12]}",
        snapshot_id=snapshot_id,
        snapshot_sha256=snapshot_sha256,
        source_scope_profile=source_scope_profile,
        released_stack_refs=released_stack_refs,
        selector_rows=selector_rows,
        predicate_rows=predicate_rows,
        compatibility_rules=compatibility_rules,
        semantic_hash=semantic_hash,
    )


def build_v47e_policy_consumer_binding_profile(
    *,
    snapshot_id: str,
    source_scope_profile: str,
    released_stack_refs: list[str],
    d1_ir: D1NormalizedIR,
    result_set: PolicyEvaluationResultSet,
    ledger: PolicyObligationLedger,
    coexistence_profile: AnmMarkdownCoexistenceProfile,
    ownership_profile: AnmSelectorPredicateOwnershipProfile,
    consumer_row_specs: list[dict[str, Any]],
    descriptive_artifact_registry: list[dict[str, Any]] | None = None,
    runtime_event_registry: list[dict[str, Any]] | None = None,
) -> AnmPolicyConsumerBindingProfile:
    snapshot_id = _require_non_empty_text(snapshot_id, field_name="snapshot_id")
    source_scope_profile = _require_non_empty_text(
        source_scope_profile,
        field_name="source_scope_profile",
    )
    if coexistence_profile.snapshot_id != snapshot_id:
        raise AnmCompileError("coexistence_profile snapshot_id must match requested snapshot_id")
    if coexistence_profile.source_scope_profile != source_scope_profile:
        raise AnmCompileError(
            "coexistence_profile source_scope_profile must match requested source_scope_profile"
        )
    if ownership_profile.snapshot_id != snapshot_id:
        raise AnmCompileError("ownership_profile snapshot_id must match requested snapshot_id")
    if ownership_profile.source_scope_profile != source_scope_profile:
        raise AnmCompileError(
            "ownership_profile source_scope_profile must match requested source_scope_profile"
        )
    if result_set.scope_snapshot != snapshot_id:
        raise AnmCompileError("result_set scope_snapshot must match requested snapshot_id")
    if ledger.scope_snapshot != snapshot_id:
        raise AnmCompileError("ledger scope_snapshot must match requested snapshot_id")
    if result_set.d_ir_ref != d1_ir.d1_ir_id:
        raise AnmCompileError("result_set d_ir_ref must match provided d1_ir")
    if result_set.result_set_id not in set(ledger.result_set_refs):
        raise AnmCompileError("ledger must reference provided result_set")

    compatible_source_refs = {row.source_ref for row in coexistence_profile.source_rows}
    if d1_ir.source_doc_ref not in compatible_source_refs:
        raise AnmCompileError(
            f"d1_ir source_doc_ref {d1_ir.source_doc_ref} is not covered by coexistence_profile"
        )

    released_stack_refs = sorted(
        {
            _require_non_empty_text(item, field_name="released_stack_refs")
            for item in released_stack_refs
        }
    )

    clause_index = {clause.clause_ref: clause for clause in d1_ir.clauses}
    result_index = {row.result_id: row for row in result_set.results}
    ledger_index = {row.obligation_id: row for row in ledger.rows}
    ownership_selector_refs = {row.selector_ref for row in ownership_profile.selector_rows}
    ownership_predicate_refs = {row.predicate_ref for row in ownership_profile.predicate_rows}

    descriptive_index = _indexed_consumer_registry(
        registry_payloads=descriptive_artifact_registry,
        ref_field="consumer_ref",
        entry_label="descriptive_artifact_registry",
    )
    runtime_index = _indexed_consumer_registry(
        registry_payloads=runtime_event_registry,
        ref_field="consumer_ref",
        entry_label="runtime_event_registry",
    )

    try:
        consumer_rows = [
            AnmPolicyConsumerRow.model_validate(payload)
            for payload in consumer_row_specs
        ]
    except ValidationError as error:
        raise AnmCompileError(str(error)) from error
    consumer_rows = sorted(consumer_rows, key=lambda item: item.consumer_ref)

    for row in consumer_rows:
        clause = clause_index.get(row.policy_source_ref)
        if clause is None:
            raise AnmCompileError(
                f"consumer row {row.consumer_ref} policy_source_ref {row.policy_source_ref} "
                "does not resolve against d1_ir"
            )
        expected_clause_hash = _clause_semantic_hash(clause)
        if row.consumer_world_kind == "released_v45_descriptive_artifact_world":
            registry_entry = descriptive_index.get(row.consumer_ref)
            if registry_entry is None:
                raise AnmCompileError(
                    f"released descriptive artifact ref {row.consumer_ref} is unresolved"
                )
        else:
            registry_entry = runtime_index.get(row.consumer_ref)
            if registry_entry is None:
                raise AnmCompileError(
                    f"runtime event stream ref {row.consumer_ref} is unresolved"
                )
        if registry_entry["snapshot_id"] != snapshot_id:
            raise AnmCompileError(f"consumer ref {row.consumer_ref} is stale")
        if registry_entry["source_scope_profile"] != source_scope_profile:
            raise AnmCompileError(
                f"consumer ref {row.consumer_ref} has incompatible source scope"
            )
        required_coexistence_source_ref = registry_entry.get("required_coexistence_source_ref")
        if (
            required_coexistence_source_ref is not None
            and required_coexistence_source_ref not in compatible_source_refs
        ):
            raise AnmCompileError(
                f"consumer ref {row.consumer_ref} bypasses released V47-C profile doctrine"
            )
        required_selector_ref = registry_entry.get("required_selector_ref")
        if (
            required_selector_ref is not None
            and required_selector_ref not in ownership_selector_refs
        ):
            raise AnmCompileError(
                f"consumer ref {row.consumer_ref} bypasses released V47-D selector doctrine"
            )
        required_predicate_ref = registry_entry.get("required_predicate_ref")
        if (
            required_predicate_ref is not None
            and required_predicate_ref not in ownership_predicate_refs
        ):
            raise AnmCompileError(
                f"consumer ref {row.consumer_ref} bypasses released V47-D predicate doctrine"
            )

        support_verdicts: set[str] = set()
        for result_ref in row.supporting_result_refs:
            result_row = result_index.get(result_ref)
            if result_row is None:
                raise AnmCompileError(
                    f"supporting result ref {result_ref} is unresolved for {row.consumer_ref}"
                )
            if result_row.clause_ref != row.policy_source_ref:
                raise AnmCompileError(
                    f"supporting result ref {result_ref} contradicts bound policy source"
                )
            if result_row.clause_semantic_hash != expected_clause_hash:
                raise AnmCompileError(
                    f"supporting result ref {result_ref} is stale against bound policy source"
                )
            support_verdicts.add(result_row.effective_verdict)
        for ledger_ref in row.supporting_ledger_refs:
            ledger_row = ledger_index.get(ledger_ref)
            if ledger_row is None:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} is unresolved for {row.consumer_ref}"
                )
            if ledger_row.latest_result_run != result_set.result_set_id:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} does not belong to result_set "
                    f"{result_set.result_set_id}"
                )
            if ledger_row.clause_ref != row.policy_source_ref:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} contradicts bound policy source"
                )
            if ledger_row.clause_semantic_hash != expected_clause_hash:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} is stale against bound policy source"
                )
            support_verdicts.add(ledger_row.latest_effective_verdict)
        if len(support_verdicts) > 1:
            raise AnmCompileError(
                "consumer row "
                f"{row.consumer_ref} has contradictory supporting result/ledger posture"
            )

    snapshot_sha256 = stable_payload_hash(
        {
            "snapshot_id": snapshot_id,
            "source_scope_profile": source_scope_profile,
            "d1_ir_ref": d1_ir.d1_ir_id,
            "d1_ir_sha256": d1_ir.source_doc_sha256,
            "result_set_ref": result_set.result_set_id,
            "ledger_ref": ledger.ledger_id,
            "coexistence_profile_id": coexistence_profile.coexistence_profile_id,
            "coexistence_snapshot_sha256": coexistence_profile.snapshot_sha256,
            "ownership_profile_id": ownership_profile.ownership_profile_id,
            "ownership_snapshot_sha256": ownership_profile.snapshot_sha256,
            "descriptive_artifact_registry": [
                descriptive_index[ref] for ref in sorted(descriptive_index)
            ],
            "runtime_event_registry": [
                runtime_index[ref] for ref in sorted(runtime_index)
            ],
        }
    )
    semantic_hash = stable_payload_hash(
        {
            "snapshot_id": snapshot_id,
            "snapshot_sha256": snapshot_sha256,
            "source_scope_profile": source_scope_profile,
            "released_stack_refs": released_stack_refs,
            "consumer_rows": [
                row.model_dump(mode="json", exclude_none=True) for row in consumer_rows
            ],
        }
    )
    return AnmPolicyConsumerBindingProfile(
        consumer_binding_profile_id=f"anm-consumer-binding:{semantic_hash[:12]}",
        snapshot_id=snapshot_id,
        snapshot_sha256=snapshot_sha256,
        source_scope_profile=source_scope_profile,
        released_stack_refs=released_stack_refs,
        consumer_rows=consumer_rows,
        semantic_hash=semantic_hash,
    )


def build_v47f_benchmark_policy_consumer_binding_profile(
    *,
    snapshot_id: str,
    source_scope_profile: str,
    released_stack_refs: list[str],
    d1_ir: D1NormalizedIR,
    result_set: PolicyEvaluationResultSet,
    ledger: PolicyObligationLedger,
    coexistence_profile: AnmMarkdownCoexistenceProfile,
    ownership_profile: AnmSelectorPredicateOwnershipProfile,
    policy_consumer_profile: AnmPolicyConsumerBindingProfile,
    benchmark_consumer_row_specs: list[dict[str, Any]],
    local_eval_registry: list[dict[str, Any]] | None = None,
    scorecard_registry: list[dict[str, Any]] | None = None,
    behavior_evidence_registry: list[dict[str, Any]] | None = None,
) -> AnmBenchmarkPolicyConsumerBindingProfile:
    snapshot_id = _require_non_empty_text(snapshot_id, field_name="snapshot_id")
    source_scope_profile = _require_non_empty_text(
        source_scope_profile,
        field_name="source_scope_profile",
    )
    if coexistence_profile.snapshot_id != snapshot_id:
        raise AnmCompileError("coexistence_profile snapshot_id must match requested snapshot_id")
    if coexistence_profile.source_scope_profile != source_scope_profile:
        raise AnmCompileError(
            "coexistence_profile source_scope_profile must match requested source_scope_profile"
        )
    if ownership_profile.snapshot_id != snapshot_id:
        raise AnmCompileError("ownership_profile snapshot_id must match requested snapshot_id")
    if ownership_profile.source_scope_profile != source_scope_profile:
        raise AnmCompileError(
            "ownership_profile source_scope_profile must match requested source_scope_profile"
        )
    if policy_consumer_profile.snapshot_id != snapshot_id:
        raise AnmCompileError(
            "policy_consumer_profile snapshot_id must match requested snapshot_id"
        )
    if policy_consumer_profile.source_scope_profile != source_scope_profile:
        raise AnmCompileError(
            "policy_consumer_profile source_scope_profile must match requested "
            "source_scope_profile"
        )
    if result_set.scope_snapshot != snapshot_id:
        raise AnmCompileError("result_set scope_snapshot must match requested snapshot_id")
    if ledger.scope_snapshot != snapshot_id:
        raise AnmCompileError("ledger scope_snapshot must match requested snapshot_id")
    if result_set.d_ir_ref != d1_ir.d1_ir_id:
        raise AnmCompileError("result_set d_ir_ref must match provided d1_ir")
    if result_set.result_set_id not in set(ledger.result_set_refs):
        raise AnmCompileError("ledger must reference provided result_set")

    compatible_source_refs = {row.source_ref for row in coexistence_profile.source_rows}
    if d1_ir.source_doc_ref not in compatible_source_refs:
        raise AnmCompileError(
            f"d1_ir source_doc_ref {d1_ir.source_doc_ref} is not covered by coexistence_profile"
        )

    released_stack_refs = sorted(
        {
            _require_non_empty_text(item, field_name="released_stack_refs")
            for item in released_stack_refs
        }
    )

    clause_index = {clause.clause_ref: clause for clause in d1_ir.clauses}
    result_index = {row.result_id: row for row in result_set.results}
    ledger_index = {row.obligation_id: row for row in ledger.rows}
    ownership_selector_refs = {row.selector_ref for row in ownership_profile.selector_rows}
    ownership_predicate_refs = {row.predicate_ref for row in ownership_profile.predicate_rows}
    policy_consumer_clause_refs = {
        row.policy_source_ref for row in policy_consumer_profile.consumer_rows
    }

    local_eval_index = _indexed_benchmark_registry(
        registry_payloads=local_eval_registry,
        ref_field="benchmark_consumer_ref",
        entry_label="local_eval_registry",
    )
    scorecard_index = _indexed_benchmark_registry(
        registry_payloads=scorecard_registry,
        ref_field="benchmark_consumer_ref",
        entry_label="scorecard_registry",
    )
    behavior_index = _indexed_benchmark_registry(
        registry_payloads=behavior_evidence_registry,
        ref_field="benchmark_consumer_ref",
        entry_label="behavior_evidence_registry",
    )

    try:
        benchmark_consumer_rows = [
            AnmBenchmarkPolicyConsumerRow.model_validate(payload)
            for payload in benchmark_consumer_row_specs
        ]
    except ValidationError as error:
        raise AnmCompileError(str(error)) from error
    benchmark_consumer_rows = sorted(
        benchmark_consumer_rows,
        key=lambda item: item.benchmark_consumer_ref,
    )

    for row in benchmark_consumer_rows:
        clause = clause_index.get(row.policy_source_ref)
        if clause is None:
            raise AnmCompileError(
                "benchmark consumer row "
                f"{row.benchmark_consumer_ref} policy_source_ref {row.policy_source_ref} "
                "does not resolve against d1_ir"
            )
        if row.policy_source_ref not in policy_consumer_clause_refs:
            raise AnmCompileError(
                f"benchmark consumer ref {row.benchmark_consumer_ref} bypasses released "
                "V47-E policy consumer doctrine"
            )
        expected_clause_hash = _clause_semantic_hash(clause)

        if row.benchmark_consumer_world_kind == "released_v42_local_eval_artifact_world":
            registry_entry = local_eval_index.get(row.benchmark_consumer_ref)
            if registry_entry is None:
                raise AnmCompileError(
                    f"released local eval ref {row.benchmark_consumer_ref} is unresolved"
                )
            artifact_payload = _load_json_artifact_ref(
                row.benchmark_consumer_ref,
                field_name="benchmark_consumer_ref",
                expected_schema="adeu_arc_local_eval_record@1",
            )
            deferred_assertions = _require_mapping_value(
                artifact_payload,
                "deferred_authority_assertions",
                field_name="benchmark_consumer_ref",
            )
            if (
                not isinstance(deferred_assertions, list)
                or "scorecard_authority_deferred" not in deferred_assertions
            ):
                raise AnmCompileError(
                    "local eval benchmark consumers must preserve released V42-D "
                    "scorecard-authority-deferred posture"
                )
        elif row.benchmark_consumer_world_kind == "released_v42_scorecard_artifact_world":
            registry_entry = scorecard_index.get(row.benchmark_consumer_ref)
            if registry_entry is None:
                raise AnmCompileError(
                    f"released scorecard manifest ref {row.benchmark_consumer_ref} is unresolved"
                )
            artifact_payload = _load_json_artifact_ref(
                row.benchmark_consumer_ref,
                field_name="benchmark_consumer_ref",
                expected_schema="adeu_arc_scorecard_manifest@1",
            )
            scorecard_source_kind = _require_non_empty_text(
                _require_mapping_value(
                    artifact_payload,
                    "scorecard_source_kind",
                    field_name="benchmark_consumer_ref",
                ),
                field_name="scorecard_source_kind",
            )
            authority_source_kind = _require_non_empty_text(
                _require_mapping_value(
                    artifact_payload,
                    "authority_source_kind",
                    field_name="benchmark_consumer_ref",
                ),
                field_name="authority_source_kind",
            )
            _require_non_empty_text(
                _require_mapping_value(
                    artifact_payload,
                    "authority_scope",
                    field_name="benchmark_consumer_ref",
                ),
                field_name="authority_scope",
            )
            _require_non_empty_text(
                _require_mapping_value(
                    artifact_payload,
                    "authority_limitations",
                    field_name="benchmark_consumer_ref",
                ),
                field_name="authority_limitations",
            )
            if scorecard_source_kind != authority_source_kind:
                raise AnmCompileError(
                    "scorecard benchmark consumers must preserve released V42-E "
                    "scorecard_source_kind / authority_source_kind posture"
                )
        else:
            registry_entry = behavior_index.get(row.benchmark_consumer_ref)
            if registry_entry is None:
                raise AnmCompileError(
                    "released behavior evidence bundle ref "
                    f"{row.benchmark_consumer_ref} is unresolved"
                )
            artifact_payload = _load_json_artifact_ref(
                row.benchmark_consumer_ref,
                field_name="benchmark_consumer_ref",
                expected_schema="adeu_arc_behavior_evidence_bundle@1",
            )
            authority_boundary_register = _require_mapping(
                _require_mapping_value(
                    artifact_payload,
                    "authority_boundary_register",
                    field_name="benchmark_consumer_ref",
                ),
                field_name="authority_boundary_register",
            )
            boundary_violation_flags = _require_mapping_value(
                authority_boundary_register,
                "boundary_violation_flags",
                field_name="authority_boundary_register",
            )
            if not isinstance(boundary_violation_flags, list) or boundary_violation_flags:
                raise AnmCompileError(
                    "behavior evidence benchmark consumers must preserve released V42-G4 "
                    "authority boundary posture"
                )
            descriptive_only_refs = _require_mapping_value(
                authority_boundary_register,
                "descriptive_only_surface_refs",
                field_name="authority_boundary_register",
            )
            if (
                not isinstance(descriptive_only_refs, list)
                or "descriptive_surface:behavior_summary" not in descriptive_only_refs
            ):
                raise AnmCompileError(
                    "behavior evidence benchmark consumers must preserve released V42-G4 "
                    "descriptive-only behavior summary posture"
                )

        if registry_entry["snapshot_id"] != snapshot_id:
            raise AnmCompileError(f"benchmark consumer ref {row.benchmark_consumer_ref} is stale")
        if registry_entry["source_scope_profile"] != source_scope_profile:
            raise AnmCompileError(
                "benchmark consumer ref "
                f"{row.benchmark_consumer_ref} has incompatible source scope"
            )
        required_coexistence_source_ref = registry_entry.get("required_coexistence_source_ref")
        if (
            required_coexistence_source_ref is not None
            and required_coexistence_source_ref not in compatible_source_refs
        ):
            raise AnmCompileError(
                f"benchmark consumer ref {row.benchmark_consumer_ref} bypasses released "
                "V47-C profile doctrine"
            )
        required_selector_ref = registry_entry.get("required_selector_ref")
        if (
            required_selector_ref is not None
            and required_selector_ref not in ownership_selector_refs
        ):
            raise AnmCompileError(
                f"benchmark consumer ref {row.benchmark_consumer_ref} bypasses released "
                "V47-D selector doctrine"
            )
        required_predicate_ref = registry_entry.get("required_predicate_ref")
        if (
            required_predicate_ref is not None
            and required_predicate_ref not in ownership_predicate_refs
        ):
            raise AnmCompileError(
                f"benchmark consumer ref {row.benchmark_consumer_ref} bypasses released "
                "V47-D predicate doctrine"
            )

        expected_subject_ref = registry_entry.get("required_support_subject_ref")
        support_verdicts: set[str] = set()
        for result_ref in row.supporting_result_refs:
            result_row = result_index.get(result_ref)
            if result_row is None:
                raise AnmCompileError(
                    f"supporting result ref {result_ref} is unresolved for "
                    f"{row.benchmark_consumer_ref}"
                )
            if result_row.clause_ref != row.policy_source_ref:
                raise AnmCompileError(
                    f"supporting result ref {result_ref} contradicts bound policy source"
                )
            if result_row.clause_semantic_hash != expected_clause_hash:
                raise AnmCompileError(
                    f"supporting result ref {result_ref} is stale against bound policy source"
                )
            if expected_subject_ref is not None:
                if result_row.result_scope_kind != "subject_scoped":
                    raise AnmCompileError(
                        f"supporting result ref {result_ref} does not cohere to benchmark "
                        f"target {expected_subject_ref}"
                    )
                if result_row.subject_ref != expected_subject_ref:
                    raise AnmCompileError(
                        f"supporting result ref {result_ref} does not cohere to benchmark "
                        f"target {expected_subject_ref}"
                    )
            support_verdicts.add(result_row.effective_verdict)
        for ledger_ref in row.supporting_ledger_refs:
            ledger_row = ledger_index.get(ledger_ref)
            if ledger_row is None:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} is unresolved for "
                    f"{row.benchmark_consumer_ref}"
                )
            if ledger_row.latest_result_run != result_set.result_set_id:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} does not belong to result_set "
                    f"{result_set.result_set_id}"
                )
            if ledger_row.clause_ref != row.policy_source_ref:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} contradicts bound policy source"
                )
            if ledger_row.clause_semantic_hash != expected_clause_hash:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} is stale against bound policy source"
                )
            if expected_subject_ref is not None and ledger_row.subject_ref != expected_subject_ref:
                raise AnmCompileError(
                    f"supporting ledger ref {ledger_ref} does not cohere to benchmark target "
                    f"{expected_subject_ref}"
                )
            support_verdicts.add(ledger_row.latest_effective_verdict)
        if len(support_verdicts) > 1:
            raise AnmCompileError(
                "benchmark consumer row "
                f"{row.benchmark_consumer_ref} has contradictory supporting result/ledger "
                "posture"
            )

    snapshot_sha256 = stable_payload_hash(
        {
            "snapshot_id": snapshot_id,
            "source_scope_profile": source_scope_profile,
            "d1_ir_ref": d1_ir.d1_ir_id,
            "d1_ir_sha256": d1_ir.source_doc_sha256,
            "result_set_ref": result_set.result_set_id,
            "ledger_ref": ledger.ledger_id,
            "coexistence_profile_id": coexistence_profile.coexistence_profile_id,
            "coexistence_snapshot_sha256": coexistence_profile.snapshot_sha256,
            "ownership_profile_id": ownership_profile.ownership_profile_id,
            "ownership_snapshot_sha256": ownership_profile.snapshot_sha256,
            "policy_consumer_profile_id": policy_consumer_profile.consumer_binding_profile_id,
            "policy_consumer_snapshot_sha256": policy_consumer_profile.snapshot_sha256,
            "local_eval_registry": [local_eval_index[ref] for ref in sorted(local_eval_index)],
            "scorecard_registry": [scorecard_index[ref] for ref in sorted(scorecard_index)],
            "behavior_evidence_registry": [
                behavior_index[ref] for ref in sorted(behavior_index)
            ],
        }
    )
    semantic_hash = stable_payload_hash(
        {
            "snapshot_id": snapshot_id,
            "snapshot_sha256": snapshot_sha256,
            "source_scope_profile": source_scope_profile,
            "released_stack_refs": released_stack_refs,
            "benchmark_consumer_rows": [
                row.model_dump(mode="json", exclude_none=True)
                for row in benchmark_consumer_rows
            ],
        }
    )
    return AnmBenchmarkPolicyConsumerBindingProfile(
        benchmark_consumer_binding_profile_id=f"anm-benchmark-consumer-binding:{semantic_hash[:12]}",
        snapshot_id=snapshot_id,
        snapshot_sha256=snapshot_sha256,
        source_scope_profile=source_scope_profile,
        released_stack_refs=released_stack_refs,
        benchmark_consumer_rows=benchmark_consumer_rows,
        semantic_hash=semantic_hash,
    )


def compile_authoritative_normative_markdown(
    *,
    source_text: str,
    source_doc_ref: str,
) -> D1NormalizedIR:
    normalized_source = _normalize_text(source_text)
    blocks = _extract_blocks(normalized_source)
    block_ids = sorted(block.block_id for block in blocks)
    if len(block_ids) != len(set(block_ids)):
        raise AnmCompileError("duplicate D@1 block ids are forbidden")

    selector_refs: list[D1SelectorRef] = []
    clauses: list[D1Clause] = []

    for block in blocks:
        selector_ref = f"{block.block_id}:selector"
        selector_refs.append(
            D1SelectorRef(
                selector_ref=selector_ref,
                selector_source_text=block.selector_source_text,
                selector_kind="bootstrap_string_selector",
            )
        )

        for clause_line in block.clause_lines:
            clause_match = _CLAUSE_RE.match(clause_line)
            if clause_match is None:
                raise AnmCompileError(f"invalid clause line: {clause_line}")
            label = clause_match.group("label")
            modal = clause_match.group("modal")
            rest = clause_match.group("rest").strip()

            qualifier_matches = list(_QUALIFIER_SEGMENT_RE.finditer(rest))
            assertion_text = rest
            qualifiers: list[D1Qualifier] = []
            if qualifier_matches:
                assertion_text = rest[: qualifier_matches[0].start()].strip()
                for match in qualifier_matches:
                    parsed = _parse_condition(match.group(2))
                    qualifier_kind = "only_if" if match.group(1) == "ONLY_IF" else "unless"
                    qualifier = D1Qualifier(
                        qualifier_kind=qualifier_kind,
                        normalized_predicate_id=parsed.normalized_predicate_id,
                        target_path=parsed.target_path,
                        expected_scalar=parsed.expected_scalar,
                        expected_count=parsed.expected_count,
                    )
                    qualifiers.append(qualifier)

            assertion_payload = _parse_assertion(assertion_text, modal=modal)
            clauses.append(
                D1Clause(
                    clause_ref=f"{block.block_id}:{label}",
                    clause_label=label,
                    modal=modal,
                    subject_selector_ref=selector_ref,
                    qualifiers=sorted(
                        qualifiers,
                        key=lambda item: (
                            item.qualifier_kind,
                            item.normalized_predicate_id,
                            item.target_path or "",
                            item.expected_count if item.expected_count is not None else -1,
                            repr(item.expected_scalar),
                        ),
                    ),
                    origin_block_ref=block.block_id,
                    **assertion_payload,
                )
            )

    selector_refs = sorted(selector_refs, key=lambda item: item.selector_ref)
    clauses = sorted(clauses, key=lambda item: item.clause_ref)
    semantic_hash = stable_payload_hash(
        {
            "source_doc_ref": source_doc_ref,
            "source_block_refs": block_ids,
            "selector_refs": [
                item.model_dump(mode="json", exclude_none=True) for item in selector_refs
            ],
            "clauses": [item.model_dump(mode="json", exclude_none=True) for item in clauses],
            "selector_zero_match_policy": "allow_empty_with_notice",
        }
    )
    d1_ir_id = f"d1-ir:{semantic_hash[:12]}"

    return D1NormalizedIR(
        d1_ir_id=d1_ir_id,
        source_doc_ref=source_doc_ref,
        source_doc_sha256=_sha256_text(normalized_source),
        source_block_refs=block_ids,
        selector_refs=selector_refs,
        selector_zero_match_policy="allow_empty_with_notice",
        clauses=clauses,
        semantic_hash=semantic_hash,
    )


def default_bootstrap_predicate_contracts() -> PredicateContractsBootstrap:
    contracts = [
        PredicateContract(
            predicate_id="bind_to",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[PredicateArgumentSpec(name="path", kind="path")],
            required_evidence_kinds=["binding_observation"],
            truth_conditions=[
                "binding_payload.path matches target path and binding_payload.bound == true"
            ],
            evidence_failure_conditions=["no binding_observation facts present for target path"],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
        PredicateContract(
            predicate_id="cardinality_eq",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[
                PredicateArgumentSpec(name="path", kind="path"),
                PredicateArgumentSpec(name="count", kind="integer"),
            ],
            required_evidence_kinds=["path_cardinality_observation"],
            truth_conditions=["at least one observed cardinality equals expected count"],
            evidence_failure_conditions=[
                "no path_cardinality_observation facts present for target path"
            ],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
        PredicateContract(
            predicate_id="eq",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[
                PredicateArgumentSpec(name="path", kind="path"),
                PredicateArgumentSpec(name="value", kind="scalar"),
            ],
            required_evidence_kinds=["value_observation"],
            truth_conditions=["at least one observed value equals expected scalar"],
            evidence_failure_conditions=["no value_observation facts present for target path"],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
        PredicateContract(
            predicate_id="explicit",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[PredicateArgumentSpec(name="path", kind="path")],
            required_evidence_kinds=["explicit_carriage_observation"],
            truth_conditions=["at least one explicit_carriage_observation is true for target path"],
            evidence_failure_conditions=[
                "no explicit_carriage_observation facts present for target path"
            ],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
        PredicateContract(
            predicate_id="present",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[PredicateArgumentSpec(name="path", kind="path")],
            required_evidence_kinds=["path_presence_observation"],
            truth_conditions=["at least one path_presence_observation is true for target path"],
            evidence_failure_conditions=[
                "no path_presence_observation facts present for target path"
            ],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
    ]
    contracts = sorted(contracts, key=lambda item: item.predicate_id)
    bundle_hash = stable_payload_hash(
        {"contracts": [item.model_dump(mode="json", exclude_none=True) for item in contracts]}
    )
    return PredicateContractsBootstrap(
        predicate_contract_bundle_id=f"predicate-contracts:{bundle_hash[:12]}",
        contracts=contracts,
    )


def _clause_semantic_hash(clause: D1Clause) -> str:
    return stable_payload_hash(clause.model_dump(mode="json", exclude_none=True))


def _facts_for_subject(
    bundle: CheckerFactBundle,
    *,
    subject_ref: str,
    fact_type: str,
    path: str | None = None,
) -> list[Any]:
    selected: list[Any] = []
    for fact in bundle.facts:
        if fact.subject_ref != subject_ref or fact.fact_type != fact_type:
            continue
        if path is not None and hasattr(fact, "path") and getattr(fact, "path") != path:
            continue
        if path is not None and fact.fact_type == "binding_observation":
            binding_path = fact.binding_payload.get("path")
            if binding_path != path:
                continue
        selected.append(fact)
    return selected


def _fact_values_for_subject(
    fact_bundle: CheckerFactBundle,
    *,
    subject_ref: str,
    fact_type: str,
    path: str,
) -> tuple[list[Any] | None, list[str]]:
    facts = _facts_for_subject(
        fact_bundle,
        subject_ref=subject_ref,
        fact_type=fact_type,
        path=path,
    )
    if not facts:
        return None, []
    return [value for fact in facts for value in fact.values], sorted(
        item.fact_id for item in facts
    )


def _scalar_matches_expected(*, observed: Any, expected: Any) -> bool:
    return type(observed) is type(expected) and observed == expected


def _supporting_contract_refs_for_clause(clause: D1Clause) -> list[str]:
    return sorted(
        {clause.normalized_predicate_id}
        | {qualifier.normalized_predicate_id for qualifier in clause.qualifiers}
    )


def _evaluate_predicate(
    *,
    predicate_id: str,
    target_path: str,
    subject_ref: str,
    fact_bundle: CheckerFactBundle,
    expected_scalar: Any = None,
    expected_count: int | None = None,
) -> tuple[str, list[str]]:
    if predicate_id == "present":
        values, fact_ids = _fact_values_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="path_presence_observation",
            path=target_path,
        )
        if values is None:
            return "unknown_evidence", []
        return ("pass" if any(values) else "fail"), fact_ids

    if predicate_id == "explicit":
        values, fact_ids = _fact_values_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="explicit_carriage_observation",
            path=target_path,
        )
        if values is None:
            return "unknown_evidence", []
        return ("pass" if any(values) else "fail"), fact_ids

    if predicate_id == "cardinality_eq":
        values, fact_ids = _fact_values_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="path_cardinality_observation",
            path=target_path,
        )
        if values is None:
            return "unknown_evidence", []
        return ("pass" if expected_count in values else "fail"), fact_ids

    if predicate_id == "bind_to":
        facts = _facts_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="binding_observation",
            path=target_path,
        )
        if not facts:
            return "unknown_evidence", []
        fact_ids = sorted(item.fact_id for item in facts)
        bound_values = [bool(fact.binding_payload.get("bound")) for fact in facts]
        return ("pass" if any(bound_values) else "fail"), fact_ids

    if predicate_id == "eq":
        values, fact_ids = _fact_values_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="value_observation",
            path=target_path,
        )
        if values is None:
            return "unknown_evidence", []
        return (
            "pass"
            if any(
                _scalar_matches_expected(observed=value, expected=expected_scalar)
                for value in values
            )
            else "fail",
            fact_ids,
        )

    raise AnmCompileError(f"unsupported predicate_id: {predicate_id}")


def _selector_subjects(
    selector: D1SelectorRef,
    fact_bundle: CheckerFactBundle,
) -> tuple[list[str], str | None]:
    selector_prefixes = {
        "artifact.emitted[*]": "artifact:",
        "companion.section[*]": "companion:",
    }
    if selector.selector_source_text in selector_prefixes:
        prefix = selector_prefixes[selector.selector_source_text]
        subjects = sorted(
            {
                fact.subject_ref
                for fact in fact_bundle.facts
                if fact.subject_ref.startswith(prefix)
            }
        )
        return subjects, None
    return [], "unsupported bootstrap selector"


def evaluate_authoritative_normative_markdown(
    *,
    d1_ir: D1NormalizedIR,
    fact_bundle: CheckerFactBundle,
    predicate_contracts: PredicateContractsBootstrap,
    result_set_id: str,
) -> PolicyEvaluationResultSet:
    contract_ids = {contract.predicate_id for contract in predicate_contracts.contracts}
    results: list[SubjectScopedResultRow | ClauseScopeBlockerResultRow] = []
    notices: list[EvaluationNotice] = []
    selector_index = {selector.selector_ref: selector for selector in d1_ir.selector_refs}

    for clause in d1_ir.clauses:
        supporting_contract_refs = _supporting_contract_refs_for_clause(clause)
        missing_contract_ids = [
            predicate_id
            for predicate_id in supporting_contract_refs
            if predicate_id not in contract_ids
        ]
        if missing_contract_ids:
            raise AnmCompileError(
                "clause "
                f"{clause.clause_ref} references missing predicate contract(s) "
                + ", ".join(missing_contract_ids)
            )

        selector = selector_index[clause.subject_selector_ref]
        subjects, selector_error = _selector_subjects(selector, fact_bundle)
        if selector_error is not None:
            results.append(
                ClauseScopeBlockerResultRow(
                    result_id=f"result:{clause.clause_ref}",
                    clause_ref=clause.clause_ref,
                    clause_semantic_hash=_clause_semantic_hash(clause),
                    applicability="active",
                    observed_outcome="unknown_resolution",
                    effective_verdict="unknown_resolution",
                    supporting_fact_refs=[],
                    supporting_contract_refs=supporting_contract_refs,
                    message=selector_error,
                )
            )
            continue

        if not subjects:
            notices.append(
                EvaluationNotice(
                    notice_id=f"notice:{clause.clause_ref}",
                    notice_kind="selector_zero_match",
                    clause_ref=clause.clause_ref,
                    selector_ref=selector.selector_ref,
                    message="selector resolved zero subjects under allow_empty_with_notice",
                )
            )
            continue

        for subject_ref in subjects:
            applicability: str = "active"
            observed_outcome: str = "not_evaluated"
            effective_verdict: str = "gated_off"
            supporting_fact_refs: set[str] = set()

            for qualifier in clause.qualifiers:
                qualifier_outcome, qualifier_fact_ids = _evaluate_predicate(
                    predicate_id=qualifier.normalized_predicate_id,
                    target_path=qualifier.target_path or "",
                    subject_ref=subject_ref,
                    fact_bundle=fact_bundle,
                    expected_scalar=qualifier.expected_scalar,
                    expected_count=qualifier.expected_count,
                )
                supporting_fact_refs.update(qualifier_fact_ids)
                if qualifier.qualifier_kind == "only_if":
                    if qualifier_outcome == "fail":
                        applicability = "gated_off"
                        observed_outcome = "not_evaluated"
                        effective_verdict = "gated_off"
                        break
                    if qualifier_outcome == "unknown_evidence":
                        applicability = "active"
                        observed_outcome = "unknown_evidence"
                        effective_verdict = "unknown_evidence"
                        break
                    if qualifier_outcome == "unknown_resolution":
                        applicability = "active"
                        observed_outcome = "unknown_resolution"
                        effective_verdict = "unknown_resolution"
                        break
                else:
                    if qualifier_outcome == "pass":
                        applicability = "excepted"
                        observed_outcome = "not_evaluated"
                        effective_verdict = "waived"
                        break
                    if qualifier_outcome == "unknown_evidence":
                        applicability = "active"
                        observed_outcome = "unknown_evidence"
                        effective_verdict = "unknown_evidence"
                        break
                    if qualifier_outcome == "unknown_resolution":
                        applicability = "active"
                        observed_outcome = "unknown_resolution"
                        effective_verdict = "unknown_resolution"
                        break

            if observed_outcome == "not_evaluated" and applicability == "active":
                observed_outcome, fact_ids = _evaluate_predicate(
                    predicate_id=clause.normalized_predicate_id,
                    target_path=clause.target_path or "",
                    subject_ref=subject_ref,
                    fact_bundle=fact_bundle,
                    expected_scalar=clause.expected_scalar,
                    expected_count=clause.expected_count,
                )
                supporting_fact_refs.update(fact_ids)
                if observed_outcome == "pass":
                    effective_verdict = "fail" if clause.modal == "MUST_NOT" else "pass"
                elif observed_outcome == "fail":
                    effective_verdict = "pass" if clause.modal == "MUST_NOT" else "fail"
                else:
                    effective_verdict = observed_outcome

            message = f"evaluated {clause.clause_ref} for {subject_ref}"
            if applicability == "gated_off":
                message = f"{clause.clause_ref} gated off by ONLY_IF false"
            elif applicability == "excepted":
                message = f"{clause.clause_ref} excepted by UNLESS true"
            elif effective_verdict == "unknown_evidence":
                message = f"{clause.clause_ref} blocked on unknown evidence"
            elif effective_verdict == "unknown_resolution":
                message = f"{clause.clause_ref} blocked on unknown resolution"

            results.append(
                SubjectScopedResultRow(
                    result_id=f"result:{clause.clause_ref}:{subject_ref}",
                    clause_ref=clause.clause_ref,
                    clause_semantic_hash=_clause_semantic_hash(clause),
                    subject_ref=subject_ref,
                    applicability=applicability,
                    observed_outcome=observed_outcome,
                    effective_verdict=effective_verdict,
                    supporting_fact_refs=sorted(supporting_fact_refs),
                    supporting_contract_refs=supporting_contract_refs,
                    message=message,
                )
            )

    return PolicyEvaluationResultSet(
        result_set_id=result_set_id,
        scope_snapshot=fact_bundle.scope_snapshot,
        d_ir_ref=d1_ir.d1_ir_id,
        fact_bundle_ref=fact_bundle.bundle_id,
        predicate_contract_ref=predicate_contracts.predicate_contract_bundle_id,
        results=sorted(results, key=lambda item: item.result_id),
        notices=sorted(notices, key=lambda item: item.notice_id),
    )


def ledger_state_for_effective_verdict(effective_verdict: str) -> str:
    mapping = {
        "pass": "satisfied",
        "fail": "violated",
        "waived": "waived",
        "deferred": "deferred",
        "gated_off": "gated_off",
        "unknown_evidence": "blocked_unknown_evidence",
        "unknown_resolution": "blocked_unknown_resolution",
    }
    return mapping[effective_verdict]


def project_policy_obligation_ledger(
    *,
    result_set: PolicyEvaluationResultSet,
    ledger_id: str,
    previous_ledger: PolicyObligationLedger | None = None,
    updated_at: str | None = None,
) -> PolicyObligationLedger:
    if (
        previous_ledger is not None
        and previous_ledger.scope_snapshot != result_set.scope_snapshot
    ):
        raise ValueError(
            "previous_ledger scope_snapshot must match result_set scope_snapshot"
        )
    existing = {
        row.obligation_id: row
        for row in previous_ledger.rows
    } if previous_ledger is not None else {}
    rows: dict[str, PolicyObligationLedgerRow] = dict(existing)
    updated_obligation_ids: set[str] = set()

    for result in result_set.results:
        if isinstance(result, ClauseScopeBlockerResultRow):
            continue
        obligation_hash = stable_payload_hash(
            {
                "clause_ref": result.clause_ref,
                "clause_semantic_hash": result.clause_semantic_hash,
                "subject_ref": result.subject_ref,
                "scope_snapshot": result_set.scope_snapshot,
            }
        )
        obligation_id = f"obligation:{obligation_hash[:12]}"
        prior_row = rows.get(obligation_id)
        rows[obligation_id] = PolicyObligationLedgerRow(
            obligation_id=obligation_id,
            clause_ref=result.clause_ref,
            clause_semantic_hash=result.clause_semantic_hash,
            subject_ref=result.subject_ref,
            latest_applicability=result.applicability,
            latest_observed_outcome=result.observed_outcome,
            latest_effective_verdict=result.effective_verdict,
            ledger_state=ledger_state_for_effective_verdict(result.effective_verdict),
            first_seen_run=(
                prior_row.first_seen_run
                if prior_row is not None
                else result_set.result_set_id
            ),
            latest_result_run=result_set.result_set_id,
            waiver_ref=prior_row.waiver_ref if prior_row is not None else None,
            deferral_ref=prior_row.deferral_ref if prior_row is not None else None,
            updated_at=updated_at or result_set.result_set_id,
        )
        updated_obligation_ids.add(obligation_id)

    current_clause_refs = {result.clause_ref for result in result_set.results} | {
        notice.clause_ref for notice in result_set.notices
    }
    if current_clause_refs:
        for obligation_id, prior_row in list(rows.items()):
            if obligation_id in updated_obligation_ids:
                continue
            if prior_row.clause_ref not in current_clause_refs:
                continue
            rows[obligation_id] = PolicyObligationLedgerRow(
                obligation_id=prior_row.obligation_id,
                clause_ref=prior_row.clause_ref,
                clause_semantic_hash=prior_row.clause_semantic_hash,
                subject_ref=prior_row.subject_ref,
                latest_applicability="active",
                latest_observed_outcome="unknown_resolution",
                latest_effective_verdict="unknown_resolution",
                ledger_state="blocked_unknown_resolution",
                first_seen_run=prior_row.first_seen_run,
                latest_result_run=result_set.result_set_id,
                waiver_ref=prior_row.waiver_ref,
                deferral_ref=prior_row.deferral_ref,
                updated_at=updated_at or result_set.result_set_id,
            )

    result_set_refs = sorted(
        set(previous_ledger.result_set_refs if previous_ledger is not None else [])
        | {result_set.result_set_id}
    )
    return PolicyObligationLedger(
        ledger_id=ledger_id,
        scope_snapshot=result_set.scope_snapshot,
        result_set_refs=result_set_refs,
        rows=sorted(rows.values(), key=lambda item: item.obligation_id),
    )


def build_v47a_reference_chain(
    *,
    source_text: str,
    source_doc_ref: str,
    fact_bundle: CheckerFactBundle,
    result_set_id: str,
    ledger_id: str,
    predicate_contracts: PredicateContractsBootstrap | None = None,
) -> tuple[
    D1NormalizedIR,
    PredicateContractsBootstrap,
    PolicyEvaluationResultSet,
    PolicyObligationLedger,
]:
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref=source_doc_ref,
    )
    contracts = predicate_contracts or default_bootstrap_predicate_contracts()
    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=contracts,
        result_set_id=result_set_id,
    )
    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id=ledger_id,
    )
    return d1_ir, contracts, result_set, ledger


__all__ = [
    "AnmCompileError",
    "compile_authoritative_normative_markdown",
    "default_bootstrap_predicate_contracts",
    "evaluate_authoritative_normative_markdown",
    "project_policy_obligation_ledger",
    "build_v47a_reference_chain",
    "build_v47c_coexistence_profile",
    "build_v47d_selector_predicate_ownership_profile",
    "build_v47e_policy_consumer_binding_profile",
    "build_v47f_benchmark_policy_consumer_binding_profile",
]
