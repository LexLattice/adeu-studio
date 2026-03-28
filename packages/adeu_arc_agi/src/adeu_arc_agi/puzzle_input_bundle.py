from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA = "adeu_arc_puzzle_input_bundle@1"
V42G1_V95_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS95.md#v95-continuation-contract-machine-checkable"
)
PuzzleSourceKind = Literal[
    "official_toolkit_local_export",
    "repo_frozen_fixture",
    "approved_imported_local_copy",
]

_REQUIRED_SOURCE_PRECEDENCE_POLICY: tuple[PuzzleSourceKind, ...] = (
    "repo_frozen_fixture",
    "official_toolkit_local_export",
    "approved_imported_local_copy",
)
_EXPECTED_PUZZLE_COUNT = 3


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    if not value:
        raise ValueError(f"{field_name} must not be empty")
    if value != value.strip():
        raise ValueError(f"{field_name} must not include leading/trailing whitespace")
    return value


def _assert_sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted lexicographically")
    return normalized


def _assert_unique_preserving_order(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return normalized


def _assert_hash(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if len(normalized) != 64:
        raise ValueError(f"{field_name} must be a 64-character lowercase hex digest")
    for ch in normalized:
        if ch not in "0123456789abcdef":
            raise ValueError(f"{field_name} must be a 64-character lowercase hex digest")
    return normalized


def _assert_frozen_local_ref(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if normalized.startswith(("http://", "https://")):
        raise ValueError(f"{field_name} must not depend on live external fetch URLs")
    if not normalized.startswith("apps/api/fixtures/arc_agi/vnext_plus95/"):
        raise ValueError(f"{field_name} must reference frozen local v95 fixture payload")
    return normalized


def compute_adeu_arc_selection_register_id(
    *,
    selection_basis: str,
    selected_puzzle_ids: list[str],
    no_retrospective_swap_posture: bool,
) -> str:
    digest = sha256_canonical_json(
        {
            "selection_basis": selection_basis,
            "selected_puzzle_ids": selected_puzzle_ids,
            "no_retrospective_swap_posture": no_retrospective_swap_posture,
        }
    )
    return f"arc_sel_{digest[:32]}"


def compute_adeu_arc_selection_register_hash(
    *,
    selection_register_id: str,
    selection_basis: str,
    selected_puzzle_ids: list[str],
    no_retrospective_swap_posture: bool,
) -> str:
    return sha256_canonical_json(
        {
            "selection_register_id": selection_register_id,
            "selection_basis": selection_basis,
            "selected_puzzle_ids": selected_puzzle_ids,
            "no_retrospective_swap_posture": no_retrospective_swap_posture,
        }
    )


def compute_adeu_arc_puzzle_identity_hash(
    *,
    normalized_payload_hash: str,
) -> str:
    return sha256_canonical_json({"normalized_payload_hash": normalized_payload_hash})


def compute_adeu_arc_puzzle_input_id(
    *,
    puzzle_id: str,
    source_kind: PuzzleSourceKind,
    source_ref: str,
    puzzle_identity_hash: str,
) -> str:
    digest = sha256_canonical_json(
        {
            "puzzle_id": puzzle_id,
            "source_kind": source_kind,
            "source_ref": source_ref,
            "puzzle_identity_hash": puzzle_identity_hash,
        }
    )
    return f"arc_puz_{digest[:32]}"


def compute_adeu_arc_bundle_identity_hash(
    *,
    selection_register_hash: str,
    canonical_puzzle_order: list[str],
    puzzle_entries: list[dict[str, Any]],
) -> str:
    return sha256_canonical_json(
        {
            "selection_register_hash": selection_register_hash,
            "canonical_puzzle_order": canonical_puzzle_order,
            "puzzle_entry_hash_register": [
                {
                    "puzzle_id": entry["puzzle_id"],
                    "puzzle_identity_hash": entry["puzzle_identity_hash"],
                }
                for entry in puzzle_entries
            ],
        }
    )


class AdeuArcPuzzleInputEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    puzzle_input_id: str
    puzzle_id: str
    source_kind: PuzzleSourceKind
    source_ref: str
    normalized_payload_ref: str
    normalized_payload: dict[str, Any]
    normalized_payload_hash: str
    puzzle_identity_hash: str
    provenance_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> AdeuArcPuzzleInputEntry:
        object.__setattr__(
            self,
            "puzzle_input_id",
            _assert_non_empty_text(self.puzzle_input_id, field_name="puzzle_input_id"),
        )
        object.__setattr__(
            self,
            "puzzle_id",
            _assert_non_empty_text(self.puzzle_id, field_name="puzzle_id"),
        )
        object.__setattr__(
            self,
            "source_ref",
            _assert_non_empty_text(self.source_ref, field_name="source_ref"),
        )
        object.__setattr__(
            self,
            "normalized_payload_ref",
            _assert_frozen_local_ref(
                self.normalized_payload_ref, field_name="normalized_payload_ref"
            ),
        )
        object.__setattr__(
            self,
            "provenance_refs",
            _assert_sorted_unique(self.provenance_refs, field_name="provenance_refs"),
        )
        if not isinstance(self.normalized_payload, dict) or not self.normalized_payload:
            raise ValueError("normalized_payload must be a non-empty object")

        computed_payload_hash = sha256_canonical_json(self.normalized_payload)
        object.__setattr__(
            self,
            "normalized_payload_hash",
            _assert_hash(
                self.normalized_payload_hash,
                field_name="normalized_payload_hash",
            ),
        )
        if self.normalized_payload_hash != computed_payload_hash:
            raise ValueError(
                "normalized_payload_hash must match canonical hash of normalized_payload"
            )

        object.__setattr__(
            self,
            "puzzle_identity_hash",
            _assert_hash(self.puzzle_identity_hash, field_name="puzzle_identity_hash"),
        )
        expected_puzzle_identity_hash = compute_adeu_arc_puzzle_identity_hash(
            normalized_payload_hash=self.normalized_payload_hash,
        )
        if self.puzzle_identity_hash != expected_puzzle_identity_hash:
            raise ValueError(
                "puzzle_identity_hash must match puzzle_id + normalized_payload_hash identity"
            )

        expected_puzzle_input_id = compute_adeu_arc_puzzle_input_id(
            puzzle_id=self.puzzle_id,
            source_kind=self.source_kind,
            source_ref=self.source_ref,
            puzzle_identity_hash=self.puzzle_identity_hash,
        )
        if self.puzzle_input_id != expected_puzzle_input_id:
            raise ValueError(
                "puzzle_input_id must match canonical source-bound puzzle identity"
            )
        return self


class AdeuArcPuzzleInputBundle(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA] = ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA
    puzzle_input_bundle_id: str
    selection_register_id: str
    selection_register_ref: str
    selection_register_hash: str
    selection_basis: str
    source_profile: str
    source_precedence_policy: list[PuzzleSourceKind] = Field(min_length=1)
    selected_puzzle_ids: list[str] = Field(
        min_length=_EXPECTED_PUZZLE_COUNT, max_length=_EXPECTED_PUZZLE_COUNT
    )
    canonical_puzzle_order: list[str] = Field(
        min_length=_EXPECTED_PUZZLE_COUNT, max_length=_EXPECTED_PUZZLE_COUNT
    )
    puzzle_entries: list[AdeuArcPuzzleInputEntry] = Field(
        min_length=_EXPECTED_PUZZLE_COUNT, max_length=_EXPECTED_PUZZLE_COUNT
    )
    bundle_identity_hash: str
    no_retrospective_swap_posture: bool = True
    provenance_refs: list[str] = Field(min_length=1)
    summary_non_authoritative: bool = True
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_bundle(self) -> AdeuArcPuzzleInputBundle:
        text_fields = (
            "puzzle_input_bundle_id",
            "selection_register_id",
            "selection_register_ref",
            "selection_register_hash",
            "selection_basis",
            "source_profile",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )

        object.__setattr__(
            self,
            "selection_register_ref",
            _assert_non_empty_text(
                self.selection_register_ref,
                field_name="selection_register_ref",
            ),
        )
        object.__setattr__(
            self,
            "source_precedence_policy",
            list(self.source_precedence_policy),
        )
        if tuple(self.source_precedence_policy) != _REQUIRED_SOURCE_PRECEDENCE_POLICY:
            raise ValueError(
                "source_precedence_policy must match released V42-G1 precedence order"
            )

        object.__setattr__(
            self,
            "selected_puzzle_ids",
            _assert_unique_preserving_order(
                self.selected_puzzle_ids, field_name="selected_puzzle_ids"
            ),
        )
        object.__setattr__(
            self,
            "canonical_puzzle_order",
            _assert_unique_preserving_order(
                self.canonical_puzzle_order, field_name="canonical_puzzle_order"
            ),
        )
        if self.canonical_puzzle_order != self.selected_puzzle_ids:
            raise ValueError(
                "canonical_puzzle_order must exactly match declared selected_puzzle_ids order"
            )

        if not self.no_retrospective_swap_posture:
            raise ValueError("no_retrospective_swap_posture must be true for v42g1 bundles")
        if not self.summary_non_authoritative:
            raise ValueError("summary_non_authoritative must be true for v42g1 bundles")

        object.__setattr__(
            self,
            "provenance_refs",
            _assert_sorted_unique(self.provenance_refs, field_name="provenance_refs"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )
        if self.selection_register_ref not in self.provenance_refs:
            raise ValueError("provenance_refs must include selection_register_ref")

        puzzle_ids_from_entries = [entry.puzzle_id for entry in self.puzzle_entries]
        if puzzle_ids_from_entries != self.canonical_puzzle_order:
            raise ValueError(
                "puzzle_entries must follow canonical_puzzle_order without undeclared/swap drift"
            )

        puzzle_identity_hashes = [entry.puzzle_identity_hash for entry in self.puzzle_entries]
        if len(puzzle_identity_hashes) != len(set(puzzle_identity_hashes)):
            raise ValueError("duplicate puzzle identity hashes are forbidden in the same bundle")

        expected_selection_register_id = compute_adeu_arc_selection_register_id(
            selection_basis=self.selection_basis,
            selected_puzzle_ids=self.selected_puzzle_ids,
            no_retrospective_swap_posture=self.no_retrospective_swap_posture,
        )
        if self.selection_register_id != expected_selection_register_id:
            raise ValueError(
                "selection_register_id must match canonical selection register identity"
            )

        expected_selection_register_hash = compute_adeu_arc_selection_register_hash(
            selection_register_id=self.selection_register_id,
            selection_basis=self.selection_basis,
            selected_puzzle_ids=self.selected_puzzle_ids,
            no_retrospective_swap_posture=self.no_retrospective_swap_posture,
        )
        object.__setattr__(
            self,
            "selection_register_hash",
            _assert_hash(self.selection_register_hash, field_name="selection_register_hash"),
        )
        if self.selection_register_hash != expected_selection_register_hash:
            raise ValueError(
                "selection_register_hash must match canonical register payload hash"
            )

        expected_bundle_identity_hash = compute_adeu_arc_bundle_identity_hash(
            selection_register_hash=self.selection_register_hash,
            canonical_puzzle_order=self.canonical_puzzle_order,
            puzzle_entries=[
                entry.model_dump(mode="json", exclude_none=False) for entry in self.puzzle_entries
            ],
        )
        object.__setattr__(
            self,
            "bundle_identity_hash",
            _assert_hash(self.bundle_identity_hash, field_name="bundle_identity_hash"),
        )
        if self.bundle_identity_hash != expected_bundle_identity_hash:
            raise ValueError(
                "bundle_identity_hash must match canonical order + entry identity hash register"
            )

        payload_without_id = self.model_dump(mode="json", exclude_none=False)
        payload_without_id.pop("puzzle_input_bundle_id", None)
        expected_bundle_id = compute_adeu_arc_puzzle_input_bundle_id(payload_without_id)
        if self.puzzle_input_bundle_id != expected_bundle_id:
            raise ValueError(
                "puzzle_input_bundle_id must match canonical full payload hash identity"
            )
        return self


def compute_adeu_arc_puzzle_input_bundle_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA)
    canonical_payload.pop("puzzle_input_bundle_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_bundle_{digest[:32]}"


def canonicalize_adeu_arc_puzzle_input_bundle_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcPuzzleInputBundle.model_validate(payload).model_dump(
        mode="json", exclude_none=False
    )


def materialize_adeu_arc_puzzle_input_bundle_payload(
    payload_without_puzzle_input_bundle_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_puzzle_input_bundle_id)
    payload.setdefault("schema", ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA)
    payload["puzzle_input_bundle_id"] = compute_adeu_arc_puzzle_input_bundle_id(payload)
    return canonicalize_adeu_arc_puzzle_input_bundle_payload(payload)


def derive_v42g1_arc_puzzle_input_bundle(
    *,
    selection_register_ref: str,
    selection_basis: str,
    selected_puzzle_ids: list[str],
    source_profile: str,
    puzzle_entries: list[dict[str, Any]],
    provenance_refs: list[str],
    evidence_refs: list[str],
    source_precedence_policy: list[PuzzleSourceKind] | None = None,
    no_retrospective_swap_posture: bool = True,
    summary_non_authoritative: bool = True,
) -> dict[str, Any]:
    selected_ids = deepcopy(selected_puzzle_ids)
    if len(selected_ids) != _EXPECTED_PUZZLE_COUNT:
        raise ValueError("selected_puzzle_ids must contain exactly three puzzle IDs in V42-G1")
    canonical_order = deepcopy(selected_ids)
    register_id = compute_adeu_arc_selection_register_id(
        selection_basis=selection_basis,
        selected_puzzle_ids=selected_ids,
        no_retrospective_swap_posture=no_retrospective_swap_posture,
    )
    register_hash = compute_adeu_arc_selection_register_hash(
        selection_register_id=register_id,
        selection_basis=selection_basis,
        selected_puzzle_ids=selected_ids,
        no_retrospective_swap_posture=no_retrospective_swap_posture,
    )
    entry_payloads: list[dict[str, Any]] = []
    for entry in puzzle_entries:
        normalized_payload = deepcopy(entry["normalized_payload"])
        normalized_payload_hash = sha256_canonical_json(normalized_payload)
        puzzle_identity_hash = compute_adeu_arc_puzzle_identity_hash(
            normalized_payload_hash=normalized_payload_hash,
        )
        entry_payloads.append(
            {
                "puzzle_input_id": compute_adeu_arc_puzzle_input_id(
                    puzzle_id=entry["puzzle_id"],
                    source_kind=entry["source_kind"],
                    source_ref=entry["source_ref"],
                    puzzle_identity_hash=puzzle_identity_hash,
                ),
                "puzzle_id": entry["puzzle_id"],
                "source_kind": entry["source_kind"],
                "source_ref": entry["source_ref"],
                "normalized_payload_ref": entry["normalized_payload_ref"],
                "normalized_payload": normalized_payload,
                "normalized_payload_hash": normalized_payload_hash,
                "puzzle_identity_hash": puzzle_identity_hash,
                "provenance_refs": deepcopy(entry["provenance_refs"]),
            }
        )
    precedence_policy = (
        list(_REQUIRED_SOURCE_PRECEDENCE_POLICY)
        if source_precedence_policy is None
        else deepcopy(source_precedence_policy)
    )
    payload_without_id: dict[str, Any] = {
        "schema": ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA,
        "selection_register_id": register_id,
        "selection_register_ref": selection_register_ref,
        "selection_register_hash": register_hash,
        "selection_basis": selection_basis,
        "source_profile": source_profile,
        "source_precedence_policy": precedence_policy,
        "selected_puzzle_ids": selected_ids,
        "canonical_puzzle_order": canonical_order,
        "puzzle_entries": entry_payloads,
        "bundle_identity_hash": compute_adeu_arc_bundle_identity_hash(
            selection_register_hash=register_hash,
            canonical_puzzle_order=canonical_order,
            puzzle_entries=entry_payloads,
        ),
        "no_retrospective_swap_posture": no_retrospective_swap_posture,
        "provenance_refs": deepcopy(provenance_refs),
        "summary_non_authoritative": summary_non_authoritative,
        "evidence_refs": deepcopy(evidence_refs),
    }
    return materialize_adeu_arc_puzzle_input_bundle_payload(payload_without_id)
