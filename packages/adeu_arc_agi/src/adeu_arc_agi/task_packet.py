from __future__ import annotations

import re
from copy import deepcopy
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

ADEU_ARC_TASK_PACKET_SCHEMA = "adeu_arc_task_packet@1"
V42A_V89_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS89.md#v42a_arc_local_adapter_contract@1"
)

ArcEnvironmentAuthority = Literal["official_arc_toolkit"]
ArcModePosture = Literal["local_offline"]
ArcNormalizationKind = Literal["identity", "subset"]

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_ADAPTER_LINEAGE_RE = re.compile(r"^arc_toolkit_local/[A-Za-z0-9._-]+$")
_TOOLKIT_LOCAL_REF_PREFIX = "toolkit://local/"


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    if not value:
        raise ValueError(f"{field_name} must not be empty")
    if value != value.strip():
        raise ValueError(f"{field_name} must not include leading or trailing whitespace")
    return value


def _assert_sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted lexicographically")
    return normalized


def _assert_sha256_hex(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name).lower()
    if not _SHA256_RE.fullmatch(normalized):
        raise ValueError(f"{field_name} must be a lowercase sha256 hex digest")
    return normalized


class ArcAdapterBoundaryPolicy(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    policy_semantics: Literal["deontic_admissibility_only"] = "deontic_admissibility_only"
    local_offline_only: bool = True
    competition_mode_allowed: bool = False
    scorecard_authority_allowed: bool = False
    replay_authority_allowed: bool = False
    observation_hypothesis_action_allowed: bool = False
    environment_semantics_redefinition_allowed: bool = False

    @model_validator(mode="after")
    def _validate_policy(self) -> ArcAdapterBoundaryPolicy:
        if not self.local_offline_only:
            raise ValueError("adapter boundary policy must enforce local_offline_only")
        if self.competition_mode_allowed:
            raise ValueError("adapter boundary policy may not allow competition mode in V42-A")
        if self.scorecard_authority_allowed:
            raise ValueError(
                "adapter boundary policy may not allow scorecard authority in V42-A"
            )
        if self.replay_authority_allowed:
            raise ValueError("adapter boundary policy may not allow replay authority in V42-A")
        if self.observation_hypothesis_action_allowed:
            raise ValueError(
                "adapter boundary policy may not smuggle observation/hypothesis/action authority"
            )
        if self.environment_semantics_redefinition_allowed:
            raise ValueError(
                "adapter boundary policy may not allow environment-semantic redefinition"
            )
        return self


class ArcLegalActionEnvelopeProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    source: Literal["toolkit_mirror"] = "toolkit_mirror"
    toolkit_envelope_hash: str
    normalization_kind: ArcNormalizationKind
    dropped_actions: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_provenance(self) -> ArcLegalActionEnvelopeProvenance:
        object.__setattr__(
            self,
            "toolkit_envelope_hash",
            _assert_sha256_hex(
                self.toolkit_envelope_hash,
                field_name="toolkit_envelope_hash",
            ),
        )
        object.__setattr__(
            self,
            "dropped_actions",
            _assert_sorted_unique(self.dropped_actions, field_name="dropped_actions"),
        )
        return self


class AdeuArcTaskPacket(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARC_TASK_PACKET_SCHEMA] = ADEU_ARC_TASK_PACKET_SCHEMA
    task_packet_id: str
    environment_authority: ArcEnvironmentAuthority = "official_arc_toolkit"
    adapter: str
    mode_posture: ArcModePosture = "local_offline"
    game_ref: str
    session_ref: str
    initial_state_ref: str
    initial_state_hash: str
    toolkit_legal_action_envelope: list[str] = Field(min_length=1)
    legal_action_envelope: list[str] = Field(min_length=1)
    legal_action_envelope_provenance: ArcLegalActionEnvelopeProvenance
    adapter_boundary_policy: ArcAdapterBoundaryPolicy

    @model_validator(mode="after")
    def _validate_task_packet(self) -> AdeuArcTaskPacket:
        object.__setattr__(
            self,
            "task_packet_id",
            _assert_non_empty_text(self.task_packet_id, field_name="task_packet_id"),
        )
        object.__setattr__(
            self,
            "adapter",
            _assert_non_empty_text(self.adapter, field_name="adapter"),
        )
        if not _ADAPTER_LINEAGE_RE.fullmatch(self.adapter):
            raise ValueError("adapter must declare official local toolkit lineage")
        object.__setattr__(
            self,
            "game_ref",
            _assert_non_empty_text(self.game_ref, field_name="game_ref"),
        )
        if not self.game_ref.startswith(_TOOLKIT_LOCAL_REF_PREFIX):
            raise ValueError("game_ref must be sourced from official local toolkit capture")
        object.__setattr__(
            self,
            "session_ref",
            _assert_non_empty_text(self.session_ref, field_name="session_ref"),
        )
        if not self.session_ref.startswith(_TOOLKIT_LOCAL_REF_PREFIX):
            raise ValueError("session_ref must be sourced from official local toolkit capture")
        object.__setattr__(
            self,
            "initial_state_ref",
            _assert_non_empty_text(self.initial_state_ref, field_name="initial_state_ref"),
        )
        if not self.initial_state_ref.startswith(_TOOLKIT_LOCAL_REF_PREFIX):
            raise ValueError(
                "initial_state_ref must be sourced from official local toolkit capture"
            )
        object.__setattr__(
            self,
            "initial_state_hash",
            _assert_sha256_hex(self.initial_state_hash, field_name="initial_state_hash"),
        )
        object.__setattr__(
            self,
            "toolkit_legal_action_envelope",
            _assert_sorted_unique(
                self.toolkit_legal_action_envelope,
                field_name="toolkit_legal_action_envelope",
            ),
        )
        object.__setattr__(
            self,
            "legal_action_envelope",
            _assert_sorted_unique(self.legal_action_envelope, field_name="legal_action_envelope"),
        )
        toolkit_set = set(self.toolkit_legal_action_envelope)
        mirrored_set = set(self.legal_action_envelope)
        if not mirrored_set.issubset(toolkit_set):
            raise ValueError(
                "legal_action_envelope must be a subset of toolkit_legal_action_envelope"
            )
        expected_toolkit_hash = sha256_canonical_json(self.toolkit_legal_action_envelope)
        if self.legal_action_envelope_provenance.toolkit_envelope_hash != expected_toolkit_hash:
            raise ValueError(
                "legal_action_envelope_provenance.toolkit_envelope_hash must match "
                "toolkit_legal_action_envelope"
            )
        expected_dropped = sorted(toolkit_set - mirrored_set)
        if self.legal_action_envelope_provenance.dropped_actions != expected_dropped:
            raise ValueError(
                "legal_action_envelope_provenance.dropped_actions must account for "
                "toolkit-vs-mirrored envelope differences"
            )
        if self.legal_action_envelope_provenance.normalization_kind == "identity":
            if expected_dropped:
                raise ValueError(
                    "normalization_kind=identity is illegal when mirrored envelope drops actions"
                )
        elif not expected_dropped:
            raise ValueError(
                "normalization_kind=subset requires at least one dropped action"
            )

        payload_without_id = self.model_dump(mode="json", exclude_none=False)
        payload_without_id.pop("task_packet_id", None)
        expected_task_packet_id = compute_adeu_arc_task_packet_id(payload_without_id)
        if self.task_packet_id != expected_task_packet_id:
            raise ValueError(
                "task_packet_id must match canonical full packet payload hash identity"
            )
        return self


def compute_adeu_arc_task_packet_id(payload_without_task_packet_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_task_packet_id)
    canonical_payload.setdefault("schema", ADEU_ARC_TASK_PACKET_SCHEMA)
    canonical_payload.pop("task_packet_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"arc_task_{digest[:32]}"


def canonicalize_adeu_arc_task_packet_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return AdeuArcTaskPacket.model_validate(payload).model_dump(mode="json", exclude_none=False)


def materialize_adeu_arc_task_packet_payload(
    payload_without_task_packet_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_task_packet_id)
    payload.setdefault("schema", ADEU_ARC_TASK_PACKET_SCHEMA)
    payload["task_packet_id"] = compute_adeu_arc_task_packet_id(payload)
    return canonicalize_adeu_arc_task_packet_payload(payload)


def derive_v42a_arc_task_packet(
    *,
    adapter: str,
    game_ref: str,
    session_ref: str,
    initial_state_ref: str,
    initial_state_hash: str,
    toolkit_legal_action_envelope: list[str],
    legal_action_envelope: list[str] | None = None,
    normalization_kind: ArcNormalizationKind = "identity",
    adapter_boundary_policy: dict[str, Any] | ArcAdapterBoundaryPolicy | None = None,
) -> dict[str, Any]:
    mirrored = (
        deepcopy(toolkit_legal_action_envelope)
        if legal_action_envelope is None
        else deepcopy(legal_action_envelope)
    )
    toolkit = deepcopy(toolkit_legal_action_envelope)
    dropped = sorted(set(toolkit) - set(mirrored))
    payload_without_task_packet_id: dict[str, Any] = {
        "schema": ADEU_ARC_TASK_PACKET_SCHEMA,
        "environment_authority": "official_arc_toolkit",
        "adapter": adapter,
        "mode_posture": "local_offline",
        "game_ref": game_ref,
        "session_ref": session_ref,
        "initial_state_ref": initial_state_ref,
        "initial_state_hash": initial_state_hash,
        "toolkit_legal_action_envelope": toolkit,
        "legal_action_envelope": mirrored,
        "legal_action_envelope_provenance": {
            "source": "toolkit_mirror",
            "toolkit_envelope_hash": sha256_canonical_json(toolkit),
            "normalization_kind": normalization_kind,
            "dropped_actions": dropped,
        },
        "adapter_boundary_policy": (
            adapter_boundary_policy.model_dump(mode="json", exclude_none=False)
            if isinstance(adapter_boundary_policy, ArcAdapterBoundaryPolicy)
            else (
                deepcopy(adapter_boundary_policy)
                if isinstance(adapter_boundary_policy, dict)
                else ArcAdapterBoundaryPolicy().model_dump(mode="json", exclude_none=False)
            )
        ),
    }
    return materialize_adeu_arc_task_packet_payload(payload_without_task_packet_id)
