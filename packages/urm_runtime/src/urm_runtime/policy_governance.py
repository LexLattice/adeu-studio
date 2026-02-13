from __future__ import annotations

import json
import sqlite3
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Literal

from .config import URMRuntimeConfig
from .errors import URMError
from .evidence import EvidenceFileWriter
from .hashing import sha256_canonical_json
from .normalization import build_internal_event
from .profile_registry import PolicyProfileEntry, PolicyProfileRegistry
from .storage import (
    IdempotencyPayloadConflict,
    PolicyActivationRow,
    PolicyRegistryRow,
    append_policy_activation_entry,
    get_latest_policy_activation_for_profile,
    get_policy_activation_by_client_request_id,
    get_policy_registry_entry,
    list_policy_activation_hashes_for_profile,
    persist_idempotency_response,
    persist_policy_registry_entry,
    reserve_request_idempotency,
    transaction,
)

POLICY_MATERIALIZE_STREAM_ID = "urm_policy_registry"
POLICY_ROLLOUT_ENDPOINT = "urm.policy.rollout"
POLICY_ROLLBACK_ENDPOINT = "urm.policy.rollback"
POLICY_MATERIALIZE_ENDPOINT = "urm.policy.materialize"
DEFAULT_DETERMINISTIC_TS = "1970-01-01T00:00:00Z"


@dataclass(frozen=True)
class ActivePolicyState:
    profile_id: str
    profile_version: str
    policy_hash: str
    source: Literal["activation_log", "profile_default"]
    activation_seq: int | None
    action: Literal["rollout", "rollback"] | None
    activation_ts: str | None
    client_request_id: str | None
    prev_policy_hash: str | None


@dataclass(frozen=True)
class PolicyActivationResult:
    profile_id: str
    profile_version: str
    action: Literal["rollout", "rollback"]
    target_policy_hash: str
    prev_policy_hash: str | None
    activation_seq: int
    activation_ts: str
    request_payload_hash: str
    idempotent_replay: bool


def _now_utc_z() -> str:
    return datetime.now(tz=timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def resolve_operation_ts(
    *,
    ts: str | None,
    use_now: bool,
    default_ts: str = DEFAULT_DETERMINISTIC_TS,
    ts_field_name: str,
) -> str:
    if use_now and ts is not None:
        raise URMError(
            code="URM_POLICY_DENIED",
            message=f"cannot combine --use-now with --{ts_field_name}",
            context={"ts_field_name": ts_field_name},
        )
    if use_now:
        return _now_utc_z()
    if ts is not None:
        return ts
    return default_ts


def _governance_stream_path(*, config: URMRuntimeConfig, stream_id: str) -> Path:
    if stream_id == POLICY_MATERIALIZE_STREAM_ID:
        path = config.evidence_root / "governance" / "policy_registry" / "urm_events.ndjson"
    elif stream_id.startswith("urm_policy:"):
        profile_id = stream_id.split(":", 1)[1]
        path = config.evidence_root / "governance" / "policy" / profile_id / "urm_events.ndjson"
    else:
        safe_stream = stream_id.replace(":", "_")
        path = config.evidence_root / "governance" / safe_stream / "urm_events.ndjson"
    path.parent.mkdir(parents=True, exist_ok=True)
    return path


def _next_seq_for_event_file(*, path: Path) -> int:
    if not path.exists():
        return 1
    last_seq = 0
    try:
        with path.open("r", encoding="utf-8", errors="replace") as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                try:
                    payload = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if isinstance(payload, dict):
                    seq = payload.get("seq")
                    if isinstance(seq, int) and seq > last_seq:
                        last_seq = seq
    except OSError:
        return 1
    return last_seq + 1


def emit_governance_event(
    *,
    config: URMRuntimeConfig,
    stream_id: str,
    event_kind: str,
    endpoint: str,
    detail: dict[str, Any],
) -> None:
    events_path = _governance_stream_path(config=config, stream_id=stream_id)
    writer = EvidenceFileWriter(
        path=events_path,
        max_line_bytes=config.max_line_bytes,
        max_file_bytes=config.max_evidence_file_bytes,
    )
    try:
        seq = _next_seq_for_event_file(path=events_path)
        event = build_internal_event(
            seq=seq,
            event=event_kind,
            stream_id=stream_id,
            source_component="urm_policy_governance",
            context={
                "role": "governance",
                "endpoint": endpoint,
            },
            detail=detail,
        )
        writer.write_json_line(event.model_dump(mode="json", by_alias=True))
    finally:
        writer.close()


def resolve_active_policy_state_for_profile(
    *,
    con: sqlite3.Connection,
    profile: PolicyProfileEntry,
) -> ActivePolicyState:
    latest = get_latest_policy_activation_for_profile(con=con, profile_id=profile.profile_id)
    if latest is None:
        return ActivePolicyState(
            profile_id=profile.profile_id,
            profile_version=profile.profile_version,
            policy_hash=profile.default_policy_hash,
            source="profile_default",
            activation_seq=None,
            action=None,
            activation_ts=None,
            client_request_id=None,
            prev_policy_hash=None,
        )
    return ActivePolicyState(
        profile_id=profile.profile_id,
        profile_version=profile.profile_version,
        policy_hash=latest.target_policy_hash,
        source="activation_log",
        activation_seq=latest.activation_seq,
        action=(
            latest.action
            if latest.action in {"rollout", "rollback"}
            else None
        ),
        activation_ts=latest.activation_ts,
        client_request_id=latest.client_request_id,
        prev_policy_hash=latest.prev_policy_hash,
    )


def resolve_active_policy_state(
    *,
    config: URMRuntimeConfig,
    registry: PolicyProfileRegistry,
    profile_id: str,
) -> ActivePolicyState:
    profile = registry.get_profile(profile_id)
    with transaction(db_path=config.db_path) as con:
        return resolve_active_policy_state_for_profile(con=con, profile=profile)


def _activation_result_to_payload(result: PolicyActivationResult) -> dict[str, Any]:
    return {
        "profile_id": result.profile_id,
        "profile_version": result.profile_version,
        "action": result.action,
        "target_policy_hash": result.target_policy_hash,
        "prev_policy_hash": result.prev_policy_hash,
        "activation_seq": result.activation_seq,
        "activation_ts": result.activation_ts,
        "request_payload_hash": result.request_payload_hash,
    }


def _activation_result_from_payload(
    payload: dict[str, Any],
    *,
    idempotent_replay: bool,
) -> PolicyActivationResult:
    action_text = str(payload.get("action", ""))
    if action_text not in {"rollout", "rollback"}:
        action: Literal["rollout", "rollback"] = "rollout"
    else:
        action = action_text  # type: ignore[assignment]
    return PolicyActivationResult(
        profile_id=str(payload["profile_id"]),
        profile_version=str(payload["profile_version"]),
        action=action,
        target_policy_hash=str(payload["target_policy_hash"]),
        prev_policy_hash=(
            str(payload["prev_policy_hash"])
            if payload.get("prev_policy_hash") is not None
            else None
        ),
        activation_seq=int(payload["activation_seq"]),
        activation_ts=str(payload["activation_ts"]),
        request_payload_hash=str(payload["request_payload_hash"]),
        idempotent_replay=idempotent_replay,
    )


def _activation_result_from_row(
    *,
    row: PolicyActivationRow,
    profile_version: str,
    idempotent_replay: bool,
) -> PolicyActivationResult:
    action_text = row.action if row.action in {"rollout", "rollback"} else "rollout"
    action: Literal["rollout", "rollback"] = action_text
    return PolicyActivationResult(
        profile_id=row.profile_id,
        profile_version=profile_version,
        action=action,
        target_policy_hash=row.target_policy_hash,
        prev_policy_hash=row.prev_policy_hash,
        activation_seq=row.activation_seq,
        activation_ts=row.activation_ts,
        request_payload_hash=row.request_payload_hash,
        idempotent_replay=idempotent_replay,
    )


def materialize_policy(
    *,
    config: URMRuntimeConfig,
    policy_hash: str,
    schema_id: str,
    policy_schema_version: str,
    policy_ir_version: str,
    semantic_policy_json: dict[str, Any],
    source_policy_ref: str,
    materialized_at: str,
    event_endpoint: str = POLICY_MATERIALIZE_ENDPOINT,
) -> PolicyRegistryRow:
    with transaction(db_path=config.db_path) as con:
        persist_policy_registry_entry(
            con=con,
            policy_hash=policy_hash,
            schema_id=schema_id,
            policy_schema_version=policy_schema_version,
            policy_ir_version=policy_ir_version,
            semantic_policy_json=semantic_policy_json,
            source_policy_ref=source_policy_ref,
            materialized_at=materialized_at,
        )
        row = get_policy_registry_entry(con=con, policy_hash=policy_hash)
    if row is None:
        raise URMError(
            code="URM_NOT_FOUND",
            message="materialized policy row not found",
            status_code=404,
            context={"policy_hash": policy_hash},
        )
    emit_governance_event(
        config=config,
        stream_id=POLICY_MATERIALIZE_STREAM_ID,
        event_kind="POLICY_MATERIALIZED",
        endpoint=event_endpoint,
        detail={
            "policy_hash": row.policy_hash,
            "schema_id": row.schema_id,
            "policy_schema_version": row.policy_schema_version,
            "policy_ir_version": row.policy_ir_version,
            "materialized_at": row.materialized_at,
            "source_policy_ref": row.source_policy_ref,
        },
    )
    return row


def _validate_rollout_target(
    *,
    profile: PolicyProfileEntry,
    target_policy_hash: str,
    registry_row: PolicyRegistryRow | None,
) -> None:
    if registry_row is None:
        raise URMError(
            code="URM_POLICY_UNKNOWN_HASH",
            message="policy hash is not materialized in policy registry",
            context={
                "profile_id": profile.profile_id,
                "target_policy_hash": target_policy_hash,
            },
        )
    if target_policy_hash not in profile.allowed_policy_hashes:
        raise URMError(
            code="URM_POLICY_ROLLOUT_HASH_NOT_ALLOWED",
            message="policy hash is not allowed for profile",
            context={
                "profile_id": profile.profile_id,
                "target_policy_hash": target_policy_hash,
                "allowed_policy_hashes": profile.allowed_policy_hashes,
            },
        )


def _reserve_idempotency(
    *,
    con: sqlite3.Connection,
    endpoint_name: str,
    client_request_id: str,
    request_payload_hash: str,
    resource_id: str,
) -> tuple[dict[str, Any] | None, bool]:
    try:
        reservation = reserve_request_idempotency(
            con=con,
            endpoint_name=endpoint_name,
            client_request_id=client_request_id,
            payload_hash=request_payload_hash,
            resource_id=resource_id,
        )
    except IdempotencyPayloadConflict as exc:
        raise URMError(
            code="URM_POLICY_IDEMPOTENCY_CONFLICT",
            message="client_request_id already used with a different payload",
            status_code=409,
            context={
                "client_request_id": client_request_id,
                "stored_payload_hash": exc.stored_payload_hash,
                "incoming_payload_hash": exc.incoming_payload_hash,
            },
        ) from exc
    if reservation.replay:
        return reservation.response_json, True
    return reservation.response_json, False


def apply_policy_activation(
    *,
    config: URMRuntimeConfig,
    registry: PolicyProfileRegistry,
    endpoint_name: Literal[POLICY_ROLLOUT_ENDPOINT, POLICY_ROLLBACK_ENDPOINT],
    action: Literal["rollout", "rollback"],
    client_request_id: str,
    profile_id: str,
    target_policy_hash: str,
    activation_ts: str,
    request_payload: dict[str, Any],
) -> PolicyActivationResult:
    profile = registry.get_profile(profile_id)
    request_payload_hash = sha256_canonical_json(request_payload)

    with transaction(db_path=config.db_path) as con:
        replay_payload, is_replay = _reserve_idempotency(
            con=con,
            endpoint_name=endpoint_name,
            client_request_id=client_request_id,
            request_payload_hash=request_payload_hash,
            resource_id=f"{profile_id}:{client_request_id}",
        )
        if is_replay:
            payload = replay_payload or {}
            return _activation_result_from_payload(payload, idempotent_replay=True)

        existing_row = get_policy_activation_by_client_request_id(
            con=con,
            client_request_id=client_request_id,
        )
        if existing_row is not None:
            result = _activation_result_from_row(
                row=existing_row,
                profile_version=profile.profile_version,
                idempotent_replay=True,
            )
            persist_idempotency_response(
                con=con,
                endpoint_name=endpoint_name,
                client_request_id=client_request_id,
                response_json=_activation_result_to_payload(result),
            )
            return result

        active_state = resolve_active_policy_state_for_profile(con=con, profile=profile)
        target_registry_row = get_policy_registry_entry(con=con, policy_hash=target_policy_hash)

        if action == "rollout":
            _validate_rollout_target(
                profile=profile,
                target_policy_hash=target_policy_hash,
                registry_row=target_registry_row,
            )
            if (
                active_state.source == "activation_log"
                and active_state.policy_hash == target_policy_hash
            ):
                raise URMError(
                    code="URM_POLICY_ROLLOUT_CONFLICT",
                    message="policy hash is already active for profile",
                    status_code=409,
                    context={
                        "profile_id": profile.profile_id,
                        "target_policy_hash": target_policy_hash,
                    },
                )
        else:
            prior_hashes = list_policy_activation_hashes_for_profile(
                con=con,
                profile_id=profile.profile_id,
            )
            if target_policy_hash not in prior_hashes:
                raise URMError(
                    code="URM_POLICY_ROLLBACK_TARGET_NOT_FOUND",
                    message="rollback target policy hash not found in profile activation history",
                    context={
                        "profile_id": profile.profile_id,
                        "target_policy_hash": target_policy_hash,
                    },
                )

        activation_seq = append_policy_activation_entry(
            con=con,
            client_request_id=client_request_id,
            request_payload_hash=request_payload_hash,
            profile_id=profile.profile_id,
            action=action,
            target_policy_hash=target_policy_hash,
            prev_policy_hash=active_state.policy_hash,
            activation_ts=activation_ts,
        )
        result = PolicyActivationResult(
            profile_id=profile.profile_id,
            profile_version=profile.profile_version,
            action=action,
            target_policy_hash=target_policy_hash,
            prev_policy_hash=active_state.policy_hash,
            activation_seq=activation_seq,
            activation_ts=activation_ts,
            request_payload_hash=request_payload_hash,
            idempotent_replay=False,
        )
        persist_idempotency_response(
            con=con,
            endpoint_name=endpoint_name,
            client_request_id=client_request_id,
            response_json=_activation_result_to_payload(result),
        )

    stream_id = f"urm_policy:{profile.profile_id}"
    emit_governance_event(
        config=config,
        stream_id=stream_id,
        event_kind="POLICY_ROLLED_OUT" if action == "rollout" else "POLICY_ROLLED_BACK",
        endpoint="/urm/policy/rollout" if action == "rollout" else "/urm/policy/rollback",
        detail={
            "profile_id": result.profile_id,
            "profile_version": result.profile_version,
            "action": result.action,
            "target_policy_hash": result.target_policy_hash,
            "prev_policy_hash": result.prev_policy_hash,
            "activation_seq": result.activation_seq,
            "activation_ts": result.activation_ts,
            "request_payload_hash": result.request_payload_hash,
            "client_request_id": client_request_id,
        },
    )
    return result
