from __future__ import annotations

import asyncio
import json
import os
import subprocess
import sys
from contextlib import contextmanager
from pathlib import Path
from textwrap import dedent
from typing import Any

import adeu_api.main as api_main
import pytest
from adeu_api.hashing import sha256_canonical_json
from adeu_api.main import CoreIRProposerRequest
from adeu_api.storage import get_core_ir_proposer_idempotency_by_client_request_id
from fastapi import FastAPI

PROPOSER_PATH = "/urm/core-ir/propose"


def _clear_provider_parity_cache() -> None:
    cache_clear = getattr(
        api_main._provider_parity_supported_providers_by_surface,
        "cache_clear",
        None,
    )
    if callable(cache_clear):
        cache_clear()


def _pythonpath_env() -> dict[str, str]:
    repo_root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(repo_root / "apps" / "api" / "src"),
        str(repo_root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    return env


def _repo_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / ".git").is_dir():
            return parent
    raise FileNotFoundError("repository root not found")


def _mock_provider_for_tests() -> str:
    providers = tuple(
        api_main._provider_parity_supported_providers_by_surface().get(
            api_main._CORE_IR_PROPOSER_SURFACE_ID,
            (),
        )
    )
    if "mock" in providers:
        return "mock"
    if providers:
        return str(providers[0])
    return "mock"


def _proposer_payload(*, client_request_id: str, provider: str, source_text: str) -> dict[str, Any]:
    return {
        "schema": "adeu_core_ir_proposer_request@0.1",
        "client_request_id": client_request_id,
        "provider": provider,
        "source_text": source_text,
    }


def _asgi_post_json(*, app: FastAPI, path: str, payload: dict[str, Any]) -> tuple[int, Any]:
    body_bytes = json.dumps(payload).encode("utf-8")
    scope = {
        "type": "http",
        "asgi": {"version": "3.0", "spec_version": "2.3"},
        "http_version": "1.1",
        "method": "POST",
        "scheme": "http",
        "path": path,
        "raw_path": path.encode("ascii"),
        "query_string": b"",
        "headers": [
            (b"host", b"testserver"),
            (b"content-type", b"application/json"),
            (b"content-length", str(len(body_bytes)).encode("ascii")),
        ],
        "client": ("testclient", 50000),
        "server": ("testserver", 80),
    }
    events: list[dict[str, Any]] = [
        {"type": "http.request", "body": body_bytes, "more_body": False}
    ]
    sent: list[dict[str, Any]] = []

    async def _receive() -> dict[str, Any]:
        if events:
            return events.pop(0)
        return {"type": "http.disconnect"}

    async def _send(message: dict[str, Any]) -> None:
        sent.append(message)

    async def _invoke() -> None:
        await app(scope, _receive, _send)

    asyncio.run(_invoke())

    start_message = next(
        message for message in sent if message["type"] == "http.response.start"
    )
    body = b"".join(
        message.get("body", b"") for message in sent if message["type"] == "http.response.body"
    )
    if not body:
        return int(start_message["status"]), None
    return int(start_message["status"]), json.loads(body.decode("utf-8"))


def _post_proposer(payload: dict[str, Any]) -> tuple[int, Any]:
    return _asgi_post_json(app=api_main.app, path=PROPOSER_PATH, payload=payload)


@pytest.fixture(autouse=True)
def _isolated_db(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("ADEU_API_DB_PATH", str((tmp_path / "api.sqlite3").resolve()))
    _clear_provider_parity_cache()
    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()
    yield
    _clear_provider_parity_cache()
    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()


def test_v37_k2_http_path_callgraph_uses_persisted_idempotency(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    provider = _mock_provider_for_tests()
    payload = _proposer_payload(
        client_request_id="v37-k2-callgraph-1",
        provider=provider,
        source_text="The operator must log every override decision.",
    )

    call_counts = {
        "storage_transaction": 0,
        "create_core_ir_proposer_idempotency_if_absent": 0,
        "get_core_ir_proposer_idempotency_by_client_request_id": 0,
    }

    original_storage_transaction = api_main.storage_transaction

    @contextmanager
    def _spy_storage_transaction(*args: Any, **kwargs: Any):
        call_counts["storage_transaction"] += 1
        with original_storage_transaction(*args, **kwargs) as con:
            yield con

    original_create = api_main.create_core_ir_proposer_idempotency_if_absent

    def _spy_create(*args: Any, **kwargs: Any) -> Any:
        call_counts["create_core_ir_proposer_idempotency_if_absent"] += 1
        return original_create(*args, **kwargs)

    original_get = api_main.get_core_ir_proposer_idempotency_by_client_request_id

    def _spy_get(*args: Any, **kwargs: Any) -> Any:
        call_counts["get_core_ir_proposer_idempotency_by_client_request_id"] += 1
        return original_get(*args, **kwargs)

    monkeypatch.setattr(api_main, "storage_transaction", _spy_storage_transaction)
    monkeypatch.setattr(api_main, "create_core_ir_proposer_idempotency_if_absent", _spy_create)
    monkeypatch.setattr(api_main, "get_core_ir_proposer_idempotency_by_client_request_id", _spy_get)

    first_status, first_payload = _post_proposer(payload)
    assert first_status == 200

    assert call_counts["storage_transaction"] >= 1
    assert call_counts["create_core_ir_proposer_idempotency_if_absent"] >= 1
    assert call_counts["get_core_ir_proposer_idempotency_by_client_request_id"] >= 2

    before_replay = dict(call_counts)
    replay_status, replay_payload = _post_proposer(payload)
    assert replay_status == 200
    assert replay_payload == first_payload

    assert (
        call_counts["create_core_ir_proposer_idempotency_if_absent"]
        == before_replay["create_core_ir_proposer_idempotency_if_absent"]
    )
    assert call_counts["storage_transaction"] == before_replay["storage_transaction"]
    assert (
        call_counts["get_core_ir_proposer_idempotency_by_client_request_id"]
        >= before_replay["get_core_ir_proposer_idempotency_by_client_request_id"] + 1
    )


def test_v37_k2_replay_is_deterministic_over_http_path() -> None:
    provider = _mock_provider_for_tests()
    payload = _proposer_payload(
        client_request_id="v37-k2-replay-http-1",
        provider=provider,
        source_text="The operator must log every override decision.",
    )

    first_status, first_payload = _post_proposer(payload)
    second_status, second_payload = _post_proposer(payload)

    assert first_status == 200
    assert second_status == 200
    assert second_payload == first_payload
    assert second_payload["schema"] == "adeu_core_ir_proposer_response@0.1"


def test_v37_k2_conflict_on_same_id_different_payload_has_structured_fields() -> None:
    provider = _mock_provider_for_tests()
    base_payload = _proposer_payload(
        client_request_id="v37-k2-conflict-payload-1",
        provider=provider,
        source_text="The operator must log every override decision.",
    )
    changed_payload = _proposer_payload(
        client_request_id=base_payload["client_request_id"],
        provider=provider,
        source_text="The operator may skip override logs when idle.",
    )

    first_status, _ = _post_proposer(base_payload)
    assert first_status == 200

    second_status, second_payload = _post_proposer(changed_payload)
    assert second_status == 400
    detail = second_payload["detail"]

    assert detail["code"] == "URM_ADEU_CORE_IR_PROPOSER_REQUEST_INVALID"
    assert detail["context"]["client_request_id"] == base_payload["client_request_id"]
    assert "provider_expected" in detail["context"]
    assert "provider_observed" in detail["context"]
    assert "request_payload_hash_expected" in detail["context"]
    assert "request_payload_hash_observed" in detail["context"]


def test_v37_k2_conflict_on_same_id_different_provider_has_structured_fields() -> None:
    provider = _mock_provider_for_tests()
    first_payload = _proposer_payload(
        client_request_id="v37-k2-conflict-provider-1",
        provider=provider,
        source_text="The operator must log every override decision.",
    )
    second_provider = "codex" if provider != "codex" else "mock"
    second_payload = _proposer_payload(
        client_request_id=first_payload["client_request_id"],
        provider=second_provider,
        source_text=first_payload["source_text"],
    )

    first_status, _ = _post_proposer(first_payload)
    assert first_status == 200

    second_status, second_body = _post_proposer(second_payload)
    assert second_status == 400
    detail = second_body["detail"]

    assert detail["code"] == "URM_ADEU_CORE_IR_PROPOSER_REQUEST_INVALID"
    assert detail["context"]["client_request_id"] == first_payload["client_request_id"]
    assert detail["context"]["provider_observed"] == second_provider
    assert "provider_expected" in detail["context"]
    assert "request_payload_hash_expected" in detail["context"]
    assert "request_payload_hash_observed" in detail["context"]


def test_v37_k2_cache_reset_does_not_change_persisted_replay_outcome() -> None:
    provider = _mock_provider_for_tests()
    payload = _proposer_payload(
        client_request_id="v37-k2-cache-reset-1",
        provider=provider,
        source_text="The operator must log every override decision.",
    )

    first_status, first_payload = _post_proposer(payload)
    assert first_status == 200

    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()

    second_status, second_payload = _post_proposer(payload)
    assert second_status == 200
    assert second_payload == first_payload


def test_v37_k2_cache_present_state_is_non_authoritative_when_row_absent() -> None:
    provider = _mock_provider_for_tests()
    payload = _proposer_payload(
        client_request_id="v37-k2-cache-only-1",
        provider=provider,
        source_text="The operator must log every override decision.",
    )
    request_model = CoreIRProposerRequest.model_validate(payload)
    cache_key = (api_main._CORE_IR_PROPOSER_SURFACE_ID, request_model.client_request_id)
    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY[cache_key] = (
        api_main._CoreIRProposerIdempotencyRecord(
            provider=request_model.provider,
            request_payload_hash=sha256_canonical_json(request_model.idempotency_payload()),
            response_payload={"schema": "invalid.schema@0"},
        )
    )

    status_code, response_payload = _post_proposer(payload)
    assert status_code == 200
    assert response_payload["schema"] == "adeu_core_ir_proposer_response@0.1"

    persisted = get_core_ir_proposer_idempotency_by_client_request_id(
        client_request_id=request_model.client_request_id
    )
    assert persisted is not None
    assert persisted.response_payload["schema"] == "adeu_core_ir_proposer_response@0.1"


def test_v37_k2_replay_is_deterministic_after_process_restart() -> None:
    provider = _mock_provider_for_tests()
    payload = _proposer_payload(
        client_request_id="v37-k2-restart-1",
        provider=provider,
        source_text="The operator must log every override decision.",
    )

    first_status, first_payload = _post_proposer(payload)
    assert first_status == 200

    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()

    probe = dedent(
        """
        import asyncio
        import json
        import sys

        import adeu_api.main as api_main

        payload = json.loads(sys.argv[1])
        cache_clear = getattr(
            api_main._provider_parity_supported_providers_by_surface,
            "cache_clear",
            None,
        )
        if callable(cache_clear):
            cache_clear()
        api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()

        body = json.dumps(payload).encode("utf-8")
        scope = {
            "type": "http",
            "asgi": {"version": "3.0", "spec_version": "2.3"},
            "http_version": "1.1",
            "method": "POST",
            "scheme": "http",
            "path": "/urm/core-ir/propose",
            "raw_path": b"/urm/core-ir/propose",
            "query_string": b"",
            "headers": [
                (b"host", b"testserver"),
                (b"content-type", b"application/json"),
                (b"content-length", str(len(body)).encode("ascii")),
            ],
            "client": ("testclient", 50000),
            "server": ("testserver", 80),
        }
        events = [{"type": "http.request", "body": body, "more_body": False}]
        sent = []

        async def _receive():
            if events:
                return events.pop(0)
            return {"type": "http.disconnect"}

        async def _send(message):
            sent.append(message)

        async def _invoke():
            await api_main.app(scope, _receive, _send)

        asyncio.run(_invoke())

        start = next(message for message in sent if message["type"] == "http.response.start")
        payload_bytes = b"".join(
            message.get("body", b"")
            for message in sent
            if message["type"] == "http.response.body"
        )
        print(
            json.dumps(
                {
                    "status_code": int(start["status"]),
                    "body": json.loads(payload_bytes.decode("utf-8")),
                },
                sort_keys=True,
            )
        )
        """
    )

    env = _pythonpath_env()
    env["ADEU_API_DB_PATH"] = os.environ["ADEU_API_DB_PATH"]
    completed = subprocess.run(
        [sys.executable, "-c", probe, json.dumps(payload, sort_keys=True)],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr

    replay = json.loads(completed.stdout.strip())
    assert replay["status_code"] == 200
    assert replay["body"] == first_payload
