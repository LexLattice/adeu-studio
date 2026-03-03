from __future__ import annotations

import asyncio
import json
import sys
from typing import Any

import adeu_api.main as api_main


def _clear_local_caches() -> None:
    cache_clear = getattr(
        api_main._provider_parity_supported_providers_by_surface,
        "cache_clear",
        None,
    )
    if callable(cache_clear):
        cache_clear()
    api_main._CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY.clear()


def _post_json(payload: dict[str, Any]) -> tuple[int, Any]:
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
    sent: list[dict[str, Any]] = []

    async def _receive() -> dict[str, Any]:
        if events:
            return events.pop(0)
        return {"type": "http.disconnect"}

    async def _send(message: dict[str, Any]) -> None:
        sent.append(message)

    async def _invoke() -> None:
        await api_main.app(scope, _receive, _send)

    asyncio.run(_invoke())

    start = next(message for message in sent if message["type"] == "http.response.start")
    payload_bytes = b"".join(
        message.get("body", b"")
        for message in sent
        if message["type"] == "http.response.body"
    )
    body_payload = json.loads(payload_bytes.decode("utf-8"))
    return int(start["status"]), body_payload


def main(argv: list[str]) -> int:
    if len(argv) != 1:
        raise SystemExit("expected one argument: payload json")

    payload = json.loads(argv[0])
    if not isinstance(payload, dict):
        raise SystemExit("payload must decode to object")

    _clear_local_caches()
    status_code, body = _post_json(payload)
    print(json.dumps({"status_code": status_code, "body": body}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
