#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import sys
import time


def _print_exec_help() -> int:
    ask_supported = os.environ.get("FAKE_CODEX_EXEC_HELP_NO_ASK_FOR_APPROVAL") != "1"
    if os.environ.get("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA") == "1":
        print("Usage: codex exec --json --sandbox <mode> [PROMPT]")
        if ask_supported:
            print("Options: --json --sandbox --ask-for-approval")
        else:
            print("Options: --json --sandbox")
    else:
        print("Usage: codex exec --json --sandbox <mode> [--output-schema <file>] [PROMPT]")
        if ask_supported:
            print("Options: --json --output-schema --sandbox --ask-for-approval")
        else:
            print("Options: --json --output-schema --sandbox")
    return 0


def _print_app_server_help() -> int:
    print("Usage: codex app-server")
    print("Subcommands: generate-json-schema")
    return 0


def _emit_jsonrpc_error(request_id: str | None, message: str) -> None:
    print(
        json.dumps(
            {
                "id": request_id,
                "error": {"code": -32602, "message": message},
            }
        ),
        flush=True,
    )


def _fake_apps() -> list[dict[str, object]]:
    raw = os.environ.get("FAKE_APP_SERVER_APPS_JSON", "").strip()
    if raw:
        try:
            parsed = json.loads(raw)
        except json.JSONDecodeError:
            parsed = None
        if isinstance(parsed, list):
            apps: list[dict[str, object]] = []
            for item in parsed:
                if isinstance(item, dict):
                    apps.append(item)
            if apps:
                return apps
    return [
        {
            "id": "calendar",
            "name": "Calendar",
            "description": "Calendar connector",
            "status": "ready",
        },
        {
            "id": "drive",
            "name": "Drive",
            "description": "Drive connector",
            "status": "ready",
        },
    ]


def _run_app_server() -> int:
    if os.environ.get("FAKE_APP_SERVER_DISABLE_READY") == "1":
        return 3

    if os.environ.get("FAKE_APP_SERVER_SILENT_READY") != "1":
        print(json.dumps({"event": "ready", "type": "ready"}), flush=True)
    thread_id = "thread-fake-1"
    turn_counter = 0
    last_turn_id = ""
    agent_counter = 0
    open_agents: set[str] = set()
    for line in sys.stdin:
        payload = line.rstrip("\n")
        try:
            message = json.loads(payload)
        except json.JSONDecodeError:
            print(json.dumps({"event": "echo", "input": payload}), flush=True)
            continue
        request_id = message.get("id")
        method = message.get("method")
        params = message.get("params", {}) if isinstance(message.get("params"), dict) else {}
        if method == "initialize":
            print(
                json.dumps({"id": request_id, "result": {"userAgent": "codex-fake/1.0.0"}}),
                flush=True,
            )
            continue
        if method == "thread/start":
            print(
                json.dumps(
                    {
                        "id": request_id,
                        "result": {
                            "thread": {"id": thread_id},
                            "approvalPolicy": "never",
                            "cwd": params.get("cwd") or ".",
                            "model": "gpt-fake",
                            "modelProvider": "openai",
                            "sandbox": {"type": "readOnly"},
                        },
                    }
                ),
                flush=True,
            )
            continue
        if method == "turn/start":
            turn_counter += 1
            turn_id = str(turn_counter)
            last_turn_id = turn_id
            input_items = params.get("input")
            text = ""
            if isinstance(input_items, list):
                for item in input_items:
                    if isinstance(item, dict) and item.get("type") == "text":
                        maybe_text = item.get("text")
                        if isinstance(maybe_text, str):
                            text = maybe_text
                            break
            print(
                json.dumps(
                    {
                        "method": "turn/started",
                        "params": {
                            "threadId": thread_id,
                            "turn": {
                                "id": turn_id,
                                "items": [],
                                "status": "inProgress",
                                "error": None,
                            },
                        },
                    }
                ),
                flush=True,
            )
            print(
                json.dumps(
                    {
                        "method": "codex/event/agent_message_delta",
                        "params": {
                            "id": turn_id,
                            "msg": {"type": "agent_message_delta", "delta": text},
                        },
                    }
                ),
                flush=True,
            )
            print(
                json.dumps(
                    {
                        "id": request_id,
                        "result": {
                            "turn": {
                                "id": turn_id,
                                "items": [],
                                "status": "completed",
                                "error": None,
                            }
                        },
                    }
                ),
                flush=True,
            )
            continue
        if method == "turn/steer":
            expected_turn_id = params.get("expectedTurnId")
            if not isinstance(expected_turn_id, str) or not expected_turn_id:
                _emit_jsonrpc_error(request_id, "expectedTurnId required")
                continue
            if last_turn_id and expected_turn_id != last_turn_id:
                _emit_jsonrpc_error(request_id, "expectedTurnId mismatch")
                continue
            print(
                json.dumps(
                    {
                        "method": "codex/event/agent_message_delta",
                        "params": {
                            "id": expected_turn_id,
                            "msg": {"type": "agent_message_delta", "delta": "steered"},
                        },
                    }
                ),
                flush=True,
            )
            print(
                json.dumps({"id": request_id, "result": {"turnId": expected_turn_id}}),
                flush=True,
            )
            continue
        if method == "spawn_agent":
            agent_counter += 1
            new_thread = f"agent-thread-{agent_counter}"
            open_agents.add(new_thread)
            print(
                json.dumps(
                    {
                        "id": request_id,
                        "result": {
                            "newThreadId": new_thread,
                            "senderThreadId": params.get("threadId"),
                        },
                    }
                ),
                flush=True,
            )
            continue
        if method == "send_input":
            receiver = params.get("receiverThreadId")
            if not isinstance(receiver, str) or receiver not in open_agents:
                _emit_jsonrpc_error(request_id, "receiverThreadId not found")
                continue
            print(
                json.dumps(
                    {
                        "id": request_id,
                        "result": {"receiverThreadId": receiver, "accepted": True},
                    }
                ),
                flush=True,
            )
            continue
        if method == "wait":
            receiver = params.get("receiverThreadId")
            if not isinstance(receiver, str) or receiver not in open_agents:
                _emit_jsonrpc_error(request_id, "receiverThreadId not found")
                continue
            wait_secs_raw = os.environ.get("FAKE_APP_SERVER_WAIT_SECS", "").strip()
            if wait_secs_raw:
                try:
                    wait_secs = float(wait_secs_raw)
                except ValueError:
                    wait_secs = 0.0
                if wait_secs > 0:
                    time.sleep(wait_secs)
            print(
                json.dumps(
                    {
                        "id": request_id,
                        "result": {"receiverThreadId": receiver, "status": "completed"},
                    }
                ),
                flush=True,
            )
            continue
        if method == "close_agent":
            receiver = params.get("receiverThreadId")
            if isinstance(receiver, str):
                open_agents.discard(receiver)
            print(
                json.dumps(
                    {"id": request_id, "result": {"receiverThreadId": receiver, "closed": True}}
                ),
                flush=True,
            )
            continue
        if method == "app/list":
            print(
                json.dumps(
                    {
                        "id": request_id,
                        "result": {
                            "apps": _fake_apps(),
                            "cursor": "cursor-1",
                        },
                    }
                ),
                flush=True,
            )
            continue
        if method == "app/list/updated":
            print(
                json.dumps(
                    {
                        "id": request_id,
                        "result": {
                            "apps": _fake_apps(),
                            "cursor": params.get("cursor"),
                            "updated": False,
                        },
                    }
                ),
                flush=True,
            )
            continue
        print(json.dumps({"event": "echo", "input": payload}), flush=True)
    return 0


def _run_exec(argv: list[str]) -> int:
    if os.environ.get("FAKE_CODEX_EXEC_FAIL") == "1":
        print("forced exec failure", file=sys.stderr)
        return 42
    required = ["--json", "--sandbox", "read-only"]
    ask_supported = os.environ.get("FAKE_CODEX_EXEC_HELP_NO_ASK_FOR_APPROVAL") != "1"
    if ask_supported:
        required.extend(["--ask-for-approval", "never"])
    for token in required:
        if token not in argv:
            print(f"missing required token: {token}", file=sys.stderr)
            return 22
    if not ask_supported and "--ask-for-approval" in argv:
        print("ask-for-approval flag unsupported", file=sys.stderr)
        return 25
    if os.environ.get("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA") == "1" and "--output-schema" in argv:
        print("output-schema flag unsupported", file=sys.stderr)
        return 24
    print(json.dumps({"event": "result", "final_output": {"artifact": {"kind": "ok"}}}))
    return 0


def main() -> int:
    argv = sys.argv[1:]
    if not argv:
        print("fake codex", file=sys.stderr)
        return 2
    if argv == ["--version"]:
        print("codex-fake 1.0.0")
        return 0
    if argv[:2] == ["exec", "--help"]:
        return _print_exec_help()
    if argv[:2] == ["app-server", "--help"]:
        return _print_app_server_help()
    if argv[:2] == ["app-server", "generate-json-schema"]:
        print("{}")
        return 0
    if argv[:1] == ["app-server"]:
        return _run_app_server()
    if argv[:1] == ["exec"]:
        return _run_exec(argv[1:])
    print(f"unsupported args: {argv!r}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
