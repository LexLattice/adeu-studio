#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import sys


def _print_exec_help() -> int:
    if os.environ.get("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA") == "1":
        print("Usage: codex exec --json --sandbox <mode> [PROMPT]")
        print("Options: --json --sandbox --ask-for-approval")
    else:
        print("Usage: codex exec --json --sandbox <mode> [--output-schema <file>] [PROMPT]")
        print("Options: --json --output-schema --sandbox --ask-for-approval")
    return 0


def _print_app_server_help() -> int:
    print("Usage: codex app-server")
    print("Subcommands: generate-json-schema")
    return 0


def _run_app_server() -> int:
    if os.environ.get("FAKE_APP_SERVER_DISABLE_READY") == "1":
        return 3

    print(json.dumps({"event": "ready", "type": "ready"}), flush=True)
    for line in sys.stdin:
        payload = line.rstrip("\n")
        print(json.dumps({"event": "echo", "input": payload}), flush=True)
    return 0


def _run_exec(argv: list[str]) -> int:
    if os.environ.get("FAKE_CODEX_EXEC_FAIL") == "1":
        print("forced exec failure", file=sys.stderr)
        return 42
    required = ["--json", "--sandbox", "read-only", "--ask-for-approval", "never"]
    for token in required:
        if token not in argv:
            print(f"missing required token: {token}", file=sys.stderr)
            return 22
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
