#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
import time
from pathlib import Path


def _append_counter(path: str | None) -> None:
    if not path:
        return
    counter = Path(path)
    counter.parent.mkdir(parents=True, exist_ok=True)
    with counter.open("a", encoding="utf-8") as handle:
        handle.write("1\n")


def main() -> int:
    if len(sys.argv) >= 3 and sys.argv[1] == "exec" and sys.argv[2] == "--help":
        if os.environ.get("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA") != "1":
            print("Usage: codex exec --json --sandbox <mode> [--output-schema <file>] [PROMPT]")
            print("Options: --json --sandbox --ask-for-approval --output-schema")
        else:
            print("Usage: codex exec --json --sandbox <mode> [PROMPT]")
            print("Options: --json --sandbox --ask-for-approval")
        return 0
    if len(sys.argv) < 2 or sys.argv[1] != "exec":
        print("expected exec subcommand", file=sys.stderr)
        return 2
    argv = sys.argv[2:]
    if os.environ.get("FAKE_CODEX_EXEC_FAIL") == "1":
        print("forced exec failure", file=sys.stderr)
        return 42
    required = [
        "--json",
        "--sandbox",
        "read-only",
        "--ask-for-approval",
        "never",
    ]
    for token in required:
        if token not in argv:
            print(f"missing required token: {token}", file=sys.stderr)
            return 22
    if os.environ.get("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA") == "1" and "--output-schema" in argv:
        print("output-schema flag unsupported", file=sys.stderr)
        return 24

    _append_counter(os.environ.get("FAKE_CODEX_CALL_COUNTER_PATH"))
    sleep_s = float(os.environ.get("FAKE_CODEX_SLEEP_SECS", "0"))
    if sleep_s > 0:
        time.sleep(sleep_s)

    fixture_path = os.environ.get("FAKE_CODEX_JSONL_PATH")
    if not fixture_path:
        print('{"type":"result","final_output":{"artifact":{"kind":"empty"}}}')
    else:
        fixture = Path(fixture_path)
        for line in fixture.read_text(encoding="utf-8").splitlines():
            print(line, flush=True)

    return int(os.environ.get("FAKE_CODEX_EXIT_CODE", "0"))


if __name__ == "__main__":
    raise SystemExit(main())
