from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from .errors import URMError
from .hashing import canonical_json
from .instruction_policy import compute_policy_hash, load_instruction_policy


def validate_policy(
    path: Path,
    *,
    strict: bool,
    schema_path: Path | None = None,
) -> dict[str, Any]:
    try:
        policy = load_instruction_policy(policy_path=path, schema_path=schema_path, strict=strict)
    except URMError as exc:
        return {
            "schema": "instruction-policy-validate@1",
            "input": str(path),
            "strict": strict,
            "valid": False,
            "issues": [
                {
                    "code": exc.detail.code,
                    "message": exc.detail.message,
                    "context": exc.detail.context,
                }
            ],
        }

    return {
        "schema": "instruction-policy-validate@1",
        "input": str(path),
        "strict": strict,
        "valid": True,
        "policy_hash": compute_policy_hash(policy),
        "rule_count": len(policy.rules),
        "issues": [],
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="policy",
        description="Instruction policy tooling: validate policy IR documents.",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate_parser = subparsers.add_parser(
        "validate",
        help="Validate an ODEU instruction policy document.",
    )
    validate_parser.add_argument("--in", dest="input_path", type=Path, required=True)
    validate_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    validate_parser.add_argument("--strict", action="store_true")

    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    if args.command == "validate":
        report = validate_policy(
            args.input_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
        )
        print(canonical_json(report))
        return 0 if report["valid"] else 1
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
