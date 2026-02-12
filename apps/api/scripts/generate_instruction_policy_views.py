from __future__ import annotations

import argparse
from pathlib import Path

from urm_runtime.instruction_policy_views import generate_instruction_policy_views


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate instruction-policy markdown views for AGENTS/SKILLS."
    )
    parser.add_argument(
        "--policy",
        type=Path,
        default=None,
        help="Optional instruction policy path (defaults to repo policy/...)",
    )
    parser.add_argument(
        "--agents-out",
        type=Path,
        default=Path("docs/generated/AGENTS_POLICY_VIEW.md"),
        help="Output markdown file for AGENTS policy view",
    )
    parser.add_argument(
        "--skills-out",
        type=Path,
        default=Path("docs/generated/SKILLS_POLICY_VIEW.md"),
        help="Output markdown file for SKILLS policy view",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Check mode: fail if outputs are out of date",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    generate_instruction_policy_views(
        policy_path=args.policy,
        agents_out=args.agents_out,
        skills_out=args.skills_out,
        check=args.check,
    )
    mode = "verified" if args.check else "wrote"
    print(f"{mode} {args.agents_out}")
    print(f"{mode} {args.skills_out}")


if __name__ == "__main__":
    main()
