from __future__ import annotations

import argparse
import sys
import warnings
from pathlib import Path

warnings.filterwarnings(
    "ignore",
    message=(
        r'Field name "schema" in "AgenticDe.*" shadows an attribute in parent '
        r'"BaseModel"'
    ),
    category=UserWarning,
)

from adeu_agentic_de import (  # noqa: E402
    DEFAULT_ACTION_PROPOSAL_PATH,
    DEFAULT_DOMAIN_PACKET_PATH,
    DEFAULT_INTERACTION_CONTRACT_PATH,
    DEFAULT_MORPH_IR_PATH,
    render_checkpoint_payload,
    render_conformance_payload,
    render_diagnostics_payload,
    run_agentic_de_interaction_v56a,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the dry-run V56-A resident-agent interaction-governance starter over "
            "the committed starter fixtures or explicit input paths."
        )
    )
    parser.add_argument("--domain-packet", type=Path, default=DEFAULT_DOMAIN_PACKET_PATH)
    parser.add_argument("--morph-ir", type=Path, default=DEFAULT_MORPH_IR_PATH)
    parser.add_argument(
        "--interaction-contract",
        type=Path,
        default=DEFAULT_INTERACTION_CONTRACT_PATH,
    )
    parser.add_argument("--action-proposal", type=Path, default=DEFAULT_ACTION_PROPOSAL_PATH)
    parser.add_argument("--checkpoint-output", type=Path, default=None)
    parser.add_argument("--diagnostics-output", type=Path, default=None)
    parser.add_argument("--conformance-output", type=Path, default=None)
    return parser.parse_args(argv)


def _write_text(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        checkpoint, diagnostics, conformance = run_agentic_de_interaction_v56a(
            domain_packet_path=args.domain_packet,
            morph_ir_path=args.morph_ir,
            interaction_contract_path=args.interaction_contract,
            action_proposal_path=args.action_proposal,
        )
    except (FileNotFoundError, ValueError) as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2
    checkpoint_payload = render_checkpoint_payload(checkpoint)
    diagnostics_payload = render_diagnostics_payload(diagnostics)
    conformance_payload = render_conformance_payload(conformance)
    if args.checkpoint_output:
        _write_text(args.checkpoint_output, checkpoint_payload)
    else:
        sys.stdout.write(checkpoint_payload)
    if args.diagnostics_output:
        _write_text(args.diagnostics_output, diagnostics_payload)
    elif any(finding.severity != "info" for finding in diagnostics.findings):
        sys.stderr.write(diagnostics_payload)
    if args.conformance_output:
        _write_text(args.conformance_output, conformance_payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
