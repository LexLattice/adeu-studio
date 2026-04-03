from __future__ import annotations

import argparse
import json
from pathlib import Path

from .census import build_symbol_census
from .coverage import build_coverage_report
from .spu import build_semantic_audit

DEFAULT_SCOPE_ID = "architecture_ir.analysis_request_settlement_export.v0"
DEFAULT_SOURCE_PATHS = [
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py",
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py",
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py",
]

def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--scope-id", default=DEFAULT_SCOPE_ID)
    parser.add_argument("--source-path", action="append", default=[])
    args = parser.parse_args()

    source_paths = args.source_path or DEFAULT_SOURCE_PATHS
    census = build_symbol_census(repo_root=args.repo_root, scope_id=args.scope_id, source_paths=source_paths)
    audit = build_semantic_audit(repo_root=args.repo_root, census=census)
    coverage = build_coverage_report(census=census, audit=audit)

    _write_json(args.out_dir / "symbol_census.json", census.model_dump(mode="json"))
    _write_json(args.out_dir / "symbol_semantic_audit.json", audit.model_dump(mode="json"))
    _write_json(args.out_dir / "symbol_audit_coverage_report.json", coverage.model_dump(mode="json"))

    return 0 if coverage.completion_status != "incomplete" else 1

if __name__ == "__main__":
    raise SystemExit(main())
