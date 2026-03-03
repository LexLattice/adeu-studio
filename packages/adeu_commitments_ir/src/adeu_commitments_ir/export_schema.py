from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .models import AdeuCommitmentsIR

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _write_schema(path: Path, schema: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(schema, indent=2, sort_keys=True) + "\n"
    path.write_text(payload, encoding="utf-8")


def _assert_no_absolute_path_material(
    value: Any,
    *,
    repo_root_path: Path,
    node_path: str = "$",
) -> None:
    if isinstance(value, dict):
        for key in sorted(value):
            _assert_no_absolute_path_material(
                value[key],
                repo_root_path=repo_root_path,
                node_path=f"{node_path}.{key}",
            )
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _assert_no_absolute_path_material(
                item,
                repo_root_path=repo_root_path,
                node_path=f"{node_path}[{index}]",
            )
        return
    if not isinstance(value, str):
        return

    normalized = value.replace("\\", "/")
    root_text = repo_root_path.as_posix()
    if root_text in normalized:
        raise RuntimeError(
            f"schema export contains repository absolute path material at {node_path}: {value!r}"
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.search(value):
        raise RuntimeError(
            f"schema export contains Windows absolute path material at {node_path}: {value!r}"
        )
    if normalized.startswith("/home/") or normalized.startswith("/Users/"):
        raise RuntimeError(
            f"schema export contains user-home absolute path material at {node_path}: {value!r}"
        )


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema = AdeuCommitmentsIR.model_json_schema(by_alias=True)
    _assert_no_absolute_path_material(schema, repo_root_path=root)

    authoritative_path = (
        root
        / "packages"
        / "adeu_commitments_ir"
        / "schema"
        / "adeu_commitments_ir.v0_1.json"
    )
    mirror_path = root / "spec" / "adeu_commitments_ir.schema.json"
    _write_schema(authoritative_path, schema)
    _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
