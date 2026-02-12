from __future__ import annotations

import ast
from pathlib import Path


def test_urm_runtime_has_no_domain_pack_imports() -> None:
    runtime_root = (
        Path(__file__).resolve().parents[3] / "packages" / "urm_runtime" / "src" / "urm_runtime"
    )
    forbidden_prefixes = ("urm_domain_",)
    offenders: list[tuple[str, str]] = []

    for path in sorted(runtime_root.rglob("*.py")):
        module_rel = path.relative_to(runtime_root).as_posix()
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name.startswith(forbidden_prefixes):
                        offenders.append((module_rel, alias.name))
            elif isinstance(node, ast.ImportFrom):
                module = node.module or ""
                if module.startswith(forbidden_prefixes):
                    offenders.append((module_rel, module))

    assert offenders == []
