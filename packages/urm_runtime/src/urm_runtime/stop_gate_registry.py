from __future__ import annotations

import re
from collections.abc import Sequence
from pathlib import Path

ACTIVE_STOP_GATE_MANIFEST_VERSIONS: tuple[int, ...] = (
    7,
    8,
    9,
    10,
    11,
    13,
    14,
    15,
    16,
    17,
    18,
    19,
    20,
    21,
    22,
    23,
    24,
    25,
    26,
)
ACTIVE_STOP_GATE_MANIFEST_VERSION_SET: frozenset[int] = frozenset(
    ACTIVE_STOP_GATE_MANIFEST_VERSIONS
)
STOP_GATE_MANIFEST_RELATIVE_TEMPLATE = (
    "apps/api/fixtures/stop_gate/vnext_plus{version}_manifest.json"
)
_MANIFEST_FLAG_PATTERN = re.compile(r"^--vnext-plus(?P<version>\d+)-manifest$")


def discover_repo_root(anchor: Path) -> Path | None:
    resolved = anchor.resolve()
    for parent in (resolved, *resolved.parents):
        if (parent / ".git").exists():
            return parent
    return None


def default_stop_gate_manifest_path(version: int) -> Path:
    if version not in ACTIVE_STOP_GATE_MANIFEST_VERSION_SET:
        raise ValueError(f"unsupported active stop-gate manifest version: {version}")
    module_path = Path(__file__).resolve()
    repo_root = discover_repo_root(module_path)
    if repo_root is None:
        raise FileNotFoundError(
            "repository root not found; stop-gate manifest paths cannot be resolved"
        )
    relative_path = STOP_GATE_MANIFEST_RELATIVE_TEMPLATE.format(version=version)
    return repo_root / relative_path


def parse_stop_gate_manifest_flag_version(token: str) -> int | None:
    match = _MANIFEST_FLAG_PATTERN.match(token)
    if match is None:
        return None
    return int(match.group("version"))


def find_inactive_stop_gate_manifest_flags(argv: Sequence[str]) -> tuple[str, ...]:
    inactive: set[str] = set()
    for token in argv:
        version = parse_stop_gate_manifest_flag_version(token)
        if version is None:
            continue
        if version not in ACTIVE_STOP_GATE_MANIFEST_VERSION_SET:
            inactive.add(token)
    return tuple(sorted(inactive))
