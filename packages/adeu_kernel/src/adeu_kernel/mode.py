from __future__ import annotations

from enum import Enum


class KernelMode(str, Enum):
    STRICT = "STRICT"
    LAX = "LAX"

