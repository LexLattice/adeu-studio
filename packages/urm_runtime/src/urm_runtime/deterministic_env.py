from __future__ import annotations

import os
import time
from collections.abc import MutableMapping


EXPECTED_DETERMINISTIC_TOOLING_ENV: dict[str, str] = {
    "TZ": "UTC",
    "LC_ALL": "C",
}


class DeterministicToolingEnvError(ValueError):
    """Raised when deterministic tooling env variables are conflicting."""

    def __init__(self, *, key: str, expected: str, actual: str | None) -> None:
        normalized_actual = "" if actual is None else actual.strip()
        detail = "<empty>" if normalized_actual == "" else normalized_actual
        super().__init__(
            f"deterministic tooling env conflict: expected {key}={expected}, got {detail}"
        )
        self.key = key
        self.expected = expected
        self.actual = normalized_actual


def ensure_deterministic_tooling_env(
    *,
    environ: MutableMapping[str, str] | None = None,
) -> None:
    env = os.environ if environ is None else environ
    tz_was_set = False

    for key, expected in EXPECTED_DETERMINISTIC_TOOLING_ENV.items():
        current = env.get(key)
        if current is None:
            env[key] = expected
            if key == "TZ":
                tz_was_set = True
            continue

        normalized = current.strip()
        if normalized == "":
            raise DeterministicToolingEnvError(key=key, expected=expected, actual=current)
        if normalized != expected:
            raise DeterministicToolingEnvError(key=key, expected=expected, actual=current)

        if current != expected:
            env[key] = expected
            if key == "TZ":
                tz_was_set = True

    if tz_was_set:
        tzset = getattr(time, "tzset", None)
        if callable(tzset):
            tzset()
