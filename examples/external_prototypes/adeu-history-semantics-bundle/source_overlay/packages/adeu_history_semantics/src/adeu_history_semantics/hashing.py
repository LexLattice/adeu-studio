from __future__ import annotations

import hashlib
import json
from typing import Any

try:  # pragma: no cover - exercised in the repo bootstrap path
    from adeu_semantic_forms import canonical_json, sha256_canonical_json
except Exception:  # pragma: no cover - tolerate partial bootstrap environments
    try:  # pragma: no cover - exercised when only urm_runtime is available
        from urm_runtime.hashing import canonical_json, sha256_canonical_json
    except Exception:  # pragma: no cover - bounded fallback for isolated package testing

        def canonical_json(value: Any) -> str:
            return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

        def sha256_canonical_json(value: Any) -> str:
            return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


__all__ = ["canonical_json", "sha256_canonical_json"]
