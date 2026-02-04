from __future__ import annotations

import hashlib


def stable_id(*parts: str, prefix: str) -> str:
    """
    Deterministic ID helper for fixtures/patch sanity.
    Use: stable_id(doc_ref, f"{start}:{end}", kind, prefix="dnorm")
    """
    joined = "\n".join(parts)
    digest = hashlib.sha256(joined.encode("utf-8")).hexdigest()[:16]
    return f"{prefix}_{digest}"

