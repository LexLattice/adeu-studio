from __future__ import annotations

import hashlib
import json

import pytest
from adeu_core_ir import (
    AdeuTrustInvariantPacket,
    canonicalize_trust_invariant_packet_payload,
)


def _proof_id(
    *,
    invariant_code: str,
    status: str,
    justification_refs: list[str],
    expected_hash: str | None = None,
    observed_hash: str | None = None,
) -> str:
    payload: dict[str, object] = {
        "invariant_code": invariant_code,
        "status": status,
        "justification_refs": justification_refs,
    }
    if expected_hash is not None:
        payload["expected_hash"] = expected_hash
    if observed_hash is not None:
        payload["observed_hash"] = observed_hash
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


def _minimal_payload() -> dict[str, object]:
    source_text_hash = "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa"
    core_ir_artifact_id = "core_ir.case_a_1"
    concept_artifact_id = "concept.case_a_1"
    coherence_ref = (
        "artifact:adeu_cross_ir_coherence_diagnostics@0.1:"
        f"{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
    )
    normative_ref = (
        "artifact:adeu_normative_advice_packet@0.1:"
        f"{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
    )
    trust_ref = (
        "artifact:adeu_trust_invariant_packet@0.1:"
        f"{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
    )

    hash_a = "3f0de140e2078c6f5492a3e6f9b06d0077d166da20c4c00da61152e85c51bb53"
    hash_b = "89f6517f4f88f92f4ef81de08c557f7f3f843fce3ebafe46d8394f4ac316ec2f"
    hash_c = "e6cc53eb491ea141b5c965a83358ed64f8693af9af33b2bfcd5f53b164f14cf6"

    proof_items = [
        {
            "invariant_code": "CANONICAL_JSON_CONFORMANCE",
            "status": "pass",
            "justification_refs": [coherence_ref, normative_ref],
            "message": "canonical-json conformance checks passed",
        },
        {
            "invariant_code": "HASH_RECOMPUTE_MATCH",
            "status": "pass",
            "justification_refs": [normative_ref],
            "expected_hash": hash_b,
            "observed_hash": hash_b,
            "message": "hash recompute parity checks passed",
        },
        {
            "invariant_code": "MANIFEST_CHAIN_STABILITY",
            "status": "pass",
            "justification_refs": [coherence_ref, normative_ref],
            "expected_hash": hash_a,
            "observed_hash": hash_a,
            "message": "manifest chain checks passed",
        },
        {
            "invariant_code": "REPLAY_HASH_STABILITY",
            "status": "pass",
            "justification_refs": [trust_ref],
            "observed_hash": hash_c,
            "message": "replay hash checks passed",
        },
    ]

    for item in proof_items:
        item["proof_id"] = _proof_id(
            invariant_code=str(item["invariant_code"]),
            status=str(item["status"]),
            justification_refs=list(item["justification_refs"]),  # type: ignore[arg-type]
            expected_hash=item.get("expected_hash"),  # type: ignore[arg-type]
            observed_hash=item.get("observed_hash"),  # type: ignore[arg-type]
        )

    return {
        "schema": "adeu_trust_invariant_packet@0.1",
        "source_text_hash": source_text_hash,
        "core_ir_artifact_id": core_ir_artifact_id,
        "concept_artifact_id": concept_artifact_id,
        "bridge_manifest_hash": hash_a,
        "normative_advice_packet_hash": hash_b,
        "proof_summary": {
            "total_checks": 4,
            "passed_checks": 4,
            "failed_checks": 0,
            "counts_by_invariant_code": {
                "CANONICAL_JSON_CONFORMANCE": 1,
                "HASH_RECOMPUTE_MATCH": 1,
                "MANIFEST_CHAIN_STABILITY": 1,
                "REPLAY_HASH_STABILITY": 1,
            },
            "counts_by_status": {"pass": 4},
        },
        "proof_items": proof_items,
    }


def test_trust_invariant_packet_model_validate_minimal_payload() -> None:
    normalized = AdeuTrustInvariantPacket.model_validate(_minimal_payload())

    assert normalized.schema == "adeu_trust_invariant_packet@0.1"
    assert normalized.proof_summary.total_checks == 4
    assert [item.invariant_code for item in normalized.proof_items] == [
        "CANONICAL_JSON_CONFORMANCE",
        "HASH_RECOMPUTE_MATCH",
        "MANIFEST_CHAIN_STABILITY",
        "REPLAY_HASH_STABILITY",
    ]


def test_canonicalize_trust_invariant_packet_payload_normalizes_valid_payload() -> None:
    canonical = canonicalize_trust_invariant_packet_payload(_minimal_payload())
    assert canonical["schema"] == "adeu_trust_invariant_packet@0.1"
    assert canonical["proof_summary"]["counts_by_status"] == {"pass": 4}
    assert canonical["proof_items"][3]["invariant_code"] == "REPLAY_HASH_STABILITY"


def test_trust_invariant_packet_rejects_replay_justification_without_self_ref() -> None:
    payload = _minimal_payload()
    replay = payload["proof_items"][3]  # type: ignore[index]
    replay["justification_refs"] = [  # type: ignore[index]
        payload["proof_items"][1]["justification_refs"][0]  # type: ignore[index]
    ]
    replay["proof_id"] = _proof_id(
        invariant_code="REPLAY_HASH_STABILITY",
        status="pass",
        justification_refs=replay["justification_refs"],  # type: ignore[arg-type]
        observed_hash=replay["observed_hash"],  # type: ignore[arg-type]
    )
    with pytest.raises(ValueError):
        AdeuTrustInvariantPacket.model_validate(payload)


def test_trust_invariant_packet_rejects_uppercase_hash() -> None:
    payload = _minimal_payload()
    payload["normative_advice_packet_hash"] = "A" * 64
    with pytest.raises(ValueError):
        AdeuTrustInvariantPacket.model_validate(payload)
