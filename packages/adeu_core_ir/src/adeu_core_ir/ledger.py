from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .models import AdeuCoreIR, CoreENode, CoreNode

LEDGER_VERSION_V0_1 = "adeu.sbr.v0_1"


def _clamp_0_1000(value: int) -> int:
    if value < 0:
        return 0
    if value > 1000:
        return 1000
    return value


def _clamp01(value: float) -> float:
    if value < 0.0:
        return 0.0
    if value > 1.0:
        return 1.0
    return value


def _ratio_to_milli(value: float) -> int:
    return _clamp_0_1000(round(1000 * value))


def _display_from_milli(value: int) -> str:
    return f"{value / 1000:.3f}"


@dataclass(frozen=True)
class ClaimLedgerScore:
    claim_id: str
    ledger_version: str
    s_milli: int
    b_milli: int
    r_milli: int
    s: str
    b: str
    r: str


def _claim_node_index(core_ir: AdeuCoreIR) -> dict[str, CoreENode]:
    claims: dict[str, CoreENode] = {}
    for node in core_ir.nodes:
        if isinstance(node, CoreENode) and node.kind == "Claim":
            claims[node.id] = node
    return claims


def _compute_claim_ledger_scores(core_ir: AdeuCoreIR) -> dict[str, ClaimLedgerScore]:
    node_index: dict[str, CoreNode] = {node.id: node for node in core_ir.nodes}
    claim_nodes = _claim_node_index(core_ir)

    supports_to_claim: dict[str, int] = {claim_id: 0 for claim_id in claim_nodes}
    refutes_to_claim: dict[str, int] = {claim_id: 0 for claim_id in claim_nodes}
    dependencies_from_claim: dict[str, list[str]] = {claim_id: [] for claim_id in claim_nodes}

    for edge in core_ir.edges:
        if edge.type == "supports" and edge.to_ref in supports_to_claim:
            supports_to_claim[edge.to_ref] += 1
        elif edge.type == "refutes" and edge.to_ref in refutes_to_claim:
            refutes_to_claim[edge.to_ref] += 1
        elif edge.type == "depends_on" and edge.from_ref in dependencies_from_claim:
            dependencies_from_claim[edge.from_ref].append(edge.to_ref)

    scores: dict[str, ClaimLedgerScore] = {}
    for claim_id, claim_node in claim_nodes.items():
        supports = supports_to_claim[claim_id]
        refutes = refutes_to_claim[claim_id]
        deps = dependencies_from_claim[claim_id]
        total_deps = len(deps)
        resolved_deps = sum(
            1
            for dep_id in deps
            if isinstance(node_index.get(dep_id), CoreENode)
            and node_index[dep_id].kind in {"Claim", "Evidence"}
        )

        evidence_support_ratio = supports / max(1, supports + refutes)
        dependency_resolution_ratio = resolved_deps / max(1, total_deps)
        provenance_anchor_ratio = 1.0 if claim_node.spans else 0.0

        evidence_support_ratio_milli = _ratio_to_milli(evidence_support_ratio)
        dependency_resolution_ratio_milli = _ratio_to_milli(dependency_resolution_ratio)
        provenance_anchor_ratio_milli = _ratio_to_milli(provenance_anchor_ratio)

        s_milli = _clamp_0_1000(
            (
                500 * evidence_support_ratio_milli
                + 300 * dependency_resolution_ratio_milli
                + 200 * provenance_anchor_ratio_milli
                + 500
            )
            // 1000
        )

        confidence = claim_node.confidence if claim_node.confidence is not None else 0.0
        b_milli = _clamp_0_1000(round(1000 * _clamp01(confidence)))
        r_milli = _clamp_0_1000(b_milli - s_milli)

        scores[claim_id] = ClaimLedgerScore(
            claim_id=claim_id,
            ledger_version=LEDGER_VERSION_V0_1,
            s_milli=s_milli,
            b_milli=b_milli,
            r_milli=r_milli,
            s=_display_from_milli(s_milli),
            b=_display_from_milli(b_milli),
            r=_display_from_milli(r_milli),
        )

    return scores


def apply_claim_ledger_scores(
    core_ir: AdeuCoreIR | dict[str, Any],
    *,
    include_display_fields: bool = True,
) -> AdeuCoreIR:
    model = core_ir if isinstance(core_ir, AdeuCoreIR) else AdeuCoreIR.model_validate(core_ir)
    scores = _compute_claim_ledger_scores(model)

    updated_nodes: list[CoreNode] = []
    for node in model.nodes:
        if isinstance(node, CoreENode) and node.kind == "Claim":
            score = scores[node.id]
            updated_nodes.append(
                CoreENode(
                    id=node.id,
                    kind=node.kind,
                    text=node.text,
                    spans=list(node.spans),
                    confidence=node.confidence,
                    ledger_version=score.ledger_version,
                    S_milli=score.s_milli,
                    B_milli=score.b_milli,
                    R_milli=score.r_milli,
                    S=score.s if include_display_fields else None,
                    B=score.b if include_display_fields else None,
                    R=score.r if include_display_fields else None,
                )
            )
        else:
            updated_nodes.append(node)

    payload = model.model_dump(mode="json", by_alias=True, exclude_none=True)
    payload["nodes"] = [
        node.model_dump(mode="json", by_alias=True, exclude_none=True) for node in updated_nodes
    ]
    return AdeuCoreIR.model_validate(payload)


def assert_claim_ledger_recompute_match(core_ir: AdeuCoreIR | dict[str, Any]) -> None:
    model = core_ir if isinstance(core_ir, AdeuCoreIR) else AdeuCoreIR.model_validate(core_ir)
    expected = _compute_claim_ledger_scores(model)

    mismatches: list[str] = []
    for node in model.nodes:
        if not isinstance(node, CoreENode) or node.kind != "Claim":
            continue
        score = expected[node.id]
        display_mismatched = False
        if node.s is not None and node.s != score.s:
            display_mismatched = True
        if node.b is not None and node.b != score.b:
            display_mismatched = True
        if node.r is not None and node.r != score.r:
            display_mismatched = True
        if (
            node.ledger_version != score.ledger_version
            or node.s_milli != score.s_milli
            or node.b_milli != score.b_milli
            or node.r_milli != score.r_milli
            or display_mismatched
        ):
            mismatches.append(node.id)

    if mismatches:
        raise ValueError(
            f"URM_ADEU_CORE_LEDGER_RECOMPUTE_MISMATCH: claims={','.join(sorted(mismatches))}"
        )
