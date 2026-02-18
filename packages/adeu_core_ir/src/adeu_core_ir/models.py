from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal

from adeu_ir import SourceSpan
from pydantic import BaseModel, ConfigDict, Field, TypeAdapter, model_validator

Layer = Literal["O", "E", "D", "U"]
CoreSchemaVersion = Literal["adeu_core_ir@0.1"]

OKind = Literal["Entity", "Concept", "RelationType"]
EKind = Literal["Claim", "Assumption", "Question", "Evidence"]
DKind = Literal["PhysicalConstraint", "Norm", "Policy", "Exception"]
UKind = Literal["Goal", "Metric", "Preference"]

EdgeType = Literal[
    "about",
    "defines",
    "supports",
    "refutes",
    "depends_on",
    "justifies",
    "gates",
    "serves_goal",
    "prioritizes",
    "excepts",
]


class CoreONode(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    layer: Literal["O"] = "O"
    kind: OKind
    label: str
    aliases: list[str] = Field(default_factory=list)


class CoreENode(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    layer: Literal["E"] = "E"
    kind: EKind
    text: str
    spans: list[SourceSpan] = Field(default_factory=list)
    confidence: float | None = None
    ledger_version: str | None = None
    s_milli: int | None = Field(default=None, alias="S_milli")
    b_milli: int | None = Field(default=None, alias="B_milli")
    r_milli: int | None = Field(default=None, alias="R_milli")
    s: str | None = Field(default=None, alias="S")
    b: str | None = Field(default=None, alias="B")
    r: str | None = Field(default=None, alias="R")

    @model_validator(mode="after")
    def _validate_ledger_fields(self) -> "CoreENode":
        if self.ledger_version is not None and self.ledger_version != "adeu.sbr.v0_1":
            raise ValueError("ledger_version must equal 'adeu.sbr.v0_1' when present")
        for value, name in (
            (self.s_milli, "S_milli"),
            (self.b_milli, "B_milli"),
            (self.r_milli, "R_milli"),
        ):
            if value is not None and not (0 <= value <= 1000):
                raise ValueError(f"{name} must be within 0..1000")
        return self


class CoreDNode(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    layer: Literal["D"] = "D"
    kind: DKind
    label: str
    constraint_kind: (
        Literal["mechanism", "resource_limit", "invariant", "law", "assumption"] | None
    ) = None
    modality: Literal["obligatory", "forbidden", "permitted"] | None = None
    condition: str | None = None
    target: str | None = None
    priority: int | None = None


class CoreUNode(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    layer: Literal["U"] = "U"
    kind: UKind
    label: str
    weight: float | None = None


CoreNode = CoreONode | CoreENode | CoreDNode | CoreUNode
_CORE_NODE_ADAPTER = TypeAdapter(CoreNode)


class CoreEdge(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    type: EdgeType
    from_ref: str = Field(alias="from")
    to_ref: str = Field(alias="to")

    @property
    def identity(self) -> tuple[EdgeType, str, str]:
        return (self.type, self.from_ref, self.to_ref)


def _node_signature(node: CoreNode) -> str:
    return f"{node.layer}.{node.kind}"


_EDGE_TYPING_MATRIX: dict[EdgeType, tuple[set[str], set[str]]] = {
    "about": (
        {"E.Claim", "E.Assumption", "E.Question", "E.Evidence"},
        {"O.Entity", "O.Concept", "O.RelationType"},
    ),
    "defines": (
        {"E.Claim", "E.Evidence"},
        {"O.Concept", "O.RelationType"},
    ),
    "supports": (
        {"E.Evidence", "E.Claim"},
        {"E.Claim"},
    ),
    "refutes": (
        {"E.Evidence", "E.Claim"},
        {"E.Claim"},
    ),
    "depends_on": (
        {"E.Claim"},
        {"E.Claim", "E.Assumption", "E.Question", "E.Evidence"},
    ),
    "justifies": (
        {"E.Claim", "E.Evidence"},
        {"D.Norm", "D.Policy"},
    ),
    "gates": (
        {"D.Policy"},
        {"E.Claim", "E.Assumption", "E.Question"},
    ),
    "serves_goal": (
        {"D.PhysicalConstraint", "D.Norm", "D.Policy", "E.Claim"},
        {"U.Goal", "U.Metric"},
    ),
    "prioritizes": (
        {"U.Preference"},
        {"U.Goal", "U.Metric", "D.PhysicalConstraint", "D.Norm", "D.Policy", "D.Exception"},
    ),
    "excepts": (
        {"D.Exception"},
        {"D.PhysicalConstraint", "D.Norm", "D.Policy"},
    ),
}

_LAYER_ORDER: dict[Layer, int] = {"O": 0, "E": 1, "D": 2, "U": 3}


def canonical_node_sort_key(node: CoreNode) -> tuple[int, str, str]:
    return (_LAYER_ORDER[node.layer], node.kind, node.id)


def canonical_edge_sort_key(edge: CoreEdge) -> tuple[EdgeType, str, str]:
    return edge.identity


class AdeuCoreIR(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: CoreSchemaVersion = "adeu_core_ir@0.1"
    source_text_hash: str
    source_text: str | None = None
    metadata: dict[str, Any] | None = None
    nodes: list[CoreNode] = Field(default_factory=list)
    edges: list[CoreEdge] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuCoreIR":
        sorted_nodes = sorted(self.nodes, key=canonical_node_sort_key)
        if self.nodes != sorted_nodes:
            raise ValueError("nodes must be sorted by (layer, kind, id)")

        sorted_edges = sorted(self.edges, key=canonical_edge_sort_key)
        if self.edges != sorted_edges:
            raise ValueError("edges must be sorted by (type, from, to)")

        node_index: dict[str, CoreNode] = {}
        for node in self.nodes:
            if node.id in node_index:
                raise ValueError(f"duplicate node id: {node.id}")
            node_index[node.id] = node

        seen_edges: set[tuple[EdgeType, str, str]] = set()
        for edge in self.edges:
            if edge.identity in seen_edges:
                raise ValueError(f"duplicate edge identity: {edge.identity}")
            seen_edges.add(edge.identity)

            from_node = node_index.get(edge.from_ref)
            to_node = node_index.get(edge.to_ref)
            if from_node is None or to_node is None:
                raise ValueError(f"dangling edge reference: from={edge.from_ref} to={edge.to_ref}")

            allowed_from, allowed_to = _EDGE_TYPING_MATRIX[edge.type]
            from_sig = _node_signature(from_node)
            to_sig = _node_signature(to_node)
            if from_sig not in allowed_from or to_sig not in allowed_to:
                raise ValueError(
                    f"edge typing violation type={edge.type} from={from_sig} to={to_sig}"
                )

        return self


def canonicalize_core_ir_payload(payload: dict[str, Any]) -> dict[str, Any]:
    normalized = deepcopy(payload)
    raw_nodes = normalized.get("nodes")
    if raw_nodes is None:
        raw_nodes = []
    if not isinstance(raw_nodes, list):
        raise ValueError("nodes must be a list")

    raw_edges = normalized.get("edges")
    if raw_edges is None:
        raw_edges = []
    if not isinstance(raw_edges, list):
        raise ValueError("edges must be a list")

    nodes: list[CoreNode] = [_CORE_NODE_ADAPTER.validate_python(item) for item in raw_nodes]
    edges: list[CoreEdge] = [CoreEdge.model_validate(item) for item in raw_edges]

    canonical_edges: list[CoreEdge] = []
    for identity in sorted({edge.identity for edge in edges}):
        canonical_edges.append(
            CoreEdge.model_validate({"type": identity[0], "from": identity[1], "to": identity[2]})
        )

    normalized["nodes"] = [
        node.model_dump(mode="json", by_alias=True, exclude_none=True)
        for node in sorted(nodes, key=canonical_node_sort_key)
    ]
    normalized["edges"] = [
        edge.model_dump(mode="json", by_alias=True, exclude_none=True) for edge in canonical_edges
    ]
    return normalized


def canonicalize_core_ir(core_ir: AdeuCoreIR | dict[str, Any]) -> AdeuCoreIR:
    payload = (
        core_ir.model_dump(mode="json", by_alias=True, exclude_none=True)
        if isinstance(core_ir, AdeuCoreIR)
        else dict(core_ir)
    )
    canonical_payload = canonicalize_core_ir_payload(payload)
    return AdeuCoreIR.model_validate(canonical_payload)
