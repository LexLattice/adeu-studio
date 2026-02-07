from __future__ import annotations

from datetime import datetime, timezone
from typing import Literal

from adeu_kernel import ValidatorBackend, build_validator_backend
from pydantic import BaseModel, ConfigDict, Field

from .models import ConceptIR
from .solver import build_concept_coherence_request

AnalysisStatus = Literal["COMPLETE", "PARTIAL", "UNAVAILABLE"]
ConstraintLabel = Literal["claim_activation", "claim_implication", "ambiguity", "link"]
EdgeKind = Literal["commitment", "presupposition"]

DEFAULT_MAX_SHRINK_ITERS = 50
DEFAULT_MAX_SOLVER_CALLS = 60
DEFAULT_MAX_FORCED_CHECKS = 40
DEFAULT_MAX_SOLVER_CALLS_TOTAL = 80


class AnalysisAtomRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    atom_name: str
    object_id: str | None = None
    json_path: str | None = None
    label: ConstraintLabel | None = None


class ClosureEdge(BaseModel):
    model_config = ConfigDict(extra="forbid")
    src_sense_id: str
    dst_sense_id: str
    kind: EdgeKind


class ClosureResult(BaseModel):
    model_config = ConfigDict(extra="forbid")
    status: AnalysisStatus
    edge_count: int = 0
    edges: list[ClosureEdge] = Field(default_factory=list)
    details: str | None = None


class MicResult(BaseModel):
    model_config = ConfigDict(extra="forbid")
    status: AnalysisStatus
    constraint_count: int = 0
    constraints: list[AnalysisAtomRef] = Field(default_factory=list)
    shrink_iters: int = 0
    solver_calls: int = 0
    details: str | None = None


class ForcedModelAssignment(BaseModel):
    model_config = ConfigDict(extra="forbid")
    symbol: str
    value: str


class ForcedCountermodel(BaseModel):
    model_config = ConfigDict(extra="forbid")
    src_sense_id: str
    dst_sense_id: str
    kind: EdgeKind
    solver_status: Literal["SAT", "UNKNOWN", "TIMEOUT", "INVALID_REQUEST", "ERROR"]
    assignments: list[ForcedModelAssignment] = Field(default_factory=list)
    details: str | None = None


class ForcedResult(BaseModel):
    model_config = ConfigDict(extra="forbid")
    status: AnalysisStatus
    candidate_count: int = 0
    forced_count: int = 0
    forced_edges: list[ClosureEdge] = Field(default_factory=list)
    countermodel_count: int = 0
    countermodels: list[ForcedCountermodel] = Field(default_factory=list)
    solver_calls: int = 0
    details: str | None = None


class ConceptAnalysis(BaseModel):
    model_config = ConfigDict(extra="forbid")
    closure: ClosureResult
    mic: MicResult
    forced: ForcedResult


class ConceptRunAtomRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    object_id: str | None = None
    json_path: str | None = None


class ConceptRunRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    run_id: str | None = None
    created_at: str | None = None
    status: str | None = None
    request_hash: str | None = None
    formula_hash: str | None = None
    evidence_model: dict[str, object] = Field(default_factory=dict)
    evidence_unsat_core: list[str] = Field(default_factory=list)
    evidence_error: str | None = None
    atom_map_json: dict[str, ConceptRunAtomRef] = Field(default_factory=dict)


def unavailable_analysis(*, details: str | None = None) -> ConceptAnalysis:
    return ConceptAnalysis(
        closure=ClosureResult(status="UNAVAILABLE", edge_count=0, edges=[], details=details),
        mic=MicResult(
            status="UNAVAILABLE",
            constraint_count=0,
            constraints=[],
            shrink_iters=0,
            solver_calls=0,
            details=details,
        ),
        forced=ForcedResult(
            status="UNAVAILABLE",
            candidate_count=0,
            forced_count=0,
            forced_edges=[],
            countermodel_count=0,
            countermodels=[],
            solver_calls=0,
            details=details,
        ),
    )


def strip_analysis_details(analysis: ConceptAnalysis) -> ConceptAnalysis:
    return analysis.model_copy(
        update={
            "closure": analysis.closure.model_copy(update={"edges": [], "details": None}),
            "mic": analysis.mic.model_copy(update={"constraints": [], "details": None}),
            "forced": analysis.forced.model_copy(
                update={"forced_edges": [], "countermodels": [], "details": None}
            ),
        }
    )


def strip_forced_details(analysis: ConceptAnalysis) -> ConceptAnalysis:
    return analysis.model_copy(
        update={
            "forced": analysis.forced.model_copy(
                update={"forced_edges": [], "countermodels": [], "details": None}
            ),
        }
    )


def pick_latest_run(runs: list[ConceptRunRef]) -> ConceptRunRef | None:
    if not runs:
        return None
    latest = runs[-1]
    latest_key = _run_key(latest, fallback_index=len(runs) - 1)
    for idx, run in enumerate(runs):
        key = _run_key(run, fallback_index=idx)
        if key > latest_key:
            latest = run
            latest_key = key
    return latest


def analyze_concept(
    concept: ConceptIR,
    *,
    run: ConceptRunRef | None,
    validator_backend: ValidatorBackend | None = None,
    max_shrink_iters: int = DEFAULT_MAX_SHRINK_ITERS,
    max_solver_calls: int = DEFAULT_MAX_SOLVER_CALLS,
    max_forced_checks: int = DEFAULT_MAX_FORCED_CHECKS,
    max_solver_calls_total: int = DEFAULT_MAX_SOLVER_CALLS_TOTAL,
) -> ConceptAnalysis:
    if run is None:
        return unavailable_analysis(details="no validator runs available")

    base_request = build_concept_coherence_request(concept)
    closure = _build_closure(concept, run)
    mic = _build_mic(
        concept,
        run,
        validator_backend=validator_backend,
        max_shrink_iters=max_shrink_iters,
        max_solver_calls=max_solver_calls,
    )
    forced = _build_forced(
        concept,
        run,
        closure=closure,
        base_request=base_request,
        validator_backend=validator_backend,
        max_forced_checks=max_forced_checks,
        max_solver_calls_total=max_solver_calls_total,
    )
    return ConceptAnalysis(closure=closure, mic=mic, forced=forced)


def _parse_timestamp(value: str | None) -> datetime | None:
    if value is None:
        return None
    text = value.strip()
    if not text:
        return None
    normalized = text.replace("Z", "+00:00")
    try:
        parsed = datetime.fromisoformat(normalized)
    except ValueError:
        return None
    if parsed.tzinfo is None:
        return parsed.replace(tzinfo=timezone.utc)
    return parsed


def _run_key(run: ConceptRunRef, *, fallback_index: int) -> tuple[int, datetime, int]:
    created_at = _parse_timestamp(run.created_at)
    has_timestamp = 1 if created_at is not None else 0
    timestamp = created_at if created_at is not None else datetime.min.replace(tzinfo=timezone.utc)
    return (has_timestamp, timestamp, fallback_index)


def _bool_value(value: object) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in {"true", "1"}:
            return True
    return False


def _link_kind_rank(kind: EdgeKind) -> int:
    if kind == "commitment":
        return 0
    return 1


def _build_closure(concept: ConceptIR, run: ConceptRunRef) -> ClosureResult:
    if run.status != "SAT":
        return ClosureResult(
            status="UNAVAILABLE",
            edge_count=0,
            edges=[],
            details=f"closure unavailable for status={run.status or 'UNKNOWN'}",
        )

    request = build_concept_coherence_request(concept)
    sense_symbols = request.payload.metadata.get("sense_symbols", {})
    if not isinstance(sense_symbols, dict):
        sense_symbols = {}
    active_senses = {
        sense_id
        for sense_id, symbol in sense_symbols.items()
        if isinstance(sense_id, str)
        and isinstance(symbol, str)
        and _bool_value(run.evidence_model.get(symbol))
    }

    if not active_senses:
        return ClosureResult(status="COMPLETE", edge_count=0, edges=[], details=None)

    adjacency: dict[str, list[tuple[str, EdgeKind]]] = {}
    for link in concept.links:
        if link.kind not in {"commitment", "presupposition"}:
            continue
        adjacency.setdefault(link.src_sense_id, []).append((link.dst_sense_id, link.kind))

    best_edges: dict[tuple[str, str], EdgeKind] = {}
    for src in sorted(active_senses):
        frontier: list[tuple[str, int]] = [(src, 0)]
        best_rank_by_node: dict[str, int] = {src: 0}
        while frontier:
            node, rank = frontier.pop(0)
            for dst, kind in adjacency.get(node, []):
                edge_rank = _link_kind_rank(kind)
                path_rank = max(rank, edge_rank)
                previous = best_rank_by_node.get(dst)
                if previous is None or path_rank < previous:
                    best_rank_by_node[dst] = path_rank
                    frontier.append((dst, path_rank))

        for dst, rank in best_rank_by_node.items():
            if src == dst:
                continue
            kind: EdgeKind = "commitment" if rank == 0 else "presupposition"
            key = (src, dst)
            prev_kind = best_edges.get(key)
            if prev_kind is None or _link_kind_rank(kind) < _link_kind_rank(prev_kind):
                best_edges[key] = kind

    edges = [
        ClosureEdge(src_sense_id=src, dst_sense_id=dst, kind=kind)
        for (src, dst), kind in sorted(
            best_edges.items(),
            key=lambda item: (item[0][0], item[0][1], _link_kind_rank(item[1]), item[1]),
        )
    ]
    return ClosureResult(status="COMPLETE", edge_count=len(edges), edges=edges, details=None)


def _constraint_label(json_path: str | None) -> ConstraintLabel | None:
    parts = _pointer_segments(json_path)
    if len(parts) == 3 and parts[0] == "claims" and parts[2] == "active":
        return "claim_activation"
    if len(parts) == 3 and parts[0] == "claims" and parts[2] == "sense_id":
        return "claim_implication"
    if len(parts) >= 2 and parts[0] == "ambiguity":
        return "ambiguity"
    if len(parts) >= 2 and parts[0] == "links":
        return "link"
    return None


def _pointer_segments(path: str | None) -> tuple[str, ...]:
    if not path:
        return ()
    text = path if path.startswith("/") else f"/{path}"
    raw = text[1:].split("/")
    return tuple(segment.replace("~1", "/").replace("~0", "~") for segment in raw)


def _build_mic(
    concept: ConceptIR,
    run: ConceptRunRef,
    *,
    validator_backend: ValidatorBackend | None,
    max_shrink_iters: int,
    max_solver_calls: int,
) -> MicResult:
    if run.status != "UNSAT":
        return MicResult(
            status="UNAVAILABLE",
            constraint_count=0,
            constraints=[],
            shrink_iters=0,
            solver_calls=0,
            details=f"mic unavailable for status={run.status or 'UNKNOWN'}",
        )

    base_request = build_concept_coherence_request(concept)
    base_refs: dict[str, AnalysisAtomRef] = {}
    for atom in base_request.payload.atom_map:
        label = _constraint_label(atom.json_path)
        if label is None:
            continue
        base_refs[atom.assertion_name] = AnalysisAtomRef(
            atom_name=atom.assertion_name,
            object_id=atom.object_id,
            json_path=atom.json_path,
            label=label,
        )

    eligible_atoms = sorted(base_refs)
    if not eligible_atoms:
        return MicResult(
            status="UNAVAILABLE",
            constraint_count=0,
            constraints=[],
            shrink_iters=0,
            solver_calls=0,
            details="no eligible constraints available for MIC",
        )

    seed = [name for name in run.evidence_unsat_core if name in base_refs]
    if not seed:
        seed = eligible_atoms.copy()

    backend = validator_backend
    if backend is None:
        try:
            backend = build_validator_backend("z3")
        except RuntimeError as exc:
            constraints = [base_refs[name] for name in sorted(seed)]
            return MicResult(
                status="PARTIAL",
                constraint_count=len(constraints),
                constraints=constraints,
                shrink_iters=0,
                solver_calls=0,
                details=str(exc),
            )

    subset = list(sorted(seed))
    solver_calls = 0
    shrink_iters = 0
    partial_reason: str | None = None
    idx = 0
    while idx < len(subset):
        if shrink_iters >= max_shrink_iters:
            partial_reason = "max_shrink_iters reached"
            break
        if solver_calls >= max_solver_calls:
            partial_reason = "max_solver_calls reached"
            break

        atom_name = subset[idx]
        trial = [name for name in subset if name != atom_name]
        if not trial:
            idx += 1
            continue

        trial_request = build_concept_coherence_request(
            concept,
            included_assertion_names=trial,
        )
        result = backend.run(trial_request)
        solver_calls += 1
        shrink_iters += 1

        if result.status == "UNSAT":
            subset = sorted(trial)
            continue
        if result.status == "SAT":
            idx += 1
            continue
        partial_reason = f"shrink recheck returned {result.status}"
        break

    constraints = [base_refs[name] for name in sorted(subset) if name in base_refs]
    status: AnalysisStatus = "COMPLETE" if partial_reason is None else "PARTIAL"
    return MicResult(
        status=status,
        constraint_count=len(constraints),
        constraints=constraints,
        shrink_iters=shrink_iters,
        solver_calls=solver_calls,
        details=partial_reason,
    )


def _normalized_bool_text(value: object | None) -> str:
    if value is None:
        return "false"
    if isinstance(value, bool):
        return "true" if value else "false"
    text = str(value).strip().lower()
    if text in {"true", "1"}:
        return "true"
    if text in {"false", "0"}:
        return "false"
    return text


def _build_forced(
    concept: ConceptIR,
    run: ConceptRunRef,
    *,
    closure: ClosureResult,
    base_request,
    validator_backend: ValidatorBackend | None,
    max_forced_checks: int,
    max_solver_calls_total: int,
) -> ForcedResult:
    base_solver_calls = 1
    if run.status != "SAT":
        return ForcedResult(
            status="UNAVAILABLE",
            candidate_count=0,
            forced_count=0,
            forced_edges=[],
            countermodel_count=0,
            countermodels=[],
            solver_calls=base_solver_calls,
            details=f"forced unavailable for status={run.status or 'UNKNOWN'}",
        )
    if closure.status != "COMPLETE":
        return ForcedResult(
            status="UNAVAILABLE",
            candidate_count=0,
            forced_count=0,
            forced_edges=[],
            countermodel_count=0,
            countermodels=[],
            solver_calls=base_solver_calls,
            details=f"forced unavailable for closure status={closure.status}",
        )

    candidates = sorted(
        closure.edges,
        key=lambda edge: (
            edge.src_sense_id,
            edge.dst_sense_id,
            _link_kind_rank(edge.kind),
            edge.kind,
        ),
    )
    if not candidates:
        return ForcedResult(
            status="COMPLETE",
            candidate_count=0,
            forced_count=0,
            forced_edges=[],
            countermodel_count=0,
            countermodels=[],
            solver_calls=base_solver_calls,
            details=None,
        )

    backend = validator_backend
    if backend is None:
        try:
            backend = build_validator_backend("z3")
        except RuntimeError as exc:
            return ForcedResult(
                status="PARTIAL",
                candidate_count=len(candidates),
                forced_count=0,
                forced_edges=[],
                countermodel_count=0,
                countermodels=[],
                solver_calls=base_solver_calls,
                details=str(exc),
            )

    metadata = (
        base_request.payload.metadata if isinstance(base_request.payload.metadata, dict) else {}
    )
    sense_symbols = metadata.get("sense_symbols")
    claim_symbols = metadata.get("claim_symbols")
    if not isinstance(sense_symbols, dict):
        sense_symbols = {}
    if not isinstance(claim_symbols, dict):
        claim_symbols = {}

    if max_solver_calls_total <= base_solver_calls:
        return ForcedResult(
            status="PARTIAL",
            candidate_count=len(candidates),
            forced_count=0,
            forced_edges=[],
            countermodel_count=0,
            countermodels=[],
            solver_calls=base_solver_calls,
            details="max_solver_calls_total reached",
        )

    forced_edges: list[ClosureEdge] = []
    countermodels: list[ForcedCountermodel] = []
    partial_reason: str | None = None
    solver_calls = base_solver_calls
    checked = 0

    for edge in candidates:
        if checked >= max_forced_checks:
            partial_reason = "max_forced_checks reached"
            break
        if solver_calls >= max_solver_calls_total:
            partial_reason = "max_solver_calls_total reached"
            break

        src_symbol = sense_symbols.get(edge.src_sense_id)
        dst_symbol = sense_symbols.get(edge.dst_sense_id)
        if not isinstance(src_symbol, str) or not isinstance(dst_symbol, str):
            partial_reason = (
                "forced analysis missing sense symbols for "
                f"{edge.src_sense_id!r}->{edge.dst_sense_id!r}"
            )
            break

        edge_formula = f"(=> {src_symbol} {dst_symbol})"
        trial_payload = base_request.payload.model_copy(
            deep=True,
            update={
                "formula_smt2": base_request.payload.formula_smt2
                + f"(assert (not {edge_formula}))\n",
                "metadata": {
                    **metadata,
                    "forced_edge": {
                        "src_sense_id": edge.src_sense_id,
                        "dst_sense_id": edge.dst_sense_id,
                        "kind": edge.kind,
                    },
                },
            },
        )
        trial_request = base_request.model_copy(deep=True, update={"payload": trial_payload})
        result = backend.run(trial_request)
        solver_calls += 1
        checked += 1

        if result.status == "UNSAT":
            forced_edges.append(edge)
            continue

        if result.status == "SAT":
            relevant_symbols = {
                *[
                    symbol
                    for symbol in sense_symbols.values()
                    if isinstance(symbol, str) and symbol
                ],
                *[
                    symbol
                    for symbol in claim_symbols.values()
                    if isinstance(symbol, str) and symbol
                ],
                src_symbol,
                dst_symbol,
            }
            assignments = [
                ForcedModelAssignment(
                    symbol=symbol,
                    value=_normalized_bool_text(result.evidence.model.get(symbol)),
                )
                for symbol in sorted(relevant_symbols)
            ]
            countermodels.append(
                ForcedCountermodel(
                    src_sense_id=edge.src_sense_id,
                    dst_sense_id=edge.dst_sense_id,
                    kind=edge.kind,
                    solver_status="SAT",
                    assignments=assignments,
                    details=None,
                )
            )
            continue

        solver_status: Literal["UNKNOWN", "TIMEOUT", "INVALID_REQUEST", "ERROR"]
        if result.status in {"UNKNOWN", "TIMEOUT", "INVALID_REQUEST", "ERROR"}:
            solver_status = result.status
        else:
            solver_status = "ERROR"
        countermodels.append(
            ForcedCountermodel(
                src_sense_id=edge.src_sense_id,
                dst_sense_id=edge.dst_sense_id,
                kind=edge.kind,
                solver_status=solver_status,
                assignments=[],
                details=result.evidence.error or f"forced check returned {result.status}",
            )
        )
        partial_reason = f"forced check returned {result.status}"
        break

    forced_edges_sorted = sorted(
        forced_edges,
        key=lambda edge: (
            edge.src_sense_id,
            edge.dst_sense_id,
            _link_kind_rank(edge.kind),
            edge.kind,
        ),
    )
    countermodels_sorted = sorted(
        countermodels,
        key=lambda item: (
            item.src_sense_id,
            item.dst_sense_id,
            _link_kind_rank(item.kind),
            item.kind,
        ),
    )

    status: AnalysisStatus = "COMPLETE" if partial_reason is None else "PARTIAL"
    return ForcedResult(
        status=status,
        candidate_count=len(candidates),
        forced_count=len(forced_edges_sorted),
        forced_edges=forced_edges_sorted,
        countermodel_count=len(countermodels_sorted),
        countermodels=countermodels_sorted,
        solver_calls=solver_calls,
        details=partial_reason,
    )
