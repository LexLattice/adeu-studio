from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Literal

from adeu_ir import SourceSpan
from adeu_ir.models import JsonPatchOp
from pydantic import BaseModel, ConfigDict, Field

from .analysis import AnalysisAtomRef, ConceptAnalysis, ForcedCountermodel
from .models import (
    Ambiguity,
    AmbiguityOption,
    Claim,
    ConceptIR,
    InferentialLink,
    Term,
    TermSense,
)

QuestionSignal = Literal["mic", "forced_countermodel", "disconnected_clusters"]
QuestionRationaleCode = Literal[
    "mic_conflict",
    "forced_nonentailment",
    "disconnected_cluster",
]

_RATIONALE_CODE_BY_SIGNAL: dict[QuestionSignal, QuestionRationaleCode] = {
    "mic": "mic_conflict",
    "forced_countermodel": "forced_nonentailment",
    "disconnected_clusters": "disconnected_cluster",
}

_RATIONALE_TEXT_BY_CODE: dict[QuestionRationaleCode, str] = {
    "mic_conflict": (
        "This question targets a minimal inconsistent core. Choosing an answer should reduce "
        "or eliminate the conflict set."
    ),
    "forced_nonentailment": (
        "This question targets an edge that is not forced by current constraints. Choosing an "
        "answer should make the intended relation explicit."
    ),
    "disconnected_cluster": (
        "This question targets disconnected term clusters. Choosing an answer should add an "
        "explicit inferential connection."
    ),
}

DEFAULT_MAX_QUESTIONS = 10
DEFAULT_MAX_ANSWERS_PER_QUESTION = 4


class ConceptQuestionAnchor(BaseModel):
    model_config = ConfigDict(extra="forbid")
    object_id: str | None = None
    json_path: str | None = None
    label: str | None = None
    span: SourceSpan | None = None


class ConceptQuestion(BaseModel):
    model_config = ConfigDict(extra="forbid")
    question_id: str
    signal: QuestionSignal
    rationale_code: QuestionRationaleCode
    rationale: str
    prompt: str
    anchors: list[ConceptQuestionAnchor] = Field(default_factory=list)
    answers: list[AmbiguityOption] = Field(default_factory=list)


@dataclass
class _QuestionContext:
    concept: ConceptIR
    term_by_id: dict[str, Term]
    sense_by_id: dict[str, TermSense]
    claim_by_id: dict[str, Claim]
    link_by_id: dict[str, InferentialLink]
    ambiguity_by_id: dict[str, Ambiguity]
    term_to_senses: dict[str, list[str]]
    sense_to_term: dict[str, str]

    @classmethod
    def from_concept(cls, concept: ConceptIR) -> "_QuestionContext":
        term_by_id = {term.id: term for term in concept.terms}
        sense_by_id = {sense.id: sense for sense in concept.senses}
        claim_by_id = {claim.id: claim for claim in concept.claims}
        link_by_id = {link.id: link for link in concept.links}
        ambiguity_by_id = {ambiguity.id: ambiguity for ambiguity in concept.ambiguity}

        term_to_senses: dict[str, list[str]] = {}
        for sense in concept.senses:
            term_to_senses.setdefault(sense.term_id, []).append(sense.id)
        for term_id in list(term_to_senses.keys()):
            term_to_senses[term_id] = sorted(term_to_senses[term_id])

        sense_to_term = {sense.id: sense.term_id for sense in concept.senses}

        return cls(
            concept=concept,
            term_by_id=term_by_id,
            sense_by_id=sense_by_id,
            claim_by_id=claim_by_id,
            link_by_id=link_by_id,
            ambiguity_by_id=ambiguity_by_id,
            term_to_senses=term_to_senses,
            sense_to_term=sense_to_term,
        )

    def span_from_ref(
        self, *, object_id: str | None = None, json_path: str | None = None
    ) -> SourceSpan | None:
        if object_id:
            for lookup in (
                self.claim_by_id,
                self.link_by_id,
                self.sense_by_id,
                self.term_by_id,
            ):
                candidate = lookup.get(object_id)
                span = _span_from_candidate(candidate)
                if span is not None:
                    return span

        path = json_path or ""
        for prefix, entries in (
            ("/claims/", self.concept.claims),
            ("/links/", self.concept.links),
            ("/senses/", self.concept.senses),
            ("/terms/", self.concept.terms),
        ):
            idx = _index_from_pointer(path, prefix=prefix)
            if idx is None:
                continue
            if not (0 <= idx < len(entries)):
                continue
            span = _span_from_candidate(entries[idx])
            if span is not None:
                return span

        return None


def build_concept_questions(
    concept: ConceptIR,
    analysis: ConceptAnalysis,
    *,
    max_questions: int = DEFAULT_MAX_QUESTIONS,
    max_answers_per_question: int = DEFAULT_MAX_ANSWERS_PER_QUESTION,
) -> list[ConceptQuestion]:
    q_cap = max(0, min(max_questions, DEFAULT_MAX_QUESTIONS))
    a_cap = max(0, min(max_answers_per_question, DEFAULT_MAX_ANSWERS_PER_QUESTION))
    if q_cap == 0 or a_cap == 0:
        return []

    context = _QuestionContext.from_concept(concept)
    used_question_ids: set[str] = set()
    used_link_ids = {link.id for link in concept.links}

    questions: list[ConceptQuestion] = []

    for question in _build_mic_questions(
        context,
        analysis,
        used_question_ids=used_question_ids,
        max_answers_per_question=a_cap,
    ):
        if len(questions) >= q_cap:
            break
        questions.append(question)

    for question in _build_forced_questions(
        context,
        analysis,
        used_question_ids=used_question_ids,
        used_link_ids=used_link_ids,
        max_answers_per_question=a_cap,
    ):
        if len(questions) >= q_cap:
            break
        questions.append(question)

    for question in _build_disconnect_questions(
        context,
        used_question_ids=used_question_ids,
        used_link_ids=used_link_ids,
        max_answers_per_question=a_cap,
    ):
        if len(questions) >= q_cap:
            break
        questions.append(question)

    return questions


def _build_mic_questions(
    context: _QuestionContext,
    analysis: ConceptAnalysis,
    *,
    used_question_ids: set[str],
    max_answers_per_question: int,
) -> list[ConceptQuestion]:
    if analysis.mic.status == "UNAVAILABLE":
        return []
    if not analysis.mic.constraints:
        return []

    questions: list[ConceptQuestion] = []
    seen_keys: set[tuple[str, str, str]] = set()
    constraints = sorted(
        analysis.mic.constraints,
        key=lambda item: (
            item.label or "",
            item.object_id or "",
            item.json_path or "",
            item.atom_name,
        ),
    )
    for constraint in constraints:
        key = (constraint.label or "", constraint.object_id or "", constraint.json_path or "")
        if key in seen_keys:
            continue
        seen_keys.add(key)

        question = _question_from_mic_constraint(
            context,
            constraint,
            used_question_ids=used_question_ids,
            max_answers_per_question=max_answers_per_question,
        )
        if question is not None:
            questions.append(question)

    return questions


def _question_from_mic_constraint(
    context: _QuestionContext,
    constraint: AnalysisAtomRef,
    *,
    used_question_ids: set[str],
    max_answers_per_question: int,
) -> ConceptQuestion | None:
    label = constraint.label
    if label == "claim_implication":
        return _question_for_claim_implication(
            context,
            constraint,
            used_question_ids=used_question_ids,
            max_answers_per_question=max_answers_per_question,
        )
    if label == "claim_activation":
        return _question_for_claim_activation(
            context,
            constraint,
            used_question_ids=used_question_ids,
        )
    if label == "ambiguity":
        return _question_for_ambiguity(
            context,
            constraint,
            used_question_ids=used_question_ids,
            max_answers_per_question=max_answers_per_question,
        )
    if label == "link":
        return _question_for_link(
            context,
            constraint,
            used_question_ids=used_question_ids,
            max_answers_per_question=max_answers_per_question,
        )
    return None


def _question_for_claim_implication(
    context: _QuestionContext,
    constraint: AnalysisAtomRef,
    *,
    used_question_ids: set[str],
    max_answers_per_question: int,
) -> ConceptQuestion | None:
    claim_idx = _claim_index(context, constraint.object_id, constraint.json_path)
    if claim_idx is None:
        return None
    claim = context.concept.claims[claim_idx]
    term_id = context.sense_to_term.get(claim.sense_id)
    candidate_senses = context.term_to_senses.get(term_id or "", [])
    if not candidate_senses:
        return None

    answers: list[AmbiguityOption] = []
    for sense_id in candidate_senses:
        answers.append(
            AmbiguityOption(
                option_id=sense_id,
                label=f"Use sense {sense_id}",
                patch=[
                    JsonPatchOp(
                        op="replace",
                        path=f"/claims/{claim_idx}/sense_id",
                        value=sense_id,
                    )
                ],
            )
        )

    anchors = [
        ConceptQuestionAnchor(
            object_id=claim.id,
            json_path=f"/claims/{claim_idx}/sense_id",
            label="claim_implication",
            span=context.span_from_ref(object_id=claim.id),
        )
    ]
    prompt = (
        f"Claim {claim.id} contributes to incoherence via its sense choice. "
        "Which sense is intended?"
    )
    return _build_question(
        question_id_base=f"mic_claim_implication_{claim.id}",
        signal="mic",
        prompt=prompt,
        anchors=anchors,
        answers=answers,
        used_question_ids=used_question_ids,
        max_answers_per_question=max_answers_per_question,
    )


def _question_for_claim_activation(
    context: _QuestionContext,
    constraint: AnalysisAtomRef,
    *,
    used_question_ids: set[str],
) -> ConceptQuestion | None:
    claim_idx = _claim_index(context, constraint.object_id, constraint.json_path)
    if claim_idx is None:
        return None
    claim = context.concept.claims[claim_idx]
    answers = [
        AmbiguityOption(
            option_id=f"remove_{claim.id}",
            label=f"Remove claim {claim.id}",
            patch=[JsonPatchOp(op="remove", path=f"/claims/{claim_idx}")],
        )
    ]
    anchors = [
        ConceptQuestionAnchor(
            object_id=claim.id,
            json_path=f"/claims/{claim_idx}",
            label="claim_activation",
            span=context.span_from_ref(object_id=claim.id),
        )
    ]
    prompt = f"Claim {claim.id} contributes to incoherence. Should this claim be removed?"
    return _build_question(
        question_id_base=f"mic_claim_activation_{claim.id}",
        signal="mic",
        prompt=prompt,
        anchors=anchors,
        answers=answers,
        used_question_ids=used_question_ids,
        max_answers_per_question=1,
    )


def _question_for_ambiguity(
    context: _QuestionContext,
    constraint: AnalysisAtomRef,
    *,
    used_question_ids: set[str],
    max_answers_per_question: int,
) -> ConceptQuestion | None:
    ambiguity_idx = _ambiguity_index(context, constraint.object_id, constraint.json_path)
    if ambiguity_idx is None:
        return None
    ambiguity = context.concept.ambiguity[ambiguity_idx]
    if not ambiguity.options:
        return None

    option_labels = ambiguity.option_labels_by_id or {}
    answers: list[AmbiguityOption] = []

    for option_id in ambiguity.options:
        detail = ambiguity.option_details_by_id.get(option_id)
        if detail is not None and detail.patch:
            patch_ops = [op.model_copy(deep=True) for op in detail.patch]
            label = option_labels.get(option_id) or detail.label or option_id
            answers.append(
                AmbiguityOption(
                    option_id=option_id,
                    label=label,
                    patch=patch_ops,
                )
            )
            continue

        generated = _generated_ambiguity_patch(
            context,
            ambiguity_idx=ambiguity_idx,
            option_id=option_id,
        )
        if not generated:
            continue
        answers.append(
            AmbiguityOption(
                option_id=option_id,
                label=option_labels.get(option_id) or f"Select {option_id}",
                patch=generated,
            )
        )

    term = context.term_by_id.get(ambiguity.term_id)
    term_label = term.label if term is not None else ambiguity.term_id
    anchors = [
        ConceptQuestionAnchor(
            object_id=ambiguity.id,
            json_path=f"/ambiguity/{ambiguity_idx}",
            label="ambiguity",
            span=context.span_from_ref(object_id=ambiguity.term_id),
        )
    ]
    prompt = (
        f"Ambiguity {ambiguity.id} for term '{term_label}' appears in the MIC. "
        "Which option should apply?"
    )
    return _build_question(
        question_id_base=f"mic_ambiguity_{ambiguity.id}",
        signal="mic",
        prompt=prompt,
        anchors=anchors,
        answers=answers,
        used_question_ids=used_question_ids,
        max_answers_per_question=max_answers_per_question,
    )


def _question_for_link(
    context: _QuestionContext,
    constraint: AnalysisAtomRef,
    *,
    used_question_ids: set[str],
    max_answers_per_question: int,
) -> ConceptQuestion | None:
    link_idx = _link_index(context, constraint.object_id, constraint.json_path)
    if link_idx is None:
        return None
    link = context.concept.links[link_idx]

    answers: list[AmbiguityOption] = [
        AmbiguityOption(
            option_id=f"remove_{link.id}",
            label=f"Remove link {link.id}",
            patch=[JsonPatchOp(op="remove", path=f"/links/{link_idx}")],
        )
    ]
    for kind in ("commitment", "presupposition", "incompatibility"):
        if kind == link.kind:
            continue
        answers.append(
            AmbiguityOption(
                option_id=f"set_{link.id}_{kind}",
                label=f"Set {link.id} kind={kind}",
                patch=[
                    JsonPatchOp(
                        op="replace",
                        path=f"/links/{link_idx}/kind",
                        value=kind,
                    )
                ],
            )
        )

    anchors = [
        ConceptQuestionAnchor(
            object_id=link.id,
            json_path=f"/links/{link_idx}",
            label="link",
            span=context.span_from_ref(object_id=link.id),
        )
    ]
    prompt = (
        f"Link {link.id} contributes to incoherence "
        f"({link.src_sense_id} -> {link.dst_sense_id}, kind={link.kind}). "
        "How should this link be revised?"
    )
    return _build_question(
        question_id_base=f"mic_link_{link.id}",
        signal="mic",
        prompt=prompt,
        anchors=anchors,
        answers=answers,
        used_question_ids=used_question_ids,
        max_answers_per_question=max_answers_per_question,
    )


def _generated_ambiguity_patch(
    context: _QuestionContext,
    *,
    ambiguity_idx: int,
    option_id: str,
) -> list[JsonPatchOp]:
    ambiguity = context.concept.ambiguity[ambiguity_idx]
    patch_ops: list[JsonPatchOp] = []
    for idx, claim in enumerate(context.concept.claims):
        if claim.sense_id in ambiguity.options and claim.sense_id != option_id:
            patch_ops.append(
                JsonPatchOp(
                    op="replace",
                    path=f"/claims/{idx}/sense_id",
                    value=option_id,
                )
            )
    patch_ops.append(JsonPatchOp(op="remove", path=f"/ambiguity/{ambiguity_idx}"))
    return patch_ops


def _build_forced_questions(
    context: _QuestionContext,
    analysis: ConceptAnalysis,
    *,
    used_question_ids: set[str],
    used_link_ids: set[str],
    max_answers_per_question: int,
) -> list[ConceptQuestion]:
    if analysis.forced.status == "UNAVAILABLE":
        return []
    if not analysis.forced.countermodels:
        return []

    questions: list[ConceptQuestion] = []
    countermodels = sorted(
        analysis.forced.countermodels,
        key=lambda item: (
            item.src_sense_id,
            item.dst_sense_id,
            item.kind,
            item.solver_status,
        ),
    )
    for countermodel in countermodels:
        question = _question_from_countermodel(
            context,
            countermodel,
            used_question_ids=used_question_ids,
            used_link_ids=used_link_ids,
            max_answers_per_question=max_answers_per_question,
        )
        if question is not None:
            questions.append(question)
    return questions


def _question_from_countermodel(
    context: _QuestionContext,
    countermodel: ForcedCountermodel,
    *,
    used_question_ids: set[str],
    used_link_ids: set[str],
    max_answers_per_question: int,
) -> ConceptQuestion | None:
    existing = {
        (link.src_sense_id, link.dst_sense_id, link.kind) for link in context.concept.links
    }
    candidates = [countermodel.kind]
    if countermodel.kind == "commitment":
        candidates.append("presupposition")
    else:
        candidates.append("commitment")

    answers: list[AmbiguityOption] = []
    for kind in candidates:
        link_key = (countermodel.src_sense_id, countermodel.dst_sense_id, kind)
        if link_key in existing:
            continue
        link_id = _next_link_id(
            f"q_link_{countermodel.src_sense_id}_{countermodel.dst_sense_id}_{kind}",
            used_link_ids,
        )
        answers.append(
            AmbiguityOption(
                option_id=f"{kind}_{countermodel.src_sense_id}_{countermodel.dst_sense_id}",
                label=(
                    f"Add {kind} link "
                    f"{countermodel.src_sense_id}->{countermodel.dst_sense_id}"
                ),
                patch=[
                    JsonPatchOp(
                        op="add",
                        path="/links/-",
                        value={
                            "id": link_id,
                            "kind": kind,
                            "src_sense_id": countermodel.src_sense_id,
                            "dst_sense_id": countermodel.dst_sense_id,
                        },
                    )
                ],
            )
        )

    if not answers:
        return None

    anchors = [
        ConceptQuestionAnchor(
            object_id=countermodel.src_sense_id,
            label="forced_countermodel",
            span=context.span_from_ref(object_id=countermodel.src_sense_id),
        ),
        ConceptQuestionAnchor(
            object_id=countermodel.dst_sense_id,
            label="forced_countermodel",
            span=context.span_from_ref(object_id=countermodel.dst_sense_id),
        ),
    ]
    prompt = (
        "This relation is not forced by the current model evidence: "
        f"{countermodel.src_sense_id} -> {countermodel.dst_sense_id} "
        f"({countermodel.kind}). Should it be asserted explicitly?"
    )
    return _build_question(
        question_id_base=(
            f"forced_{countermodel.src_sense_id}_{countermodel.dst_sense_id}_{countermodel.kind}"
        ),
        signal="forced_countermodel",
        prompt=prompt,
        anchors=anchors,
        answers=answers,
        used_question_ids=used_question_ids,
        max_answers_per_question=max_answers_per_question,
    )


def _build_disconnect_questions(
    context: _QuestionContext,
    *,
    used_question_ids: set[str],
    used_link_ids: set[str],
    max_answers_per_question: int,
) -> list[ConceptQuestion]:
    components = _term_components(context)
    if len(components) <= 1:
        return []

    questions: list[ConceptQuestion] = []
    existing = {
        (link.src_sense_id, link.dst_sense_id, link.kind) for link in context.concept.links
    }

    for left_idx in range(len(components)):
        for right_idx in range(left_idx + 1, len(components)):
            left_component = components[left_idx]
            right_component = components[right_idx]
            left_sense = _representative_sense(context, left_component)
            right_sense = _representative_sense(context, right_component)
            if left_sense is None or right_sense is None:
                continue

            answers: list[AmbiguityOption] = []
            for src, dst, kind in (
                (left_sense, right_sense, "commitment"),
                (left_sense, right_sense, "presupposition"),
                (right_sense, left_sense, "commitment"),
                (right_sense, left_sense, "presupposition"),
            ):
                key = (src, dst, kind)
                if key in existing:
                    continue
                link_id = _next_link_id(f"q_link_{src}_{dst}_{kind}", used_link_ids)
                answers.append(
                    AmbiguityOption(
                        option_id=f"{kind}_{src}_{dst}",
                        label=f"Add {kind} link {src}->{dst}",
                        patch=[
                            JsonPatchOp(
                                op="add",
                                path="/links/-",
                                value={
                                    "id": link_id,
                                    "kind": kind,
                                    "src_sense_id": src,
                                    "dst_sense_id": dst,
                                },
                            )
                        ],
                    )
                )
            if not answers:
                continue

            left_term = left_component[0]
            right_term = right_component[0]
            anchors = [
                ConceptQuestionAnchor(
                    object_id=left_term,
                    label="disconnected_clusters",
                    span=context.span_from_ref(object_id=left_term),
                ),
                ConceptQuestionAnchor(
                    object_id=right_term,
                    label="disconnected_clusters",
                    span=context.span_from_ref(object_id=right_term),
                ),
            ]
            prompt = (
                "These term clusters are disconnected: "
                f"{_cluster_text(context, left_component)} and "
                f"{_cluster_text(context, right_component)}. "
                "Should they be linked?"
            )
            question = _build_question(
                question_id_base=f"disconnect_{left_term}_{right_term}",
                signal="disconnected_clusters",
                prompt=prompt,
                anchors=anchors,
                answers=answers,
                used_question_ids=used_question_ids,
                max_answers_per_question=max_answers_per_question,
            )
            if question is not None:
                questions.append(question)

    return questions


def _build_question(
    *,
    question_id_base: str,
    signal: QuestionSignal,
    prompt: str,
    anchors: list[ConceptQuestionAnchor],
    answers: list[AmbiguityOption],
    used_question_ids: set[str],
    max_answers_per_question: int,
) -> ConceptQuestion | None:
    deduped: dict[str, AmbiguityOption] = {}
    for answer in answers:
        deduped.setdefault(answer.option_id, answer)
    trimmed = list(deduped.values())[:max_answers_per_question]
    if not trimmed:
        return None

    question_id = _next_question_id(question_id_base, used_question_ids)
    rationale_code = _RATIONALE_CODE_BY_SIGNAL[signal]
    return ConceptQuestion(
        question_id=question_id,
        signal=signal,
        rationale_code=rationale_code,
        rationale=_RATIONALE_TEXT_BY_CODE[rationale_code],
        prompt=prompt,
        anchors=anchors,
        answers=trimmed,
    )


def _claim_index(
    context: _QuestionContext, object_id: str | None, json_path: str | None
) -> int | None:
    if object_id:
        for idx, claim in enumerate(context.concept.claims):
            if claim.id == object_id:
                return idx
    idx = _index_from_pointer(json_path or "", prefix="/claims/")
    if idx is None:
        return None
    if 0 <= idx < len(context.concept.claims):
        return idx
    return None


def _link_index(
    context: _QuestionContext, object_id: str | None, json_path: str | None
) -> int | None:
    if object_id:
        for idx, link in enumerate(context.concept.links):
            if link.id == object_id:
                return idx
    idx = _index_from_pointer(json_path or "", prefix="/links/")
    if idx is None:
        return None
    if 0 <= idx < len(context.concept.links):
        return idx
    return None


def _ambiguity_index(
    context: _QuestionContext, object_id: str | None, json_path: str | None
) -> int | None:
    if object_id:
        for idx, ambiguity in enumerate(context.concept.ambiguity):
            if ambiguity.id == object_id:
                return idx
    idx = _index_from_pointer(json_path or "", prefix="/ambiguity/")
    if idx is None:
        return None
    if 0 <= idx < len(context.concept.ambiguity):
        return idx
    return None


def _index_from_pointer(path: str, *, prefix: str) -> int | None:
    if not path.startswith(prefix):
        return None
    token = path[len(prefix) :].split("/")[0]
    try:
        return int(token)
    except ValueError:
        return None


def _span_from_candidate(
    candidate: Term | TermSense | Claim | InferentialLink | None,
) -> SourceSpan | None:
    if candidate is None:
        return None
    provenance = candidate.provenance
    if provenance is None:
        return None
    return provenance.span


def _term_components(context: _QuestionContext) -> list[list[str]]:
    adjacency: dict[str, set[str]] = {term.id: set() for term in context.concept.terms}
    for link in context.concept.links:
        src_term = context.sense_to_term.get(link.src_sense_id)
        dst_term = context.sense_to_term.get(link.dst_sense_id)
        if src_term is None or dst_term is None:
            continue
        adjacency.setdefault(src_term, set()).add(dst_term)
        adjacency.setdefault(dst_term, set()).add(src_term)

    components: list[list[str]] = []
    seen: set[str] = set()
    for term_id in sorted(adjacency.keys()):
        if term_id in seen:
            continue
        frontier = deque([term_id])
        seen.add(term_id)
        component: list[str] = []
        while frontier:
            current = frontier.popleft()
            component.append(current)
            for neighbor in sorted(adjacency.get(current, set())):
                if neighbor in seen:
                    continue
                seen.add(neighbor)
                frontier.append(neighbor)
        components.append(sorted(component))

    return components


def _representative_sense(context: _QuestionContext, component: list[str]) -> str | None:
    candidate_senses: list[str] = []
    for term_id in component:
        candidate_senses.extend(context.term_to_senses.get(term_id, []))
    if not candidate_senses:
        return None
    return sorted(candidate_senses)[0]


def _cluster_text(context: _QuestionContext, component: list[str]) -> str:
    labels: list[str] = []
    for term_id in component[:2]:
        term = context.term_by_id.get(term_id)
        labels.append(term.label if term is not None else term_id)
    if len(component) > 2:
        labels.append(f"+{len(component) - 2} more")
    return ", ".join(labels)


def _next_question_id(base: str, used_question_ids: set[str]) -> str:
    stem = _sanitize_token(base)
    candidate = stem
    suffix = 2
    while candidate in used_question_ids:
        candidate = f"{stem}_{suffix}"
        suffix += 1
    used_question_ids.add(candidate)
    return candidate


def _next_link_id(base: str, used_link_ids: set[str]) -> str:
    stem = _sanitize_token(base)
    candidate = stem
    suffix = 2
    while candidate in used_link_ids:
        candidate = f"{stem}_{suffix}"
        suffix += 1
    used_link_ids.add(candidate)
    return candidate


def _sanitize_token(value: str) -> str:
    cleaned = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in value)
    cleaned = cleaned.strip("_")
    return cleaned or "q"
