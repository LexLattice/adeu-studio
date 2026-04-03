from __future__ import annotations

import re
from itertools import product
from typing import Iterable

from .models import (
    ParseAmbiguity,
    SemanticLexiconEntry,
    SemanticNormalForm,
    SemanticParseCandidate,
    SemanticParseProfile,
    SemanticParseResult,
    SemanticStatementCore,
    sha256_canonical_json,
)

_REPO_PATH_RE = re.compile(r"(?:[A-Za-z0-9_.-]+/)+[A-Za-z0-9_.-]+")
_BOUNDARY_ALNUM_RE = r"[a-z0-9_]"


def _normalize_text(text: str) -> str:
    lowered = text.casefold()
    normalized = re.sub(r"[^a-z0-9_:/.\-]+", " ", lowered)
    normalized = re.sub(r"\s+", " ", normalized).strip()
    return normalized


def _contains_normalized_phrase(normalized_text: str, phrase: str) -> bool:
    normalized_phrase = _normalize_text(phrase)
    if not normalized_phrase:
        return False
    pattern = rf"(?<!{_BOUNDARY_ALNUM_RE}){re.escape(normalized_phrase)}(?!{_BOUNDARY_ALNUM_RE})"
    return re.search(pattern, normalized_text) is not None


def _contains_exact_phrase(text: str, phrase: str) -> bool:
    candidate = phrase.casefold().strip()
    if not candidate:
        return False
    pattern = rf"(?<!{_BOUNDARY_ALNUM_RE}){re.escape(candidate)}(?!{_BOUNDARY_ALNUM_RE})"
    return re.search(pattern, text.casefold()) is not None


def _best_anchor_strength(
    *,
    anchor_id: str,
    aliases: Iterable[object],
    raw_text: str,
    normalized_text: str,
) -> tuple[int, int] | None:
    strengths: list[tuple[int, int]] = []
    if _contains_exact_phrase(raw_text, anchor_id):
        strengths.append((3, len(anchor_id)))
    for alias in aliases:
        alias_text = getattr(alias, "alias")
        alias_kind = getattr(alias, "alias_kind")
        if alias_kind == "exact_phrase" and _contains_exact_phrase(raw_text, alias_text):
            strengths.append((2, len(_normalize_text(alias_text))))
        elif alias_kind == "normalized_phrase" and _contains_normalized_phrase(
            normalized_text, alias_text
        ):
            strengths.append((1, len(_normalize_text(alias_text))))
    return max(strengths) if strengths else None


def _best_lexicon_strength(
    *,
    canonical_value: str,
    aliases: Iterable[object],
    raw_text: str,
    normalized_text: str,
) -> tuple[int, int] | None:
    strengths: list[tuple[int, int]] = []
    if _contains_exact_phrase(raw_text, canonical_value):
        strengths.append((2, len(canonical_value)))
    for alias in aliases:
        alias_text = getattr(alias, "alias")
        alias_kind = getattr(alias, "alias_kind")
        if alias_kind == "exact_phrase" and _contains_exact_phrase(raw_text, alias_text):
            strengths.append((2, len(_normalize_text(alias_text))))
        elif alias_kind == "normalized_phrase" and _contains_normalized_phrase(
            normalized_text, alias_text
        ):
            strengths.append((1, len(_normalize_text(alias_text))))
    return max(strengths) if strengths else None


def _collect_best_anchor_matches(
    *,
    text: str,
    anchors: Iterable[object],
    attr_name: str = "anchor_id",
) -> list[str]:
    raw_text = text.casefold()
    normalized_text = _normalize_text(text)
    scored: list[tuple[tuple[int, int], str]] = []
    for anchor in anchors:
        strength = _best_anchor_strength(
            anchor_id=getattr(anchor, attr_name),
            aliases=getattr(anchor, "aliases"),
            raw_text=raw_text,
            normalized_text=normalized_text,
        )
        if strength is not None:
            scored.append((strength, getattr(anchor, attr_name)))
    if not scored:
        return []
    best_strength = max(strength for strength, _ in scored)
    return sorted({value for strength, value in scored if strength == best_strength})


def _collect_best_lexicon_matches(
    *,
    text: str,
    entries: Iterable[SemanticLexiconEntry],
) -> list[str]:
    raw_text = text.casefold()
    normalized_text = _normalize_text(text)
    scored: list[tuple[tuple[int, int], str]] = []
    for entry in entries:
        strength = _best_lexicon_strength(
            canonical_value=entry.canonical_value,
            aliases=entry.aliases,
            raw_text=raw_text,
            normalized_text=normalized_text,
        )
        if strength is not None:
            scored.append((strength, entry.canonical_value))
    if not scored:
        return []
    best_strength = max(strength for strength, _ in scored)
    return sorted({value for strength, value in scored if strength == best_strength})


def _collect_all_lexicon_matches(
    *,
    text: str,
    entries: Iterable[SemanticLexiconEntry],
) -> list[str]:
    raw_text = text.casefold()
    normalized_text = _normalize_text(text)
    matches: set[str] = set()
    for entry in entries:
        strength = _best_lexicon_strength(
            canonical_value=entry.canonical_value,
            aliases=entry.aliases,
            raw_text=raw_text,
            normalized_text=normalized_text,
        )
        if strength is not None:
            matches.add(entry.canonical_value)
    return sorted(matches)


def _collect_repo_paths(text: str) -> list[str]:
    candidates: set[str] = set()
    for match in _REPO_PATH_RE.findall(text):
        value = match.strip(" .,;:()[]{}<>\"'")
        if value:
            candidates.add(value)
    return sorted(candidates)


def _build_normal_form(
    *,
    profile: SemanticParseProfile,
    scope_anchor_id: str,
    policy_anchor_id: str,
    worker_anchor_id: str,
    mutation_posture: str,
    artifact_kind: str,
    allow_paths: list[str],
    forbid_effects: list[str],
) -> SemanticNormalForm:
    statement_cores = [
        SemanticStatementCore(
            relation_kind="bind_scope_anchor",
            object_value=scope_anchor_id,
            lane_tag="scope",
            object_kind="scope_anchor",
            evidence=[f"scope_anchor:{scope_anchor_id}"],
        ),
        SemanticStatementCore(
            relation_kind="bind_policy_anchor",
            object_value=policy_anchor_id,
            lane_tag="policy",
            object_kind="policy_anchor",
            evidence=[f"policy_anchor:{policy_anchor_id}"],
        ),
        SemanticStatementCore(
            relation_kind="use_worker_subject",
            object_value=worker_anchor_id,
            lane_tag="worker",
            object_kind="worker_subject",
            evidence=[f"worker_anchor:{worker_anchor_id}"],
        ),
        SemanticStatementCore(
            relation_kind="set_mutation_posture",
            object_value=mutation_posture,
            lane_tag="mutation",
            object_kind="mutation_posture",
            evidence=[f"mutation_posture:{mutation_posture}"],
        ),
        SemanticStatementCore(
            relation_kind="produce_artifact_kind",
            object_value=artifact_kind,
            lane_tag="deliverable",
            object_kind="artifact_kind",
            evidence=[f"artifact_kind:{artifact_kind}"],
        ),
    ]
    statement_cores.extend(
        SemanticStatementCore(
            relation_kind="allow_path",
            object_value=path,
            lane_tag="constraint",
            object_kind="repo_rel_path",
            evidence=[f"allow_path:{path}"],
        )
        for path in allow_paths
    )
    statement_cores.extend(
        SemanticStatementCore(
            relation_kind="forbid_effect",
            object_value=effect,
            lane_tag="constraint",
            object_kind="effect_tag",
            evidence=[f"forbid_effect:{effect}"],
        )
        for effect in forbid_effects
    )
    return SemanticNormalForm.model_validate(
        {
            "normal_form_id": "derived-by-model-validator",
            "profile_id": profile.profile_id,
            "domain_kind": profile.domain_kind,
            "statement_cores": [
                core.model_dump(mode="json", by_alias=True, exclude_none=True)
                for core in statement_cores
            ],
            "semantic_hash": "derived-by-model-validator",
            "confidence_band": "medium",
            "uncertainty_notes": [],
        }
    )


def _build_candidate(
    *,
    normal_form: SemanticNormalForm,
    scope_anchor_id: str,
    policy_anchor_id: str,
    worker_anchor_id: str,
    mutation_posture: str,
    artifact_kind: str,
    allow_paths: list[str],
    forbid_effects: list[str],
    candidate_rank: int,
) -> SemanticParseCandidate:
    return SemanticParseCandidate.model_validate(
        {
            "candidate_id": "derived-by-model-validator",
            "candidate_rank": candidate_rank,
            "normal_form": normal_form.model_dump(mode="json", by_alias=True, exclude_none=True),
            "evidence_summary": sorted(
                [
                    f"scope_anchor={scope_anchor_id}",
                    f"policy_anchor={policy_anchor_id}",
                    f"worker_anchor={worker_anchor_id}",
                    f"mutation_posture={mutation_posture}",
                    f"artifact_kind={artifact_kind}",
                ]
                + [f"allow_path={path}" for path in allow_paths]
                + [f"forbid_effect={effect}" for effect in forbid_effects]
            ),
        }
    )


def _dedupe_candidates(
    candidates: Iterable[SemanticParseCandidate],
) -> list[SemanticParseCandidate]:
    deduped_by_hash: dict[str, SemanticParseCandidate] = {}
    for candidate in candidates:
        semantic_hash = candidate.normal_form.semantic_hash
        if semantic_hash in deduped_by_hash:
            existing = deduped_by_hash[semantic_hash]
            existing.evidence_summary = sorted(
                set(existing.evidence_summary) | set(candidate.evidence_summary)
            )
            continue
        deduped_by_hash[semantic_hash] = candidate
    ordered = sorted(deduped_by_hash.values(), key=lambda item: item.normal_form.semantic_hash)
    rebuilt: list[SemanticParseCandidate] = []
    for rank, candidate in enumerate(ordered, start=1):
        rebuilt.append(
            SemanticParseCandidate.model_validate(
                {
                    "candidate_id": "derived-by-model-validator",
                    "candidate_rank": rank,
                    "normal_form": candidate.normal_form.model_dump(
                        mode="json", by_alias=True, exclude_none=True
                    ),
                    "evidence_summary": candidate.evidence_summary,
                }
            )
        )
    return rebuilt


def _build_parse_result(
    *,
    profile: SemanticParseProfile,
    input_text: str,
    parse_status: str,
    candidates: list[SemanticParseCandidate],
    ambiguities: list[ParseAmbiguity],
    rejected_reason_codes: list[str],
    notices: list[str],
) -> SemanticParseResult:
    input_text_hash = sha256_canonical_json({"input_text": input_text})
    return SemanticParseResult.model_validate(
        {
            "schema": "adeu_semantic_parse_result@1",
            "parse_result_id": f"parse:{input_text_hash[:16]}",
            "profile_id": profile.profile_id,
            "input_kind": "natural_language",
            "input_text": input_text,
            "input_text_hash": input_text_hash,
            "parse_status": parse_status,
            "candidates": [
                candidate.model_dump(mode="json", by_alias=True, exclude_none=True)
                for candidate in candidates
            ],
            "ambiguities": [
                ambiguity.model_dump(mode="json", by_alias=True, exclude_none=True)
                for ambiguity in ambiguities
            ],
            "rejected_reason_codes": rejected_reason_codes,
            "notices": notices,
        }
    )


def _build_resolution_ambiguity(
    *,
    ambiguity_id: str,
    alternatives: list[str],
    notes: str,
) -> ParseAmbiguity:
    return ParseAmbiguity(
        ambiguity_id=ambiguity_id,
        ambiguity_kind="missing_required_anchor",
        alternatives=alternatives,
        notes=notes,
    )


def _build_unsupported_result(
    *,
    input_text: str,
    profile: SemanticParseProfile,
    unsupported_hits: list[str],
) -> SemanticParseResult:
    return _build_parse_result(
        profile=profile,
        input_text=input_text,
        parse_status="rejected_unsupported",
        candidates=[],
        ambiguities=[],
        rejected_reason_codes=["ASL-PARSE-UNSUPPORTED"],
        notices=[f"unsupported pattern(s): {', '.join(sorted(unsupported_hits))}"],
    )


def _collect_worker_matches(text: str, profile: SemanticParseProfile) -> list[str]:
    return _collect_best_anchor_matches(text=text, anchors=profile.worker_anchors)


def parse_nl_to_semantic_result(
    *,
    text: str,
    profile: SemanticParseProfile,
) -> SemanticParseResult:
    normalized = _normalize_text(text)
    unsupported_hits = []
    for pattern in profile.unsupported_patterns:
        normalized_pattern = _normalize_text(pattern)
        if not normalized_pattern:
            continue
        if _contains_normalized_phrase(normalized, normalized_pattern):
            unsupported_hits.append(pattern)
    if unsupported_hits:
        return _build_unsupported_result(
            input_text=text,
            profile=profile,
            unsupported_hits=unsupported_hits,
        )

    scope_matches = _collect_best_anchor_matches(text=text, anchors=profile.scope_anchors)
    policy_matches = _collect_best_anchor_matches(text=text, anchors=profile.policy_anchors)
    worker_matches = _collect_worker_matches(text, profile)
    mutation_matches = _collect_best_lexicon_matches(text=text, entries=profile.mutation_lexicon)
    artifact_kind_matches = _collect_best_lexicon_matches(
        text=text, entries=profile.artifact_kind_lexicon
    )
    effect_matches = _collect_all_lexicon_matches(text=text, entries=profile.effect_lexicon)
    path_matches = _collect_repo_paths(text)

    ambiguities: list[ParseAmbiguity] = []

    if not scope_matches:
        ambiguities.append(
            _build_resolution_ambiguity(
                ambiguity_id="missing_scope_anchor",
                alternatives=[],
                notes="No released scope anchor was resolved from the bounded starter calculus.",
            )
        )
    elif len(scope_matches) > 1:
        ambiguities.append(
            ParseAmbiguity(
                ambiguity_id="scope_alternatives",
                ambiguity_kind="multiple_scope_anchor_matches",
                alternatives=scope_matches,
                notes="Input matched more than one released scope anchor alias.",
            )
        )

    if not policy_matches:
        ambiguities.append(
            _build_resolution_ambiguity(
                ambiguity_id="missing_policy_anchor",
                alternatives=[],
                notes="No released policy anchor was resolved from the bounded starter calculus.",
            )
        )
    elif len(policy_matches) > 1:
        ambiguities.append(
            ParseAmbiguity(
                ambiguity_id="policy_alternatives",
                ambiguity_kind="multiple_policy_anchor_matches",
                alternatives=policy_matches,
                notes="Input matched more than one released policy anchor alias.",
            )
        )

    if len(worker_matches) != 1:
        ambiguities.append(
            _build_resolution_ambiguity(
                ambiguity_id="worker_resolution",
                alternatives=worker_matches,
                notes=(
                    "Exactly one released worker anchor must be resolved before "
                    "a canonical semantic object can be licensed."
                ),
            )
        )

    if len(mutation_matches) != 1:
        ambiguities.append(
            _build_resolution_ambiguity(
                ambiguity_id="mutation_resolution",
                alternatives=mutation_matches,
                notes=(
                    "Exactly one released mutation posture must be resolved before "
                    "a canonical semantic object can be licensed."
                ),
            )
        )

    if len(artifact_kind_matches) != 1:
        ambiguities.append(
            _build_resolution_ambiguity(
                ambiguity_id="artifact_kind_resolution",
                alternatives=artifact_kind_matches,
                notes=(
                    "Exactly one released artifact kind must be resolved before "
                    "a canonical semantic object can be licensed."
                ),
            )
        )

    if (
        len(scope_matches) == 0
        or len(policy_matches) == 0
        or len(worker_matches) != 1
        or len(mutation_matches) != 1
        or len(artifact_kind_matches) != 1
    ):
        return _build_parse_result(
            profile=profile,
            input_text=text,
            parse_status="clarification_required",
            candidates=[],
            ambiguities=ambiguities,
            rejected_reason_codes=[],
            notices=[
                "Clarification is required before a canonical semantic object can be licensed."
            ],
        )

    raw_candidates: list[SemanticParseCandidate] = []
    for rank, (scope_anchor_id, policy_anchor_id) in enumerate(
        product(scope_matches, policy_matches),
        start=1,
    ):
        normal_form = _build_normal_form(
            profile=profile,
            scope_anchor_id=scope_anchor_id,
            policy_anchor_id=policy_anchor_id,
            worker_anchor_id=worker_matches[0],
            mutation_posture=mutation_matches[0],
            artifact_kind=artifact_kind_matches[0],
            allow_paths=path_matches,
            forbid_effects=effect_matches,
        )
        raw_candidates.append(
            _build_candidate(
                normal_form=normal_form,
                scope_anchor_id=scope_anchor_id,
                policy_anchor_id=policy_anchor_id,
                worker_anchor_id=worker_matches[0],
                mutation_posture=mutation_matches[0],
                artifact_kind=artifact_kind_matches[0],
                allow_paths=path_matches,
                forbid_effects=effect_matches,
                candidate_rank=rank,
            )
        )

    candidates = _dedupe_candidates(raw_candidates)
    parse_status = "resolved_singleton" if len(candidates) == 1 else "typed_alternatives"
    return _build_parse_result(
        profile=profile,
        input_text=text,
        parse_status=parse_status,
        candidates=candidates,
        ambiguities=ambiguities,
        rejected_reason_codes=[],
        notices=[
            "Natural-language recovery is profile-relative and bounded to released anchors only."
        ],
    )


__all__ = ["parse_nl_to_semantic_result"]
