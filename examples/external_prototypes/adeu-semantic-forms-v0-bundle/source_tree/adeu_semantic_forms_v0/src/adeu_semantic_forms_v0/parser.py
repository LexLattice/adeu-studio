from __future__ import annotations

import re
from itertools import product

from .models import (
    ParseAmbiguity,
    SemanticClause,
    SemanticNormalForm,
    SemanticParseCandidate,
    SemanticParseProfile,
    SemanticParseResult,
)

_REPO_PATH_RE = re.compile(r"(?:[A-Za-z0-9_.-]+/)+[A-Za-z0-9_.-]+")


def _normalize_text(text: str) -> str:
    lowered = text.casefold()
    normalized = re.sub(r"[^a-z0-9_:/.\-]+", " ", lowered)
    normalized = re.sub(r"\s+", " ", normalized).strip()
    return normalized


def _alias_matches(normalized_text: str, alias: str) -> bool:
    alias_norm = _normalize_text(alias)
    return alias_norm in normalized_text


def _best_anchor_matches(anchors, normalized: str, attr_name: str = "anchor_id") -> list[str]:
    scored: list[tuple[int, str]] = []
    for anchor in anchors:
        score = max((len(_normalize_text(alias.alias)) for alias in anchor.aliases if _alias_matches(normalized, alias.alias)), default=0)
        if score > 0:
            scored.append((score, getattr(anchor, attr_name)))
    if not scored:
        return []
    best = max(score for score, _ in scored)
    return sorted(dict.fromkeys(anchor_id for score, anchor_id in scored if score == best))


def _collect_scope_anchor_matches(text: str, profile: SemanticParseProfile) -> list[str]:
    normalized = _normalize_text(text)
    return _best_anchor_matches(profile.scope_anchors, normalized)


def _collect_policy_anchor_matches(text: str, profile: SemanticParseProfile) -> list[str]:
    normalized = _normalize_text(text)
    return _best_anchor_matches(profile.policy_anchors, normalized)


def _collect_worker_matches(text: str, profile: SemanticParseProfile) -> list[str]:
    normalized = _normalize_text(text)
    return _best_anchor_matches(profile.worker_anchors, normalized)


def _collect_mutation_matches(text: str, profile: SemanticParseProfile) -> list[str]:
    normalized = _normalize_text(text)
    matches: list[str] = []
    for entry in profile.mutation_lexicon:
        if any(_alias_matches(normalized, alias.alias) for alias in entry.aliases):
            matches.append(entry.canonical_value)
    return sorted(dict.fromkeys(matches))


def _collect_artifact_kind_matches(text: str, profile: SemanticParseProfile) -> list[str]:
    normalized = _normalize_text(text)
    matches: list[str] = []
    for entry in profile.artifact_kind_lexicon:
        if any(_alias_matches(normalized, alias.alias) for alias in entry.aliases):
            matches.append(entry.canonical_value)
    return sorted(dict.fromkeys(matches))


def _collect_effect_matches(text: str, profile: SemanticParseProfile) -> list[str]:
    normalized = _normalize_text(text)
    matches: list[str] = []
    for entry in profile.effect_lexicon:
        if any(_alias_matches(normalized, alias.alias) for alias in entry.aliases):
            matches.append(entry.canonical_value)
    return sorted(dict.fromkeys(matches))


def _collect_repo_paths(text: str) -> list[str]:
    candidates = []
    for match in _REPO_PATH_RE.findall(text):
        if "/" not in match:
            continue
        value = match.strip(" .,;:()[]{}<>\"'")
        if value:
            candidates.append(value)
    return sorted(dict.fromkeys(candidates))


def _build_candidate(
    *,
    profile_id: str,
    scope_anchor_id: str,
    policy_anchor_id: str,
    worker_anchor_id: str,
    mutation_posture: str,
    artifact_kind: str,
    allow_paths: list[str],
    forbid_effects: list[str],
) -> SemanticNormalForm:
    clauses = [
        SemanticClause(
            relation_kind="bind_scope_anchor",
            object_value=scope_anchor_id,
            lane_tag="scope",
            object_kind="scope_anchor",
            evidence=[f"scope_anchor:{scope_anchor_id}"],
        ),
        SemanticClause(
            relation_kind="bind_policy_anchor",
            object_value=policy_anchor_id,
            lane_tag="policy",
            object_kind="policy_anchor",
            evidence=[f"policy_anchor:{policy_anchor_id}"],
        ),
        SemanticClause(
            relation_kind="use_worker_subject",
            object_value=worker_anchor_id,
            lane_tag="worker",
            object_kind="worker_subject",
            evidence=[f"worker_anchor:{worker_anchor_id}"],
        ),
        SemanticClause(
            relation_kind="set_mutation_posture",
            object_value=mutation_posture,
            lane_tag="mutation",
            object_kind="mutation_posture",
            evidence=[f"mutation_posture:{mutation_posture}"],
        ),
        SemanticClause(
            relation_kind="produce_artifact_kind",
            object_value=artifact_kind,
            lane_tag="deliverable",
            object_kind="artifact_kind",
            evidence=[f"artifact_kind:{artifact_kind}"],
        ),
    ]
    clauses.extend(
        SemanticClause(
            relation_kind="allow_path",
            object_value=path,
            lane_tag="constraint",
            object_kind="repo_rel_path",
            evidence=[f"allow_path:{path}"],
        )
        for path in allow_paths
    )
    clauses.extend(
        SemanticClause(
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
            "profile_id": profile_id,
            "clauses": [clause.model_dump(mode="json") for clause in clauses],
            "semantic_hash": "derived-by-model-validator",
        }
    )


def parse_nl_to_semantic_form(
    *,
    text: str,
    profile: SemanticParseProfile,
) -> SemanticParseResult:
    normalized = _normalize_text(text)
    unsupported_hits = []
    for pattern in profile.unsupported_patterns:
        pat = _normalize_text(pattern)
        if not pat:
            continue
        # Require whole-phrase token boundary match rather than raw substring match.
        if re.search(rf"(?<![a-z0-9_]){re.escape(pat)}(?![a-z0-9_])", normalized):
            unsupported_hits.append(pattern)
    if unsupported_hits:
        return SemanticParseResult.model_validate(
            {
                "profile_id": profile.profile_id,
                "input_text": text,
                "input_text_hash": "derived-by-model-validator",
                "parse_status": "rejected_unsupported",
                "candidates": [],
                "ambiguities": [],
                "rejected_reason_codes": ["ASL-PARSE-UNSUPPORTED"],
                "notices": [f"unsupported pattern(s): {', '.join(sorted(unsupported_hits))}"],
                "parse_result_id": "derived-by-model-validator",
            }
        )

    scope_matches = _collect_scope_anchor_matches(text, profile)
    policy_matches = _collect_policy_anchor_matches(text, profile)
    worker_matches = _collect_worker_matches(text, profile) or [
        "worker:repo_internal_single_codex_worker:default"
    ]
    mutation_matches = _collect_mutation_matches(text, profile) or ["read_only"]
    artifact_kind_matches = _collect_artifact_kind_matches(text, profile) or [
        "taskpack_binding_spec_seed"
    ]
    effect_matches = _collect_effect_matches(text, profile)
    path_matches = _collect_repo_paths(text)

    ambiguities: list[ParseAmbiguity] = []
    if not scope_matches:
        ambiguities.append(
            ParseAmbiguity(
                ambiguity_id="missing_scope",
                ambiguity_kind="missing_required_anchor",
                alternatives=[],
                notes="No released scope anchor could be recovered from input text.",
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
            ParseAmbiguity(
                ambiguity_id="missing_policy",
                ambiguity_kind="missing_required_anchor",
                alternatives=[],
                notes="No released policy anchor could be recovered from input text.",
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

    if any(ambiguity.ambiguity_kind == "missing_required_anchor" for ambiguity in ambiguities):
        return SemanticParseResult.model_validate(
            {
                "profile_id": profile.profile_id,
                "input_text": text,
                "input_text_hash": "derived-by-model-validator",
                "parse_status": "clarification_required",
                "candidates": [],
                "ambiguities": [item.model_dump(mode="json") for item in ambiguities],
                "rejected_reason_codes": [],
                "notices": ["Required semantic anchors were missing."],
                "parse_result_id": "derived-by-model-validator",
            }
        )

    candidates = []
    for rank, (scope_anchor, policy_anchor) in enumerate(product(scope_matches, policy_matches), start=1):
        normal_form = _build_candidate(
            profile_id=profile.profile_id,
            scope_anchor_id=scope_anchor,
            policy_anchor_id=policy_anchor,
            worker_anchor_id=worker_matches[0],
            mutation_posture=mutation_matches[0],
            artifact_kind=artifact_kind_matches[0],
            allow_paths=path_matches,
            forbid_effects=effect_matches,
        )
        candidates.append(
            SemanticParseCandidate(
                candidate_id=f"candidate:{normal_form.semantic_hash[:12]}",
                candidate_rank=rank,
                normal_form=normal_form,
                evidence_summary=sorted(
                    [
                        f"scope_anchor={scope_anchor}",
                        f"policy_anchor={policy_anchor}",
                        f"worker_anchor={worker_matches[0]}",
                        f"mutation_posture={mutation_matches[0]}",
                        f"artifact_kind={artifact_kind_matches[0]}",
                    ]
                    + [f"allow_path={path}" for path in path_matches]
                    + [f"forbid_effect={effect}" for effect in effect_matches]
                ),
            )
        )

    parse_status = "resolved_singleton" if len(candidates) == 1 else "typed_alternatives"
    return SemanticParseResult.model_validate(
        {
            "profile_id": profile.profile_id,
            "input_text": text,
            "input_text_hash": "derived-by-model-validator",
            "parse_status": parse_status,
            "candidates": [candidate.model_dump(mode="json") for candidate in candidates],
            "ambiguities": [item.model_dump(mode="json") for item in ambiguities],
            "rejected_reason_codes": [],
            "notices": [
                "Natural-language recovery is profile-relative and bounded to released anchors only."
            ],
            "parse_result_id": "derived-by-model-validator",
        }
    )
