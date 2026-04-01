from __future__ import annotations

import re
from dataclasses import dataclass
from hashlib import sha256
from typing import Any

from adeu_commitments_ir import (
    CheckerFactBundle,
    ClauseScopeBlockerResultRow,
    D1Clause,
    D1NormalizedIR,
    D1Qualifier,
    D1SelectorRef,
    EvaluationNotice,
    PolicyEvaluationResultSet,
    PolicyObligationLedger,
    PolicyObligationLedgerRow,
    PredicateArgumentSpec,
    PredicateContract,
    PredicateContractsBootstrap,
    SubjectScopedResultRow,
    stable_payload_hash,
)

_D1_BLOCK_HEADER_RE = re.compile(r"^:::D@1(?:\s+id=(?P<block_id>[A-Za-z0-9_.-]+))\s*$")
_CLAUSE_RE = re.compile(r"^@(?P<label>[A-Za-z0-9_.-]+)\s+(?P<modal>MUST|MUST_NOT)\s+(?P<rest>.+)$")
_PREDICATE_CALL_RE = re.compile(
    r"^(?P<name>[A-Za-z_][A-Za-z0-9_]*)\((?P<args>.*)\)$"
)
_QUALIFIER_SEGMENT_RE = re.compile(
    r"(ONLY_IF|UNLESS)\s+(.+?)(?=(?:\s+(?:ONLY_IF|UNLESS)\s+)|$)"
)


class AnmCompileError(ValueError):
    """Fail-closed bounded ANM / D@1 compilation error."""


@dataclass(frozen=True)
class _ParsedBlock:
    block_id: str
    selector_source_text: str
    clause_lines: list[str]


def _normalize_text(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")


def _sha256_text(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def _json_scalar_from_text(value_text: str) -> str | int | bool | None:
    normalized = value_text.strip()
    if normalized == "true":
        return True
    if normalized == "false":
        return False
    if normalized == "null":
        return None
    if re.fullmatch(r"-?[0-9]+", normalized):
        return int(normalized)
    if (
        len(normalized) >= 2
        and normalized[0] == '"'
        and normalized[-1] == '"'
    ):
        return normalized[1:-1]
    return normalized


def _split_args(args_text: str) -> list[str]:
    if not args_text.strip():
        return []
    return [part.strip() for part in args_text.split(",")]


def _parse_condition(condition_text: str) -> D1Qualifier:
    normalized = condition_text.strip()
    predicate_match = _PREDICATE_CALL_RE.match(normalized)
    if predicate_match is not None:
        name = predicate_match.group("name")
        args = _split_args(predicate_match.group("args"))
        if name in {"present", "explicit", "bind_to"} and len(args) == 1:
            return D1Qualifier(
                qualifier_kind="only_if",
                normalized_predicate_id=name,
                target_path=args[0],
            )
        if name == "cardinality_eq" and len(args) == 2:
            return D1Qualifier(
                qualifier_kind="only_if",
                normalized_predicate_id="cardinality_eq",
                target_path=args[0],
                expected_count=int(args[1]),
            )
        raise AnmCompileError(f"unsupported qualifier predicate call: {condition_text}")

    if "==" in normalized:
        target_path, expected = normalized.split("==", 1)
        return D1Qualifier(
            qualifier_kind="only_if",
            normalized_predicate_id="eq",
            target_path=target_path.strip(),
            expected_scalar=_json_scalar_from_text(expected),
        )

    raise AnmCompileError(f"unsupported qualifier condition: {condition_text}")


def _parse_assertion(assertion_text: str, *, modal: str) -> dict[str, Any]:
    normalized = assertion_text.strip()
    if " AND " in normalized or " OR " in normalized:
        raise AnmCompileError("boolean composition is forbidden in V47-A")
    if normalized.startswith("DEFERRED "):
        raise AnmCompileError("source-level DEFERRED is forbidden in V47-A")

    for prefix, kind, predicate_id in (
        ("REQUIRED ", "required", "present"),
        ("EXPLICIT ", "explicit", "explicit"),
        ("EXACTLY_ONE ", "exactly_one", "cardinality_eq"),
    ):
        if normalized.startswith(prefix):
            target_path = normalized[len(prefix) :].strip()
            payload: dict[str, Any] = {
                "assertion_kind": kind,
                "normalized_predicate_id": predicate_id,
                "target_path": target_path,
            }
            if kind == "exactly_one":
                payload["expected_count"] = 1
            return payload

    predicate_match = _PREDICATE_CALL_RE.match(normalized)
    if predicate_match is not None:
        name = predicate_match.group("name")
        args = _split_args(predicate_match.group("args"))
        if modal == "MUST_NOT":
            raise AnmCompileError("MUST_NOT predicate calls are forbidden in V47-A")
        if name in {"present", "explicit", "bind_to"} and len(args) == 1:
            return {
                "assertion_kind": "predicate_call",
                "normalized_predicate_id": name,
                "target_path": args[0],
            }
        if name == "cardinality_eq" and len(args) == 2:
            return {
                "assertion_kind": "predicate_call",
                "normalized_predicate_id": "cardinality_eq",
                "target_path": args[0],
                "expected_count": int(args[1]),
            }
        raise AnmCompileError(f"unsupported predicate call: {assertion_text}")

    if "==" in normalized:
        target_path, expected = normalized.split("==", 1)
        return {
            "assertion_kind": "comparison",
            "normalized_predicate_id": "eq",
            "target_path": target_path.strip(),
            "expected_scalar": _json_scalar_from_text(expected),
        }

    raise AnmCompileError(f"unsupported assertion form: {assertion_text}")


def _extract_blocks(source_text: str) -> list[_ParsedBlock]:
    lines = _normalize_text(source_text).split("\n")
    blocks: list[_ParsedBlock] = []
    current_block_id: str | None = None
    current_selector: str | None = None
    current_clauses: list[str] = []

    for line in lines:
        header_match = _D1_BLOCK_HEADER_RE.match(line.strip())
        if header_match is not None:
            if current_block_id is not None:
                raise AnmCompileError("nested D@1 blocks are forbidden")
            block_id = header_match.group("block_id")
            if block_id is None:
                raise AnmCompileError("D@1 block id is required")
            current_block_id = block_id
            current_selector = None
            current_clauses = []
            continue

        if current_block_id is None:
            continue

        if line.strip() == ":::":
            if current_selector is None:
                raise AnmCompileError(f"D@1 block {current_block_id} is missing ON selector")
            if not current_clauses:
                raise AnmCompileError(f"D@1 block {current_block_id} contains no clauses")
            blocks.append(
                _ParsedBlock(
                    block_id=current_block_id,
                    selector_source_text=current_selector,
                    clause_lines=list(current_clauses),
                )
            )
            current_block_id = None
            current_selector = None
            current_clauses = []
            continue

        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("NOTE "):
            continue
        if stripped.startswith("ON "):
            if current_selector is not None:
                raise AnmCompileError(f"D@1 block {current_block_id} declares multiple selectors")
            current_selector = stripped[3:].strip()
            continue
        if stripped.startswith("@"):
            current_clauses.append(stripped)
            continue

        raise AnmCompileError(f"unsupported line inside D@1 block {current_block_id}: {stripped}")

    if current_block_id is not None:
        raise AnmCompileError(f"D@1 block {current_block_id} was not closed")
    if not blocks:
        raise AnmCompileError("no D@1 blocks found; prose inference is forbidden")
    return blocks


def compile_authoritative_normative_markdown(
    *,
    source_text: str,
    source_doc_ref: str,
) -> D1NormalizedIR:
    normalized_source = _normalize_text(source_text)
    blocks = _extract_blocks(normalized_source)
    block_ids = sorted(block.block_id for block in blocks)
    if len(block_ids) != len(set(block_ids)):
        raise AnmCompileError("duplicate D@1 block ids are forbidden")

    selector_refs: list[D1SelectorRef] = []
    clauses: list[D1Clause] = []

    for block in blocks:
        selector_ref = f"{block.block_id}:selector"
        selector_refs.append(
            D1SelectorRef(
                selector_ref=selector_ref,
                selector_source_text=block.selector_source_text,
                selector_kind="bootstrap_string_selector",
            )
        )

        for clause_line in block.clause_lines:
            clause_match = _CLAUSE_RE.match(clause_line)
            if clause_match is None:
                raise AnmCompileError(f"invalid clause line: {clause_line}")
            label = clause_match.group("label")
            modal = clause_match.group("modal")
            rest = clause_match.group("rest").strip()

            qualifier_matches = list(_QUALIFIER_SEGMENT_RE.finditer(rest))
            assertion_text = rest
            qualifiers: list[D1Qualifier] = []
            if qualifier_matches:
                assertion_text = rest[: qualifier_matches[0].start()].strip()
                for match in qualifier_matches:
                    parsed = _parse_condition(match.group(2))
                    qualifier_kind = "only_if" if match.group(1) == "ONLY_IF" else "unless"
                    qualifier = D1Qualifier(
                        qualifier_kind=qualifier_kind,
                        normalized_predicate_id=parsed.normalized_predicate_id,
                        target_path=parsed.target_path,
                        expected_scalar=parsed.expected_scalar,
                        expected_count=parsed.expected_count,
                    )
                    qualifiers.append(qualifier)

            assertion_payload = _parse_assertion(assertion_text, modal=modal)
            clauses.append(
                D1Clause(
                    clause_ref=f"{block.block_id}:{label}",
                    clause_label=label,
                    modal=modal,
                    subject_selector_ref=selector_ref,
                    qualifiers=sorted(
                        qualifiers,
                        key=lambda item: (
                            item.qualifier_kind,
                            item.normalized_predicate_id,
                            item.target_path or "",
                            item.expected_count if item.expected_count is not None else -1,
                            repr(item.expected_scalar),
                        ),
                    ),
                    origin_block_ref=block.block_id,
                    **assertion_payload,
                )
            )

    selector_refs = sorted(selector_refs, key=lambda item: item.selector_ref)
    clauses = sorted(clauses, key=lambda item: item.clause_ref)
    semantic_hash = stable_payload_hash(
        {
            "source_doc_ref": source_doc_ref,
            "source_block_refs": block_ids,
            "selector_refs": [
                item.model_dump(mode="json", exclude_none=True) for item in selector_refs
            ],
            "clauses": [item.model_dump(mode="json", exclude_none=True) for item in clauses],
            "selector_zero_match_policy": "allow_empty_with_notice",
        }
    )
    d1_ir_id = f"d1-ir:{semantic_hash[:12]}"

    return D1NormalizedIR(
        d1_ir_id=d1_ir_id,
        source_doc_ref=source_doc_ref,
        source_doc_sha256=_sha256_text(normalized_source),
        source_block_refs=block_ids,
        selector_refs=selector_refs,
        selector_zero_match_policy="allow_empty_with_notice",
        clauses=clauses,
        semantic_hash=semantic_hash,
    )


def default_bootstrap_predicate_contracts() -> PredicateContractsBootstrap:
    contracts = [
        PredicateContract(
            predicate_id="bind_to",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[PredicateArgumentSpec(name="path", kind="path")],
            required_evidence_kinds=["binding_observation"],
            truth_conditions=[
                "binding_payload.path matches target path and binding_payload.bound == true"
            ],
            evidence_failure_conditions=["no binding_observation facts present for target path"],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
        PredicateContract(
            predicate_id="cardinality_eq",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[
                PredicateArgumentSpec(name="path", kind="path"),
                PredicateArgumentSpec(name="count", kind="integer"),
            ],
            required_evidence_kinds=["path_cardinality_observation"],
            truth_conditions=["at least one observed cardinality equals expected count"],
            evidence_failure_conditions=[
                "no path_cardinality_observation facts present for target path"
            ],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
        PredicateContract(
            predicate_id="eq",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[
                PredicateArgumentSpec(name="path", kind="path"),
                PredicateArgumentSpec(name="value", kind="scalar"),
            ],
            required_evidence_kinds=["value_observation"],
            truth_conditions=["at least one observed value equals expected scalar"],
            evidence_failure_conditions=["no value_observation facts present for target path"],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
        PredicateContract(
            predicate_id="explicit",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[PredicateArgumentSpec(name="path", kind="path")],
            required_evidence_kinds=["explicit_carriage_observation"],
            truth_conditions=["at least one explicit_carriage_observation is true for target path"],
            evidence_failure_conditions=[
                "no explicit_carriage_observation facts present for target path"
            ],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
        PredicateContract(
            predicate_id="present",
            owner_layer="bootstrap_d",
            version="1",
            argument_schema=[PredicateArgumentSpec(name="path", kind="path")],
            required_evidence_kinds=["path_presence_observation"],
            truth_conditions=["at least one path_presence_observation is true for target path"],
            evidence_failure_conditions=[
                "no path_presence_observation facts present for target path"
            ],
            resolution_failure_conditions=["subject resolution failed before predicate evaluation"],
        ),
    ]
    contracts = sorted(contracts, key=lambda item: item.predicate_id)
    bundle_hash = stable_payload_hash(
        {"contracts": [item.model_dump(mode="json", exclude_none=True) for item in contracts]}
    )
    return PredicateContractsBootstrap(
        predicate_contract_bundle_id=f"predicate-contracts:{bundle_hash[:12]}",
        contracts=contracts,
    )


def _clause_semantic_hash(clause: D1Clause) -> str:
    return stable_payload_hash(clause.model_dump(mode="json", exclude_none=True))


def _facts_for_subject(
    bundle: CheckerFactBundle,
    *,
    subject_ref: str,
    fact_type: str,
    path: str | None = None,
) -> list[Any]:
    selected: list[Any] = []
    for fact in bundle.facts:
        if fact.subject_ref != subject_ref or fact.fact_type != fact_type:
            continue
        if path is not None and hasattr(fact, "path") and getattr(fact, "path") != path:
            continue
        if path is not None and fact.fact_type == "binding_observation":
            binding_path = fact.binding_payload.get("path")
            if binding_path != path:
                continue
        selected.append(fact)
    return selected


def _fact_values_for_subject(
    fact_bundle: CheckerFactBundle,
    *,
    subject_ref: str,
    fact_type: str,
    path: str,
) -> tuple[list[Any] | None, list[str]]:
    facts = _facts_for_subject(
        fact_bundle,
        subject_ref=subject_ref,
        fact_type=fact_type,
        path=path,
    )
    if not facts:
        return None, []
    return [value for fact in facts for value in fact.values], sorted(
        item.fact_id for item in facts
    )


def _scalar_matches_expected(*, observed: Any, expected: Any) -> bool:
    return type(observed) is type(expected) and observed == expected


def _supporting_contract_refs_for_clause(clause: D1Clause) -> list[str]:
    return sorted(
        {clause.normalized_predicate_id}
        | {qualifier.normalized_predicate_id for qualifier in clause.qualifiers}
    )


def _evaluate_predicate(
    *,
    predicate_id: str,
    target_path: str,
    subject_ref: str,
    fact_bundle: CheckerFactBundle,
    expected_scalar: Any = None,
    expected_count: int | None = None,
) -> tuple[str, list[str]]:
    if predicate_id == "present":
        values, fact_ids = _fact_values_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="path_presence_observation",
            path=target_path,
        )
        if values is None:
            return "unknown_evidence", []
        return ("pass" if any(values) else "fail"), fact_ids

    if predicate_id == "explicit":
        values, fact_ids = _fact_values_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="explicit_carriage_observation",
            path=target_path,
        )
        if values is None:
            return "unknown_evidence", []
        return ("pass" if any(values) else "fail"), fact_ids

    if predicate_id == "cardinality_eq":
        values, fact_ids = _fact_values_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="path_cardinality_observation",
            path=target_path,
        )
        if values is None:
            return "unknown_evidence", []
        return ("pass" if expected_count in values else "fail"), fact_ids

    if predicate_id == "bind_to":
        facts = _facts_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="binding_observation",
            path=target_path,
        )
        if not facts:
            return "unknown_evidence", []
        fact_ids = sorted(item.fact_id for item in facts)
        bound_values = [bool(fact.binding_payload.get("bound")) for fact in facts]
        return ("pass" if any(bound_values) else "fail"), fact_ids

    if predicate_id == "eq":
        values, fact_ids = _fact_values_for_subject(
            fact_bundle,
            subject_ref=subject_ref,
            fact_type="value_observation",
            path=target_path,
        )
        if values is None:
            return "unknown_evidence", []
        return (
            "pass"
            if any(
                _scalar_matches_expected(observed=value, expected=expected_scalar)
                for value in values
            )
            else "fail",
            fact_ids,
        )

    raise AnmCompileError(f"unsupported predicate_id: {predicate_id}")


def _selector_subjects(
    selector: D1SelectorRef,
    fact_bundle: CheckerFactBundle,
) -> tuple[list[str], str | None]:
    if selector.selector_source_text == "artifact.emitted[*]":
        subjects = sorted({fact.subject_ref for fact in fact_bundle.facts})
        return subjects, None
    return [], "unsupported bootstrap selector"


def evaluate_authoritative_normative_markdown(
    *,
    d1_ir: D1NormalizedIR,
    fact_bundle: CheckerFactBundle,
    predicate_contracts: PredicateContractsBootstrap,
    result_set_id: str,
) -> PolicyEvaluationResultSet:
    contract_ids = {contract.predicate_id for contract in predicate_contracts.contracts}
    results: list[SubjectScopedResultRow | ClauseScopeBlockerResultRow] = []
    notices: list[EvaluationNotice] = []
    selector_index = {selector.selector_ref: selector for selector in d1_ir.selector_refs}

    for clause in d1_ir.clauses:
        supporting_contract_refs = _supporting_contract_refs_for_clause(clause)
        missing_contract_ids = [
            predicate_id
            for predicate_id in supporting_contract_refs
            if predicate_id not in contract_ids
        ]
        if missing_contract_ids:
            raise AnmCompileError(
                "clause "
                f"{clause.clause_ref} references missing predicate contract(s) "
                + ", ".join(missing_contract_ids)
            )

        selector = selector_index[clause.subject_selector_ref]
        subjects, selector_error = _selector_subjects(selector, fact_bundle)
        if selector_error is not None:
            results.append(
                ClauseScopeBlockerResultRow(
                    result_id=f"result:{clause.clause_ref}",
                    clause_ref=clause.clause_ref,
                    clause_semantic_hash=_clause_semantic_hash(clause),
                    applicability="active",
                    observed_outcome="unknown_resolution",
                    effective_verdict="unknown_resolution",
                    supporting_fact_refs=[],
                    supporting_contract_refs=supporting_contract_refs,
                    message=selector_error,
                )
            )
            continue

        if not subjects:
            notices.append(
                EvaluationNotice(
                    notice_id=f"notice:{clause.clause_ref}",
                    notice_kind="selector_zero_match",
                    clause_ref=clause.clause_ref,
                    selector_ref=selector.selector_ref,
                    message="selector resolved zero subjects under allow_empty_with_notice",
                )
            )
            continue

        for subject_ref in subjects:
            applicability: str = "active"
            observed_outcome: str = "not_evaluated"
            effective_verdict: str = "gated_off"
            supporting_fact_refs: set[str] = set()

            for qualifier in clause.qualifiers:
                qualifier_outcome, qualifier_fact_ids = _evaluate_predicate(
                    predicate_id=qualifier.normalized_predicate_id,
                    target_path=qualifier.target_path or "",
                    subject_ref=subject_ref,
                    fact_bundle=fact_bundle,
                    expected_scalar=qualifier.expected_scalar,
                    expected_count=qualifier.expected_count,
                )
                supporting_fact_refs.update(qualifier_fact_ids)
                if qualifier.qualifier_kind == "only_if":
                    if qualifier_outcome == "fail":
                        applicability = "gated_off"
                        observed_outcome = "not_evaluated"
                        effective_verdict = "gated_off"
                        break
                    if qualifier_outcome == "unknown_evidence":
                        applicability = "active"
                        observed_outcome = "unknown_evidence"
                        effective_verdict = "unknown_evidence"
                        break
                    if qualifier_outcome == "unknown_resolution":
                        applicability = "active"
                        observed_outcome = "unknown_resolution"
                        effective_verdict = "unknown_resolution"
                        break
                else:
                    if qualifier_outcome == "pass":
                        applicability = "excepted"
                        observed_outcome = "not_evaluated"
                        effective_verdict = "waived"
                        break
                    if qualifier_outcome == "unknown_evidence":
                        applicability = "active"
                        observed_outcome = "unknown_evidence"
                        effective_verdict = "unknown_evidence"
                        break
                    if qualifier_outcome == "unknown_resolution":
                        applicability = "active"
                        observed_outcome = "unknown_resolution"
                        effective_verdict = "unknown_resolution"
                        break

            if observed_outcome == "not_evaluated" and applicability == "active":
                observed_outcome, fact_ids = _evaluate_predicate(
                    predicate_id=clause.normalized_predicate_id,
                    target_path=clause.target_path or "",
                    subject_ref=subject_ref,
                    fact_bundle=fact_bundle,
                    expected_scalar=clause.expected_scalar,
                    expected_count=clause.expected_count,
                )
                supporting_fact_refs.update(fact_ids)
                if observed_outcome == "pass":
                    effective_verdict = "fail" if clause.modal == "MUST_NOT" else "pass"
                elif observed_outcome == "fail":
                    effective_verdict = "pass" if clause.modal == "MUST_NOT" else "fail"
                else:
                    effective_verdict = observed_outcome

            message = f"evaluated {clause.clause_ref} for {subject_ref}"
            if applicability == "gated_off":
                message = f"{clause.clause_ref} gated off by ONLY_IF false"
            elif applicability == "excepted":
                message = f"{clause.clause_ref} excepted by UNLESS true"
            elif effective_verdict == "unknown_evidence":
                message = f"{clause.clause_ref} blocked on unknown evidence"
            elif effective_verdict == "unknown_resolution":
                message = f"{clause.clause_ref} blocked on unknown resolution"

            results.append(
                SubjectScopedResultRow(
                    result_id=f"result:{clause.clause_ref}:{subject_ref}",
                    clause_ref=clause.clause_ref,
                    clause_semantic_hash=_clause_semantic_hash(clause),
                    subject_ref=subject_ref,
                    applicability=applicability,
                    observed_outcome=observed_outcome,
                    effective_verdict=effective_verdict,
                    supporting_fact_refs=sorted(supporting_fact_refs),
                    supporting_contract_refs=supporting_contract_refs,
                    message=message,
                )
            )

    return PolicyEvaluationResultSet(
        result_set_id=result_set_id,
        scope_snapshot=fact_bundle.scope_snapshot,
        d_ir_ref=d1_ir.d1_ir_id,
        fact_bundle_ref=fact_bundle.bundle_id,
        predicate_contract_ref=predicate_contracts.predicate_contract_bundle_id,
        results=sorted(results, key=lambda item: item.result_id),
        notices=sorted(notices, key=lambda item: item.notice_id),
    )


def ledger_state_for_effective_verdict(effective_verdict: str) -> str:
    mapping = {
        "pass": "satisfied",
        "fail": "violated",
        "waived": "waived",
        "deferred": "deferred",
        "gated_off": "gated_off",
        "unknown_evidence": "blocked_unknown_evidence",
        "unknown_resolution": "blocked_unknown_resolution",
    }
    return mapping[effective_verdict]


def project_policy_obligation_ledger(
    *,
    result_set: PolicyEvaluationResultSet,
    ledger_id: str,
    previous_ledger: PolicyObligationLedger | None = None,
    updated_at: str | None = None,
) -> PolicyObligationLedger:
    if (
        previous_ledger is not None
        and previous_ledger.scope_snapshot != result_set.scope_snapshot
    ):
        raise ValueError(
            "previous_ledger scope_snapshot must match result_set scope_snapshot"
        )
    existing = {
        row.obligation_id: row
        for row in previous_ledger.rows
    } if previous_ledger is not None else {}
    rows: dict[str, PolicyObligationLedgerRow] = dict(existing)

    for result in result_set.results:
        if isinstance(result, ClauseScopeBlockerResultRow):
            continue
        obligation_hash = stable_payload_hash(
            {
                "clause_ref": result.clause_ref,
                "clause_semantic_hash": result.clause_semantic_hash,
                "subject_ref": result.subject_ref,
                "scope_snapshot": result_set.scope_snapshot,
            }
        )
        obligation_id = f"obligation:{obligation_hash[:12]}"
        prior_row = rows.get(obligation_id)
        rows[obligation_id] = PolicyObligationLedgerRow(
            obligation_id=obligation_id,
            clause_ref=result.clause_ref,
            clause_semantic_hash=result.clause_semantic_hash,
            subject_ref=result.subject_ref,
            latest_applicability=result.applicability,
            latest_observed_outcome=result.observed_outcome,
            latest_effective_verdict=result.effective_verdict,
            ledger_state=ledger_state_for_effective_verdict(result.effective_verdict),
            first_seen_run=(
                prior_row.first_seen_run
                if prior_row is not None
                else result_set.result_set_id
            ),
            latest_result_run=result_set.result_set_id,
            waiver_ref=prior_row.waiver_ref if prior_row is not None else None,
            deferral_ref=prior_row.deferral_ref if prior_row is not None else None,
            updated_at=updated_at or result_set.result_set_id,
        )

    result_set_refs = sorted(
        set(previous_ledger.result_set_refs if previous_ledger is not None else [])
        | {result_set.result_set_id}
    )
    return PolicyObligationLedger(
        ledger_id=ledger_id,
        scope_snapshot=result_set.scope_snapshot,
        result_set_refs=result_set_refs,
        rows=sorted(rows.values(), key=lambda item: item.obligation_id),
    )


def build_v47a_reference_chain(
    *,
    source_text: str,
    source_doc_ref: str,
    fact_bundle: CheckerFactBundle,
    result_set_id: str,
    ledger_id: str,
    predicate_contracts: PredicateContractsBootstrap | None = None,
) -> tuple[
    D1NormalizedIR,
    PredicateContractsBootstrap,
    PolicyEvaluationResultSet,
    PolicyObligationLedger,
]:
    d1_ir = compile_authoritative_normative_markdown(
        source_text=source_text,
        source_doc_ref=source_doc_ref,
    )
    contracts = predicate_contracts or default_bootstrap_predicate_contracts()
    result_set = evaluate_authoritative_normative_markdown(
        d1_ir=d1_ir,
        fact_bundle=fact_bundle,
        predicate_contracts=contracts,
        result_set_id=result_set_id,
    )
    ledger = project_policy_obligation_ledger(
        result_set=result_set,
        ledger_id=ledger_id,
    )
    return d1_ir, contracts, result_set, ledger


__all__ = [
    "AnmCompileError",
    "compile_authoritative_normative_markdown",
    "default_bootstrap_predicate_contracts",
    "evaluate_authoritative_normative_markdown",
    "project_policy_obligation_ledger",
    "build_v47a_reference_chain",
]
