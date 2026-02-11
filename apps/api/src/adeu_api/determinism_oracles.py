from __future__ import annotations

import difflib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from adeu_concepts import ConceptIR
from adeu_ir import AdeuIR
from adeu_ir.models import JsonPatchOp
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode
from fastapi import HTTPException

import adeu_api.main as api_main
from adeu_api.hashing import canonical_json

ORACLE_SCHEMA_VERSION = "odeu.determinism-oracles@1"
BRIDGE_FIXTURE_ROOT = Path("examples/eval/oracles/bridge")
QUESTIONS_FIXTURE_ROOT = Path("examples/eval/oracles/questions")
PATCH_FIXTURE_ROOT = Path("examples/eval/oracles/patch")


@dataclass(frozen=True)
class OracleCaseResult:
    domain: str
    case_id: str
    family: str
    status: str
    message: str
    diff: str | None = None

    def as_dict(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "domain": self.domain,
            "case_id": self.case_id,
            "family": self.family,
            "status": self.status,
            "message": self.message,
        }
        if self.diff:
            payload["diff"] = self.diff
        return payload


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"fixture must be a JSON object: {path}")
    return payload


def _fixture_paths(relative_root: Path) -> list[Path]:
    root = _repo_root() / relative_root
    if not root.exists():
        return []
    return sorted(root.glob("*.json"))


def _canonical_payload(value: Any) -> str:
    return canonical_json(value)


def _unified_json_diff(left: Any, right: Any, *, left_name: str, right_name: str) -> str:
    left_json = _canonical_payload(left).splitlines()
    right_json = _canonical_payload(right).splitlines()
    return "\n".join(
        difflib.unified_diff(
            left_json,
            right_json,
            fromfile=left_name,
            tofile=right_name,
            lineterm="",
        )
    )


def _permuted_adeu_ir(ir: AdeuIR) -> AdeuIR:
    return ir.model_copy(
        update={
            "O": ir.O.model_copy(
                update={
                    "entities": list(reversed(ir.O.entities)),
                    "definitions": list(reversed(ir.O.definitions)),
                }
            ),
            "D_norm": ir.D_norm.model_copy(
                update={
                    "statements": list(reversed(ir.D_norm.statements)),
                    "exceptions": list(reversed(ir.D_norm.exceptions)),
                }
            ),
        }
    )


def _permuted_concept_ir(ir: ConceptIR) -> ConceptIR:
    return ir.model_copy(
        update={
            "terms": list(reversed(ir.terms)),
            "senses": list(reversed(ir.senses)),
            "claims": list(reversed(ir.claims)),
            "links": list(reversed(ir.links)),
            "ambiguity": list(reversed(ir.ambiguity)),
        }
    )


def _load_adeu_ir(path: str) -> AdeuIR:
    fixture_path = _repo_root() / path
    return AdeuIR.model_validate(_load_json(fixture_path))


def _load_concept_ir(path: str) -> ConceptIR:
    fixture_path = _repo_root() / path
    return ConceptIR.model_validate(_load_json(fixture_path))


def _load_text(path: str) -> str:
    fixture_path = _repo_root() / path
    return fixture_path.read_text(encoding="utf-8").strip()


def _map_signal_to_rationale(signal: str) -> str:
    mapping = {
        "mic": "mic_conflict",
        "forced_countermodel": "forced_nonentailment",
        "disconnected_clusters": "disconnected_cluster",
    }
    return mapping.get(signal, "")


def _question_payload(response: api_main.ConceptQuestionsResponse) -> list[dict[str, Any]]:
    return [
        question.model_dump(mode="json", by_alias=True, exclude_none=True)
        for question in response.questions
    ]


def _bridge_case_results(path: Path) -> list[OracleCaseResult]:
    payload = _load_json(path)
    case_id = str(payload.get("case_id", path.stem))
    ir = _load_adeu_ir(str(payload["ir_path"]))
    mode = KernelMode(str(payload.get("request", {}).get("mode", "LAX")))
    include_analysis = bool(payload.get("request", {}).get("include_analysis_details", True))
    include_forced = bool(payload.get("request", {}).get("include_forced_details", True))

    request = api_main.AdeuAnalyzeConceptsRequest(
        ir=ir,
        mode=mode,
        include_analysis_details=include_analysis,
        include_forced_details=include_forced,
    )
    left = api_main.analyze_adeu_as_concepts(request).bridge_loss_report.model_dump(
        mode="json", by_alias=True, exclude_none=True
    )
    right = api_main.analyze_adeu_as_concepts(request).bridge_loss_report.model_dump(
        mode="json", by_alias=True, exclude_none=True
    )

    results: list[OracleCaseResult] = []
    if left == right:
        results.append(
            OracleCaseResult(
                domain="bridge",
                case_id=case_id,
                family="idempotence",
                status="PASS",
                message="bridge_loss_report is identical across repeated runs",
            )
        )
    else:
        results.append(
            OracleCaseResult(
                domain="bridge",
                case_id=case_id,
                family="idempotence",
                status="FAIL",
                message="bridge_loss_report changed across repeated runs",
                diff=_unified_json_diff(
                    left,
                    right,
                    left_name="bridge_loss_report[0]",
                    right_name="bridge_loss_report[1]",
                ),
            )
        )

    permuted_ir = _permuted_adeu_ir(ir)
    permuted_request = api_main.AdeuAnalyzeConceptsRequest(
        ir=permuted_ir,
        mode=mode,
        include_analysis_details=include_analysis,
        include_forced_details=include_forced,
    )
    permuted = api_main.analyze_adeu_as_concepts(permuted_request).bridge_loss_report.model_dump(
        mode="json", by_alias=True, exclude_none=True
    )
    if left == permuted:
        results.append(
            OracleCaseResult(
                domain="bridge",
                case_id=case_id,
                family="ordering",
                status="PASS",
                message="bridge_loss_report is invariant to ADEU input permutations",
            )
        )
    else:
        results.append(
            OracleCaseResult(
                domain="bridge",
                case_id=case_id,
                family="ordering",
                status="FAIL",
                message="bridge_loss_report differs under ADEU input permutation",
                diff=_unified_json_diff(
                    left,
                    permuted,
                    left_name="bridge_loss_report[base]",
                    right_name="bridge_loss_report[permuted]",
                ),
            )
        )

    entries = left.get("entries", [])
    summary = left.get("summary", {})
    triples: set[tuple[str, str, str]] = set()
    structural_has_paths = False
    for entry in entries:
        triple = (
            str(entry.get("feature_key", "")),
            str(entry.get("scope", "")),
            str(entry.get("status", "")),
        )
        triples.add(triple)
        if entry.get("scope") == "structural" and entry.get("source_paths"):
            structural_has_paths = True
    expected_counts = {
        "preserved_count": sum(1 for item in entries if item.get("status") == "preserved"),
        "projected_count": sum(1 for item in entries if item.get("status") == "projected"),
        "not_modeled_count": sum(1 for item in entries if item.get("status") == "not_modeled"),
    }
    conservation_ok = (
        len(triples) == len(entries)
        and not structural_has_paths
        and all(summary.get(key) == value for key, value in expected_counts.items())
    )
    if conservation_ok:
        results.append(
            OracleCaseResult(
                domain="bridge",
                case_id=case_id,
                family="conservation",
                status="PASS",
                message="bridge summary/entry invariants are preserved",
            )
        )
    else:
        results.append(
            OracleCaseResult(
                domain="bridge",
                case_id=case_id,
                family="conservation",
                status="FAIL",
                message="bridge summary/entry invariants failed",
                diff=_unified_json_diff(
                    {
                        "entry_count": len(entries),
                        "unique_triples": len(triples),
                        "structural_has_paths": structural_has_paths,
                        "summary": summary,
                    },
                    {
                        "entry_count": len(entries),
                        "unique_triples": len(entries),
                        "structural_has_paths": False,
                        "summary": expected_counts,
                    },
                    left_name="actual",
                    right_name="expected",
                ),
            )
        )
    return results


def _questions_case_results(path: Path) -> list[OracleCaseResult]:
    payload = _load_json(path)
    case_id = str(payload.get("case_id", path.stem))
    ir = _load_concept_ir(str(payload["ir_path"]))
    source_text = _load_text(str(payload["source_text_path"]))
    mode = KernelMode(str(payload.get("request", {}).get("mode", "LAX")))
    include_forced = bool(payload.get("request", {}).get("include_forced_details", False))

    request = api_main.ConceptQuestionsRequest(
        ir=ir,
        source_text=source_text,
        mode=mode,
        include_forced_details=include_forced,
        expected_ir_hash=api_main._concept_ir_hash(ir),
    )
    left = api_main.concept_questions_endpoint(request)
    right = api_main.concept_questions_endpoint(request)

    results: list[OracleCaseResult] = []
    left_questions = _question_payload(left)
    right_questions = _question_payload(right)
    if left_questions == right_questions:
        results.append(
            OracleCaseResult(
                domain="questions",
                case_id=case_id,
                family="idempotence",
                status="PASS",
                message="questions payload is identical across repeated runs",
            )
        )
    else:
        results.append(
            OracleCaseResult(
                domain="questions",
                case_id=case_id,
                family="idempotence",
                status="FAIL",
                message="questions payload changed across repeated runs",
                diff=_unified_json_diff(
                    left_questions,
                    right_questions,
                    left_name="questions[0]",
                    right_name="questions[1]",
                ),
            )
        )

    permuted_ir = _permuted_concept_ir(ir)
    permuted_response = api_main.concept_questions_endpoint(
        api_main.ConceptQuestionsRequest(
            ir=permuted_ir,
            source_text=source_text,
            mode=mode,
            include_forced_details=include_forced,
            expected_ir_hash=api_main._concept_ir_hash(permuted_ir),
        )
    )
    left_order = [question.question_id for question in left.questions]
    permuted_order = [question.question_id for question in permuted_response.questions]
    if left_order == permuted_order:
        results.append(
            OracleCaseResult(
                domain="questions",
                case_id=case_id,
                family="ordering",
                status="PASS",
                message="question ordering is invariant to concept input permutations",
            )
        )
    else:
        results.append(
            OracleCaseResult(
                domain="questions",
                case_id=case_id,
                family="ordering",
                status="FAIL",
                message="question ordering differs under concept input permutation",
                diff=_unified_json_diff(
                    left_order,
                    permuted_order,
                    left_name="question_ids[base]",
                    right_name="question_ids[permuted]",
                ),
            )
        )

    question_ids = [question.question_id for question in left.questions]
    conservation_ok = (
        left.question_count == len(left.questions)
        and len(set(question_ids)) == len(question_ids)
        and all(
            _map_signal_to_rationale(question.signal) == question.rationale_code
            and bool(question.rationale.strip())
            and 0 < len(question.answers) <= left.max_answers_per_question
            for question in left.questions
        )
    )
    if conservation_ok:
        results.append(
            OracleCaseResult(
                domain="questions",
                case_id=case_id,
                family="conservation",
                status="PASS",
                message="question invariants are preserved",
            )
        )
    else:
        conservation_detail = {
            "question_count_ok": left.question_count == len(left.questions),
            "question_ids_unique": len(set(question_ids)) == len(question_ids),
            "all_questions_pass_invariants": all(
                _map_signal_to_rationale(question.signal) == question.rationale_code
                and bool(question.rationale.strip())
                and 0 < len(question.answers) <= left.max_answers_per_question
                for question in left.questions
            ),
        }
        results.append(
            OracleCaseResult(
                domain="questions",
                case_id=case_id,
                family="conservation",
                status="FAIL",
                message="question invariants failed",
                diff=_unified_json_diff(
                    conservation_detail,
                    {key: True for key in conservation_detail},
                    left_name="actual",
                    right_name="expected",
                ),
            )
        )
    return results


def _patch_case_results(path: Path) -> list[OracleCaseResult]:
    payload = _load_json(path)
    case_id = str(payload.get("case_id", path.stem))
    ir = _load_concept_ir(str(payload["ir_path"]))
    source_text = _load_text(str(payload["source_text_path"]))
    mode = KernelMode(str(payload.get("request", {}).get("mode", "LAX")))
    success_ops = [JsonPatchOp.model_validate(item) for item in payload["success_patch_ops"]]
    failure_ops = [JsonPatchOp.model_validate(item) for item in payload["failure_patch_ops"]]
    base_before = ir.model_dump(mode="json", by_alias=True, exclude_none=True)

    success_request = api_main.ConceptApplyPatchRequest(
        ir=ir,
        ir_hash=api_main._concept_ir_hash(ir),
        patch_ops=success_ops,
        source_text=source_text,
        mode=mode,
        dry_run=False,
        include_validator_runs=False,
    )
    first = api_main.apply_concept_patch_endpoint(success_request).model_dump(
        mode="json", by_alias=True, exclude_none=True
    )
    second = api_main.apply_concept_patch_endpoint(success_request).model_dump(
        mode="json", by_alias=True, exclude_none=True
    )

    results: list[OracleCaseResult] = []
    if first == second:
        results.append(
            OracleCaseResult(
                domain="patch",
                case_id=case_id,
                family="idempotence",
                status="PASS",
                message="patch success payload is identical across repeated runs",
            )
        )
    else:
        results.append(
            OracleCaseResult(
                domain="patch",
                case_id=case_id,
                family="idempotence",
                status="FAIL",
                message="patch success payload changed across repeated runs",
                diff=_unified_json_diff(
                    first, second, left_name="patch_success[0]", right_name="patch_success[1]"
                ),
            )
        )

    try:
        api_main.apply_concept_patch_endpoint(
            api_main.ConceptApplyPatchRequest(
                ir=ir,
                ir_hash=api_main._concept_ir_hash(ir),
                patch_ops=failure_ops,
                source_text=source_text,
                mode=mode,
                dry_run=False,
                include_validator_runs=False,
            )
        )
        ordering_ok = False
        failure_detail: dict[str, Any] = {"errors": [], "code": "expected failure but succeeded"}
    except HTTPException as exc:
        detail = exc.detail if isinstance(exc.detail, dict) else {"detail": exc.detail}
        raw_errors = detail.get("errors")
        errors = raw_errors if isinstance(raw_errors, list) else []
        has_error_payload = isinstance(raw_errors, list) and len(errors) > 0
        ordering_ok = has_error_payload and errors == sorted(
            errors,
            key=lambda item: (item.get("op_index"), item.get("path"), item.get("code")),
        )
        failure_detail = detail

    if ordering_ok:
        results.append(
            OracleCaseResult(
                domain="patch",
                case_id=case_id,
                family="ordering",
                status="PASS",
                message="patch failure errors are deterministically ordered",
            )
        )
    else:
        results.append(
            OracleCaseResult(
                domain="patch",
                case_id=case_id,
                family="ordering",
                status="FAIL",
                message="patch failure errors are not deterministically ordered",
                diff=_unified_json_diff(
                    failure_detail.get("errors", []),
                    sorted(
                        failure_detail.get("errors", []),
                        key=lambda item: (
                            item.get("op_index"),
                            item.get("path"),
                            item.get("code"),
                        ),
                    ),
                    left_name="errors[actual]",
                    right_name="errors[sorted]",
                ),
            )
        )

    base_after = ir.model_dump(mode="json", by_alias=True, exclude_none=True)
    first_refs = first.get("evidence_refs", [])
    conservation_ok = (
        base_before == base_after
        and first.get("patched_ir") != base_before
        and any(ref.get("kind") == "event" for ref in first_refs)
        and any(ref.get("kind") in {"validator", "artifact"} for ref in first_refs)
    )
    if conservation_ok:
        results.append(
            OracleCaseResult(
                domain="patch",
                case_id=case_id,
                family="conservation",
                status="PASS",
                message="patch invariants are preserved",
            )
        )
    else:
        results.append(
            OracleCaseResult(
                domain="patch",
                case_id=case_id,
                family="conservation",
                status="FAIL",
                message="patch invariants failed",
                diff=_unified_json_diff(
                    {
                        "base_unchanged": base_before == base_after,
                        "patched_changed": first.get("patched_ir") != base_before,
                        "evidence_refs": first_refs,
                    },
                    {
                        "base_unchanged": True,
                        "patched_changed": True,
                        "evidence_refs": [{"kind": "event"}, {"kind": "validator|artifact"}],
                    },
                    left_name="actual",
                    right_name="expected",
                ),
            )
        )
    return results


def build_determinism_oracle_report() -> dict[str, Any]:
    bridge_paths = _fixture_paths(BRIDGE_FIXTURE_ROOT)
    questions_paths = _fixture_paths(QUESTIONS_FIXTURE_ROOT)
    patch_paths = _fixture_paths(PATCH_FIXTURE_ROOT)
    if not bridge_paths:
        raise RuntimeError("no bridge oracle fixtures found under examples/eval/oracles/bridge")
    if not questions_paths:
        raise RuntimeError(
            "no questions oracle fixtures found under examples/eval/oracles/questions"
        )
    if not patch_paths:
        raise RuntimeError("no patch oracle fixtures found under examples/eval/oracles/patch")

    results: list[OracleCaseResult] = []
    for path in bridge_paths:
        results.extend(_bridge_case_results(path))
    for path in questions_paths:
        results.extend(_questions_case_results(path))
    for path in patch_paths:
        results.extend(_patch_case_results(path))

    passed = sum(1 for result in results if result.status == "PASS")
    failed = sum(1 for result in results if result.status == "FAIL")
    report = {
        "schema": ORACLE_SCHEMA_VERSION,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "fixture_roots": {
            "bridge": str(BRIDGE_FIXTURE_ROOT),
            "questions": str(QUESTIONS_FIXTURE_ROOT),
            "patch": str(PATCH_FIXTURE_ROOT),
        },
        "summary": {
            "total": len(results),
            "passed": passed,
            "failed": failed,
        },
        "results": [result.as_dict() for result in results],
    }
    return json.loads(canonical_json(report))


def write_determinism_oracle_report(output_path: Path) -> dict[str, Any]:
    report = build_determinism_oracle_report()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if report["summary"]["failed"] > 0:
        failures = [item for item in report["results"] if item["status"] == "FAIL"]
        preview = failures[:3]
        lines = [
            "determinism oracle failures detected:",
            *(
                f"- {item['domain']}/{item['case_id']}/{item['family']}: {item['message']}"
                for item in preview
            ),
        ]
        raise RuntimeError("\n".join(lines))
    return report
