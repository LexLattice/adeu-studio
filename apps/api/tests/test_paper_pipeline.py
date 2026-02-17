from __future__ import annotations

from adeu_api.paper_pipeline import (
    build_flow_gate_diagnostics,
    classify_flow_divergence,
    derive_cleaned_source_text,
    select_best_flow,
)


def _flow(
    *,
    label: str,
    passes: bool,
    word_count: int,
    candidate_hash: str,
    artifact_id: str = "artifact-same",
    abstract_text: str = "A stable abstract sentence. Another sentence.",
    sentence_count: int = 2,
    candidate_date_like: bool = False,
) -> dict:
    checks = {"min_words": passes, "max_words": True}
    return {
        "label": label,
        "extract": {
            "result": {
                "word_count": word_count,
                "candidate_hash": candidate_hash,
                "abstract_text": abstract_text,
                "sentence_count": sentence_count,
                "candidate_date_like": candidate_date_like,
            }
        },
        "check": {"result": {"passes": passes, "checks": checks}},
        "emit": {"result": {"artifact_id": artifact_id}},
    }


def test_derive_cleaned_source_text_slices_between_abstract_and_intro() -> None:
    raw = (
        "2026-02-12\n\nTitle Block\n\nAbstract\n"
        "AI agents can delegate complex work across mixed teams. "
        "This abstract should be retained.\n\n"
        "1 Introduction\n"
        "This section should be removed from cleaned output."
    )
    cleaned = derive_cleaned_source_text(raw)
    assert cleaned.startswith("Abstract")
    assert "This section should be removed" not in cleaned


def test_select_best_flow_prefers_passing_candidate() -> None:
    raw_flow = _flow(
        label="raw_pdf_text",
        passes=False,
        word_count=1,
        candidate_hash="aaa",
    )
    cleaned_flow = _flow(
        label="cleaned_text",
        passes=True,
        word_count=141,
        candidate_hash="bbb",
    )

    selected, reasons = select_best_flow([raw_flow, cleaned_flow])
    assert selected["label"] == "cleaned_text"
    assert reasons[0] == "cleaned_text:all_pass"
    assert "raw_pdf_text:fail[min_words]" in reasons


def test_select_best_flow_tie_breaks_deterministically() -> None:
    a = _flow(label="a", passes=True, word_count=10, candidate_hash="hash-x")
    b = _flow(label="b", passes=True, word_count=10, candidate_hash="hash-y")
    selected, _ = select_best_flow([a, b])
    assert selected["label"] == "b"


def test_build_flow_gate_diagnostics_emits_fail_codes() -> None:
    diagnostics = build_flow_gate_diagnostics(
        extract_result={
            "sentence_count": 1,
            "candidate_date_like": True,
        },
        check_result={
            "passes": False,
            "word_count": 1,
            "checks": {
                "min_words": False,
                "max_words": True,
            },
        },
    )
    assert diagnostics["structural_passes"] is False
    assert diagnostics["fail_codes"] == ["MIN_WORDS", "MIN_SENTENCES", "DATE_HEURISTIC"]
    assert diagnostics["gate_results"]["min_sentences"] is False
    assert diagnostics["gate_results"]["candidate_date_like"] is True


def test_classify_flow_divergence_reports_major_when_artifacts_diverge() -> None:
    same_a = _flow(
        label="a",
        passes=True,
        word_count=20,
        candidate_hash="h1",
        artifact_id="artifact-1",
    )
    same_b = _flow(
        label="b",
        passes=True,
        word_count=20,
        candidate_hash="h2",
        artifact_id="artifact-1",
    )
    diverged, cls = classify_flow_divergence([same_a, same_b])
    assert diverged is False
    assert cls == "none"

    major_a = _flow(
        label="raw",
        passes=True,
        word_count=80,
        candidate_hash="ha",
        artifact_id="artifact-a",
        abstract_text="First abstract content. Different direction.",
    )
    major_b = _flow(
        label="clean",
        passes=True,
        word_count=140,
        candidate_hash="hb",
        artifact_id="artifact-b",
        abstract_text="Second abstract has materially different content and boundaries.",
    )
    diverged, cls = classify_flow_divergence([major_a, major_b])
    assert diverged is True
    assert cls == "major"
