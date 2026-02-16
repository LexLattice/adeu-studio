from __future__ import annotations

from adeu_api.paper_pipeline import derive_cleaned_source_text, select_best_flow


def _flow(*, label: str, passes: bool, word_count: int, candidate_hash: str) -> dict:
    checks = {"min_words": passes, "max_words": True}
    return {
        "label": label,
        "extract": {"result": {"word_count": word_count, "candidate_hash": candidate_hash}},
        "check": {"result": {"passes": passes, "checks": checks}},
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
