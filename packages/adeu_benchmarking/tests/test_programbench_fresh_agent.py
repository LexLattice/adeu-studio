from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_benchmarking.programbench_fresh_agent import (
    FIGLET_TASK_ID,
    PACKET_MANIFEST_FILENAME,
    WORKER_PROMPT_FILENAME,
    FreshAgentHarnessError,
    ReferenceProbe,
    _bounded_excerpt,
    create_figlet_packet_from_visible_root,
    render_figlet_reconstruction_prompt,
)


def test_reference_probe_payload_requires_argv_list() -> None:
    with pytest.raises(FreshAgentHarnessError, match="argv as a list"):
        ReferenceProbe.from_payload({"argv": "-v", "stdin": ""})


def test_reference_probe_payload_rejects_nul_bytes() -> None:
    with pytest.raises(FreshAgentHarnessError, match="NUL"):
        ReferenceProbe.from_payload({"argv": ["hello\x00"], "stdin": ""})


def test_reference_probe_payload_rejects_host_absolute_paths() -> None:
    with pytest.raises(FreshAgentHarnessError, match="/workspace"):
        ReferenceProbe.from_payload(
            {"argv": ["-d", "/tmp/pb-fresh-agent-figlet-001/visible/fonts"], "stdin": ""}
        )


def test_reference_probe_payload_accepts_workspace_absolute_paths() -> None:
    probe = ReferenceProbe.from_payload({"argv": ["-d", "/workspace/fonts", "hello"], "stdin": ""})

    assert probe.argv == ("-d", "/workspace/fonts", "hello")


def test_bounded_excerpt_replaces_invalid_utf8() -> None:
    assert _bounded_excerpt(b"abc\xffdef", limit=5) == "abc�d"


def test_create_figlet_packet_from_visible_root_writes_reconstruction_prompt(
    tmp_path: Path,
) -> None:
    visible_root = tmp_path / "visible"
    visible_root.mkdir()
    (visible_root / "README").write_text("FIGlet task-visible readme\n")
    (visible_root / "figlet.6").write_text("FIGlet man page\n")

    output_dir = tmp_path / "packet"
    packet = create_figlet_packet_from_visible_root(
        visible_root=visible_root,
        output_dir=output_dir,
        image="example/image:task_cleanroom",
    )

    assert packet["task_id"] == FIGLET_TASK_ID
    assert packet["reconstruction_phase_posture"] == "reconstruction_only_no_code"
    assert packet["coding_phase_posture"] == "deferred_until_locked_implementation_checklist"

    manifest = json.loads((output_dir / PACKET_MANIFEST_FILENAME).read_text())
    assert manifest["worker_visible_file_count"] == 2
    prompt = (output_dir / WORKER_PROMPT_FILENAME).read_text()
    assert "Do not write code" in prompt
    assert "implementation_obligation_checklist" in prompt
    assert "STOP_STATUS: reconstruction_complete_no_code" in prompt


def test_create_figlet_packet_rejects_forbidden_visible_executable(tmp_path: Path) -> None:
    visible_root = tmp_path / "visible"
    visible_root.mkdir()
    (visible_root / "README").write_text("task-visible readme\n")
    (visible_root / "executable").write_text("reference executable must not leak\n")

    with pytest.raises(FreshAgentHarnessError, match="forbidden path"):
        create_figlet_packet_from_visible_root(
            visible_root=visible_root,
            output_dir=tmp_path / "packet",
        )


def test_reconstruction_prompt_names_forbidden_evidence() -> None:
    prompt = render_figlet_reconstruction_prompt(
        {
            "task_id": FIGLET_TASK_ID,
            "worker_visible_root": "/tmp/packet/visible",
            "forbidden_worker_evidence": [
                "hidden tests",
                "prior candidate code",
                "prior score or pass/fail result",
            ],
            "required_reconstruction_outputs": [
                "evidence_inventory",
                "implementation_obligation_checklist",
            ],
        }
    )

    assert "hidden tests" in prompt
    assert "prior candidate code" in prompt
    assert "prior score or pass/fail result" in prompt
    assert "The harness response is evidence" in prompt
    assert "/workspace/fonts" in prompt
