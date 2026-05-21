from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

FIGLET_TASK_ID = "cmatsuoka__figlet.202a0a8"
FIGLET_CLEANROOM_IMAGE = "programbench/cmatsuoka_1776_figlet.202a0a8:task_cleanroom"
PACKET_SCHEMA = "programbench_fresh_agent_packet@0"
REFERENCE_PROBE_SCHEMA = "programbench_reference_probe_observation@0"

WORKER_PROMPT_FILENAME = "RECONSTRUCTION_PHASE_PROMPT.md"
WORKER_README_FILENAME = "README_WORKER_PACKET.md"
PACKET_MANIFEST_FILENAME = "fresh_worker_packet.json"

FIGLET_VISIBLE_WORKSPACE_PATHS = ("FAQ", "LICENSE", "README", "figlet.6", "fonts")
FORBIDDEN_PACKET_PATH_NAMES = {
    "executable",
    "submission.tar.gz",
    "tests.json",
    "eval.json",
    "results.xml",
}
FORBIDDEN_WORKER_EVIDENCE = (
    "hidden tests",
    "ProgramBench evaluator output",
    "official evaluator feedback",
    "prior candidate code",
    "prior score or pass/fail result",
    "reference executable bytes or disassembly",
    "internet lookup",
    "external source repositories",
    "original upstream source beyond task-visible docs",
)


class FreshAgentHarnessError(RuntimeError):
    """Raised when the local fresh-agent harness cannot preserve clean boundaries."""


@dataclass(frozen=True)
class ReferenceProbe:
    argv: tuple[str, ...]
    stdin: str = ""

    @classmethod
    def from_payload(cls, payload: dict[str, Any]) -> "ReferenceProbe":
        argv = payload.get("argv")
        stdin = payload.get("stdin", "")
        if not isinstance(argv, list):
            raise FreshAgentHarnessError("reference probe payload must contain argv as a list")
        if not isinstance(stdin, str):
            raise FreshAgentHarnessError("reference probe stdin must be a string")
        _ensure_probe_argv(argv)
        return cls(argv=tuple(argv), stdin=stdin)


def _sha256_bytes(value: bytes) -> str:
    return "sha256:" + hashlib.sha256(value).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _bounded_excerpt(value: bytes, *, limit: int = 512) -> str:
    return value[:limit].decode("utf-8", errors="replace")


def _ensure_probe_argv(argv: list[str]) -> None:
    if not argv:
        raise FreshAgentHarnessError("reference probe argv must contain at least one argument")
    for token in argv:
        if not isinstance(token, str):
            raise FreshAgentHarnessError("reference probe argv entries must be strings")
        if "\x00" in token:
            raise FreshAgentHarnessError("reference probe argv entries must not contain NUL bytes")
        if len(token) > 4096:
            raise FreshAgentHarnessError("reference probe argv entries must be bounded")
        if token.startswith("/") and not token.startswith("/workspace/"):
            raise FreshAgentHarnessError(
                "reference probe argv absolute paths must point inside /workspace"
            )


def _relative_file_manifest(root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        relative_path = path.relative_to(root).as_posix()
        if any(part in FORBIDDEN_PACKET_PATH_NAMES for part in path.relative_to(root).parts):
            raise FreshAgentHarnessError(
                f"worker-visible packet contains forbidden path: {relative_path}"
            )
        rows.append(
            {
                "path": relative_path,
                "bytes": path.stat().st_size,
                "sha256": _sha256_file(path),
            }
        )
    if not rows:
        raise FreshAgentHarnessError("worker-visible packet must contain at least one file")
    return rows


def create_figlet_packet_from_visible_root(
    *,
    visible_root: Path,
    output_dir: Path,
    image: str = FIGLET_CLEANROOM_IMAGE,
) -> dict[str, Any]:
    """Create the fresh-worker packet metadata around an already materialized visible tree."""

    visible_root = visible_root.resolve()
    output_dir = output_dir.resolve()
    if not visible_root.is_dir():
        raise FreshAgentHarnessError(f"visible root does not exist: {visible_root}")
    output_dir.mkdir(parents=True, exist_ok=True)

    file_manifest = _relative_file_manifest(visible_root)
    packet = {
        "packet_schema": PACKET_SCHEMA,
        "task_id": FIGLET_TASK_ID,
        "source_image": image,
        "worker_visible_root": str(visible_root),
        "worker_visible_file_count": len(file_manifest),
        "worker_visible_file_manifest": file_manifest,
        "allowed_evidence_posture": "task_visible_files_and_brokered_reference_probes_only",
        "forbidden_worker_evidence": list(FORBIDDEN_WORKER_EVIDENCE),
        "reconstruction_phase_posture": "reconstruction_only_no_code",
        "coding_phase_posture": "deferred_until_locked_implementation_checklist",
        "probe_contract": {
            "probe_request_shape": {
                "argv": [
                    "argument tokens for /workspace/executable, excluding executable",
                    "use /workspace paths for reference probes, e.g. /workspace/fonts",
                ],
                "stdin": "string stdin payload",
            },
            "probe_response_shape": {
                "exit_code": "integer",
                "stdout_sha256": "sha256 hash",
                "stderr_sha256": "sha256 hash",
                "stdout_excerpt": "bounded UTF-8 replacement excerpt",
                "stderr_excerpt": "bounded UTF-8 replacement excerpt",
                "stdout_bytes": "integer",
                "stderr_bytes": "integer",
            },
            "probe_authority_posture": "reference_observation_only_not_hidden_test_oracle",
        },
        "required_reconstruction_outputs": [
            "evidence_inventory",
            "program_odeu_profile",
            "behavior_obligations",
            "implementation_obligation_checklist",
            "witness_probe_requests",
            "uncertainty_or_remand_list",
            "stop_status_reconstruction_complete_no_code",
        ],
    }

    manifest_path = output_dir / PACKET_MANIFEST_FILENAME
    prompt_path = output_dir / WORKER_PROMPT_FILENAME
    readme_path = output_dir / WORKER_README_FILENAME
    manifest_path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n")
    prompt_path.write_text(render_figlet_reconstruction_prompt(packet))
    readme_path.write_text(render_worker_packet_readme(packet))
    return packet


def build_figlet_worker_packet(
    output_dir: Path,
    *,
    image: str = FIGLET_CLEANROOM_IMAGE,
    overwrite: bool = False,
) -> dict[str, Any]:
    """Copy task-visible files from the cleanroom image and write a fresh worker packet."""

    output_dir = output_dir.resolve()
    if output_dir.exists() and any(output_dir.iterdir()):
        if not overwrite:
            raise FreshAgentHarnessError(
                f"output dir is not empty; pass overwrite=True to replace it: {output_dir}"
            )
        shutil.rmtree(output_dir)
    visible_root = output_dir / "visible"
    visible_root.mkdir(parents=True, exist_ok=True)

    container_id = _run_text(["docker", "create", image]).strip()
    try:
        for workspace_path in FIGLET_VISIBLE_WORKSPACE_PATHS:
            _run_text(
                [
                    "docker",
                    "cp",
                    f"{container_id}:/workspace/{workspace_path}",
                    str(visible_root / workspace_path),
                ]
            )
    finally:
        subprocess.run(["docker", "rm", "-f", container_id], check=False, capture_output=True)

    return create_figlet_packet_from_visible_root(
        visible_root=visible_root,
        output_dir=output_dir,
        image=image,
    )


def render_figlet_reconstruction_prompt(packet: dict[str, Any]) -> str:
    visible_root = packet["worker_visible_root"]
    forbidden = "\n".join(f"- {item}" for item in packet["forbidden_worker_evidence"])
    required = "\n".join(
        f"{index}. {item}"
        for index, item in enumerate(packet["required_reconstruction_outputs"], 1)
    )
    return f"""# ProgramBench Fresh Reconstruction Worker Packet

Task: `{packet["task_id"]}`

You are in the reconstruction phase only. Do not write code, draft code,
create files, propose patches, or package a submission in this phase.

Allowed evidence:
- Files under `{visible_root}`.
- Reference observations returned by the harness probe broker.

Forbidden evidence:
{forbidden}

Probe requests may ask the harness to run the reference executable. A request
must be JSON with this shape:

```json
{{"argv": ["-d", "/workspace/fonts", "hello"], "stdin": ""}}
```

The harness response is evidence, but it is not hidden-test truth and it does
not authorize coding.

Required reconstruction-phase output:
{required}

The implementation obligation checklist must be explicit enough that a later
coding phase can implement it without re-deciding the behavior ontology.

End with exactly:

```text
STOP_STATUS: reconstruction_complete_no_code
```
"""


def render_worker_packet_readme(packet: dict[str, Any]) -> str:
    return f"""# Fresh Worker Packet

This packet is for one local cleanroom ProgramBench reconstruction specimen.

- Task: `{packet["task_id"]}`
- Visible file root: `{packet["worker_visible_root"]}`
- Visible file count: `{packet["worker_visible_file_count"]}`
- Phase: reconstruction only
- Coding: deferred until an implementation checklist is reviewed and locked

Use `{WORKER_PROMPT_FILENAME}` as the worker instruction. Do not expose prior
attempts, evaluator results, hidden tests, candidate code, or benchmark scores
to the worker.
"""


def run_reference_probe(
    probe: ReferenceProbe,
    *,
    image: str = FIGLET_CLEANROOM_IMAGE,
    excerpt_bytes: int = 512,
) -> dict[str, Any]:
    """Run one argv-shaped reference probe and return bounded observation metadata."""

    payload = json.dumps({"argv": list(probe.argv), "stdin": probe.stdin}, sort_keys=True)
    script = r"""
import hashlib
import json
import subprocess
import sys

payload = json.loads(sys.argv[1])
completed = subprocess.run(
    ["/workspace/executable", *payload["argv"]],
    cwd="/workspace",
    input=payload["stdin"].encode("utf-8"),
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
)

def digest(value):
    return "sha256:" + hashlib.sha256(value).hexdigest()

def excerpt(value):
    limit = int(sys.argv[2])
    return value[:limit].decode("utf-8", errors="replace")

print(json.dumps({
    "exit_code": completed.returncode,
    "stdout_sha256": digest(completed.stdout),
    "stderr_sha256": digest(completed.stderr),
    "stdout_excerpt": excerpt(completed.stdout),
    "stderr_excerpt": excerpt(completed.stderr),
    "stdout_bytes": len(completed.stdout),
    "stderr_bytes": len(completed.stderr),
}, sort_keys=True))
"""
    completed = subprocess.run(
        [
            "docker",
            "run",
            "--rm",
            "--network",
            "none",
            "--entrypoint",
            "/usr/bin/python3",
            image,
            "-c",
            script,
            payload,
            str(excerpt_bytes),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        raise FreshAgentHarnessError(
            "reference probe failed before observation capture: "
            f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
        )
    observation = json.loads(completed.stdout)
    observation.update(
        {
            "observation_schema": REFERENCE_PROBE_SCHEMA,
            "task_id": FIGLET_TASK_ID,
            "argv": list(probe.argv),
            "stdin_sha256": _sha256_bytes(probe.stdin.encode("utf-8")),
            "probe_authority_posture": "reference_observation_only_not_hidden_test_oracle",
        }
    )
    return observation


def _run_text(argv: list[str]) -> str:
    completed = subprocess.run(argv, check=False, capture_output=True, text=True)
    if completed.returncode != 0:
        raise FreshAgentHarnessError(
            f"command failed: {argv!r}\nstdout={completed.stdout}\nstderr={completed.stderr}"
        )
    return completed.stdout


def _build_packet_command(args: argparse.Namespace) -> int:
    packet = build_figlet_worker_packet(
        Path(args.output_dir),
        image=args.image,
        overwrite=args.overwrite,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))
    return 0


def _reference_probe_command(args: argparse.Namespace) -> int:
    payload = json.loads(args.argv_json)
    stdin = args.stdin
    if args.stdin_file:
        stdin = Path(args.stdin_file).read_text()
    probe = ReferenceProbe.from_payload({"argv": payload, "stdin": stdin})
    observation = run_reference_probe(probe, image=args.image, excerpt_bytes=args.excerpt_bytes)
    print(json.dumps(observation, indent=2, sort_keys=True))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="python -m adeu_benchmarking.programbench_fresh_agent",
        description="ProgramBench fresh-context worker packet and reference probe broker.",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    packet_parser = subparsers.add_parser("build-figlet-packet")
    packet_parser.add_argument("output_dir")
    packet_parser.add_argument("--image", default=FIGLET_CLEANROOM_IMAGE)
    packet_parser.add_argument("--overwrite", action="store_true")
    packet_parser.set_defaults(func=_build_packet_command)

    probe_parser = subparsers.add_parser("reference-probe")
    probe_parser.add_argument(
        "--argv-json",
        required=True,
        help="JSON list of executable arguments",
    )
    probe_parser.add_argument("--stdin", default="")
    probe_parser.add_argument("--stdin-file")
    probe_parser.add_argument("--image", default=FIGLET_CLEANROOM_IMAGE)
    probe_parser.add_argument("--excerpt-bytes", type=int, default=512)
    probe_parser.set_defaults(func=_reference_probe_command)

    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
