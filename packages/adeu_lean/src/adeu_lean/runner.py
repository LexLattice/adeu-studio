from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path
from tempfile import NamedTemporaryFile

from adeu_ir import ProofInput

from .models import DEFAULT_SEMANTICS_VERSION, OBLIGATION_KINDS, LeanRequest, LeanResult

_OBLIGATION_TO_CORE_THEOREM = {
    "pred_closed_world": "pred_closed_world_missing_false",
    "exception_gating": "exception_gating_false_not_defeat",
    "conflict_soundness": "conflict_soundness",
}

_OBLIGATION_TO_THEOREM_TYPE = {
    "pred_closed_world": (
        "∀ (defs : String → Bool) (termId : String), defs termId = false → "
        "AdeuCore.evalPred { defs := defs, docs := fun _ => false } (.defined termId) = false"
    ),
    "exception_gating": (
        "∀ (ctx : AdeuCore.EvalCtx) (pred : AdeuCore.Pred), "
        "AdeuCore.evaluatable ctx pred → AdeuCore.evalPred ctx pred = false → "
        "¬ AdeuCore.exceptionDefeatsNorm ctx pred"
    ),
    "conflict_soundness": (
        "∀ (left right : Prop), "
        "AdeuCore.conflictCandidate left right → AdeuCore.conflict left right"
    ),
}


def _sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _sanitize_theorem_name(value: str) -> str:
    cleaned = re.sub(r"[^a-zA-Z0-9_]+", "_", value).strip("_")
    if not cleaned:
        cleaned = "adeu_theorem"
    if cleaned[0].isdigit():
        cleaned = f"t_{cleaned}"
    return cleaned


def _hash_inputs(inputs: list[ProofInput]) -> str:
    payload = [
        {
            "object_id": item.object_id,
            "json_path": item.json_path,
            "formula_hash": item.formula_hash,
        }
        for item in inputs
    ]
    serialized = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return _sha256(serialized)


def build_wrapper_theorem_source(
    *,
    theorem_id: str,
    obligation_kind: str,
    semantics_version: str,
    inputs_hash: str,
) -> str:
    theorem_name = _sanitize_theorem_name(theorem_id)
    core_theorem = _OBLIGATION_TO_CORE_THEOREM[obligation_kind]
    theorem_type = _OBLIGATION_TO_THEOREM_TYPE[obligation_kind]
    return (
        "import AdeuCore\n\n"
        f'def adeuSemanticsVersion_{theorem_name} : String := "{semantics_version}"\n'
        f'def adeuInputsHash_{theorem_name} : String := "{inputs_hash}"\n'
        f'def adeuObligationKind_{theorem_name} : String := "{obligation_kind}"\n\n'
        f"theorem {theorem_name} : {theorem_type} := by\n"
        f"  exact AdeuCore.{core_theorem}\n"
    )


def build_obligation_requests(
    *,
    theorem_prefix: str,
    inputs: list[ProofInput],
    semantics_version: str = DEFAULT_SEMANTICS_VERSION,
) -> list[LeanRequest]:
    requests: list[LeanRequest] = []
    inputs_hash = _hash_inputs(inputs)
    for obligation_kind in OBLIGATION_KINDS:
        theorem_id = f"{theorem_prefix}_{obligation_kind}"
        theorem_src = build_wrapper_theorem_source(
            theorem_id=theorem_id,
            obligation_kind=obligation_kind,
            semantics_version=semantics_version,
            inputs_hash=inputs_hash,
        )
        requests.append(
            LeanRequest(
                theorem_id=theorem_id,
                theorem_src=theorem_src,
                semantics_version=semantics_version,
                obligation_kind=obligation_kind,
                inputs=inputs,
                metadata={
                    "inputs_hash": inputs_hash,
                    "theorem_src_hash": _sha256(theorem_src),
                    "obligation_kind": obligation_kind,
                },
            )
        )
    return requests


def _run_command(
    *,
    cmd: list[str],
    cwd: Path,
    timeout_s: float,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        cwd=str(cwd),
        timeout=timeout_s,
    )


def _lean_version(
    *,
    cwd: Path,
    lake_bin: str,
    lean_bin: str,
    timeout_s: float,
) -> str | None:
    try:
        proc = _run_command(
            cmd=[lake_bin, "env", "lean", "--version"],
            cwd=cwd,
            timeout_s=timeout_s,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            return proc.stdout.strip().splitlines()[0]
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    try:
        proc = _run_command(cmd=[lean_bin, "--version"], cwd=cwd, timeout_s=timeout_s)
        if proc.returncode == 0 and proc.stdout.strip():
            return proc.stdout.strip().splitlines()[0]
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    return None


def run_lean_request(
    request: LeanRequest,
    *,
    timeout_ms: int,
    lean_bin: str,
    lake_bin: str = "lake",
    project_root: Path | None = None,
) -> LeanResult:
    if timeout_ms <= 0:
        raise RuntimeError("timeout_ms must be positive")
    project_dir = project_root or (Path(__file__).resolve().parents[2])
    timeout_s = max(1.0, timeout_ms / 1000.0)

    with NamedTemporaryFile(
        mode="w",
        suffix=".lean",
        prefix="adeu_obligation_",
        encoding="utf-8",
        dir=project_dir,
    ) as handle:
        handle.write(request.theorem_src)
        handle.flush()
        file_name = Path(handle.name).name

        proc: subprocess.CompletedProcess[str] | None = None
        used_cmd: list[str] | None = None
        errors: list[str] = []
        for cmd in ([lake_bin, "env", "lean", file_name], [lean_bin, file_name]):
            try:
                proc = _run_command(cmd=cmd, cwd=project_dir, timeout_s=timeout_s)
                used_cmd = cmd
                if proc.returncode == 0:
                    break
            except FileNotFoundError:
                errors.append(f"binary not found: {cmd[0]}")
                continue
            except subprocess.TimeoutExpired:
                return LeanResult(
                    theorem_id=request.theorem_id,
                    status="failed",
                    proof_hash=_sha256(request.theorem_src + "::timeout"),
                    lean_version=_lean_version(
                        cwd=project_dir,
                        lake_bin=lake_bin,
                        lean_bin=lean_bin,
                        timeout_s=1.0,
                    ),
                    details={"error": "lean proof-check timeout"},
                )

        if proc is None or used_cmd is None:
            return LeanResult(
                theorem_id=request.theorem_id,
                status="failed",
                proof_hash=_sha256(request.theorem_src + "::missing_binary"),
                lean_version=None,
                details={"error": "; ".join(sorted(set(errors)))},
            )

    result_hash = _sha256(
        request.theorem_src
        + "\n--stdout--\n"
        + (proc.stdout or "")
        + "\n--stderr--\n"
        + (proc.stderr or "")
        + "\n--cmd--\n"
        + " ".join(used_cmd)
    )
    status = "proved" if proc.returncode == 0 else "failed"
    details: dict[str, object] = {
        "returncode": proc.returncode,
        "command": used_cmd,
    }
    if proc.stdout.strip():
        details["stdout"] = proc.stdout.strip()
    if proc.stderr.strip():
        details["stderr"] = proc.stderr.strip()
    return LeanResult(
        theorem_id=request.theorem_id,
        status=status,
        proof_hash=result_hash,
        lean_version=_lean_version(
            cwd=project_dir,
            lake_bin=lake_bin,
            lean_bin=lean_bin,
            timeout_s=1.0,
        ),
        details=details,
    )
