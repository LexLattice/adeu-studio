from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

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

_RUNNER_TEMP_ROOT_NAME = ".adeu_lean_tmp"
_LEAN_WORKSPACE_TOKEN = "<LEAN_WORKSPACE>"
_LEAN_SOURCE_TOKEN = "<LEAN_SOURCE>"
_ANSI_ESCAPE_RE = re.compile(r"\x1B\[[0-?]*[ -/]*[@-~]")


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
    env = dict(os.environ)
    env.setdefault("NO_COLOR", "1")
    env.setdefault("CLICOLOR", "0")
    env.setdefault("CLICOLOR_FORCE", "0")
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        cwd=str(cwd),
        timeout=timeout_s,
        env=env,
    )


def _resolve_project_dir(project_root: Path | None) -> Path:
    candidate = (
        project_root.resolve()
        if project_root is not None
        else Path(__file__).resolve().parents[2]
    )
    sentinel_checks = (
        candidate / "pyproject.toml",
        candidate / "AdeuCore",
        candidate / "src" / "adeu_lean",
    )
    if (
        not sentinel_checks[0].is_file()
        or not sentinel_checks[1].is_dir()
        or not sentinel_checks[2].is_dir()
    ):
        raise RuntimeError(
            "unable to resolve adeu_lean project root: expected pyproject.toml, "
            "AdeuCore/, and src/adeu_lean/"
        )
    return candidate


def _derive_request_identity(request: LeanRequest) -> str:
    payload = {
        "theorem_id": request.theorem_id,
        "semantics_version": request.semantics_version,
        "obligation_kind_or_empty": request.obligation_kind or "",
        "theorem_src_hash": _sha256(request.theorem_src),
        "inputs_hash": _hash_inputs(request.inputs),
    }
    serialized = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return _sha256(serialized)


def _workspace_paths(*, project_dir: Path, request: LeanRequest) -> tuple[Path, Path, Path, str]:
    temp_root = project_dir / _RUNNER_TEMP_ROOT_NAME
    identity_hash = _derive_request_identity(request)
    workspace_dir = temp_root / f"req_{identity_hash}"
    source_path = workspace_dir / "obligation.lean"
    source_argument = source_path.relative_to(project_dir).as_posix()
    return temp_root, workspace_dir, source_path, source_argument


def _normalize_diagnostic_text(text: str, replacements: list[tuple[str, str]]) -> str:
    normalized = _ANSI_ESCAPE_RE.sub("", text)
    for source, target in replacements:
        normalized = normalized.replace(source, target)
    return normalized


def _build_projection_replacements(
    *,
    project_dir: Path,
    temp_root: Path,
    workspace_dir: Path,
    source_path: Path,
    source_argument: str,
) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()

    def add(source: str, target: str) -> None:
        if not source:
            return
        pair = (source, target)
        if pair in seen:
            return
        seen.add(pair)
        pairs.append(pair)

    temp_root_rel = temp_root.relative_to(project_dir).as_posix()
    workspace_rel = workspace_dir.relative_to(project_dir).as_posix()
    source_abs = source_path.resolve().as_posix()

    add(source_abs, _LEAN_SOURCE_TOKEN)
    add(source_argument, _LEAN_SOURCE_TOKEN)
    add(workspace_dir.resolve().as_posix(), _LEAN_WORKSPACE_TOKEN)
    add(workspace_rel, _LEAN_WORKSPACE_TOKEN)
    add(temp_root.resolve().as_posix(), _LEAN_WORKSPACE_TOKEN)
    add(temp_root_rel, _LEAN_WORKSPACE_TOKEN)
    return sorted(pairs, key=lambda pair: len(pair[0]), reverse=True)


def _normalize_command_for_hash(*, used_cmd: list[str], source_argument: str) -> list[str]:
    normalized = list(used_cmd)
    for idx, value in enumerate(normalized):
        if value == source_argument:
            normalized[idx] = _LEAN_SOURCE_TOKEN
            break
    return normalized


def _cleanup_workspace(workspace_dir: Path) -> None:
    try:
        shutil.rmtree(workspace_dir)
    except FileNotFoundError:
        return


def _workspace_overlap_or_collision_result(
    *,
    request: LeanRequest,
    workspace_dir: Path,
    source_path: Path,
) -> LeanResult:
    if source_path.exists():
        try:
            existing = source_path.read_text(encoding="utf-8")
        except OSError:
            existing = None
        if existing is not None and existing != request.theorem_src:
            return LeanResult(
                theorem_id=request.theorem_id,
                status="failed",
                proof_hash=_sha256(request.theorem_src + "::deterministic_collision"),
                lean_version=None,
                details={
                    "error": "deterministic temp-path collision with non-matching content",
                    "reason": "DETERMINISTIC_PATH_COLLISION",
                    "workspace": workspace_dir.name,
                },
            )

    return LeanResult(
        theorem_id=request.theorem_id,
        status="failed",
        proof_hash=_sha256(request.theorem_src + "::deterministic_overlap"),
        lean_version=None,
        details={
            "error": "deterministic temp-path overlap",
            "reason": "DETERMINISTIC_PATH_OVERLAP",
            "workspace": workspace_dir.name,
        },
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
    project_dir = _resolve_project_dir(project_root)
    timeout_s = max(1.0, timeout_ms / 1000.0)
    temp_root, workspace_dir, source_path, source_argument = _workspace_paths(
        project_dir=project_dir,
        request=request,
    )

    proc: subprocess.CompletedProcess[str] | None = None
    used_cmd: list[str] | None = None
    errors: list[str] = []
    claimed_workspace = False

    try:
        temp_root.mkdir(parents=True, exist_ok=True)
        try:
            workspace_dir.mkdir(mode=0o700)
            claimed_workspace = True
        except FileExistsError:
            return _workspace_overlap_or_collision_result(
                request=request,
                workspace_dir=workspace_dir,
                source_path=source_path,
            )

        source_path.write_text(request.theorem_src, encoding="utf-8")

        for cmd in ([lake_bin, "env", "lean", source_argument], [lean_bin, source_argument]):
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

        replacements = _build_projection_replacements(
            project_dir=project_dir,
            temp_root=temp_root,
            workspace_dir=workspace_dir,
            source_path=source_path,
            source_argument=source_argument,
        )
        projected_stdout = _normalize_diagnostic_text(proc.stdout or "", replacements).strip()
        projected_stderr = _normalize_diagnostic_text(proc.stderr or "", replacements).strip()
        projected_cmd = _normalize_command_for_hash(
            used_cmd=used_cmd,
            source_argument=source_argument,
        )
        result_hash = _sha256(
            request.theorem_src
            + "\n--stdout--\n"
            + projected_stdout
            + "\n--stderr--\n"
            + projected_stderr
            + "\n--cmd--\n"
            + " ".join(projected_cmd)
        )
        status = "proved" if proc.returncode == 0 else "failed"
        details: dict[str, object] = {
            "returncode": proc.returncode,
            "command": projected_cmd,
        }
        if projected_stdout:
            details["stdout"] = projected_stdout
        if projected_stderr:
            details["stderr"] = projected_stderr
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
    finally:
        if claimed_workspace:
            _cleanup_workspace(workspace_dir)
