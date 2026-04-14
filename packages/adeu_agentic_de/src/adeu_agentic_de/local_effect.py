from __future__ import annotations

import hashlib
import json
import shutil
from dataclasses import dataclass
from pathlib import Path

from .models import AgenticDeObservedWriteEntry, LocalWriteKind

DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT = Path("artifacts/agentic_de/v57/local_effect")
LOCAL_EFFECT_RUNTIME_DIRNAME = "runtime"
LOCAL_EFFECT_OBSERVER_DIRNAME = "_observer"
DEFAULT_LOCAL_EFFECT_TARGET_RELATIVE_PATH = Path("runtime/reference_patch_candidate.diff")
DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT = (
    "--- v57a bounded local effect patch candidate ---\n"
    "+ one bounded local write effect observed inside the designated sandbox root\n"
)


@dataclass(frozen=True)
class ObservedLocalWriteEffect:
    designated_sandbox_root: str
    pre_state_ref: str
    observed_write_set: list[AgenticDeObservedWriteEntry]
    post_state_ref: str
    observed_effect: str
    observation_outcome: str
    boundedness_verdict: str
    boundedness_note: str


def resolve_designated_local_effect_sandbox_root(*, repo_root_path: Path) -> Path:
    return repo_root_path / DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _relative_display(path: Path, *, repo_root_path: Path) -> str:
    return path.relative_to(repo_root_path).as_posix()


def _assert_safe_relative_target(relative_target: Path) -> None:
    if relative_target.is_absolute():
        raise ValueError("local-effect target must be relative to the designated sandbox root")
    if not relative_target.parts:
        raise ValueError("local-effect target must not be empty")
    if any(part in {"", ".", ".."} for part in relative_target.parts):
        raise ValueError("local-effect target may not use empty, dot, or parent traversal parts")
    if relative_target.parts[0] == LOCAL_EFFECT_OBSERVER_DIRNAME:
        raise ValueError("local-effect target may not write into the internal observer area")


def _assert_no_symlink_components(*, sandbox_root: Path, candidate: Path) -> None:
    current = sandbox_root
    if current.exists() and current.is_symlink():
        raise ValueError("designated local-effect sandbox root may not be a symlink")
    relative = candidate.relative_to(sandbox_root)
    for part in relative.parts:
        current = current / part
        if current.exists() and current.is_symlink():
            raise ValueError(
                "sandbox anti-escape law forbids symlink components inside the designated root"
            )


def _assert_within_designated_sandbox(*, sandbox_root: Path, candidate: Path) -> None:
    sandbox_resolved = sandbox_root.resolve()
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(sandbox_resolved)
    except ValueError as exc:
        raise ValueError(
            "sandbox anti-escape law forbids parent traversal or indirect redirection outside "
            "the designated local-effect root"
        ) from exc


def _ensure_clean_runtime_tree(*, sandbox_root: Path) -> None:
    sandbox_root.mkdir(parents=True, exist_ok=True)
    for child_name in (LOCAL_EFFECT_RUNTIME_DIRNAME, LOCAL_EFFECT_OBSERVER_DIRNAME):
        child = sandbox_root / child_name
        if child.exists():
            if child.is_symlink():
                raise ValueError("sandbox anti-escape law forbids symlink runtime helper paths")
            shutil.rmtree(child)
        child.mkdir(parents=True, exist_ok=True)


def _snapshot_sandbox_state(*, sandbox_root: Path, repo_root_path: Path) -> dict[str, object]:
    files: list[dict[str, object]] = []
    for path in sorted(sandbox_root.rglob("*")):
        if not path.is_file():
            continue
        if LOCAL_EFFECT_OBSERVER_DIRNAME in path.relative_to(sandbox_root).parts:
            continue
        if path.name == ".gitignore":
            continue
        files.append(
            {
                "relative_path": _relative_display(path, repo_root_path=repo_root_path),
                "size_bytes": path.stat().st_size,
                "content_sha256": _sha256_file(path),
            }
        )
    return {
        "sandbox_root": _relative_display(sandbox_root, repo_root_path=repo_root_path),
        "file_count": len(files),
        "files": files,
    }


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def observe_local_write_effect(
    *,
    repo_root_path: Path,
    write_kind: LocalWriteKind,
    target_relative_path: str,
    payload_text: str,
    expected_relative_paths: tuple[str, ...] | None = None,
    expected_content_contains: str | None = None,
) -> ObservedLocalWriteEffect:
    sandbox_root = resolve_designated_local_effect_sandbox_root(repo_root_path=repo_root_path)
    _ensure_clean_runtime_tree(sandbox_root=sandbox_root)

    relative_target = Path(target_relative_path.strip())
    _assert_safe_relative_target(relative_target)
    target_path = sandbox_root / relative_target
    _assert_no_symlink_components(sandbox_root=sandbox_root, candidate=target_path)
    _assert_within_designated_sandbox(sandbox_root=sandbox_root, candidate=target_path)

    pre_state_path = sandbox_root / LOCAL_EFFECT_OBSERVER_DIRNAME / "reference_pre_state.json"
    post_state_path = sandbox_root / LOCAL_EFFECT_OBSERVER_DIRNAME / "reference_post_state.json"
    pre_state_payload = _snapshot_sandbox_state(
        sandbox_root=sandbox_root,
        repo_root_path=repo_root_path,
    )
    _write_json(pre_state_path, pre_state_payload)

    target_path.parent.mkdir(parents=True, exist_ok=True)
    _assert_no_symlink_components(sandbox_root=sandbox_root, candidate=target_path.parent)
    _assert_within_designated_sandbox(sandbox_root=sandbox_root, candidate=target_path.parent)

    payload_bytes = payload_text.encode("utf-8")
    existed_before = target_path.exists()
    if write_kind == "create_new":
        if existed_before:
            raise ValueError("create_new local-write subset requires the target path to be absent")
        target_path.write_bytes(payload_bytes)
    elif write_kind == "append_only":
        if not existed_before:
            raise ValueError("append_only local-write subset requires the target path to exist")
        with target_path.open("ab") as handle:
            handle.write(payload_bytes)
    else:
        raise ValueError(f"unsupported local-write kind for V57-A: {write_kind}")

    observed_write_set: list[AgenticDeObservedWriteEntry]
    if payload_bytes:
        observed_write_set = [
            AgenticDeObservedWriteEntry(
                relative_path=_relative_display(target_path, repo_root_path=repo_root_path),
                write_kind=write_kind,
                existed_before=existed_before,
                bytes_written=len(payload_bytes),
                content_sha256=_sha256_file(target_path),
            )
        ]
    else:
        observed_write_set = []

    post_state_payload = _snapshot_sandbox_state(
        sandbox_root=sandbox_root,
        repo_root_path=repo_root_path,
    )
    _write_json(post_state_path, post_state_payload)

    actual_relative_paths = tuple(entry.relative_path for entry in observed_write_set)
    expected_paths = (
        expected_relative_paths
        if expected_relative_paths is not None
        else (_relative_display(target_path, repo_root_path=repo_root_path),)
    )
    if not observed_write_set:
        observation_outcome = "no_effect_observed"
        boundedness_verdict = "bounded"
        boundedness_note = "no file content change was observed inside the designated sandbox root"
        observed_effect = "no local write effect observed inside the designated sandbox root"
    elif any(path not in expected_paths for path in actual_relative_paths):
        observation_outcome = "out_of_scope_write_observed"
        boundedness_verdict = "failed"
        boundedness_note = (
            "observed writes escaped the checkpoint-entitled local-write scope even though "
            "they remained path-local"
        )
        observed_effect = (
            "observed write set did not match the checkpoint-entitled local-write target set"
        )
    elif (
        expected_content_contains is not None
        and expected_content_contains not in target_path.read_text(encoding="utf-8")
    ):
        observation_outcome = "mismatched_effect_observed"
        boundedness_verdict = "bounded"
        boundedness_note = (
            "effect stayed within the designated sandbox root but diverged semantically"
        )
        observed_effect = "observed local write stayed bounded but did not match expected content"
    else:
        observation_outcome = "bounded_effect_observed"
        boundedness_verdict = "bounded"
        boundedness_note = "observed local write remained inside the designated sandbox root"
        observed_effect = (
            "observed bounded local write remained inside the designated sandbox root and "
            "matched the checkpoint-entitled target"
        )

    return ObservedLocalWriteEffect(
        designated_sandbox_root=_relative_display(sandbox_root, repo_root_path=repo_root_path),
        pre_state_ref=_relative_display(pre_state_path, repo_root_path=repo_root_path),
        observed_write_set=observed_write_set,
        post_state_ref=_relative_display(post_state_path, repo_root_path=repo_root_path),
        observed_effect=observed_effect,
        observation_outcome=observation_outcome,
        boundedness_verdict=boundedness_verdict,
        boundedness_note=boundedness_note,
    )
