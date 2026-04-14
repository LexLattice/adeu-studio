from __future__ import annotations

import hashlib
import json
import shutil
from dataclasses import dataclass
from pathlib import Path

from .models import (
    AgenticDeObservedRestorationWriteEntry,
    AgenticDeObservedWriteEntry,
    LocalWriteKind,
)

DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT = Path("artifacts/agentic_de/v57/local_effect")
LOCAL_EFFECT_RUNTIME_DIRNAME = "runtime"
LOCAL_EFFECT_OBSERVER_DIRNAME = "_observer"
DEFAULT_LOCAL_EFFECT_TARGET_RELATIVE_PATH = Path("runtime/reference_patch_candidate.diff")
DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT = (
    "--- v57a bounded local effect patch candidate ---\n"
    "+ one bounded local write effect observed inside the designated sandbox root\n"
)
MAX_HASH_FILE_SIZE_BYTES = 100 * 1024 * 1024
MAX_TEXT_READ_SIZE_BYTES = 10 * 1024 * 1024
HASH_CHUNK_SIZE_BYTES = 8192


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


@dataclass(frozen=True)
class ObservedLocalRestorationEffect:
    designated_sandbox_root: str
    restoration_pre_state_ref: str
    restoration_observed_write_set: list[AgenticDeObservedRestorationWriteEntry]
    restoration_post_state_ref: str
    restoration_effect: str
    restoration_outcome: str
    restoration_boundedness_verdict: str
    restoration_boundedness_note: str


def resolve_designated_local_effect_sandbox_root(*, repo_root_path: Path) -> Path:
    return repo_root_path / DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


DEFAULT_LOCAL_EFFECT_PAYLOAD_SHA256 = _sha256_bytes(
    DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT.encode("utf-8")
)


def _sha256_file(path: Path) -> str:
    if path.stat().st_size > MAX_HASH_FILE_SIZE_BYTES:
        raise ValueError("file size exceeds safety limit for hashing")
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(HASH_CHUNK_SIZE_BYTES):
            digest.update(chunk)
    return digest.hexdigest()


def _read_text_with_size_guard(path: Path) -> str:
    if path.stat().st_size > MAX_TEXT_READ_SIZE_BYTES:
        raise ValueError("file size exceeds safety limit for text inspection")
    return path.read_text(encoding="utf-8")


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


def _assert_repo_contained_path(*, repo_root_path: Path, candidate: Path) -> None:
    repo_root_resolved = repo_root_path.resolve()
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_resolved)
    except ValueError as exc:
        raise ValueError(
            "sandbox anti-escape law forbids paths outside the repository root"
        ) from exc


def _assert_no_symlink_components(*, repo_root_path: Path, candidate: Path) -> None:
    current = repo_root_path.resolve()
    if current.exists() and current.is_symlink():
        raise ValueError("repository root may not be a symlink for V57-A local-effect observation")
    relative = candidate.relative_to(repo_root_path)
    for part in relative.parts:
        current = current / part
        if current.exists() and current.is_symlink():
            raise ValueError(
                "sandbox anti-escape law forbids symlink components from the repository root "
                "through the designated local-effect root"
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


def _ensure_clean_runtime_tree(*, repo_root_path: Path, sandbox_root: Path) -> None:
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=sandbox_root)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=sandbox_root)
    sandbox_root.mkdir(parents=True, exist_ok=True)
    for child_name in (LOCAL_EFFECT_RUNTIME_DIRNAME, LOCAL_EFFECT_OBSERVER_DIRNAME):
        child = sandbox_root / child_name
        _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=child)
        _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=child)
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
    _ensure_clean_runtime_tree(repo_root_path=repo_root_path, sandbox_root=sandbox_root)

    relative_target = Path(target_relative_path.strip())
    _assert_safe_relative_target(relative_target)
    target_path = sandbox_root / relative_target
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=target_path)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=target_path)
    _assert_within_designated_sandbox(sandbox_root=sandbox_root, candidate=target_path)

    pre_state_path = sandbox_root / LOCAL_EFFECT_OBSERVER_DIRNAME / "reference_pre_state.json"
    post_state_path = sandbox_root / LOCAL_EFFECT_OBSERVER_DIRNAME / "reference_post_state.json"
    pre_state_payload = _snapshot_sandbox_state(
        sandbox_root=sandbox_root,
        repo_root_path=repo_root_path,
    )
    _write_json(pre_state_path, pre_state_payload)

    target_path.parent.mkdir(parents=True, exist_ok=True)
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=target_path.parent)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=target_path.parent)
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
    effect_observed = write_kind == "create_new" or bool(payload_bytes)
    if effect_observed:
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
    actual_path_set = set(actual_relative_paths)
    expected_path_set = set(expected_paths)
    if not observed_write_set:
        observation_outcome = "no_effect_observed"
        boundedness_verdict = "bounded"
        boundedness_note = "no file content change was observed inside the designated sandbox root"
        observed_effect = "no local write effect observed inside the designated sandbox root"
    elif not actual_path_set.issubset(expected_path_set):
        observation_outcome = "out_of_scope_write_observed"
        boundedness_verdict = "failed"
        boundedness_note = (
            "observed writes escaped the checkpoint-entitled local-write scope even though "
            "they remained path-local"
        )
        observed_effect = (
            "observed write set did not match the checkpoint-entitled local-write target set"
        )
    elif actual_path_set != expected_path_set:
        observation_outcome = "mismatched_effect_observed"
        boundedness_verdict = "bounded"
        boundedness_note = (
            "effect stayed within the designated sandbox root but did not satisfy the full "
            "checkpoint-entitled target set"
        )
        observed_effect = (
            "observed local write stayed bounded but did not cover the full expected write set"
        )
    elif (
        expected_content_contains is not None
        and expected_content_contains not in _read_text_with_size_guard(target_path)
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


def observe_local_write_restoration_effect(
    *,
    repo_root_path: Path,
    restoration_target_relative_path: str,
    materialized_observed_content_text: str,
    expected_relative_paths: tuple[str, ...] | None = None,
    materialize_observed_effect: bool = True,
) -> ObservedLocalRestorationEffect:
    sandbox_root = resolve_designated_local_effect_sandbox_root(repo_root_path=repo_root_path)
    _ensure_clean_runtime_tree(repo_root_path=repo_root_path, sandbox_root=sandbox_root)

    relative_target = Path(restoration_target_relative_path.strip())
    _assert_safe_relative_target(relative_target)
    target_path = sandbox_root / relative_target
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=target_path)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=target_path)
    _assert_within_designated_sandbox(sandbox_root=sandbox_root, candidate=target_path)

    target_path.parent.mkdir(parents=True, exist_ok=True)
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=target_path.parent)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=target_path.parent)
    _assert_within_designated_sandbox(sandbox_root=sandbox_root, candidate=target_path.parent)

    payload_bytes = materialized_observed_content_text.encode("utf-8")
    if materialize_observed_effect:
        target_path.write_bytes(payload_bytes)

    pre_state_path = (
        sandbox_root / LOCAL_EFFECT_OBSERVER_DIRNAME / "reference_restoration_pre_state.json"
    )
    post_state_path = (
        sandbox_root / LOCAL_EFFECT_OBSERVER_DIRNAME / "reference_restoration_post_state.json"
    )
    pre_state_payload = _snapshot_sandbox_state(
        sandbox_root=sandbox_root,
        repo_root_path=repo_root_path,
    )
    _write_json(pre_state_path, pre_state_payload)

    existed_before_restoration = target_path.exists()
    restoration_observed_write_set: list[AgenticDeObservedRestorationWriteEntry]
    if existed_before_restoration:
        removed_content_sha256 = _sha256_file(target_path)
        bytes_removed = target_path.stat().st_size
        target_path.unlink()
        restoration_observed_write_set = [
            AgenticDeObservedRestorationWriteEntry(
                relative_path=_relative_display(target_path, repo_root_path=repo_root_path),
                restoration_operation="compensating_remove_create_new_artifact",
                existed_before_restoration=True,
                exists_after_restoration=target_path.exists(),
                bytes_removed=bytes_removed,
                removed_content_sha256=removed_content_sha256,
            )
        ]
    else:
        restoration_observed_write_set = []

    post_state_payload = _snapshot_sandbox_state(
        sandbox_root=sandbox_root,
        repo_root_path=repo_root_path,
    )
    _write_json(post_state_path, post_state_payload)

    actual_relative_paths = tuple(entry.relative_path for entry in restoration_observed_write_set)
    expected_paths = (
        expected_relative_paths
        if expected_relative_paths is not None
        else (_relative_display(target_path, repo_root_path=repo_root_path),)
    )
    actual_path_set = set(actual_relative_paths)
    expected_path_set = set(expected_paths)
    if not restoration_observed_write_set:
        restoration_outcome = "no_restoration_effect_observed"
        restoration_boundedness_verdict = "bounded"
        restoration_boundedness_note = (
            "no compensating restoration effect was observed inside the designated sandbox root"
        )
        restoration_effect = (
            "no bounded compensating restoration effect was observed inside the designated "
            "sandbox root"
        )
    elif not actual_path_set.issubset(expected_path_set):
        restoration_outcome = "restoration_out_of_scope_write_observed"
        restoration_boundedness_verdict = "failed"
        restoration_boundedness_note = (
            "observed restoration writes escaped the derived compensating scope even though "
            "they remained path-local"
        )
        restoration_effect = (
            "observed restoration write set did not match the derived compensating target set"
        )
    elif actual_path_set != expected_path_set:
        restoration_outcome = "restoration_mismatched_effect_observed"
        restoration_boundedness_verdict = "bounded"
        restoration_boundedness_note = (
            "restoration stayed within the designated sandbox root but did not satisfy the "
            "full derived compensating target set"
        )
        restoration_effect = (
            "observed restoration stayed bounded but did not cover the full expected "
            "compensating target set"
        )
    else:
        restoration_outcome = "restoration_effect_observed"
        restoration_boundedness_verdict = "bounded"
        restoration_boundedness_note = (
            "observed compensating restoration remained inside the designated sandbox root"
        )
        restoration_effect = (
            "observed bounded compensating restoration remained inside the designated sandbox "
            "root and matched the derived compensating target"
        )

    return ObservedLocalRestorationEffect(
        designated_sandbox_root=_relative_display(sandbox_root, repo_root_path=repo_root_path),
        restoration_pre_state_ref=_relative_display(pre_state_path, repo_root_path=repo_root_path),
        restoration_observed_write_set=restoration_observed_write_set,
        restoration_post_state_ref=_relative_display(
            post_state_path, repo_root_path=repo_root_path
        ),
        restoration_effect=restoration_effect,
        restoration_outcome=restoration_outcome,
        restoration_boundedness_verdict=restoration_boundedness_verdict,
        restoration_boundedness_note=restoration_boundedness_note,
    )
