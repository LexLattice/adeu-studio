from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

from .models import AgenticDeObservedRestorationWriteEntry, AgenticDeObservedWriteEntry

DESIGNATED_WORKSPACE_CONTINUITY_ROOT = Path(
    "artifacts/agentic_de/v59/workspace_continuity"
)
WORKSPACE_CONTINUITY_RUNTIME_DIRNAME = "runtime"
WORKSPACE_CONTINUITY_OBSERVER_DIRNAME = "_observer"
DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH = Path(
    "runtime/reference_patch_candidate.diff"
)
DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT = (
    "--- v59a bounded persistent workspace continuity patch candidate ---\n"
    "+ one bounded create_new write observed inside the declared continuity root\n"
)
MAX_HASH_FILE_SIZE_BYTES = 100 * 1024 * 1024
MAX_TEXT_READ_SIZE_BYTES = 10 * 1024 * 1024
HASH_CHUNK_SIZE_BYTES = 8192
GOVERNED_LINEAGE_MARKER_NAME = "reference_governed_target_lineage.json"


@dataclass(frozen=True)
class WorkspaceContinuityState:
    declared_continuity_root: str
    snapshot_ref: str
    target_relative_path: str
    target_exists: bool
    target_content_sha256: str | None
    non_target_context_paths: tuple[str, ...]
    prior_governed_lineage_ref: str | None
    prior_governed_content_sha256: str | None
    marker_ref: str | None
    marker_parse_error: str | None


@dataclass(frozen=True)
class WorkspaceOccupancyAssessment:
    occupancy_verdict: str
    prior_governed_lineage_ref: str | None
    drift_posture_summary: str
    out_of_band_evidence_summary: str
    occupancy_witness_basis_summary: str
    root_origin_ids: list[str]


@dataclass(frozen=True)
class ObservedWorkspaceContinuityEffect:
    declared_continuity_root: str
    pre_state_ref: str
    observed_write_set: list[AgenticDeObservedWriteEntry]
    post_state_ref: str
    observed_effect: str
    observation_outcome: str
    boundedness_verdict: str
    boundedness_note: str
    post_state_summary: str


@dataclass(frozen=True)
class ObservedWorkspaceContinuityRestorationEffect:
    declared_continuity_root: str
    restoration_pre_state_ref: str
    restoration_observed_write_set: list[AgenticDeObservedRestorationWriteEntry]
    restoration_post_state_ref: str
    restoration_effect: str
    restoration_outcome: str
    restoration_boundedness_verdict: str
    restoration_boundedness_note: str
    prior_governed_state_baseline_summary: str
    prior_governed_state_baseline_match_verdict: str
    restoration_time_target_or_region_state_summary: str


def resolve_workspace_continuity_root(*, repo_root_path: Path) -> Path:
    return repo_root_path / DESIGNATED_WORKSPACE_CONTINUITY_ROOT


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
        raise ValueError("workspace-continuity target must be relative to the continuity root")
    if not relative_target.parts:
        raise ValueError("workspace-continuity target must not be empty")
    if any(part in {"", ".", ".."} for part in relative_target.parts):
        raise ValueError(
            "workspace-continuity target may not use empty, dot, or parent traversal parts"
        )
    if relative_target.parts[0] == WORKSPACE_CONTINUITY_OBSERVER_DIRNAME:
        raise ValueError(
            "workspace-continuity target may not write into the internal observer area"
        )


def _assert_repo_contained_path(*, repo_root_path: Path, candidate: Path) -> None:
    repo_root_resolved = repo_root_path.resolve()
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_resolved)
    except ValueError as exc:
        raise ValueError(
            "continuity anti-escape law forbids paths outside the repository root"
        ) from exc


def _assert_no_symlink_components(*, repo_root_path: Path, candidate: Path) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V59-A continuity")
    current = repo_root_path
    relative = candidate.relative_to(repo_root_path)
    for part in relative.parts:
        current = current / part
        if current.exists() and current.is_symlink():
            raise ValueError(
                "continuity anti-escape law forbids symlink components from the repository "
                "root through the declared continuity root"
            )


def _assert_within_continuity_root(*, continuity_root: Path, candidate: Path) -> None:
    continuity_resolved = continuity_root.resolve()
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(continuity_resolved)
    except ValueError as exc:
        raise ValueError(
            "continuity anti-escape law forbids parent traversal or indirect redirection "
            "outside the declared continuity root"
        ) from exc


def _ensure_continuity_tree(*, repo_root_path: Path, continuity_root: Path) -> None:
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=continuity_root)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=continuity_root)
    continuity_root.mkdir(parents=True, exist_ok=True)
    for child_name in (
        WORKSPACE_CONTINUITY_RUNTIME_DIRNAME,
        WORKSPACE_CONTINUITY_OBSERVER_DIRNAME,
    ):
        child = continuity_root / child_name
        _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=child)
        _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=child)
        if child.exists() and child.is_symlink():
            raise ValueError("continuity anti-escape law forbids symlink helper paths")
        child.mkdir(parents=True, exist_ok=True)


def _snapshot_continuity_state_payload(
    *,
    continuity_root: Path,
    repo_root_path: Path,
) -> dict[str, object]:
    files: list[dict[str, object]] = []
    for path in sorted(continuity_root.rglob("*")):
        if path.is_symlink():
            raise ValueError(
                "continuity anti-escape law forbids symlinked entries in continuity snapshots"
            )
        if not path.is_file():
            continue
        if WORKSPACE_CONTINUITY_OBSERVER_DIRNAME in path.relative_to(continuity_root).parts:
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
        "continuity_root": _relative_display(continuity_root, repo_root_path=repo_root_path),
        "file_count": len(files),
        "files": files,
    }


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def snapshot_workspace_continuity_state(
    *,
    repo_root_path: Path,
    target_relative_path: str,
    snapshot_name: str,
) -> WorkspaceContinuityState:
    continuity_root = resolve_workspace_continuity_root(repo_root_path=repo_root_path)
    _ensure_continuity_tree(repo_root_path=repo_root_path, continuity_root=continuity_root)

    relative_target = Path(target_relative_path.strip())
    _assert_safe_relative_target(relative_target)
    target_path = continuity_root / relative_target
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=target_path)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=target_path)
    _assert_within_continuity_root(continuity_root=continuity_root, candidate=target_path)

    snapshot_path = continuity_root / WORKSPACE_CONTINUITY_OBSERVER_DIRNAME / snapshot_name
    payload = _snapshot_continuity_state_payload(
        continuity_root=continuity_root,
        repo_root_path=repo_root_path,
    )
    _write_json(snapshot_path, payload)

    target_display = _relative_display(target_path, repo_root_path=repo_root_path)
    non_target_context_paths = tuple(
        file_entry["relative_path"]
        for file_entry in payload["files"]
        if file_entry["relative_path"] != target_display
    )

    marker_path = (
        continuity_root
        / WORKSPACE_CONTINUITY_OBSERVER_DIRNAME
        / GOVERNED_LINEAGE_MARKER_NAME
    )
    marker_ref: str | None = None
    marker_parse_error: str | None = None
    prior_governed_lineage_ref: str | None = None
    prior_governed_content_sha256: str | None = None
    if marker_path.exists():
        marker_ref = _relative_display(marker_path, repo_root_path=repo_root_path)
        try:
            marker_payload = json.loads(_read_text_with_size_guard(marker_path))
            if not isinstance(marker_payload, dict):
                raise ValueError("marker payload must be an object")
            marker_target = marker_payload.get("target_relative_path")
            marker_lineage_ref = marker_payload.get("governed_observation_ref")
            marker_content_sha = marker_payload.get("target_content_sha256")
            if (
                isinstance(marker_target, str)
                and marker_target == target_relative_path
                and isinstance(marker_lineage_ref, str)
                and marker_lineage_ref.strip()
                and isinstance(marker_content_sha, str)
                and marker_content_sha.strip()
            ):
                prior_governed_lineage_ref = marker_lineage_ref.strip()
                prior_governed_content_sha256 = marker_content_sha.strip()
            elif isinstance(marker_target, str) and marker_target == target_relative_path:
                marker_parse_error = "target marker fields malformed"
        except (ValueError, OSError) as exc:
            marker_parse_error = str(exc)

    target_exists = target_path.exists()
    target_content_sha256: str | None = None
    if target_exists:
        target_content_sha256 = _sha256_file(target_path)

    return WorkspaceContinuityState(
        declared_continuity_root=_relative_display(
            continuity_root,
            repo_root_path=repo_root_path,
        ),
        snapshot_ref=_relative_display(snapshot_path, repo_root_path=repo_root_path),
        target_relative_path=target_display,
        target_exists=target_exists,
        target_content_sha256=target_content_sha256,
        non_target_context_paths=non_target_context_paths,
        prior_governed_lineage_ref=prior_governed_lineage_ref,
        prior_governed_content_sha256=prior_governed_content_sha256,
        marker_ref=marker_ref,
        marker_parse_error=marker_parse_error,
    )


def classify_workspace_occupancy(
    *,
    state: WorkspaceContinuityState,
) -> WorkspaceOccupancyAssessment:
    non_target_count = len(state.non_target_context_paths)
    if not state.target_exists:
        return WorkspaceOccupancyAssessment(
            occupancy_verdict="unoccupied",
            prior_governed_lineage_ref=None,
            drift_posture_summary=(
                "target absent inside declared continuity root; non-target occupants remain "
                f"contextual only ({non_target_count} non-target files)"
            ),
            out_of_band_evidence_summary="no out-of-band target occupancy detected",
            occupancy_witness_basis_summary=(
                "declared continuity snapshot confirms target absence inside the selected "
                "target path"
            ),
            root_origin_ids=[
                f"continuity_root:{state.declared_continuity_root}",
                f"target:{state.target_relative_path}",
            ],
        )
    if state.marker_parse_error is not None:
        return WorkspaceOccupancyAssessment(
            occupancy_verdict="occupied_unknown",
            prior_governed_lineage_ref=None,
            drift_posture_summary=(
                "target occupied but prior governed continuity marker is malformed or unreadable"
            ),
            out_of_band_evidence_summary=(
                "occupancy origin could not be resolved from the declared continuity evidence "
                "chain"
            ),
            occupancy_witness_basis_summary=(
                "target present in declared continuity snapshot but marker parsing failed"
            ),
            root_origin_ids=[
                f"continuity_root:{state.declared_continuity_root}",
                f"target:{state.target_relative_path}",
            ],
        )
    if (
        state.prior_governed_lineage_ref is not None
        and state.prior_governed_content_sha256 is not None
    ):
        if state.target_content_sha256 == state.prior_governed_content_sha256:
            return WorkspaceOccupancyAssessment(
                occupancy_verdict="occupied_prior_governed_exact",
                prior_governed_lineage_ref=state.prior_governed_lineage_ref,
                drift_posture_summary=(
                    "target occupied by prior governed artifact with exact persisted content"
                ),
                out_of_band_evidence_summary=(
                    "no out-of-band target occupancy detected beyond the matched governed "
                    "lineage"
                ),
                occupancy_witness_basis_summary=(
                    "target present and governed lineage marker matches the persisted target "
                    "content hash"
                ),
                root_origin_ids=[
                    f"continuity_root:{state.declared_continuity_root}",
                    f"target:{state.target_relative_path}",
                    f"prior_lineage:{state.prior_governed_lineage_ref}",
                ],
            )
        return WorkspaceOccupancyAssessment(
            occupancy_verdict="occupied_prior_governed_drifted",
            prior_governed_lineage_ref=state.prior_governed_lineage_ref,
            drift_posture_summary=(
                "target occupied by prior governed artifact but current content diverges from "
                "the persisted governed marker"
            ),
            out_of_band_evidence_summary=(
                "target occupancy remains lineage-linked but content drift is unresolved in "
                "the starter slice"
            ),
            occupancy_witness_basis_summary=(
                "target present and governed lineage marker resolves, but persisted content "
                "hash differs from current target content"
            ),
            root_origin_ids=[
                f"continuity_root:{state.declared_continuity_root}",
                f"target:{state.target_relative_path}",
                f"prior_lineage:{state.prior_governed_lineage_ref}",
            ],
        )
    return WorkspaceOccupancyAssessment(
        occupancy_verdict="occupied_out_of_band",
        prior_governed_lineage_ref=None,
        drift_posture_summary=(
            "target occupied without a matching prior governed lineage marker inside the "
            "declared continuity root"
        ),
        out_of_band_evidence_summary=(
            "target presence is treated as out-of-band occupancy because no governed marker "
            "matches the selected target path"
        ),
        occupancy_witness_basis_summary=(
            "target present in declared continuity snapshot with no matching governed lineage "
            "marker for the selected target path"
        ),
        root_origin_ids=[
            f"continuity_root:{state.declared_continuity_root}",
            f"target:{state.target_relative_path}",
        ],
    )


def observe_workspace_continuity_create_new_effect(
    *,
    repo_root_path: Path,
    pre_state: WorkspaceContinuityState,
    target_relative_path: str,
    payload_text: str,
    expected_relative_paths: tuple[str, ...] | None = None,
    expected_content_contains: str | None = None,
) -> ObservedWorkspaceContinuityEffect:
    continuity_root = resolve_workspace_continuity_root(repo_root_path=repo_root_path)
    _ensure_continuity_tree(repo_root_path=repo_root_path, continuity_root=continuity_root)

    relative_target = Path(target_relative_path.strip())
    _assert_safe_relative_target(relative_target)
    target_path = continuity_root / relative_target
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=target_path)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=target_path)
    _assert_within_continuity_root(continuity_root=continuity_root, candidate=target_path)

    payload_bytes = payload_text.encode("utf-8")
    if pre_state.target_exists:
        raise ValueError("V59-A create_new continuity subset requires the target path to be absent")

    target_path.parent.mkdir(parents=True, exist_ok=True)
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=target_path.parent)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=target_path.parent)
    _assert_within_continuity_root(continuity_root=continuity_root, candidate=target_path.parent)

    target_path.write_bytes(payload_bytes)
    observed_write_set = [
        AgenticDeObservedWriteEntry(
            relative_path=_relative_display(target_path, repo_root_path=repo_root_path),
            write_kind="create_new",
            existed_before=False,
            bytes_written=len(payload_bytes),
            content_sha256=_sha256_file(target_path),
        )
    ]

    post_state = snapshot_workspace_continuity_state(
        repo_root_path=repo_root_path,
        target_relative_path=target_relative_path,
        snapshot_name="reference_post_state.json",
    )
    actual_relative_paths = tuple(entry.relative_path for entry in observed_write_set)
    expected_paths = (
        expected_relative_paths
        if expected_relative_paths is not None
        else (_relative_display(target_path, repo_root_path=repo_root_path),)
    )
    actual_path_set = set(actual_relative_paths)
    expected_path_set = set(expected_paths)
    if not actual_path_set.issubset(expected_path_set):
        observation_outcome = "out_of_scope_write_observed"
        boundedness_verdict = "failed"
        boundedness_note = (
            "observed writes escaped the checkpoint-entitled continuity target set even though "
            "they remained path-local"
        )
        observed_effect = (
            "observed write set did not match the continuity-entitled local-write target set"
        )
    elif actual_path_set != expected_path_set:
        observation_outcome = "mismatched_effect_observed"
        boundedness_verdict = "bounded"
        boundedness_note = (
            "effect stayed within the declared continuity root but did not satisfy the full "
            "continuity-entitled target set"
        )
        observed_effect = (
            "observed continuity local write stayed bounded but did not cover the full "
            "expected target set"
        )
    elif (
        expected_content_contains is not None
        and expected_content_contains not in _read_text_with_size_guard(target_path)
    ):
        observation_outcome = "mismatched_effect_observed"
        boundedness_verdict = "bounded"
        boundedness_note = (
            "effect stayed within the declared continuity root but diverged semantically"
        )
        observed_effect = (
            "observed continuity local write stayed bounded but did not match expected content"
        )
    else:
        observation_outcome = "bounded_effect_observed"
        boundedness_verdict = "bounded"
        boundedness_note = (
            "observed local write remained inside the declared continuity root"
        )
        observed_effect = (
            "observed bounded local write remained inside the declared continuity root and "
            "matched the continuity-entitled target"
        )

    return ObservedWorkspaceContinuityEffect(
        declared_continuity_root=pre_state.declared_continuity_root,
        pre_state_ref=pre_state.snapshot_ref,
        observed_write_set=observed_write_set,
        post_state_ref=post_state.snapshot_ref,
        observed_effect=observed_effect,
        observation_outcome=observation_outcome,
        boundedness_verdict=boundedness_verdict,
        boundedness_note=boundedness_note,
        post_state_summary=(
            f"target_present={'true' if post_state.target_exists else 'false'};"
            f"non_target_context_count={len(post_state.non_target_context_paths)}"
        ),
    )


def observe_workspace_continuity_create_new_restoration_effect(
    *,
    repo_root_path: Path,
    target_relative_path: str,
    expected_prior_governed_lineage_ref: str,
    expected_target_content_sha256: str,
    expected_relative_paths: tuple[str, ...] | None = None,
    materialize_restoration_effect: bool = True,
) -> ObservedWorkspaceContinuityRestorationEffect:
    continuity_root = resolve_workspace_continuity_root(repo_root_path=repo_root_path)
    _ensure_continuity_tree(repo_root_path=repo_root_path, continuity_root=continuity_root)

    relative_target = Path(target_relative_path.strip())
    _assert_safe_relative_target(relative_target)
    target_path = continuity_root / relative_target
    _assert_repo_contained_path(repo_root_path=repo_root_path, candidate=target_path)
    _assert_no_symlink_components(repo_root_path=repo_root_path, candidate=target_path)
    _assert_within_continuity_root(continuity_root=continuity_root, candidate=target_path)

    pre_state = snapshot_workspace_continuity_state(
        repo_root_path=repo_root_path,
        target_relative_path=target_relative_path,
        snapshot_name="reference_restoration_pre_state.json",
    )
    prior_governed_state_baseline_summary = (
        f"target_present={'true' if pre_state.target_exists else 'false'};"
        f"marker_present={'true' if pre_state.marker_ref is not None else 'false'};"
        "lineage_ref_present="
        f"{'true' if pre_state.prior_governed_lineage_ref is not None else 'false'};"
        f"non_target_context_count={len(pre_state.non_target_context_paths)}"
    )
    restoration_time_target_or_region_state_summary = (
        f"target_present={'true' if pre_state.target_exists else 'false'};"
        f"target_content_sha256={pre_state.target_content_sha256 or 'absent'};"
        f"marker_parse_error={pre_state.marker_parse_error or 'none'};"
        f"non_target_context_count={len(pre_state.non_target_context_paths)}"
    )
    if not pre_state.target_exists:
        raise ValueError(
            "V59-B continuity-safe restoration requires the selected target to exist "
            "inside the declared continuity root"
        )
    if pre_state.marker_parse_error is not None:
        raise ValueError(
            "V59-B continuity-safe restoration requires a readable prior governed "
            "continuity marker"
        )
    if pre_state.prior_governed_lineage_ref != expected_prior_governed_lineage_ref:
        raise ValueError(
            "V59-B continuity-safe restoration requires prior governed lineage to bind "
            "the shipped V59-A observation"
        )
    if pre_state.prior_governed_content_sha256 != expected_target_content_sha256:
        raise ValueError(
            "V59-B continuity-safe restoration requires prior governed-state baseline "
            "content to match the shipped V59-A observed artifact"
        )
    if pre_state.target_content_sha256 != expected_target_content_sha256:
        raise ValueError(
            "V59-B continuity-safe restoration requires current target state to match "
            "the shipped governed baseline before restore"
        )

    restoration_observed_write_set: list[AgenticDeObservedRestorationWriteEntry]
    if materialize_restoration_effect:
        removed_bytes = target_path.stat().st_size
        removed_sha256 = _sha256_file(target_path)
        target_path.unlink()
        restoration_observed_write_set = [
            AgenticDeObservedRestorationWriteEntry(
                relative_path=_relative_display(target_path, repo_root_path=repo_root_path),
                restoration_operation="compensating_remove_create_new_artifact",
                existed_before_restoration=True,
                exists_after_restoration=False,
                bytes_removed=removed_bytes,
                removed_content_sha256=removed_sha256,
            )
        ]
    else:
        restoration_observed_write_set = []

    post_state = snapshot_workspace_continuity_state(
        repo_root_path=repo_root_path,
        target_relative_path=target_relative_path,
        snapshot_name="reference_restoration_post_state.json",
    )
    actual_relative_paths = tuple(
        entry.relative_path for entry in restoration_observed_write_set
    )
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
            "no compensating restore effect was observed inside the declared continuity root"
        )
        restoration_effect = (
            "no continuity-safe compensating restore effect observed inside the declared "
            "continuity root"
        )
    elif not actual_path_set.issubset(expected_path_set):
        restoration_outcome = "restoration_out_of_scope_write_observed"
        restoration_boundedness_verdict = "failed"
        restoration_boundedness_note = (
            "restoration writes escaped the continuity-entitled compensating scope even "
            "though they remained path-local"
        )
        restoration_effect = (
            "observed continuity-safe restoration write set did not match the bounded "
            "compensating target set"
        )
    elif actual_path_set != expected_path_set or post_state.target_exists:
        restoration_outcome = "restoration_mismatched_effect_observed"
        restoration_boundedness_verdict = "bounded"
        restoration_boundedness_note = (
            "restoration stayed within the declared continuity root but did not fully "
            "remove the selected target state"
        )
        restoration_effect = (
            "observed continuity-safe restoration stayed bounded but did not match the "
            "full compensating restore expectation"
        )
    else:
        restoration_outcome = "restoration_effect_observed"
        restoration_boundedness_verdict = "bounded"
        restoration_boundedness_note = (
            "observed continuity-safe compensating restore remained inside the declared "
            "continuity root"
        )
        restoration_effect = (
            "observed bounded continuity-safe compensating restore removed the selected "
            "create_new target inside the declared continuity root"
        )

    return ObservedWorkspaceContinuityRestorationEffect(
        declared_continuity_root=pre_state.declared_continuity_root,
        restoration_pre_state_ref=pre_state.snapshot_ref,
        restoration_observed_write_set=restoration_observed_write_set,
        restoration_post_state_ref=post_state.snapshot_ref,
        restoration_effect=restoration_effect,
        restoration_outcome=restoration_outcome,
        restoration_boundedness_verdict=restoration_boundedness_verdict,
        restoration_boundedness_note=restoration_boundedness_note,
        prior_governed_state_baseline_summary=prior_governed_state_baseline_summary,
        prior_governed_state_baseline_match_verdict="matched",
        restoration_time_target_or_region_state_summary=(
            restoration_time_target_or_region_state_summary
        ),
    )


def write_workspace_governed_lineage_marker(
    *,
    repo_root_path: Path,
    target_relative_path: str,
    governed_observation_ref: str,
    target_content_sha256: str,
) -> str:
    continuity_root = resolve_workspace_continuity_root(repo_root_path=repo_root_path)
    _ensure_continuity_tree(repo_root_path=repo_root_path, continuity_root=continuity_root)
    marker_path = (
        continuity_root
        / WORKSPACE_CONTINUITY_OBSERVER_DIRNAME
        / GOVERNED_LINEAGE_MARKER_NAME
    )
    payload = {
        "target_relative_path": target_relative_path,
        "governed_observation_ref": governed_observation_ref,
        "target_content_sha256": target_content_sha256,
    }
    _write_json(marker_path, payload)
    return _relative_display(marker_path, repo_root_path=repo_root_path)
