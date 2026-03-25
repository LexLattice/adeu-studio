from __future__ import annotations

import hashlib
import re
import subprocess
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json, sha256_text

from .root_family import AuthorityBoundaryPolicy

ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA = "adeu_architecture_analysis_request@1"
V41A_V83_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS83.md#v41a_practical_analysis_request_contract@1"
)

AnalysisArtifactKind = Literal["documentation", "source_code", "configuration", "test"]
AnalysisSnapshotMode = Literal["committed_tree", "materialized_snapshot"]
CapturedInputKind = Literal["maintainer_brief", "accepted_doc"]

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")
_SHA1_RE = re.compile(r"^[0-9a-f]{40}$")
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_DOCUMENTATION_SUFFIXES = {".md", ".rst", ".txt"}
_SOURCE_CODE_SUFFIXES = {
    ".cjs",
    ".go",
    ".java",
    ".js",
    ".jsx",
    ".kt",
    ".lean",
    ".mjs",
    ".php",
    ".py",
    ".rb",
    ".rs",
    ".sh",
    ".ts",
    ".tsx",
}
_CONFIGURATION_SUFFIXES = {
    ".cfg",
    ".ini",
    ".json",
    ".lock",
    ".toml",
    ".yaml",
    ".yml",
}
_CONFIGURATION_NAMES = {"Dockerfile", "Makefile"}
_TEST_SUFFIXES = (
    ".spec.js",
    ".spec.jsx",
    ".spec.mjs",
    ".spec.py",
    ".spec.ts",
    ".spec.tsx",
    ".test.js",
    ".test.jsx",
    ".test.mjs",
    ".test.py",
    ".test.ts",
    ".test.tsx",
    "_test.py",
)


def _validation_context(
    repository_root: Path | None = None,
    **extra: Any,
) -> dict[str, Any]:
    context = {"repository_root": repository_root}
    context.update(extra)
    return context


def _resolve_repository_root(explicit_root: Path | None = None) -> Path:
    if explicit_root is not None:
        return explicit_root.resolve(strict=True)
    return repo_root(anchor=Path(__file__))


def _normalize_repo_relative_path(raw_path: str, *, field_name: str) -> str:
    value = raw_path.strip().replace("\\", "/")
    if not value:
        raise ValueError(f"{field_name} must not be empty")
    if value.startswith("/") or value.startswith("\\") or _WINDOWS_ABSOLUTE_PATH_RE.match(value):
        raise ValueError(f"{field_name} must be repo-relative")
    parts: list[str] = []
    for part in value.split("/"):
        if part in ("", "."):
            continue
        if part == "..":
            if not parts:
                raise ValueError(f"{field_name} must not escape repository root")
            parts.pop()
            continue
        parts.append(part)
    if not parts:
        raise ValueError(f"{field_name} resolves to repository root")
    return "/".join(parts)


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return normalized


def _assert_sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return sorted(normalized)


def _dump_json_payload(model: BaseModel) -> dict[str, Any]:
    return model.model_dump(mode="json", exclude_none=False)


def _run_git(
    repository_root: Path,
    *args: str,
    binary: bool = False,
) -> subprocess.CompletedProcess[bytes] | subprocess.CompletedProcess[str]:
    kwargs: dict[str, Any] = {
        "cwd": repository_root,
        "capture_output": True,
        "check": False,
    }
    if not binary:
        kwargs["text"] = True
        kwargs["encoding"] = "utf-8"
    result = subprocess.run(["git", *args], **kwargs)
    if result.returncode != 0:
        stderr = result.stderr.decode("utf-8", errors="replace") if binary else result.stderr
        raise ValueError(stderr.strip() or f"git {' '.join(args)} failed")
    return result


def _sha256_git_text(
    path: str,
    *,
    repository_root: Path,
    rev: str,
) -> str:
    result = _run_git(repository_root, "show", f"{rev}:{path}", binary=True)
    return hashlib.sha256(result.stdout).hexdigest()


def _sha256_repo_file(path: str, *, repository_root: Path) -> str:
    file_path = repository_root / path
    if not file_path.is_file():
        raise ValueError(f"referenced repo-relative path does not exist: {path}")
    return sha256_text(file_path.read_text(encoding="utf-8"))


def _path_is_within_prefix(path: str, prefix: str) -> bool:
    return path == prefix or path.startswith(f"{prefix}/")


def _path_is_excluded(path: str, exclusions: list[str]) -> bool:
    return any(_path_is_within_prefix(path, exclusion) for exclusion in exclusions)


def _infer_artifact_kind(path: str) -> AnalysisArtifactKind:
    normalized = _normalize_repo_relative_path(path, field_name="path")
    parts = normalized.split("/")
    name = parts[-1]
    suffix = Path(name).suffix.lower()
    lowered_name = name.lower()
    if (
        "tests" in parts
        or lowered_name == "tests.py"
        or lowered_name.startswith("test_")
        or any(lowered_name.endswith(suffix_name) for suffix_name in _TEST_SUFFIXES)
    ):
        return "test"
    if suffix in _DOCUMENTATION_SUFFIXES:
        return "documentation"
    if name in _CONFIGURATION_NAMES or suffix in _CONFIGURATION_SUFFIXES:
        return "configuration"
    if suffix in _SOURCE_CODE_SUFFIXES:
        return "source_code"
    raise ValueError(f"unable to infer allowed artifact kind for {normalized}")


def _canonical_source_set_hash_basis(payload: dict[str, Any]) -> dict[str, Any]:
    return deepcopy(payload)


def compute_adeu_architecture_analysis_source_set_hash(payload: dict[str, Any]) -> str:
    return sha256_canonical_json(_canonical_source_set_hash_basis(payload))


class AnalysisRequestScope(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    subtree_root: str
    include_paths: list[str] = Field(default_factory=list)
    exclude_paths: list[str] = Field(default_factory=list)
    allowed_artifact_kinds: list[AnalysisArtifactKind]

    @model_validator(mode="after")
    def _validate_scope(self) -> AnalysisRequestScope:
        object.__setattr__(
            self,
            "subtree_root",
            _normalize_repo_relative_path(self.subtree_root, field_name="subtree_root"),
        )
        object.__setattr__(
            self,
            "include_paths",
            sorted(
                {
                    _normalize_repo_relative_path(path, field_name="include_paths")
                    for path in self.include_paths
                }
            ),
        )
        object.__setattr__(
            self,
            "exclude_paths",
            sorted(
                {
                    _normalize_repo_relative_path(path, field_name="exclude_paths")
                    for path in self.exclude_paths
                }
            ),
        )
        allowed_kinds = sorted(set(self.allowed_artifact_kinds))
        if len(allowed_kinds) != len(self.allowed_artifact_kinds):
            raise ValueError("allowed_artifact_kinds must not contain duplicates")
        object.__setattr__(self, "allowed_artifact_kinds", allowed_kinds)
        return self


class AnalysisSnapshotIdentity(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    commit_sha: str | None = None
    tree_sha: str | None = None
    snapshot_manifest_ref: str | None = None
    snapshot_manifest_hash: str | None = None

    @model_validator(mode="after")
    def _validate_identity_shape(self) -> AnalysisSnapshotIdentity:
        if self.commit_sha is not None:
            commit_sha = _assert_non_empty_text(self.commit_sha, field_name="commit_sha")
            if not _SHA1_RE.fullmatch(commit_sha):
                raise ValueError("commit_sha must be a 40-character lowercase hex git id")
            object.__setattr__(self, "commit_sha", commit_sha)
        if self.tree_sha is not None:
            tree_sha = _assert_non_empty_text(self.tree_sha, field_name="tree_sha")
            if not _SHA1_RE.fullmatch(tree_sha):
                raise ValueError("tree_sha must be a 40-character lowercase hex git id")
            object.__setattr__(self, "tree_sha", tree_sha)
        if self.snapshot_manifest_ref is not None:
            object.__setattr__(
                self,
                "snapshot_manifest_ref",
                _normalize_repo_relative_path(
                    self.snapshot_manifest_ref,
                    field_name="snapshot_manifest_ref",
                ),
            )
        if self.snapshot_manifest_hash is not None:
            snapshot_manifest_hash = _assert_non_empty_text(
                self.snapshot_manifest_hash,
                field_name="snapshot_manifest_hash",
            )
            if not _SHA256_RE.fullmatch(snapshot_manifest_hash):
                raise ValueError(
                    "snapshot_manifest_hash must be a 64-character lowercase hex digest"
                )
            object.__setattr__(self, "snapshot_manifest_hash", snapshot_manifest_hash)
        return self


class CapturedInput(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    input_ref: str
    input_kind: CapturedInputKind
    label: str
    content: str
    content_sha256: str

    @model_validator(mode="after")
    def _validate_input(self) -> CapturedInput:
        object.__setattr__(
            self,
            "input_ref",
            _assert_non_empty_text(self.input_ref, field_name="input_ref"),
        )
        object.__setattr__(
            self,
            "label",
            _assert_non_empty_text(self.label, field_name="label"),
        )
        object.__setattr__(
            self,
            "content",
            _assert_non_empty_text(self.content, field_name="content"),
        )
        content_sha256 = _assert_non_empty_text(
            self.content_sha256,
            field_name="content_sha256",
        )
        if not _SHA256_RE.fullmatch(content_sha256):
            raise ValueError("content_sha256 must be a 64-character lowercase hex digest")
        if sha256_text(self.content) != content_sha256:
            raise ValueError("content_sha256 must match content")
        object.__setattr__(self, "content_sha256", content_sha256)
        return self


class AuthorityBoundaryPolicyPin(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    policy_ref: str | None = None
    inline_policy: AuthorityBoundaryPolicy | None = None

    @model_validator(mode="after")
    def _validate_policy_pin(self, info: ValidationInfo) -> AuthorityBoundaryPolicyPin:
        if (self.policy_ref is None) == (self.inline_policy is None):
            raise ValueError(
                "authority_boundary_policy must provide exactly one of "
                "policy_ref or inline_policy"
            )
        if self.policy_ref is not None:
            policy_ref = _assert_non_empty_text(self.policy_ref, field_name="policy_ref")
            object.__setattr__(self, "policy_ref", policy_ref)
            repository_root = info.context.get("repository_root") if info.context else None
            if repository_root is not None:
                policy_path = policy_ref.split("#", 1)[0]
                if not policy_path.startswith("docs/"):
                    raise ValueError("policy_ref must resolve to a repo-local docs path")
                if not (repository_root / policy_path).is_file():
                    raise ValueError(f"policy_ref does not exist: {policy_path}")
        return self


class ArchitectureAnalysisSourceItem(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    path: str
    artifact_kind: AnalysisArtifactKind
    sha256: str

    @model_validator(mode="after")
    def _validate_item(self, info: ValidationInfo) -> ArchitectureAnalysisSourceItem:
        normalized_path = _normalize_repo_relative_path(self.path, field_name="path")
        object.__setattr__(self, "path", normalized_path)
        sha256 = _assert_non_empty_text(self.sha256, field_name="sha256")
        if not _SHA256_RE.fullmatch(sha256):
            raise ValueError("sha256 must be a 64-character lowercase hex digest")
        object.__setattr__(self, "sha256", sha256)
        inferred_kind = _infer_artifact_kind(normalized_path)
        if self.artifact_kind != inferred_kind:
            raise ValueError(
                f"artifact_kind for {normalized_path} must be {inferred_kind!r}, "
                f"got {self.artifact_kind!r}"
            )
        repository_root = info.context.get("repository_root") if info.context else None
        snapshot_mode = info.context.get("snapshot_mode") if info.context else None
        snapshot_identity = info.context.get("snapshot_identity") if info.context else None
        if (
            repository_root is not None
            and snapshot_mode is not None
            and snapshot_identity is not None
        ):
            if snapshot_mode == "committed_tree":
                rev = snapshot_identity.commit_sha or snapshot_identity.tree_sha
                if rev is None:
                    raise ValueError("snapshot_identity must bind commit_sha or tree_sha")
                actual = _sha256_git_text(normalized_path, repository_root=repository_root, rev=rev)
            else:
                actual = _sha256_repo_file(normalized_path, repository_root=repository_root)
            if actual != sha256:
                raise ValueError(f"sha256 does not match snapshot contents for {normalized_path}")
        return self


class ArchitectureAnalysisSourceSet(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    items: list[ArchitectureAnalysisSourceItem]

    @model_validator(mode="after")
    def _validate_items(self) -> ArchitectureAnalysisSourceSet:
        if not self.items:
            raise ValueError("source_set.items must not be empty")
        paths = [item.path for item in self.items]
        normalized_paths = sorted(paths)
        if len(normalized_paths) != len(set(normalized_paths)):
            raise ValueError("source_set.items must not contain duplicate normalized paths")
        if normalized_paths != paths:
            items_by_path = {item.path: item for item in self.items}
            object.__setattr__(self, "items", [items_by_path[path] for path in normalized_paths])
        return self


class AdeuArchitectureAnalysisRequest(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA]
    analysis_request_id: str
    repo_root_ref: str
    request_scope: AnalysisRequestScope
    snapshot_mode: AnalysisSnapshotMode
    snapshot_identity: AnalysisSnapshotIdentity
    source_set: ArchitectureAnalysisSourceSet
    source_set_hash: str
    maintainer_brief_refs: list[str]
    accepted_doc_refs: list[str]
    declared_non_goals: list[str] = Field(default_factory=list)
    authority_boundary_policy: AuthorityBoundaryPolicyPin
    settlement_frame_ref: str | None = None
    captured_inputs: list[CapturedInput] = Field(default_factory=list)
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_request(self, info: ValidationInfo) -> AdeuArchitectureAnalysisRequest:
        object.__setattr__(
            self,
            "analysis_request_id",
            _assert_non_empty_text(self.analysis_request_id, field_name="analysis_request_id"),
        )
        object.__setattr__(
            self,
            "repo_root_ref",
            _assert_non_empty_text(self.repo_root_ref, field_name="repo_root_ref"),
        )
        object.__setattr__(
            self,
            "maintainer_brief_refs",
            _assert_sorted_unique(self.maintainer_brief_refs, field_name="maintainer_brief_refs"),
        )
        object.__setattr__(
            self,
            "accepted_doc_refs",
            _assert_sorted_unique(self.accepted_doc_refs, field_name="accepted_doc_refs"),
        )
        object.__setattr__(
            self,
            "declared_non_goals",
            _assert_sorted_unique(self.declared_non_goals, field_name="declared_non_goals"),
        )
        object.__setattr__(
            self,
            "notes",
            _assert_sorted_unique(self.notes, field_name="notes"),
        )
        if self.settlement_frame_ref is not None:
            object.__setattr__(
                self,
                "settlement_frame_ref",
                _assert_non_empty_text(
                    self.settlement_frame_ref,
                    field_name="settlement_frame_ref",
                ),
            )

        if self.snapshot_mode == "committed_tree":
            if (
                self.snapshot_identity.commit_sha is None
                and self.snapshot_identity.tree_sha is None
            ):
                raise ValueError("committed_tree requires commit_sha or tree_sha")
            if (
                self.snapshot_identity.snapshot_manifest_ref is not None
                or self.snapshot_identity.snapshot_manifest_hash is not None
            ):
                raise ValueError("committed_tree must not bind snapshot manifest identity")
        else:
            if (
                self.snapshot_identity.snapshot_manifest_ref is None
                and self.snapshot_identity.snapshot_manifest_hash is None
            ):
                raise ValueError(
                    "materialized_snapshot requires snapshot_manifest_ref or snapshot_manifest_hash"
                )
            if (
                self.snapshot_identity.commit_sha is not None
                or self.snapshot_identity.tree_sha is not None
            ):
                raise ValueError("materialized_snapshot must not bind commit_sha or tree_sha")

        captured_input_ids = {item.input_ref: item for item in self.captured_inputs}
        if len(captured_input_ids) != len(self.captured_inputs):
            raise ValueError("captured_inputs must not contain duplicate input_ref")

        source_item_by_path = {item.path: item for item in self.source_set.items}
        scope = self.request_scope
        for path in source_item_by_path:
            if _path_is_excluded(path, scope.exclude_paths):
                raise ValueError(f"source_set item {path} is excluded by request_scope")
            in_subtree = _path_is_within_prefix(path, scope.subtree_root)
            is_explicit_addition = path in scope.include_paths
            if not in_subtree and not is_explicit_addition:
                raise ValueError(f"source_set item {path} is outside request_scope")
            if source_item_by_path[path].artifact_kind not in scope.allowed_artifact_kinds:
                raise ValueError(f"source_set item {path} violates allowed_artifact_kinds")

        expected_hash = compute_adeu_architecture_analysis_source_set_hash(
            self.source_set.model_dump(mode="json", exclude_none=False)
        )
        if self.source_set_hash != expected_hash:
            raise ValueError("source_set_hash must match canonical source_set payload")

        if not self.maintainer_brief_refs:
            raise ValueError("maintainer_brief_refs must not be empty")
        if not self.accepted_doc_refs:
            raise ValueError("accepted_doc_refs must not be empty")

        def _validate_ref(ref: str, *, field_name: str, expected_kind: CapturedInputKind) -> None:
            source_item = source_item_by_path.get(ref)
            if source_item is not None:
                if source_item.artifact_kind != "documentation":
                    raise ValueError(f"{field_name} ref {ref!r} must point to documentation")
                return
            captured = captured_input_ids.get(ref)
            if captured is None:
                raise ValueError(
                    f"{field_name} ref {ref!r} must resolve to source_set content "
                    "or captured_inputs"
                )
            if captured.input_kind != expected_kind:
                raise ValueError(f"{field_name} ref {ref!r} has wrong captured input kind")

        for ref in self.maintainer_brief_refs:
            _validate_ref(ref, field_name="maintainer_brief_refs", expected_kind="maintainer_brief")
        for ref in self.accepted_doc_refs:
            _validate_ref(ref, field_name="accepted_doc_refs", expected_kind="accepted_doc")

        return self


def _list_committed_files(
    scope: AnalysisRequestScope,
    *,
    repository_root: Path,
    rev: str,
) -> list[str]:
    subtree_result = _run_git(
        repository_root,
        "ls-tree",
        "-r",
        "--name-only",
        rev,
        "--",
        scope.subtree_root,
    )
    paths = {
        _normalize_repo_relative_path(path, field_name="request_scope.subtree_root")
        for path in subtree_result.stdout.splitlines()
        if path.strip()
    }
    for include_path in scope.include_paths:
        _run_git(repository_root, "cat-file", "-e", f"{rev}:{include_path}")
        paths.add(include_path)
    return sorted(paths)


def _list_materialized_snapshot_files(
    scope: AnalysisRequestScope,
    *,
    repository_root: Path,
) -> list[str]:
    subtree_path = repository_root / scope.subtree_root
    if not subtree_path.is_dir():
        raise ValueError(f"subtree_root does not exist as a directory: {scope.subtree_root}")
    paths: set[str] = set()
    for file_path in subtree_path.rglob("*"):
        if file_path.is_file():
            paths.add(
                _normalize_repo_relative_path(
                    str(file_path.relative_to(repository_root)),
                    field_name="subtree_root",
                )
            )
    for include_path in scope.include_paths:
        candidate = repository_root / include_path
        if not candidate.is_file():
            raise ValueError(f"include_paths entry does not exist as a file: {include_path}")
        paths.add(include_path)
    return sorted(paths)


def capture_adeu_architecture_analysis_source_set_payload(
    *,
    request_scope: dict[str, Any] | AnalysisRequestScope,
    snapshot_mode: AnalysisSnapshotMode,
    snapshot_identity: dict[str, Any] | AnalysisSnapshotIdentity,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    scope = (
        request_scope
        if isinstance(request_scope, AnalysisRequestScope)
        else AnalysisRequestScope.model_validate(request_scope)
    )
    identity = (
        snapshot_identity
        if isinstance(snapshot_identity, AnalysisSnapshotIdentity)
        else AnalysisSnapshotIdentity.model_validate(snapshot_identity)
    )
    if snapshot_mode == "committed_tree":
        rev = identity.commit_sha or identity.tree_sha
        if rev is None:
            raise ValueError("committed_tree source-set capture requires commit_sha or tree_sha")
        candidate_paths = _list_committed_files(scope, repository_root=root, rev=rev)
        items = [
            {
                "path": path,
                "artifact_kind": _infer_artifact_kind(path),
                "sha256": _sha256_git_text(path, repository_root=root, rev=rev),
            }
            for path in candidate_paths
            if not _path_is_excluded(path, scope.exclude_paths)
            and _infer_artifact_kind(path) in scope.allowed_artifact_kinds
        ]
    else:
        candidate_paths = _list_materialized_snapshot_files(scope, repository_root=root)
        items = [
            {
                "path": path,
                "artifact_kind": _infer_artifact_kind(path),
                "sha256": _sha256_repo_file(path, repository_root=root),
            }
            for path in candidate_paths
            if not _path_is_excluded(path, scope.exclude_paths)
            and _infer_artifact_kind(path) in scope.allowed_artifact_kinds
        ]
    return _dump_json_payload(
        ArchitectureAnalysisSourceSet.model_validate(
            {"items": items},
            context=_validation_context(
                root,
                snapshot_mode=snapshot_mode,
                snapshot_identity=identity,
            ),
        )
    )


def canonicalize_adeu_architecture_analysis_request_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    snapshot_mode = payload.get("snapshot_mode")
    snapshot_identity_payload = payload.get("snapshot_identity", {})
    snapshot_identity = AnalysisSnapshotIdentity.model_validate(snapshot_identity_payload)
    return _dump_json_payload(
        AdeuArchitectureAnalysisRequest.model_validate(
            payload,
            context=_validation_context(
                root,
                snapshot_mode=snapshot_mode,
                snapshot_identity=snapshot_identity,
            ),
        )
    )


def materialize_adeu_architecture_analysis_request_payload(
    payload_without_source_set: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    payload = deepcopy(payload_without_source_set)
    snapshot_mode = payload["snapshot_mode"]
    snapshot_identity = payload["snapshot_identity"]
    request_scope = payload["request_scope"]
    source_set = capture_adeu_architecture_analysis_source_set_payload(
        request_scope=request_scope,
        snapshot_mode=snapshot_mode,
        snapshot_identity=snapshot_identity,
        repository_root=root,
    )
    payload["source_set"] = source_set
    payload["source_set_hash"] = compute_adeu_architecture_analysis_source_set_hash(source_set)
    payload.setdefault("settlement_frame_ref", None)
    payload.setdefault("captured_inputs", [])
    payload.setdefault("declared_non_goals", [])
    payload.setdefault("notes", [])
    return canonicalize_adeu_architecture_analysis_request_payload(
        payload,
        repository_root=root,
    )
