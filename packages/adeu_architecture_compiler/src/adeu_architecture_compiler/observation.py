from __future__ import annotations

import ast
import re
from pathlib import Path, PurePosixPath
from typing import Any, Literal

from adeu_architecture_ir import (
    ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA,
    ADEU_ARCHITECTURE_ANALYSIS_SETTLEMENT_FRAME_SCHEMA,
    AdeuArchitectureAnalysisRequest,
    AdeuArchitectureAnalysisSettlementFrame,
)
from adeu_architecture_ir.analysis_request import AuthorityBoundaryPolicyPin
from pydantic import BaseModel, ConfigDict, Field, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .conformance import (
    _assert_non_empty_text,
    _assert_sorted_unique,
    _load_repo_json,
    _normalize_repo_relative_path,
    _resolve_repository_root,
)

ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA = "adeu_architecture_observation_frame@1"
V41C_V85_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS85.md#v85-continuation-contract-machine-checkable"
)

ObservationMode = Literal["direct", "derived"]
ObservationCompileEntitlement = Literal["entitled", "blocked"]
ObservableKind = Literal["dashboard", "events", "metrics", "observability", "report", "telemetry"]
ObservationFactKind = Literal[
    "authority_source",
    "boundary",
    "evidence_hook",
    "implementation_unit",
    "observability_hook",
    "workflow",
]
UnresolvedReasonKind = Literal[
    "ambiguous_structure",
    "missing_source_signal",
    "requires_cross_file_resolution",
    "requires_non_source_context",
]

_HEX_64_RE = re.compile(r"^[0-9a-f]{64}$")
_OBSERVABILITY_NAME_MARKERS = (
    "dashboard",
    "events",
    "metrics",
    "observability",
    "report",
    "telemetry",
)
_AUTHORITY_CONFIG_NAMES = {
    "dockerfile",
    "makefile",
    "package.json",
    "pyproject.toml",
    "setup.cfg",
}


def _validation_context(
    repository_root: Path | None = None,
    **extra: Any,
) -> dict[str, Any]:
    context = {"repository_root": repository_root}
    context.update(extra)
    return context


def _normalize_artifact_ref(raw_ref: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(raw_ref, field_name=field_name)
    if "#" not in normalized:
        return _normalize_repo_relative_path(normalized, field_name=field_name)
    path_part, fragment = normalized.split("#", 1)
    if not fragment.strip():
        raise ValueError(f"{field_name} must not end with an empty fragment")
    normalized_path = _normalize_repo_relative_path(path_part, field_name=field_name)
    return f"{normalized_path}#{fragment.strip()}"


def _artifact_ref_path(ref: str) -> str:
    return ref.split("#", 1)[0]


def _assert_sha256(value: str, *, field_name: str) -> str:
    digest = _assert_non_empty_text(value, field_name=field_name)
    if not _HEX_64_RE.fullmatch(digest):
        raise ValueError(f"{field_name} must be a 64-character lowercase hex sha256")
    return digest


def _normalize_source_hashes(
    source_hashes: dict[str, str],
    *,
    field_name: str,
) -> dict[str, str]:
    normalized: dict[str, str] = {}
    for path, digest in source_hashes.items():
        normalized_path = _normalize_repo_relative_path(path, field_name=f"{field_name} key")
        normalized[normalized_path] = _assert_sha256(
            digest,
            field_name=f"{field_name}[{path}]",
        )
    return {path: normalized[path] for path in sorted(normalized)}


def _request_source_lookup(request: AdeuArchitectureAnalysisRequest) -> dict[str, tuple[str, str]]:
    return {
        item.path: (item.artifact_kind, item.sha256)
        for item in request.source_set.items
    }


def _load_analysis_request_from_ref(
    analysis_request_ref: str,
    *,
    repository_root: Path,
) -> AdeuArchitectureAnalysisRequest:
    payload = _load_repo_json(
        _artifact_ref_path(analysis_request_ref),
        repository_root=repository_root,
    )
    if payload.get("schema") != ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA:
        raise ValueError(
            "analysis_request_ref must resolve to adeu_architecture_analysis_request@1"
        )
    return AdeuArchitectureAnalysisRequest.model_validate(
        payload,
        context={"repository_root": repository_root},
    )


def _load_settlement_from_ref(
    settlement_frame_ref: str,
    *,
    repository_root: Path,
    request: AdeuArchitectureAnalysisRequest,
) -> AdeuArchitectureAnalysisSettlementFrame:
    payload = _load_repo_json(
        _artifact_ref_path(settlement_frame_ref),
        repository_root=repository_root,
    )
    if payload.get("schema") != ADEU_ARCHITECTURE_ANALYSIS_SETTLEMENT_FRAME_SCHEMA:
        raise ValueError(
            "settlement_frame_ref must resolve to "
            "adeu_architecture_analysis_settlement_frame@1"
        )
    return AdeuArchitectureAnalysisSettlementFrame.model_validate(
        payload,
        context={"repository_root": repository_root, "analysis_request": request},
    )


def _slug(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", value.lower()).strip("_")


def _source_hashes_for_refs(
    source_refs: list[str],
    *,
    request: AdeuArchitectureAnalysisRequest,
) -> dict[str, str]:
    source_lookup = _request_source_lookup(request)
    return {ref: source_lookup[ref][1] for ref in sorted(source_refs)}


def _read_text(path: str, *, repository_root: Path) -> str:
    return (repository_root / path).read_text(encoding="utf-8")


def _python_module_name(path: str, *, subtree_root: str) -> str | None:
    normalized_subtree = PurePosixPath(subtree_root)
    normalized_path = PurePosixPath(path)
    try:
        relative = normalized_path.relative_to(normalized_subtree)
    except ValueError:
        return None
    if normalized_path.suffix != ".py":
        return None
    root_package = normalized_subtree.name
    parts = list(relative.parts)
    if not parts:
        return root_package
    if parts[-1] == "__init__.py":
        suffix_parts = parts[:-1]
    else:
        suffix_parts = [*parts[:-1], normalized_path.stem]
    if not suffix_parts:
        return root_package
    return ".".join([root_package, *suffix_parts])


def _import_dependency_paths(
    path: str,
    *,
    source_text: str,
    module_name: str,
    module_by_name: dict[str, str],
) -> list[str]:
    try:
        tree = ast.parse(source_text)
    except SyntaxError:
        return []

    module_parts = module_name.split(".")
    is_package_init = path.endswith("__init__.py")
    anchor_parts = module_parts if is_package_init else module_parts[:-1]
    dependencies: set[str] = set()

    def _register_module(candidate: str) -> None:
        if candidate in module_by_name:
            dependencies.add(module_by_name[candidate])

    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                _register_module(alias.name)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        if node.level == 0:
            base_parts = node.module.split(".") if node.module else []
        else:
            keep = len(anchor_parts) - (node.level - 1)
            if keep <= 0:
                base_parts = []
            else:
                base_parts = anchor_parts[:keep]
            if node.module:
                base_parts = [*base_parts, *node.module.split(".")]
        if base_parts:
            _register_module(".".join(base_parts))
        for alias in node.names:
            if alias.name == "*":
                continue
            if base_parts:
                _register_module(".".join([*base_parts, alias.name]))
            elif node.level > 0:
                _register_module(alias.name)
    return sorted(dependencies)


def _default_observation_frame_id(settlement_frame_id: str) -> str:
    if "settlement" in settlement_frame_id:
        return settlement_frame_id.replace("settlement", "observation")
    return f"{settlement_frame_id}_observation_frame"


class _ObservationEntryBase(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    observation_mode: ObservationMode
    source_refs: list[str]
    source_hashes: dict[str, str]

    @model_validator(mode="after")
    def _validate_common(self) -> "_ObservationEntryBase":
        source_refs = _assert_sorted_unique(
            self.source_refs,
            field_name="source_refs",
            allow_empty=False,
        )
        object.__setattr__(self, "source_refs", source_refs)
        source_hashes = _normalize_source_hashes(self.source_hashes, field_name="source_hashes")
        if list(source_hashes) != source_refs:
            raise ValueError("source_hashes must cover exactly source_refs")
        object.__setattr__(self, "source_hashes", source_hashes)
        return self


class ObservedImplementationUnit(_ObservationEntryBase):
    model_config = ConfigDict(extra="forbid", frozen=True)

    unit_id: str
    unit_kind: str
    fact_kind: Literal["implementation_unit"] = "implementation_unit"
    summary: str

    @model_validator(mode="after")
    def _validate_entry(self) -> "ObservedImplementationUnit":
        object.__setattr__(
            self,
            "unit_id",
            _assert_non_empty_text(self.unit_id, field_name="unit_id"),
        )
        object.__setattr__(
            self,
            "unit_kind",
            _assert_non_empty_text(self.unit_kind, field_name="unit_kind"),
        )
        object.__setattr__(
            self,
            "summary",
            _assert_non_empty_text(self.summary, field_name="summary"),
        )
        return self


class ObservedBoundary(_ObservationEntryBase):
    model_config = ConfigDict(extra="forbid", frozen=True)

    boundary_id: str
    boundary_kind: str
    fact_kind: Literal["boundary"] = "boundary"
    crossing_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_entry(self) -> "ObservedBoundary":
        object.__setattr__(
            self, "boundary_id", _assert_non_empty_text(self.boundary_id, field_name="boundary_id")
        )
        object.__setattr__(
            self,
            "boundary_kind",
            _assert_non_empty_text(self.boundary_kind, field_name="boundary_kind"),
        )
        object.__setattr__(
            self,
            "crossing_refs",
            _assert_sorted_unique(self.crossing_refs, field_name="crossing_refs"),
        )
        return self


class ObservedWorkflow(_ObservationEntryBase):
    model_config = ConfigDict(extra="forbid", frozen=True)

    workflow_id: str
    fact_kind: Literal["workflow"] = "workflow"
    step_refs: list[str]

    @model_validator(mode="after")
    def _validate_entry(self) -> "ObservedWorkflow":
        object.__setattr__(
            self, "workflow_id", _assert_non_empty_text(self.workflow_id, field_name="workflow_id")
        )
        object.__setattr__(
            self,
            "step_refs",
            _assert_sorted_unique(self.step_refs, field_name="step_refs", allow_empty=False),
        )
        return self


class ObservedAuthoritySource(_ObservationEntryBase):
    model_config = ConfigDict(extra="forbid", frozen=True)

    authority_source_id: str
    mechanism_kind: str
    fact_kind: Literal["authority_source"] = "authority_source"

    @model_validator(mode="after")
    def _validate_entry(self) -> "ObservedAuthoritySource":
        object.__setattr__(
            self,
            "authority_source_id",
            _assert_non_empty_text(self.authority_source_id, field_name="authority_source_id"),
        )
        object.__setattr__(
            self,
            "mechanism_kind",
            _assert_non_empty_text(self.mechanism_kind, field_name="mechanism_kind"),
        )
        return self


class ObservedEvidenceHook(_ObservationEntryBase):
    model_config = ConfigDict(extra="forbid", frozen=True)

    evidence_hook_id: str
    hook_kind: str
    fact_kind: Literal["evidence_hook"] = "evidence_hook"

    @model_validator(mode="after")
    def _validate_entry(self) -> "ObservedEvidenceHook":
        object.__setattr__(
            self,
            "evidence_hook_id",
            _assert_non_empty_text(self.evidence_hook_id, field_name="evidence_hook_id"),
        )
        object.__setattr__(
            self,
            "hook_kind",
            _assert_non_empty_text(self.hook_kind, field_name="hook_kind"),
        )
        return self


class ObservedObservabilityHook(_ObservationEntryBase):
    model_config = ConfigDict(extra="forbid", frozen=True)

    observability_hook_id: str
    hook_kind: str
    observable_kind: ObservableKind
    fact_kind: Literal["observability_hook"] = "observability_hook"

    @model_validator(mode="after")
    def _validate_entry(self) -> "ObservedObservabilityHook":
        object.__setattr__(
            self,
            "observability_hook_id",
            _assert_non_empty_text(self.observability_hook_id, field_name="observability_hook_id"),
        )
        object.__setattr__(
            self,
            "hook_kind",
            _assert_non_empty_text(self.hook_kind, field_name="hook_kind"),
        )
        return self


class UnresolvedObservation(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    observation_id: str
    observation_kind: str
    observation_mode: ObservationMode
    source_refs: list[str]
    source_hashes: dict[str, str]
    unresolved_reason_kind: UnresolvedReasonKind
    rationale: str

    @model_validator(mode="after")
    def _validate_entry(self) -> "UnresolvedObservation":
        object.__setattr__(
            self,
            "observation_id",
            _assert_non_empty_text(self.observation_id, field_name="observation_id"),
        )
        object.__setattr__(
            self,
            "observation_kind",
            _assert_non_empty_text(self.observation_kind, field_name="observation_kind"),
        )
        source_refs = _assert_sorted_unique(
            self.source_refs,
            field_name="source_refs",
            allow_empty=False,
        )
        object.__setattr__(self, "source_refs", source_refs)
        source_hashes = _normalize_source_hashes(self.source_hashes, field_name="source_hashes")
        if list(source_hashes) != source_refs:
            raise ValueError("source_hashes must cover exactly source_refs")
        object.__setattr__(self, "source_hashes", source_hashes)
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        return self


class AdeuArchitectureObservationFrame(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA] = (
        ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA
    )
    observation_frame_id: str
    analysis_request_id: str
    analysis_request_ref: str
    settlement_frame_id: str
    settlement_frame_ref: str
    source_set_hash: str
    authority_boundary_policy: AuthorityBoundaryPolicyPin
    upstream_compile_entitlement: ObservationCompileEntitlement
    upstream_blocking_refs: list[str] = Field(default_factory=list)
    observed_units: list[ObservedImplementationUnit] = Field(default_factory=list)
    observed_boundaries: list[ObservedBoundary] = Field(default_factory=list)
    observed_workflows: list[ObservedWorkflow] = Field(default_factory=list)
    observed_authority_sources: list[ObservedAuthoritySource] = Field(default_factory=list)
    observed_evidence_hooks: list[ObservedEvidenceHook] = Field(default_factory=list)
    observed_observability_hooks: list[ObservedObservabilityHook] = Field(default_factory=list)
    unresolved_observations: list[UnresolvedObservation] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_frame(self, info: ValidationInfo) -> "AdeuArchitectureObservationFrame":
        object.__setattr__(
            self,
            "observation_frame_id",
            _assert_non_empty_text(self.observation_frame_id, field_name="observation_frame_id"),
        )
        object.__setattr__(
            self,
            "analysis_request_id",
            _assert_non_empty_text(self.analysis_request_id, field_name="analysis_request_id"),
        )
        analysis_request_ref = _normalize_artifact_ref(
            self.analysis_request_ref,
            field_name="analysis_request_ref",
        )
        object.__setattr__(self, "analysis_request_ref", analysis_request_ref)
        object.__setattr__(
            self,
            "settlement_frame_id",
            _assert_non_empty_text(self.settlement_frame_id, field_name="settlement_frame_id"),
        )
        settlement_frame_ref = _normalize_artifact_ref(
            self.settlement_frame_ref,
            field_name="settlement_frame_ref",
        )
        object.__setattr__(self, "settlement_frame_ref", settlement_frame_ref)
        object.__setattr__(
            self,
            "source_set_hash",
            _assert_sha256(self.source_set_hash, field_name="source_set_hash"),
        )
        object.__setattr__(
            self,
            "upstream_blocking_refs",
            _assert_sorted_unique(
                self.upstream_blocking_refs,
                field_name="upstream_blocking_refs",
            ),
        )

        def _sort_by_id(entries: list[Any], *, id_field: str, field_name: str) -> list[Any]:
            keyed = {getattr(entry, id_field): entry for entry in entries}
            if len(keyed) != len(entries):
                raise ValueError(f"{field_name} must not contain duplicate {id_field}")
            return [keyed[key] for key in sorted(keyed)]

        object.__setattr__(
            self,
            "observed_units",
            _sort_by_id(self.observed_units, id_field="unit_id", field_name="observed_units"),
        )
        object.__setattr__(
            self,
            "observed_boundaries",
            _sort_by_id(
                self.observed_boundaries,
                id_field="boundary_id",
                field_name="observed_boundaries",
            ),
        )
        object.__setattr__(
            self,
            "observed_workflows",
            _sort_by_id(
                self.observed_workflows,
                id_field="workflow_id",
                field_name="observed_workflows",
            ),
        )
        object.__setattr__(
            self,
            "observed_authority_sources",
            _sort_by_id(
                self.observed_authority_sources,
                id_field="authority_source_id",
                field_name="observed_authority_sources",
            ),
        )
        object.__setattr__(
            self,
            "observed_evidence_hooks",
            _sort_by_id(
                self.observed_evidence_hooks,
                id_field="evidence_hook_id",
                field_name="observed_evidence_hooks",
            ),
        )
        object.__setattr__(
            self,
            "observed_observability_hooks",
            _sort_by_id(
                self.observed_observability_hooks,
                id_field="observability_hook_id",
                field_name="observed_observability_hooks",
            ),
        )
        object.__setattr__(
            self,
            "unresolved_observations",
            _sort_by_id(
                self.unresolved_observations,
                id_field="observation_id",
                field_name="unresolved_observations",
            ),
        )

        typed_ids: dict[str, str] = {}
        for field_name, entries, id_field in (
            ("observed_units", self.observed_units, "unit_id"),
            ("observed_boundaries", self.observed_boundaries, "boundary_id"),
            ("observed_workflows", self.observed_workflows, "workflow_id"),
            (
                "observed_authority_sources",
                self.observed_authority_sources,
                "authority_source_id",
            ),
            ("observed_evidence_hooks", self.observed_evidence_hooks, "evidence_hook_id"),
            (
                "observed_observability_hooks",
                self.observed_observability_hooks,
                "observability_hook_id",
            ),
            ("unresolved_observations", self.unresolved_observations, "observation_id"),
        ):
            for entry in entries:
                entry_id = getattr(entry, id_field)
                if entry_id in typed_ids:
                    raise ValueError(
                        "observation ids must be globally unique across the observation frame"
                    )
                typed_ids[entry_id] = field_name

        repository_root = None
        request = None
        settlement = None
        if info.context:
            repository_root = info.context.get("repository_root")
            request = info.context.get("analysis_request")
            settlement = info.context.get("analysis_settlement")
        if repository_root is not None and request is None:
            request = _load_analysis_request_from_ref(
                analysis_request_ref,
                repository_root=repository_root,
            )
        if repository_root is not None and settlement is None and request is not None:
            settlement = _load_settlement_from_ref(
                settlement_frame_ref,
                repository_root=repository_root,
                request=request,
            )
        if request is not None:
            if self.analysis_request_id != request.analysis_request_id:
                raise ValueError("analysis_request_id must match released V41-A request boundary")
            if self.source_set_hash != request.source_set_hash:
                raise ValueError("source_set_hash must match released V41-A request boundary")
            if (
                self.authority_boundary_policy.model_dump(mode="json", exclude_none=False)
                != request.authority_boundary_policy.model_dump(mode="json", exclude_none=False)
            ):
                raise ValueError(
                    "authority_boundary_policy must match released V41-A request boundary"
                )

            source_lookup = _request_source_lookup(request)
            for group in (
                self.observed_units,
                self.observed_boundaries,
                self.observed_workflows,
                self.observed_authority_sources,
                self.observed_evidence_hooks,
                self.observed_observability_hooks,
                self.unresolved_observations,
            ):
                for entry in group:
                    for source_ref in entry.source_refs:
                        if source_ref not in source_lookup:
                            raise ValueError(
                                f"source_ref {source_ref!r} must resolve inside the released "
                                "V41-A request boundary"
                            )
                        artifact_kind, digest = source_lookup[source_ref]
                        if artifact_kind == "documentation":
                            raise ValueError(
                                "observed entry source_refs may not rely on documentation items"
                            )
                        if entry.source_hashes[source_ref] != digest:
                            raise ValueError(
                                f"source_hashes for {source_ref!r} must match released "
                                "V41-A source_set hashes"
                            )

        if settlement is not None:
            if self.settlement_frame_id != settlement.settlement_frame_id:
                raise ValueError(
                    "settlement_frame_id must match released V41-B settlement boundary"
                )
            if self.analysis_request_id != settlement.analysis_request_id:
                raise ValueError(
                    "analysis_request_id must match released V41-B settlement boundary"
                )
            if self.source_set_hash != settlement.source_set_hash:
                raise ValueError("source_set_hash must match released V41-B settlement boundary")
            if self.upstream_compile_entitlement != settlement.compile_entitlement:
                raise ValueError(
                    "upstream_compile_entitlement must match released V41-B settlement posture"
                )
            expected_blocking_refs = sorted(
                entry.blocking_ref_id for entry in settlement.blocking_lineage
            )
            if self.upstream_blocking_refs != expected_blocking_refs:
                raise ValueError(
                    "upstream_blocking_refs must match released V41-B blocking_lineage ids"
                )

        for boundary in self.observed_boundaries:
            for crossing_ref in boundary.crossing_refs:
                if crossing_ref not in typed_ids:
                    raise ValueError(
                        f"crossing_ref {crossing_ref!r} must resolve to a typed observation entry"
                    )
        for workflow in self.observed_workflows:
            for step_ref in workflow.step_refs:
                if step_ref not in typed_ids:
                    raise ValueError(
                        f"step_ref {step_ref!r} must resolve to a typed observation entry"
                    )

        return self


def canonicalize_adeu_architecture_observation_frame_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest | None = None,
    analysis_settlement_payload: (
        dict[str, Any] | AdeuArchitectureAnalysisSettlementFrame | None
    ) = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    request = analysis_request_payload
    if request is not None and not isinstance(request, AdeuArchitectureAnalysisRequest):
        request = AdeuArchitectureAnalysisRequest.model_validate(
            request,
            context={"repository_root": root},
        )
    settlement = analysis_settlement_payload
    if settlement is not None and not isinstance(
        settlement, AdeuArchitectureAnalysisSettlementFrame
    ):
        settlement = AdeuArchitectureAnalysisSettlementFrame.model_validate(
            settlement,
            context=_validation_context(root, analysis_request=request),
        )
    return AdeuArchitectureObservationFrame.model_validate(
        payload,
        context=_validation_context(
            root,
            analysis_request=request,
            analysis_settlement=settlement,
        ),
    ).model_dump(mode="json", exclude_none=True)


def _derive_unit_kind(path: str) -> str:
    name = PurePosixPath(path).name
    if name == "__init__.py":
        return "package_initializer"
    if name == "export_schema.py":
        return "schema_export_module"
    if path.endswith(".py"):
        return "python_module"
    return "source_file"


def _derive_units(
    request: AdeuArchitectureAnalysisRequest,
) -> list[ObservedImplementationUnit]:
    units: list[ObservedImplementationUnit] = []
    for item in request.source_set.items:
        if item.artifact_kind != "source_code":
            continue
        units.append(
            ObservedImplementationUnit.model_validate(
                {
                    "unit_id": f"unit_{_slug(item.path)}",
                    "unit_kind": _derive_unit_kind(item.path),
                    "observation_mode": "direct",
                    "source_refs": [item.path],
                    "source_hashes": _source_hashes_for_refs([item.path], request=request),
                    "summary": f"Observed implementation unit at {item.path}.",
                }
            )
        )
    return units


def _derive_boundaries(
    request: AdeuArchitectureAnalysisRequest,
    *,
    unit_id_by_path: dict[str, str],
    import_paths_by_path: dict[str, list[str]],
) -> list[ObservedBoundary]:
    source_code_paths = [
        item.path for item in request.source_set.items if item.artifact_kind == "source_code"
    ]
    if not source_code_paths:
        return []
    subtree_root = request.request_scope.subtree_root
    boundary_source_refs = sorted(
        path for path in source_code_paths if path.startswith(f"{subtree_root}/")
    )
    if not boundary_source_refs:
        boundary_source_refs = sorted(source_code_paths)

    crossing_unit_ids: set[str] = set()
    for path in boundary_source_refs:
        for dependency_path in import_paths_by_path.get(path, []):
            if dependency_path not in boundary_source_refs:
                crossing_unit_ids.add(unit_id_by_path[dependency_path])

    return [
        ObservedBoundary.model_validate(
            {
                "boundary_id": f"boundary_{_slug(subtree_root)}",
                "boundary_kind": "package_subtree_boundary",
                "observation_mode": "derived",
                "source_refs": boundary_source_refs,
                "source_hashes": _source_hashes_for_refs(boundary_source_refs, request=request),
                "crossing_refs": sorted(crossing_unit_ids),
            }
        )
    ]


def _derive_workflows(
    request: AdeuArchitectureAnalysisRequest,
    *,
    unit_id_by_path: dict[str, str],
    import_paths_by_path: dict[str, list[str]],
) -> list[ObservedWorkflow]:
    workflows: list[ObservedWorkflow] = []
    for path, imported_paths in sorted(import_paths_by_path.items()):
        if PurePosixPath(path).name != "__init__.py" or not imported_paths:
            continue
        step_refs = [unit_id_by_path[dependency_path] for dependency_path in imported_paths]
        step_refs.append(unit_id_by_path[path])
        source_refs = sorted({path, *imported_paths})
        workflows.append(
            ObservedWorkflow.model_validate(
                {
                    "workflow_id": (
                        f"workflow_{_slug(PurePosixPath(path).parent.as_posix())}_exports"
                    ),
                    "observation_mode": "derived",
                    "source_refs": source_refs,
                    "source_hashes": _source_hashes_for_refs(source_refs, request=request),
                    "step_refs": step_refs,
                }
            )
        )
    if workflows:
        return workflows

    fallback_paths = [
        item.path for item in request.source_set.items if item.artifact_kind == "source_code"
    ]
    if len(fallback_paths) < 2:
        return []
    return [
        ObservedWorkflow.model_validate(
            {
                "workflow_id": "workflow_source_slice_ordered",
                "observation_mode": "derived",
                "source_refs": sorted(fallback_paths),
                "source_hashes": _source_hashes_for_refs(sorted(fallback_paths), request=request),
                "step_refs": [unit_id_by_path[path] for path in sorted(fallback_paths)],
            }
        )
    ]


def _derive_authority_sources(
    request: AdeuArchitectureAnalysisRequest,
    *,
    repository_root: Path,
) -> list[ObservedAuthoritySource]:
    sources: list[ObservedAuthoritySource] = []
    for item in request.source_set.items:
        name = PurePosixPath(item.path).name.lower()
        if item.artifact_kind == "configuration" and name in _AUTHORITY_CONFIG_NAMES:
            sources.append(
                ObservedAuthoritySource.model_validate(
                    {
                        "authority_source_id": f"authority_{_slug(item.path)}",
                        "mechanism_kind": "package_configuration",
                        "observation_mode": "direct",
                        "source_refs": [item.path],
                        "source_hashes": _source_hashes_for_refs([item.path], request=request),
                    }
                )
            )
            continue
        if item.artifact_kind == "source_code" and PurePosixPath(item.path).name == "__init__.py":
            source_text = _read_text(item.path, repository_root=repository_root)
            if "__all__" in source_text:
                sources.append(
                    ObservedAuthoritySource.model_validate(
                        {
                            "authority_source_id": f"authority_{_slug(item.path)}",
                            "mechanism_kind": "module_export_table",
                            "observation_mode": "direct",
                            "source_refs": [item.path],
                            "source_hashes": _source_hashes_for_refs([item.path], request=request),
                        }
                    )
                )
    return sources


def _derive_evidence_hooks(
    request: AdeuArchitectureAnalysisRequest,
) -> list[ObservedEvidenceHook]:
    hooks: list[ObservedEvidenceHook] = []
    for item in request.source_set.items:
        if item.artifact_kind != "test":
            continue
        hook_kind = "pytest_module" if item.path.endswith(".py") else "test_artifact"
        hooks.append(
            ObservedEvidenceHook.model_validate(
                {
                    "evidence_hook_id": f"evidence_{_slug(item.path)}",
                    "hook_kind": hook_kind,
                    "observation_mode": "direct",
                    "source_refs": [item.path],
                    "source_hashes": _source_hashes_for_refs([item.path], request=request),
                }
            )
        )
    return hooks


def _derive_observability_hooks(
    request: AdeuArchitectureAnalysisRequest,
) -> list[ObservedObservabilityHook]:
    hooks: list[ObservedObservabilityHook] = []
    for item in request.source_set.items:
        basename = PurePosixPath(item.path).name.lower()
        marker = next((token for token in _OBSERVABILITY_NAME_MARKERS if token in basename), None)
        if marker is None:
            continue
        hook_kind = (
            f"{marker}_artifact"
            if item.artifact_kind == "configuration"
            else f"{marker}_surface"
        )
        hooks.append(
            ObservedObservabilityHook.model_validate(
                {
                    "observability_hook_id": f"observability_{_slug(item.path)}",
                    "hook_kind": hook_kind,
                    "observable_kind": marker,
                    "observation_mode": "direct",
                    "source_refs": [item.path],
                    "source_hashes": _source_hashes_for_refs([item.path], request=request),
                }
            )
        )
    return hooks


def _derive_unresolved_observations(
    request: AdeuArchitectureAnalysisRequest,
    *,
    observability_hooks: list[ObservedObservabilityHook],
) -> list[UnresolvedObservation]:
    observability_source_refs = sorted(
        {
            ref
            for hook in observability_hooks
            for ref in hook.source_refs
        }
    )
    if not observability_source_refs:
        candidate_refs = [
            item.path
            for item in request.source_set.items
            if item.artifact_kind in {"configuration", "source_code", "test"}
        ][:2]
        if not candidate_refs:
            return []
        return [
            UnresolvedObservation.model_validate(
                {
                    "observation_id": "unresolved_observability_surface",
                    "observation_kind": "observability_hook",
                    "observation_mode": "derived",
                    "source_refs": candidate_refs,
                    "source_hashes": _source_hashes_for_refs(candidate_refs, request=request),
                    "unresolved_reason_kind": "missing_source_signal",
                    "rationale": (
                        "The released source_set does not contain a concrete observability "
                        "surface that proves runtime signal emission."
                    ),
                }
            )
        ]

    if any(hook.observable_kind == "events" for hook in observability_hooks):
        return []

    source_refs = observability_source_refs[:2]
    return [
        UnresolvedObservation.model_validate(
            {
                "observation_id": "unresolved_runtime_signal_join",
                "observation_kind": "observability_signal_join",
                "observation_mode": "derived",
                "source_refs": source_refs,
                "source_hashes": _source_hashes_for_refs(source_refs, request=request),
                "unresolved_reason_kind": "requires_non_source_context",
                "rationale": (
                    "Committed observability artifacts are present, but the released "
                    "source_set does not by itself establish a live runtime signal join path."
                ),
            }
        )
    ]


def _derive_import_paths_by_source(
    request: AdeuArchitectureAnalysisRequest,
    *,
    repository_root: Path,
) -> dict[str, list[str]]:
    subtree_root = request.request_scope.subtree_root
    module_by_name = {}
    source_code_paths = [
        item.path for item in request.source_set.items if item.artifact_kind == "source_code"
    ]
    for path in source_code_paths:
        module_name = _python_module_name(path, subtree_root=subtree_root)
        if module_name is not None:
            module_by_name[module_name] = path

    import_paths_by_path: dict[str, list[str]] = {}
    for path in source_code_paths:
        module_name = _python_module_name(path, subtree_root=subtree_root)
        if module_name is None or not path.endswith(".py"):
            import_paths_by_path[path] = []
            continue
        source_text = _read_text(path, repository_root=repository_root)
        import_paths_by_path[path] = _import_dependency_paths(
            path,
            source_text=source_text,
            module_name=module_name,
            module_by_name=module_by_name,
        )
    return import_paths_by_path


def derive_v41c_observation_frame(
    *,
    analysis_request_payload: dict[str, Any] | AdeuArchitectureAnalysisRequest,
    analysis_request_path: str,
    settlement_frame_payload: dict[str, Any] | AdeuArchitectureAnalysisSettlementFrame,
    settlement_frame_path: str,
    observation_frame_id: str | None = None,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    request = analysis_request_payload
    if not isinstance(request, AdeuArchitectureAnalysisRequest):
        request = AdeuArchitectureAnalysisRequest.model_validate(
            analysis_request_payload,
            context={"repository_root": root},
        )
    settlement = settlement_frame_payload
    if not isinstance(settlement, AdeuArchitectureAnalysisSettlementFrame):
        settlement = AdeuArchitectureAnalysisSettlementFrame.model_validate(
            settlement_frame_payload,
            context=_validation_context(root, analysis_request=request),
        )

    normalized_request_ref = _normalize_artifact_ref(
        analysis_request_path,
        field_name="analysis_request_path",
    )
    normalized_settlement_ref = _normalize_artifact_ref(
        settlement_frame_path,
        field_name="settlement_frame_path",
    )
    if settlement.analysis_request_ref != normalized_request_ref:
        raise ValueError("settlement analysis_request_ref must match analysis_request_path")

    unit_id_by_path = {
        item.path: f"unit_{_slug(item.path)}"
        for item in request.source_set.items
        if item.artifact_kind == "source_code"
    }
    import_paths_by_path = _derive_import_paths_by_source(request, repository_root=root)
    observed_units = _derive_units(request)
    observed_boundaries = _derive_boundaries(
        request,
        unit_id_by_path=unit_id_by_path,
        import_paths_by_path=import_paths_by_path,
    )
    observed_workflows = _derive_workflows(
        request,
        unit_id_by_path=unit_id_by_path,
        import_paths_by_path=import_paths_by_path,
    )
    observed_authority_sources = _derive_authority_sources(
        request,
        repository_root=root,
    )
    observed_evidence_hooks = _derive_evidence_hooks(request)
    observed_observability_hooks = _derive_observability_hooks(request)
    unresolved_observations = _derive_unresolved_observations(
        request,
        observability_hooks=observed_observability_hooks,
    )

    payload = {
        "schema": ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA,
        "observation_frame_id": observation_frame_id
        or _default_observation_frame_id(settlement.settlement_frame_id),
        "analysis_request_id": request.analysis_request_id,
        "analysis_request_ref": normalized_request_ref,
        "settlement_frame_id": settlement.settlement_frame_id,
        "settlement_frame_ref": normalized_settlement_ref,
        "source_set_hash": request.source_set_hash,
        "authority_boundary_policy": request.authority_boundary_policy.model_dump(
            mode="json",
            exclude_none=False,
        ),
        "upstream_compile_entitlement": settlement.compile_entitlement,
        "upstream_blocking_refs": [
            entry.blocking_ref_id for entry in settlement.blocking_lineage
        ],
        "observed_units": [entry.model_dump(mode="json") for entry in observed_units],
        "observed_boundaries": [entry.model_dump(mode="json") for entry in observed_boundaries],
        "observed_workflows": [entry.model_dump(mode="json") for entry in observed_workflows],
        "observed_authority_sources": [
            entry.model_dump(mode="json") for entry in observed_authority_sources
        ],
        "observed_evidence_hooks": [
            entry.model_dump(mode="json") for entry in observed_evidence_hooks
        ],
        "observed_observability_hooks": [
            entry.model_dump(mode="json") for entry in observed_observability_hooks
        ],
        "unresolved_observations": [
            entry.model_dump(mode="json") for entry in unresolved_observations
        ],
    }
    return canonicalize_adeu_architecture_observation_frame_payload(
        payload,
        repository_root=root,
        analysis_request_payload=request,
        analysis_settlement_payload=settlement,
    )


def compute_adeu_architecture_observation_frame_hash(payload: dict[str, Any]) -> str:
    return sha256_canonical_json(
        canonicalize_adeu_architecture_observation_frame_payload(payload)
    )


__all__ = [
    "ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA",
    "V41C_V85_CONTRACT_SOURCE",
    "AdeuArchitectureObservationFrame",
    "ObservedAuthoritySource",
    "ObservedBoundary",
    "ObservedEvidenceHook",
    "ObservedImplementationUnit",
    "ObservedObservabilityHook",
    "ObservedWorkflow",
    "UnresolvedObservation",
    "canonicalize_adeu_architecture_observation_frame_payload",
    "compute_adeu_architecture_observation_frame_hash",
    "derive_v41c_observation_frame",
]
