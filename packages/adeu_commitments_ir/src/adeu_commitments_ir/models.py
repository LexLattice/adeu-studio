from __future__ import annotations

from pathlib import PurePosixPath
from typing import Annotated, Any, Literal

from adeu_ir import SourceSpan
from pydantic import BaseModel, ConfigDict, Field, TypeAdapter, model_validator

from .reason_codes import validate_reason_code

CommitmentsSchemaVersion = Literal["adeu_commitments_ir@0.1"]
CommitmentsModuleKind = Literal["arc_lock", "slice_spec", "stop_gate"]
CommitmentsModuleStatus = Literal["draft", "frozen", "superseded"]
CommitmentsSeverity = Literal["ERROR", "WARN", "INFO"]
CommitmentsLockKind = Literal[
    "freeze",
    "required",
    "forbidden",
    "additive_only",
    "exact_set",
]
CommitmentsEffectTag = Literal[
    "schema_export",
    "contract_validation",
    "continuity_check",
    "artifact_generation",
    "diagnostics_emission",
]
CommitmentsAssertionType = Literal[
    "schema_contract",
    "continuity_guard",
    "surface_match",
    "determinism",
]
CommitmentsSurfaceKind = Literal["schema", "manifest", "file", "markdown_json_block"]
CommitmentsEvidenceType = Literal[
    "test_report",
    "lint_output",
    "ci_run",
    "artifact_hash",
    "doc_json",
]
CommitmentsTrustLane = Literal["mapping", "solver", "proof", "tooling"]
CommitmentsEvidenceQuality = Literal["low", "medium", "high"]
ADEU_COMMITMENTS_IR_SCHEMA = "adeu_commitments_ir@0.1"


def _require_non_empty(value: str, *, field_name: str) -> str:
    if not value:
        raise ValueError(f"{field_name} must not be empty")
    return value


def _require_repo_rel_path(value: str, *, field_name: str) -> str:
    normalized = value.replace("\\", "/").strip()
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    if normalized.startswith("/"):
        raise ValueError(f"{field_name} must be repository-relative")
    parts = PurePosixPath(normalized).parts
    if ".." in parts:
        raise ValueError(f"{field_name} must not include parent traversal")
    return str(PurePosixPath(normalized))


def _assert_sorted_unique(values: list[str], *, field_name: str) -> None:
    if any(not value for value in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


class CommitmentsCompiler(BaseModel):
    model_config = ConfigDict(extra="forbid")

    name: str = Field(min_length=1)
    version: str = Field(min_length=1)
    pass_versions: list[str] = Field(default_factory=list)
    config_hash: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "CommitmentsCompiler":
        _assert_sorted_unique(self.pass_versions, field_name="pass_versions")
        return self


class CommitmentsSourceFile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    path: str = Field(min_length=1)
    semantic_source_hash: str = Field(min_length=1)
    file_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "CommitmentsSourceFile":
        self.path = _require_repo_rel_path(self.path, field_name="path")
        return self


class CommitmentsSourceSet(BaseModel):
    model_config = ConfigDict(extra="forbid")

    repo_root_rel: str = Field(min_length=1)
    files: list[CommitmentsSourceFile] = Field(default_factory=list)
    source_set_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "CommitmentsSourceSet":
        self.repo_root_rel = _require_repo_rel_path(self.repo_root_rel, field_name="repo_root_rel")
        ordered_paths = [item.path for item in self.files]
        _assert_sorted_unique(ordered_paths, field_name="files.path")
        return self


class CommitmentsModuleSource(BaseModel):
    model_config = ConfigDict(extra="forbid")

    path: str = Field(min_length=1)
    span: SourceSpan | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "CommitmentsModuleSource":
        self.path = _require_repo_rel_path(self.path, field_name="source.path")
        return self


class CommitmentsODEUSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    o: list[str] = Field(default_factory=list, alias="O")
    d_norm: list[str] = Field(default_factory=list, alias="D_norm")
    e: list[str] = Field(default_factory=list, alias="E")
    u: list[str] = Field(default_factory=list, alias="U")

    @model_validator(mode="after")
    def _validate_contract(self) -> "CommitmentsODEUSummary":
        _assert_sorted_unique(self.o, field_name="odeu.O")
        _assert_sorted_unique(self.d_norm, field_name="odeu.D_norm")
        _assert_sorted_unique(self.e, field_name="odeu.E")
        _assert_sorted_unique(self.u, field_name="odeu.U")
        return self


class CommitmentsLock(BaseModel):
    model_config = ConfigDict(extra="forbid")

    lock_id: str = Field(min_length=1)
    kind: CommitmentsLockKind
    severity: Literal["ERROR", "WARN"]
    target: str = Field(min_length=1)
    params: dict[str, Any] = Field(default_factory=dict)
    source: CommitmentsModuleSource | None = None


class CommitmentsSurfaceRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    surface_id: str = Field(min_length=1)
    surface_kind: CommitmentsSurfaceKind
    selector: str = Field(min_length=1)


class CommitmentsAssertion(BaseModel):
    model_config = ConfigDict(extra="forbid")

    assertion_id: str = Field(min_length=1)
    assertion_type: CommitmentsAssertionType
    target: str = Field(min_length=1)
    expected: dict[str, Any] = Field(default_factory=dict)


class CommitmentsEvidenceRequirement(BaseModel):
    model_config = ConfigDict(extra="forbid")

    evidence_id: str = Field(min_length=1)
    evidence_type: CommitmentsEvidenceType
    trust_lane: CommitmentsTrustLane
    quality: CommitmentsEvidenceQuality
    required: bool = True


class CommitmentsDiagnostic(BaseModel):
    model_config = ConfigDict(extra="forbid")

    code: str = Field(min_length=1, pattern=r"^ASC-CIR-[0-9]{4}$")
    severity: CommitmentsSeverity
    message: str = Field(min_length=1)
    module_id: str | None = None
    source: CommitmentsModuleSource | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "CommitmentsDiagnostic":
        validate_reason_code(self.code)
        if self.module_id is not None:
            self.module_id = _require_non_empty(self.module_id.strip(), field_name="module_id")
        return self


class _CommitmentsModuleBase(BaseModel):
    model_config = ConfigDict(extra="forbid")

    module_id: str = Field(min_length=1)
    module_kind: CommitmentsModuleKind
    title: str = Field(min_length=1)
    status: CommitmentsModuleStatus = "draft"
    source: CommitmentsModuleSource
    depends_on: list[str] = Field(default_factory=list)
    odeu: CommitmentsODEUSummary | None = None
    effects_declared: list[CommitmentsEffectTag] = Field(default_factory=list)
    locks: list[CommitmentsLock] = Field(default_factory=list)
    surfaces: list[CommitmentsSurfaceRef] = Field(default_factory=list)
    assertions: list[CommitmentsAssertion] = Field(default_factory=list)
    evidence_requirements: list[CommitmentsEvidenceRequirement] = Field(default_factory=list)
    module_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_CommitmentsModuleBase":
        _assert_sorted_unique(self.depends_on, field_name="depends_on")
        _assert_sorted_unique(self.effects_declared, field_name="effects_declared")
        lock_ids = [item.lock_id for item in self.locks]
        _assert_sorted_unique(lock_ids, field_name="locks.lock_id")
        surface_ids = [item.surface_id for item in self.surfaces]
        _assert_sorted_unique(surface_ids, field_name="surfaces.surface_id")
        assertion_ids = [item.assertion_id for item in self.assertions]
        _assert_sorted_unique(assertion_ids, field_name="assertions.assertion_id")
        evidence_ids = [item.evidence_id for item in self.evidence_requirements]
        _assert_sorted_unique(evidence_ids, field_name="evidence_requirements.evidence_id")
        return self


class ArcLockModule(_CommitmentsModuleBase):
    module_kind: Literal["arc_lock"] = "arc_lock"
    arc_id: str = Field(min_length=1)


class SliceSpecModule(_CommitmentsModuleBase):
    module_kind: Literal["slice_spec"] = "slice_spec"
    arc_id: str = Field(min_length=1)
    slice_id: str = Field(min_length=1)


class StopGateModule(_CommitmentsModuleBase):
    module_kind: Literal["stop_gate"] = "stop_gate"
    arc_id: str = Field(min_length=1)
    stop_gate_id: str = Field(min_length=1)


CommitmentsModule = Annotated[
    ArcLockModule | SliceSpecModule | StopGateModule,
    Field(discriminator="module_kind"),
]
_COMMITMENTS_MODULE_ADAPTER = TypeAdapter(CommitmentsModule)


class AdeuCommitmentsIR(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: CommitmentsSchemaVersion = ADEU_COMMITMENTS_IR_SCHEMA
    compiler: CommitmentsCompiler
    source_set: CommitmentsSourceSet
    modules: list[CommitmentsModule] = Field(default_factory=list)
    diagnostics: list[CommitmentsDiagnostic] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuCommitmentsIR":
        module_identity = [
            (module.module_kind, module.module_id)
            for module in self.modules
        ]
        if module_identity != sorted(module_identity):
            raise ValueError("modules must be sorted by (module_kind, module_id)")
        module_ids = [module.module_id for module in self.modules]
        _assert_sorted_unique(module_ids, field_name="modules.module_id")

        diagnostic_identity = [
            (
                diagnostic.severity,
                diagnostic.code,
                diagnostic.module_id or "",
                diagnostic.message,
            )
            for diagnostic in self.diagnostics
        ]
        if diagnostic_identity != sorted(diagnostic_identity):
            raise ValueError(
                "diagnostics must be sorted by (severity, code, module_id, message)"
            )
        return self


def canonicalize_commitments_ir_payload(
    payload: AdeuCommitmentsIR | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AdeuCommitmentsIR)
        else AdeuCommitmentsIR.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_commitments_module_payload(payload: dict[str, Any]) -> dict[str, Any]:
    normalized = _COMMITMENTS_MODULE_ADAPTER.validate_python(payload)
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


__all__ = [
    "ADEU_COMMITMENTS_IR_SCHEMA",
    "CommitmentsSchemaVersion",
    "CommitmentsModuleKind",
    "CommitmentsModuleStatus",
    "CommitmentsSeverity",
    "CommitmentsLockKind",
    "CommitmentsEffectTag",
    "CommitmentsAssertionType",
    "CommitmentsSurfaceKind",
    "CommitmentsEvidenceType",
    "CommitmentsTrustLane",
    "CommitmentsEvidenceQuality",
    "CommitmentsCompiler",
    "CommitmentsSourceFile",
    "CommitmentsSourceSet",
    "CommitmentsModuleSource",
    "CommitmentsODEUSummary",
    "CommitmentsLock",
    "CommitmentsSurfaceRef",
    "CommitmentsAssertion",
    "CommitmentsEvidenceRequirement",
    "CommitmentsDiagnostic",
    "ArcLockModule",
    "SliceSpecModule",
    "StopGateModule",
    "CommitmentsModule",
    "AdeuCommitmentsIR",
    "canonicalize_commitments_ir_payload",
    "canonicalize_commitments_module_payload",
]
