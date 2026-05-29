from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

REPO_BEHAVIORAL_REPLAY_MANIFEST_SCHEMA = "repo_behavioral_replay_manifest@1"
REPO_BEHAVIORAL_PROBE_CONTRACT_SCHEMA = "repo_behavioral_probe_contract@1"
REPO_BEHAVIORAL_CANONICALIZATION_PROFILE_SCHEMA = (
    "repo_behavioral_canonicalization_profile@1"
)
REPO_BEHAVIORAL_OBSERVATION_HASH_SCHEMA = "repo_behavioral_observation_hash@1"
REPO_BEHAVIORAL_REPLAY_MANIFEST_VALIDATION_REPORT_SCHEMA = (
    "repo_behavioral_replay_manifest_validation_report@1"
)
REPO_BEHAVIORAL_REPLAY_LOCK_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "repo_behavioral_replay_lock_non_authority_guardrail@1"
)

ManifestAuthorityLayer = Literal["support", "planning", "architecture", "lock", "observed"]
ManifestLifecycleState = Literal[
    "draft",
    "proposed",
    "locked",
    "released",
    "stale",
    "superseded",
    "invalid",
]
ManifestVisibilityPosture = Literal[
    "implementation_visible_regression",
    "checker_only_sealed",
    "orchestrator_only",
    "public_reference_matrix",
    "source_tail_matrix",
]
PatchRiskKind = Literal[
    "control_plane_parser",
    "public_schema_mode_dispatch",
    "resource_route_topology",
    "input_dialect_reader",
    "transform_or_embedded_language",
    "state_lifecycle_mutation",
    "subject_identity_binding",
    "output_router_renderer",
    "diagnostic_exit_channel",
    "runtime_substrate_dependency",
    "side_effect_workspace",
    "config_policy_activation",
    "generic_fallback_or_default_behavior",
    "other",
]
ProtectedSurfaceKind = Literal[
    "exit_code",
    "stdout",
    "stderr",
    "output_file_tree",
    "process_state",
    "timeout_status",
]
FixtureTreeProtectionKind = Literal[
    "read_only",
    "mutating_expected",
    "workspace_mutation_allowed",
]
CanonicalizationRuleKind = Literal[
    "text_replace",
    "json_sort_keys",
    "xml_sort_attributes",
    "path_prefix_replace",
    "ordering_sort_rows",
    "file_tree_hash",
    "process_state_projection",
    "timing_bucket",
]
ProtectedSurfaceEffect = Literal[
    "preserves_protected_signal",
    "ignores_unprotected_noise",
    "hides_protected_change",
]
ExpectedObservationAuthorityPosture = Literal[
    "clean_reference_observation",
    "locked_local_probe",
    "source_tail_matrix",
    "post_eval_pressure_only",
]
ExpectedObservationProvenanceKind = Literal[
    "reference_executable",
    "locked_local_probe",
    "public_schema_observation",
    "source_tail_matrix",
    "post_eval_pressure",
]
EvidenceBoundaryPosture = Literal[
    "clean_first_pass_allowed",
    "clean_first_pass_disallowed",
    "post_eval_pressure_only",
    "source_postmortem_pressure",
    "official_like_pressure",
    "local_locked_probe_delta",
]
CleanFirstPassPosture = Literal["clean", "not_clean", "clean_first_pass_disallowed"]
ObservationSurfaceKind = Literal[
    "exit_code",
    "stdout",
    "stderr",
    "output_file_tree",
    "process_state",
    "timeout_status",
]
HashAlgorithm = Literal["sha256"]
HashDomain = Literal[
    "expected_reference_observation",
    "candidate_observation",
    "suite_root",
    "manifest",
    "object",
]
ReplayValidationStatus = Literal["valid_for_manifest_lock", "invalid", "blocked"]
ManifestValidationDiagnosticKind = Literal[
    "missing_required_field",
    "duplicate_probe_id",
    "missing_expected_observation_hash",
    "unknown_canonicalization_profile",
    "empty_protected_surface_set",
    "missing_file_tree_fixture_hash",
    "suite_root_hash_mismatch",
    "manifest_hash_mismatch",
    "profile_hash_mismatch",
    "probe_contract_hash_mismatch",
    "missing_owner_sentinel",
    "missing_expected_observation_provenance",
    "missing_execution_environment",
    "protected_ignored_surface_conflict",
    "forbidden_canonicalization",
    "missing_mutation_policy",
    "unsafe_sensitive_material",
    "lifecycle_promotion_forbidden",
    "unknown_owner_surface",
    "guardrail_authority_violation",
    "missing_probe_contract",
]
DiagnosticSeverity = Literal["error", "warning"]

_KNOWN_OWNER_SURFACES = {
    "control_plane_parser",
    "public_schema_mode_dispatch",
    "resource_route_topology",
    "input_dialect_reader",
    "transform_or_embedded_language",
    "state_lifecycle_mutation",
    "subject_identity_binding",
    "output_router_renderer",
    "diagnostic_exit_channel",
    "runtime_substrate_dependency",
    "side_effect_workspace",
    "config_policy_activation",
    "generic_fallback_or_default_behavior",
}
_UNPROMOTABLE_LIFECYCLES = {"draft", "proposed", "stale", "superseded", "invalid"}
_SECRET_MARKERS = ("SECRET", "TOKEN", "PASS", "KEY", "AUTH", "CREDENTIALS")
_PROTECTED_FORBIDDEN_HIDE_SURFACES = {
    "exit_code",
    "stderr",
    "output_file_tree",
    "process_state",
    "timeout_status",
}


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


def _assert_sha256(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "sha256:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must start with sha256:")
    digest = normalized.removeprefix(prefix)
    if len(digest) != 64 or any(ch not in "0123456789abcdef" for ch in digest):
        raise ValueError(f"{field_name} must use sha256:<64 lowercase hex>")
    return normalized


def _dump(model: BaseModel) -> dict[str, Any]:
    return model.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonical_payload(
    payload: BaseModel | dict[str, Any],
    *,
    object_kind: str,
    object_version: str = "1",
    hash_algorithm: HashAlgorithm = "sha256",
    canonicalization_profile_hash: str | None = None,
    drop_keys: set[str] | None = None,
) -> dict[str, Any]:
    if isinstance(payload, BaseModel):
        payload_data = _dump(payload)
    else:
        payload_data = dict(payload)
    for key in drop_keys or set():
        payload_data.pop(key, None)
    schema_id = str(payload_data.get("schema", object_kind))
    return {
        "schema_id": schema_id,
        "object_kind": object_kind,
        "object_version": object_version,
        "hash_algorithm": hash_algorithm,
        "canonicalization_profile_hash": canonicalization_profile_hash,
        "payload": payload_data,
    }


def canonical_hash(
    payload: BaseModel | dict[str, Any],
    *,
    object_kind: str,
    object_version: str = "1",
    hash_algorithm: HashAlgorithm = "sha256",
    canonicalization_profile_hash: str | None = None,
    drop_keys: set[str] | None = None,
) -> str:
    if hash_algorithm != "sha256":
        raise ValueError("only sha256 is supported")
    return (
        "sha256:"
        + sha256_canonical_json(
            canonical_payload(
                payload,
                object_kind=object_kind,
                object_version=object_version,
                hash_algorithm=hash_algorithm,
                canonicalization_profile_hash=canonicalization_profile_hash,
                drop_keys=drop_keys,
            )
        )
    )


def suite_root_hash_for(
    *,
    probe_contract_refs: list[str],
    probe_contract_hashes: list[str] | None = None,
    expected_observation_hash_refs: list[str],
    expected_observation_hashes: list[str] | None = None,
    canonicalization_profile_ref: str,
    canonicalization_profile_hash: str,
) -> str:
    return canonical_hash(
        {
            "schema": "repo_behavioral_replay_suite_root@1",
            "probe_contract_refs": _assert_sorted_unique(
                probe_contract_refs,
                field_name="probe_contract_refs",
            ),
            "probe_contract_hashes": _assert_sorted_unique(
                probe_contract_hashes or [],
                field_name="probe_contract_hashes",
            ),
            "expected_observation_hash_refs": _assert_sorted_unique(
                expected_observation_hash_refs,
                field_name="expected_observation_hash_refs",
            ),
            "expected_observation_hashes": _assert_sorted_unique(
                expected_observation_hashes or [],
                field_name="expected_observation_hashes",
            ),
            "canonicalization_profile_ref": _assert_non_empty_text(
                canonicalization_profile_ref,
                field_name="canonicalization_profile_ref",
            ),
            "canonicalization_profile_hash": _assert_sha256(
                canonicalization_profile_hash,
                field_name="canonicalization_profile_hash",
            ),
        },
        object_kind="repo_behavioral_replay_suite_root",
        canonicalization_profile_hash=canonicalization_profile_hash,
    )


class _BrlBase(BaseModel):
    model_config = MODEL_CONFIG


class ManifestScope(_BrlBase):
    bounded_claim: str
    certificate_use_allowed: bool = False
    promotion_use_allowed: bool = False

    @model_validator(mode="after")
    def _validate_scope(self) -> ManifestScope:
        object.__setattr__(
            self,
            "bounded_claim",
            _assert_non_empty_text(self.bounded_claim, field_name="bounded_claim"),
        )
        return self


class OwnerSurfaceRow(_BrlBase):
    owner_surface: str
    patch_risk_kind: PatchRiskKind
    protected_sibling_probe_refs: list[str] = Field(default_factory=list)
    required_when_touched: bool = True
    coverage_posture: str
    local_extension_posture: Literal["none", "declared_local_extension"] = "none"
    taxonomy_ref: str | None = None

    @model_validator(mode="after")
    def _validate_row(self) -> OwnerSurfaceRow:
        object.__setattr__(
            self,
            "owner_surface",
            _assert_non_empty_text(self.owner_surface, field_name="owner_surface"),
        )
        object.__setattr__(
            self,
            "coverage_posture",
            _assert_non_empty_text(self.coverage_posture, field_name="coverage_posture"),
        )
        object.__setattr__(
            self,
            "protected_sibling_probe_refs",
            _assert_sorted_unique(
                self.protected_sibling_probe_refs,
                field_name="protected_sibling_probe_refs",
            ),
        )
        if self.owner_surface not in _KNOWN_OWNER_SURFACES:
            if self.local_extension_posture != "declared_local_extension" or not self.taxonomy_ref:
                raise ValueError(
                    "unknown owner_surface requires declared local extension posture "
                    "and taxonomy_ref"
                )
        if self.taxonomy_ref is not None:
            object.__setattr__(
                self,
                "taxonomy_ref",
                _assert_non_empty_text(self.taxonomy_ref, field_name="taxonomy_ref"),
            )
        if self.required_when_touched and not self.protected_sibling_probe_refs:
            raise ValueError("required owner surfaces must declare protected sibling probes")
        return self


class ExecutionEnvironmentRow(_BrlBase):
    execution_environment_ref: str
    execution_environment_hash: str
    os: str
    arch: str
    runtime: str
    interpreter: str
    dependency_lock_ref: str
    locale: str
    timezone: str
    terminal_profile_ref: str
    env_policy_ref: str

    @model_validator(mode="after")
    def _validate_row(self) -> ExecutionEnvironmentRow:
        for field_name in (
            "execution_environment_ref",
            "os",
            "arch",
            "runtime",
            "interpreter",
            "dependency_lock_ref",
            "locale",
            "timezone",
            "terminal_profile_ref",
            "env_policy_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "execution_environment_hash",
            _assert_sha256(
                self.execution_environment_hash,
                field_name="execution_environment_hash",
            ),
        )
        return self


class SurfacePolicy(_BrlBase):
    raw_observed_surfaces: list[ObservationSurfaceKind] = Field(default_factory=list)
    canonicalized_surfaces: list[ObservationSurfaceKind] = Field(default_factory=list)
    protected_surfaces: list[ProtectedSurfaceKind] = Field(default_factory=list)
    explicitly_ignored_surfaces: list[ObservationSurfaceKind] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_policy(self) -> SurfacePolicy:
        for field_name in (
            "raw_observed_surfaces",
            "canonicalized_surfaces",
            "protected_surfaces",
            "explicitly_ignored_surfaces",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        protected = set(self.protected_surfaces)
        ignored = set(self.explicitly_ignored_surfaces)
        if protected & ignored:
            raise ValueError("protected surfaces cannot be explicitly ignored")
        if not protected:
            raise ValueError("protected surfaces must not be empty")
        return self


class CanonicalizationRuleRow(_BrlBase):
    rule_id: str
    rule_kind: CanonicalizationRuleKind
    applies_to_surfaces: list[ObservationSurfaceKind]
    scope: str
    protected_surface_effect: ProtectedSurfaceEffect
    rule_hash: str | None = None

    @model_validator(mode="after")
    def _validate_row(self) -> CanonicalizationRuleRow:
        for field_name in ("rule_id", "scope"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "applies_to_surfaces",
            _assert_sorted_unique(self.applies_to_surfaces, field_name="applies_to_surfaces"),
        )
        if self.rule_hash is not None:
            object.__setattr__(
                self,
                "rule_hash",
                _assert_sha256(self.rule_hash, field_name="rule_hash"),
            )
        return self


class RepoBehavioralCanonicalizationProfile(_BrlBase):
    schema: Literal[REPO_BEHAVIORAL_CANONICALIZATION_PROFILE_SCHEMA]
    canonicalization_profile_ref: str
    profile_version: str
    profile_hash: str | None = None
    text_rules: list[str] = Field(default_factory=list)
    structured_rules: list[str] = Field(default_factory=list)
    path_rules: list[str] = Field(default_factory=list)
    ordering_rules: list[str] = Field(default_factory=list)
    file_tree_rules: list[str] = Field(default_factory=list)
    process_rules: list[str] = Field(default_factory=list)
    timing_rules: list[str] = Field(default_factory=list)
    forbidden_normalizations: list[str] = Field(default_factory=list)
    rule_rows: list[CanonicalizationRuleRow]

    @model_validator(mode="after")
    def _validate_profile(self) -> RepoBehavioralCanonicalizationProfile:
        for field_name in ("canonicalization_profile_ref", "profile_version"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "text_rules",
            "structured_rules",
            "path_rules",
            "ordering_rules",
            "file_tree_rules",
            "process_rules",
            "timing_rules",
            "forbidden_normalizations",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(self.rule_rows, attr_name="rule_id", field_name="rule_rows")
        object.__setattr__(self, "rule_rows", sorted(self.rule_rows, key=lambda row: row.rule_id))
        for row in self.rule_rows:
            if (
                row.protected_surface_effect == "hides_protected_change"
                and set(row.applies_to_surfaces) & _PROTECTED_FORBIDDEN_HIDE_SURFACES
            ):
                raise ValueError("canonicalization cannot hide protected behavioral surfaces")
        if self.profile_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_canonicalization_profile",
                drop_keys={"profile_hash"},
            )
            if self.profile_hash != expected:
                raise ValueError("profile_hash must match canonicalization profile payload")
        return self


class RepoBehavioralProbeContract(_BrlBase):
    schema: Literal[REPO_BEHAVIORAL_PROBE_CONTRACT_SCHEMA]
    probe_id: str
    probe_label: str
    owner_surface: str
    protected_sibling_group_ref: str
    argv: list[str] = Field(default_factory=list)
    stdin_ref: str | None = None
    env_delta: dict[str, str] = Field(default_factory=dict)
    cwd_ref: str
    fixture_tree_hash_before: str | None = None
    fixture_tree_hash_after_expected: str | None = None
    fixture_tree_protection_kind: FixtureTreeProtectionKind = "read_only"
    workspace_write_allowlist: list[str] = Field(default_factory=list)
    cleanup_policy_ref: str | None = None
    protected_surfaces: list[ProtectedSurfaceKind]
    surface_policy: SurfacePolicy
    fixture_policy: str
    timeout_policy_ref: str
    canonicalization_profile_ref: str
    canonicalization_profile_hash: str
    expected_observation_hash_ref: str
    probe_contract_hash: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> RepoBehavioralProbeContract:
        for field_name in (
            "probe_id",
            "probe_label",
            "owner_surface",
            "protected_sibling_group_ref",
            "cwd_ref",
            "fixture_policy",
            "timeout_policy_ref",
            "canonicalization_profile_ref",
            "expected_observation_hash_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.owner_surface not in _KNOWN_OWNER_SURFACES and not self.owner_surface.startswith(
            "local:"
        ):
            raise ValueError("probe owner_surface must be known or local:<name>")
        if self.stdin_ref is not None:
            object.__setattr__(
                self,
                "stdin_ref",
                _assert_non_empty_text(self.stdin_ref, field_name="stdin_ref"),
            )
        for field_name in ("fixture_tree_hash_before", "fixture_tree_hash_after_expected"):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(self, field_name, _assert_sha256(value, field_name=field_name))
        object.__setattr__(
            self,
            "canonicalization_profile_hash",
            _assert_sha256(
                self.canonicalization_profile_hash,
                field_name="canonicalization_profile_hash",
            ),
        )
        object.__setattr__(
            self,
            "argv",
            [_assert_non_empty_text(value, field_name="argv") for value in self.argv],
        )
        object.__setattr__(
            self,
            "workspace_write_allowlist",
            _assert_sorted_unique(
                self.workspace_write_allowlist,
                field_name="workspace_write_allowlist",
            ),
        )
        object.__setattr__(
            self,
            "protected_surfaces",
            _assert_sorted_unique(self.protected_surfaces, field_name="protected_surfaces"),
        )
        if not self.protected_surfaces:
            raise ValueError("protected_surfaces must not be empty")
        if set(self.protected_surfaces) - set(self.surface_policy.protected_surfaces):
            raise ValueError("surface_policy must include every probe protected surface")
        if "output_file_tree" in self.protected_surfaces and self.fixture_tree_hash_before is None:
            raise ValueError("output_file_tree protection requires fixture_tree_hash_before")
        if self.fixture_tree_protection_kind != "read_only":
            if self.fixture_tree_hash_after_expected is None and not self.workspace_write_allowlist:
                raise ValueError("mutating probes require after-hash or workspace mutation policy")
        elif self.fixture_tree_hash_after_expected is not None:
            raise ValueError("read_only probes cannot declare expected fixture mutation")
        if self.cleanup_policy_ref is not None:
            object.__setattr__(
                self,
                "cleanup_policy_ref",
                _assert_non_empty_text(
                    self.cleanup_policy_ref,
                    field_name="cleanup_policy_ref",
                ),
            )
        if self.probe_contract_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_probe_contract",
                canonicalization_profile_hash=self.canonicalization_profile_hash,
                drop_keys={"probe_contract_hash"},
            )
            if self.probe_contract_hash != expected:
                raise ValueError("probe_contract_hash must match canonical probe contract payload")
        return self


class ExpectedObservationProvenance(_BrlBase):
    provenance_kind: ExpectedObservationProvenanceKind
    source_ref: str
    source_hash: str
    authority_layer: ManifestAuthorityLayer
    evidence_boundary_posture: EvidenceBoundaryPosture
    clean_first_pass_posture: CleanFirstPassPosture
    authority_posture: ExpectedObservationAuthorityPosture

    @model_validator(mode="after")
    def _validate_provenance(self) -> ExpectedObservationProvenance:
        object.__setattr__(
            self,
            "source_ref",
            _assert_non_empty_text(self.source_ref, field_name="source_ref"),
        )
        object.__setattr__(
            self,
            "source_hash",
            _assert_sha256(self.source_hash, field_name="source_hash"),
        )
        return self


class RepoBehavioralObservationHash(_BrlBase):
    schema: Literal[REPO_BEHAVIORAL_OBSERVATION_HASH_SCHEMA]
    observation_hash_ref: str
    probe_id: str
    hash_algorithm: HashAlgorithm = "sha256"
    canonical_material_kind: str
    hash_domain: HashDomain = "expected_reference_observation"
    exit_code: int | None = None
    stdout_hash: str | None = None
    stderr_hash: str | None = None
    output_file_tree_hash: str | None = None
    process_state_hash: str | None = None
    timeout_status: str | None = None
    canonical_observation_hash: str | None = None
    expected_observation_provenance: ExpectedObservationProvenance

    @model_validator(mode="after")
    def _validate_observation_hash(self) -> RepoBehavioralObservationHash:
        for field_name in ("observation_hash_ref", "probe_id", "canonical_material_kind"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "stdout_hash",
            "stderr_hash",
            "output_file_tree_hash",
            "process_state_hash",
        ):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(self, field_name, _assert_sha256(value, field_name=field_name))
        if self.timeout_status is not None:
            object.__setattr__(
                self,
                "timeout_status",
                _assert_non_empty_text(self.timeout_status, field_name="timeout_status"),
            )
        if self.canonical_observation_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_observation_hash",
                drop_keys={"canonical_observation_hash"},
            )
            if self.canonical_observation_hash != expected:
                raise ValueError(
                    "canonical_observation_hash must match canonical observation payload"
                )
        return self


class RepoBehavioralReplayManifest(_BrlBase):
    schema: Literal[REPO_BEHAVIORAL_REPLAY_MANIFEST_SCHEMA]
    manifest_id: str
    manifest_version: str
    manifest_authority_layer: ManifestAuthorityLayer
    manifest_lifecycle_state: ManifestLifecycleState
    manifest_visibility_posture: ManifestVisibilityPosture
    manifest_scope: ManifestScope
    product_ref: str
    candidate_artifact_kind: str
    protected_owner_surfaces: list[str]
    owner_surface_rows: list[OwnerSurfaceRow]
    owner_surface_map_ref: str
    owner_surface_map_hash: str
    owner_surface_taxonomy_version: str
    canonicalization_profile_ref: str
    canonicalization_profile_hash: str
    execution_environment_ref: str
    execution_environment_hash: str
    sensitive_material_policy_ref: str
    safe_rendering_policy_ref: str
    raw_material_storage_policy_ref: str
    redaction_profile_ref: str
    probe_contract_refs: list[str]
    probe_contract_hashes: list[str] = Field(default_factory=list)
    expected_observation_hash_refs: list[str]
    expected_observation_hashes: list[str] = Field(default_factory=list)
    suite_root_hash: str | None = None
    manifest_hash: str | None = None

    @model_validator(mode="after")
    def _validate_manifest(self) -> RepoBehavioralReplayManifest:
        for field_name in (
            "manifest_id",
            "manifest_version",
            "product_ref",
            "candidate_artifact_kind",
            "owner_surface_map_ref",
            "owner_surface_taxonomy_version",
            "canonicalization_profile_ref",
            "execution_environment_ref",
            "sensitive_material_policy_ref",
            "safe_rendering_policy_ref",
            "raw_material_storage_policy_ref",
            "redaction_profile_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "owner_surface_map_hash",
            "canonicalization_profile_hash",
            "execution_environment_hash",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sha256(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "protected_owner_surfaces",
            "probe_contract_refs",
            "probe_contract_hashes",
            "expected_observation_hash_refs",
            "expected_observation_hashes",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if not self.protected_owner_surfaces:
            raise ValueError("protected_owner_surfaces must not be empty")
        if not self.probe_contract_refs:
            raise ValueError("probe_contract_refs must not be empty")
        if not self.expected_observation_hash_refs:
            raise ValueError("expected_observation_hash_refs must not be empty")
        _assert_unique_rows(
            self.owner_surface_rows,
            attr_name="owner_surface",
            field_name="owner_surface_rows",
        )
        object.__setattr__(
            self,
            "owner_surface_rows",
            sorted(self.owner_surface_rows, key=lambda row: row.owner_surface),
        )
        row_surfaces = {row.owner_surface for row in self.owner_surface_rows}
        missing_surfaces = sorted(set(self.protected_owner_surfaces) - row_surfaces)
        if missing_surfaces:
            raise ValueError(f"protected owner surfaces missing rows: {missing_surfaces}")
        if self.manifest_lifecycle_state in _UNPROMOTABLE_LIFECYCLES and (
            self.manifest_scope.certificate_use_allowed
            or self.manifest_scope.promotion_use_allowed
        ):
            raise ValueError("unpromotable manifest lifecycle cannot claim promotion use")
        expected_suite_root = suite_root_hash_for(
            probe_contract_refs=self.probe_contract_refs,
            probe_contract_hashes=self.probe_contract_hashes,
            expected_observation_hash_refs=self.expected_observation_hash_refs,
            expected_observation_hashes=self.expected_observation_hashes,
            canonicalization_profile_ref=self.canonicalization_profile_ref,
            canonicalization_profile_hash=self.canonicalization_profile_hash,
        )
        if self.suite_root_hash is not None:
            object.__setattr__(
                self,
                "suite_root_hash",
                _assert_sha256(self.suite_root_hash, field_name="suite_root_hash"),
            )
            if self.suite_root_hash != expected_suite_root:
                raise ValueError("suite_root_hash must match canonical child hash order")
        if self.manifest_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_replay_manifest",
                canonicalization_profile_hash=self.canonicalization_profile_hash,
                drop_keys={"manifest_hash"},
            )
            if self.manifest_hash != expected:
                raise ValueError("manifest_hash must match canonical manifest payload")
        return self


class ManifestValidationDiagnosticRow(_BrlBase):
    diagnostic_ref: str
    severity: DiagnosticSeverity
    diagnostic_code: ManifestValidationDiagnosticKind
    message: str
    object_refs: list[str] = Field(default_factory=list)
    probe_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_row(self) -> ManifestValidationDiagnosticRow:
        for field_name in ("diagnostic_ref", "message"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("object_refs", "probe_refs"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class RepoBehavioralReplayManifestValidationReport(_BrlBase):
    schema: Literal[REPO_BEHAVIORAL_REPLAY_MANIFEST_VALIDATION_REPORT_SCHEMA]
    validation_report_ref: str
    manifest_id: str
    manifest_hash: str
    validation_status: ReplayValidationStatus
    diagnostic_rows: list[ManifestValidationDiagnosticRow]
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoBehavioralReplayManifestValidationReport:
        for field_name in ("validation_report_ref", "manifest_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "manifest_hash",
            _assert_sha256(self.manifest_hash, field_name="manifest_hash"),
        )
        _assert_unique_rows(
            self.diagnostic_rows,
            attr_name="diagnostic_ref",
            field_name="diagnostic_rows",
        )
        object.__setattr__(
            self,
            "diagnostic_rows",
            sorted(self.diagnostic_rows, key=lambda row: row.diagnostic_ref),
        )
        if self.validation_status == "valid_for_manifest_lock" and self.diagnostic_rows:
            raise ValueError("valid_for_manifest_lock report cannot contain diagnostics")
        if self.validation_status != "valid_for_manifest_lock" and not self.diagnostic_rows:
            raise ValueError("invalid/blocked reports require diagnostics")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_replay_manifest_validation_report",
                drop_keys={"canonical_output_hash"},
            )
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match validation report payload")
        return self


class RepoBehavioralReplayLockNonAuthorityGuardrail(_BrlBase):
    schema: Literal[REPO_BEHAVIORAL_REPLAY_LOCK_NON_AUTHORITY_GUARDRAIL_SCHEMA]
    guardrail_ref: str
    semantic_authority_granted: bool
    domain_ontology_authority_granted: bool
    hob_closure_authority_granted: bool
    otb_transition_authority_granted: bool
    probe_generation_authority_granted: bool
    probe_execution_authority_granted: bool
    candidate_replay_execution_authority_granted: bool
    observation_capture_authority_granted: bool
    candidate_comparison_authority_granted: bool
    impact_cone_selection_authority_granted: bool
    no_regression_certificate_authority_granted: bool
    implementation_authority_granted: bool
    worker_dispatch_authority_granted: bool
    product_authority_granted: bool
    official_eval_authority_granted: bool
    future_family_selection_granted: bool
    slice_scope_posture: Literal["brl_0a_manifest_validation_only"]
    replay_execution_posture: Literal["deferred_to_brl_0b"]
    certificate_posture: Literal["deferred_to_brl_0c"]

    @model_validator(mode="after")
    def _validate_guardrail(self) -> RepoBehavioralReplayLockNonAuthorityGuardrail:
        object.__setattr__(
            self,
            "guardrail_ref",
            _assert_non_empty_text(self.guardrail_ref, field_name="guardrail_ref"),
        )
        authority_fields = [
            "semantic_authority_granted",
            "domain_ontology_authority_granted",
            "hob_closure_authority_granted",
            "otb_transition_authority_granted",
            "probe_generation_authority_granted",
            "probe_execution_authority_granted",
            "candidate_replay_execution_authority_granted",
            "observation_capture_authority_granted",
            "candidate_comparison_authority_granted",
            "impact_cone_selection_authority_granted",
            "no_regression_certificate_authority_granted",
            "implementation_authority_granted",
            "worker_dispatch_authority_granted",
            "product_authority_granted",
            "official_eval_authority_granted",
            "future_family_selection_granted",
        ]
        granted = [field_name for field_name in authority_fields if getattr(self, field_name)]
        if granted:
            raise ValueError(f"BRL-0-A guardrail cannot grant authority: {granted}")
        return self


def _assert_unique_rows(rows: list[Any], *, attr_name: str, field_name: str) -> None:
    seen: set[str] = set()
    for row in rows:
        value = getattr(row, attr_name)
        if value in seen:
            raise ValueError(f"{field_name} must not contain duplicate {attr_name} {value!r}")
        seen.add(value)


def _diagnostic(
    *,
    index: int,
    diagnostic_code: ManifestValidationDiagnosticKind,
    message: str,
    object_refs: list[str] | None = None,
    probe_refs: list[str] | None = None,
) -> ManifestValidationDiagnosticRow:
    return ManifestValidationDiagnosticRow(
        diagnostic_ref=f"diagnostic:{index:04d}:{diagnostic_code}",
        severity="error",
        diagnostic_code=diagnostic_code,
        message=message,
        object_refs=object_refs or [],
        probe_refs=probe_refs or [],
    )


def load_replay_manifest(
    payload: RepoBehavioralReplayManifest | dict[str, Any],
) -> RepoBehavioralReplayManifest:
    if isinstance(payload, RepoBehavioralReplayManifest):
        return payload
    return RepoBehavioralReplayManifest.model_validate(payload)


def validate_replay_manifest(
    *,
    manifest: RepoBehavioralReplayManifest | dict[str, Any],
    probe_contracts: list[RepoBehavioralProbeContract | dict[str, Any]],
    canonicalization_profiles: list[RepoBehavioralCanonicalizationProfile | dict[str, Any]],
    expected_observation_hashes: list[RepoBehavioralObservationHash | dict[str, Any]],
    guardrail: RepoBehavioralReplayLockNonAuthorityGuardrail | dict[str, Any] | None = None,
) -> RepoBehavioralReplayManifestValidationReport:
    diagnostics: list[ManifestValidationDiagnosticRow] = []

    loaded_manifest = load_replay_manifest(manifest)
    loaded_probes = [
        probe
        if isinstance(probe, RepoBehavioralProbeContract)
        else RepoBehavioralProbeContract.model_validate(probe)
        for probe in probe_contracts
    ]
    loaded_profiles = [
        profile
        if isinstance(profile, RepoBehavioralCanonicalizationProfile)
        else RepoBehavioralCanonicalizationProfile.model_validate(profile)
        for profile in canonicalization_profiles
    ]
    loaded_observations = [
        observation
        if isinstance(observation, RepoBehavioralObservationHash)
        else RepoBehavioralObservationHash.model_validate(observation)
        for observation in expected_observation_hashes
    ]
    loaded_guardrail = (
        default_non_authority_guardrail()
        if guardrail is None
        else (
            guardrail
            if isinstance(guardrail, RepoBehavioralReplayLockNonAuthorityGuardrail)
            else RepoBehavioralReplayLockNonAuthorityGuardrail.model_validate(guardrail)
        )
    )

    probe_by_ref = {probe.probe_id: probe for probe in loaded_probes}
    if len(probe_by_ref) != len(loaded_probes):
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="duplicate_probe_id",
                message="probe contracts contain duplicate probe_id values",
            )
        )
    profile_by_ref = {
        profile.canonicalization_profile_ref: profile for profile in loaded_profiles
    }
    observation_by_ref = {
        observation.observation_hash_ref: observation for observation in loaded_observations
    }

    missing_probe_refs = sorted(set(loaded_manifest.probe_contract_refs) - set(probe_by_ref))
    if missing_probe_refs:
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="missing_probe_contract",
                message=f"manifest references missing probe contracts: {missing_probe_refs}",
                probe_refs=missing_probe_refs,
            )
        )
    missing_observation_refs = sorted(
        set(loaded_manifest.expected_observation_hash_refs) - set(observation_by_ref)
    )
    if missing_observation_refs:
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="missing_expected_observation_hash",
                message=(
                    "manifest references missing expected observations: "
                    f"{missing_observation_refs}"
                ),
                object_refs=missing_observation_refs,
            )
        )
    loaded_profile = profile_by_ref.get(loaded_manifest.canonicalization_profile_ref)
    if loaded_profile is None:
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="unknown_canonicalization_profile",
                message="manifest references missing canonicalization profile",
                object_refs=[loaded_manifest.canonicalization_profile_ref],
            )
        )
    elif loaded_profile.profile_hash != loaded_manifest.canonicalization_profile_hash:
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="profile_hash_mismatch",
                message=(
                    "supplied canonicalization profile hash does not match manifest "
                    "canonicalization_profile_hash"
                ),
                object_refs=[loaded_manifest.canonicalization_profile_ref],
            )
        )
    if loaded_manifest.manifest_hash is None:
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="manifest_hash_mismatch",
                message="manifest_hash is required for lock validation",
            )
        )
    if loaded_manifest.suite_root_hash is None:
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="suite_root_hash_mismatch",
                message="suite_root_hash is required for lock validation",
            )
        )
    if loaded_guardrail.candidate_replay_execution_authority_granted:
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="guardrail_authority_violation",
                message="BRL-0-A guardrail cannot grant replay authority",
            )
        )
    referenced_probes = [
        probe_by_ref[probe_ref]
        for probe_ref in loaded_manifest.probe_contract_refs
        if probe_ref in probe_by_ref
    ]
    actual_probe_hashes: list[str] = []
    for probe in referenced_probes:
        if probe.probe_contract_hash is None:
            diagnostics.append(
                _diagnostic(
                    index=len(diagnostics) + 1,
                    diagnostic_code="probe_contract_hash_mismatch",
                    message="referenced probe contract lacks probe_contract_hash",
                    probe_refs=[probe.probe_id],
                )
            )
        else:
            actual_probe_hashes.append(probe.probe_contract_hash)
    if sorted(actual_probe_hashes) != sorted(loaded_manifest.probe_contract_hashes):
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="probe_contract_hash_mismatch",
                message="manifest probe_contract_hashes do not match supplied probe contracts",
                probe_refs=loaded_manifest.probe_contract_refs,
            )
        )

    actual_observation_hashes: list[str] = []
    for observation_ref in loaded_manifest.expected_observation_hash_refs:
        observation = observation_by_ref.get(observation_ref)
        if observation is not None and observation.canonical_observation_hash is not None:
            actual_observation_hashes.append(observation.canonical_observation_hash)
    if sorted(actual_observation_hashes) != sorted(loaded_manifest.expected_observation_hashes):
        diagnostics.append(
            _diagnostic(
                index=len(diagnostics) + 1,
                diagnostic_code="missing_expected_observation_hash",
                message=(
                    "manifest expected_observation_hashes do not match supplied "
                    "expected observations"
                ),
                object_refs=loaded_manifest.expected_observation_hash_refs,
            )
        )

    if loaded_manifest.suite_root_hash is not None:
        actual_suite_root_hash = suite_root_hash_for(
            probe_contract_refs=loaded_manifest.probe_contract_refs,
            probe_contract_hashes=actual_probe_hashes,
            expected_observation_hash_refs=loaded_manifest.expected_observation_hash_refs,
            expected_observation_hashes=actual_observation_hashes,
            canonicalization_profile_ref=loaded_manifest.canonicalization_profile_ref,
            canonicalization_profile_hash=loaded_manifest.canonicalization_profile_hash,
        )
        if loaded_manifest.suite_root_hash != actual_suite_root_hash:
            diagnostics.append(
                _diagnostic(
                    index=len(diagnostics) + 1,
                    diagnostic_code="suite_root_hash_mismatch",
                    message="manifest suite_root_hash does not match supplied child hashes",
                )
            )

    for probe in loaded_probes:
        if any(marker in key.upper() for key in probe.env_delta for marker in _SECRET_MARKERS):
            required_policy_refs = [
                loaded_manifest.sensitive_material_policy_ref,
                loaded_manifest.safe_rendering_policy_ref,
                loaded_manifest.raw_material_storage_policy_ref,
                loaded_manifest.redaction_profile_ref,
            ]
            if any(not ref.strip() for ref in required_policy_refs):
                diagnostics.append(
                    _diagnostic(
                        index=len(diagnostics) + 1,
                        diagnostic_code="unsafe_sensitive_material",
                        message=(
                            "secret-like environment values require safe rendering/storage "
                            "policy"
                        ),
                        probe_refs=[probe.probe_id],
                    )
                )
        observation = observation_by_ref.get(probe.expected_observation_hash_ref)
        if observation is None:
            diagnostics.append(
                _diagnostic(
                    index=len(diagnostics) + 1,
                    diagnostic_code="missing_expected_observation_hash",
                    message="probe references missing expected observation hash",
                    probe_refs=[probe.probe_id],
                    object_refs=[probe.expected_observation_hash_ref],
                )
            )
        elif observation.probe_id != probe.probe_id:
            diagnostics.append(
                _diagnostic(
                    index=len(diagnostics) + 1,
                    diagnostic_code="missing_expected_observation_hash",
                    message="expected observation hash probe_id does not match probe contract",
                    probe_refs=[probe.probe_id, observation.probe_id],
                )
            )
        elif observation.canonical_observation_hash is None:
            diagnostics.append(
                _diagnostic(
                    index=len(diagnostics) + 1,
                    diagnostic_code="missing_expected_observation_hash",
                    message="expected observation hash lacks canonical_observation_hash",
                    probe_refs=[probe.probe_id],
                    object_refs=[observation.observation_hash_ref],
                )
            )
    status: ReplayValidationStatus = "invalid" if diagnostics else "valid_for_manifest_lock"
    report_without_hash = RepoBehavioralReplayManifestValidationReport(
        schema=REPO_BEHAVIORAL_REPLAY_MANIFEST_VALIDATION_REPORT_SCHEMA,
        validation_report_ref=f"validation:{loaded_manifest.manifest_id}",
        manifest_id=loaded_manifest.manifest_id,
        manifest_hash=loaded_manifest.manifest_hash
        or canonical_hash(
            loaded_manifest,
            object_kind="repo_behavioral_replay_manifest",
            canonicalization_profile_hash=loaded_manifest.canonicalization_profile_hash,
            drop_keys={"manifest_hash"},
        ),
        validation_status=status,
        diagnostic_rows=diagnostics,
    )
    payload = report_without_hash.model_dump(mode="json", exclude_none=True)
    payload["canonical_output_hash"] = canonical_hash(
        report_without_hash,
        object_kind="repo_behavioral_replay_manifest_validation_report",
        drop_keys={"canonical_output_hash"},
    )
    return RepoBehavioralReplayManifestValidationReport.model_validate(payload)


def default_non_authority_guardrail() -> RepoBehavioralReplayLockNonAuthorityGuardrail:
    return RepoBehavioralReplayLockNonAuthorityGuardrail(
        schema=REPO_BEHAVIORAL_REPLAY_LOCK_NON_AUTHORITY_GUARDRAIL_SCHEMA,
        guardrail_ref="brl-0-a:non-authority",
        semantic_authority_granted=False,
        domain_ontology_authority_granted=False,
        hob_closure_authority_granted=False,
        otb_transition_authority_granted=False,
        probe_generation_authority_granted=False,
        probe_execution_authority_granted=False,
        candidate_replay_execution_authority_granted=False,
        observation_capture_authority_granted=False,
        candidate_comparison_authority_granted=False,
        impact_cone_selection_authority_granted=False,
        no_regression_certificate_authority_granted=False,
        implementation_authority_granted=False,
        worker_dispatch_authority_granted=False,
        product_authority_granted=False,
        official_eval_authority_granted=False,
        future_family_selection_granted=False,
        slice_scope_posture="brl_0a_manifest_validation_only",
        replay_execution_posture="deferred_to_brl_0b",
        certificate_posture="deferred_to_brl_0c",
    )
