from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, ValidationInfo, model_validator
from urm_runtime.hashing import sha256_canonical_json

from .conformance import (
    _assert_non_empty_text,
    _assert_sorted_unique,
    _load_repo_json,
    _normalize_repo_relative_path,
    _resolve_repository_root,
    _sha256_repo_file,
    _validation_context,
)

V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA = (
    "v40f_architecture_release_integration_evidence@1"
)
V40F_V82_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS82.md#v82-continuation-contract-machine-checkable"
)
V40F_RELEASE_ARC = "vNext+82"
V40F_RELEASE_FAMILY = "V40"
V40F_V81_STOP_GATE_REF = "artifacts/stop_gate/metrics_v81_closeout.json"
V40F_RUNTIME_OBSERVABILITY_COMPARISON_REF = (
    "artifacts/agent_harness/v81/evidence_inputs/runtime_observability_comparison_v81.json"
)

_HEX_64_RE = re.compile(r"^[0-9a-f]{64}$")
_RELEASED_PATHS = ("V40-A", "V40-B", "V40-C", "V40-D", "V40-E")
_DEFERRED_SURFACE_REFS = (
    "ux_morph_ir@1",
    "rendered_surface_release",
    "surface_compiler_export",
    "api_human_review_workbench_routes",
    "web_human_review_workbench_routes",
    "formal_sidecar_authority_promotion",
)
_FORMAL_SIDECAR_PREFIXES = ("RequestProject/", "docs/formal/")
_SURFACE_ARTIFACT_PREFIXES = (
    "apps/api/fixtures/",
    "packages/adeu_architecture_ir/schema/",
    "packages/adeu_architecture_compiler/schema/",
    "packages/adeu_core_ir/schema/",
)
_DEFAULT_NOTES = (
    "v82 family evidence binds the released V40-A through V40-E ladder as one canonical "
    "integration artifact, keeps stop-gate continuity anchored to the released v81 "
    "baseline, and records deferred surfaces explicitly without promoting runtime "
    "observability or the Lean sidecar into release authority."
)


@dataclass(frozen=True)
class _ReleasePathSpec:
    path_label: str
    evidence_ref: str
    evidence_schema: str
    closeout_doc_ref: str
    release_surface_refs: tuple[str, ...]


_RELEASE_PATH_SPECS: tuple[_ReleasePathSpec, ...] = (
    _ReleasePathSpec(
        path_label="V40-A",
        evidence_ref="artifacts/agent_harness/v77/evidence_inputs/v40a_architecture_semantic_root_evidence_v77.json",
        evidence_schema="v40a_architecture_semantic_root_evidence@1",
        closeout_doc_ref="docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS77.md",
        release_surface_refs=(
            "apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_boundary_graph_v77_reference.json",
            "apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_intent_packet_v77_reference.json",
            "apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_ontology_frame_v77_reference.json",
            "apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_semantic_ir_v77_reference.json",
            "apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_world_hypothesis_v77_reference.json",
            "packages/adeu_architecture_ir/schema/adeu_architecture_boundary_graph.v1.json",
            "packages/adeu_architecture_ir/schema/adeu_architecture_intent_packet.v1.json",
            "packages/adeu_architecture_ir/schema/adeu_architecture_ontology_frame.v1.json",
            "packages/adeu_architecture_ir/schema/adeu_architecture_semantic_ir.v1.json",
            "packages/adeu_architecture_ir/schema/adeu_architecture_world_hypothesis.v1.json",
        ),
    ),
    _ReleasePathSpec(
        path_label="V40-B",
        evidence_ref="artifacts/agent_harness/v78/evidence_inputs/v40b_architecture_compiler_evidence_v78.json",
        evidence_schema="v40b_architecture_compiler_evidence@1",
        closeout_doc_ref="docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS78.md",
        release_surface_refs=(
            "apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json",
            "apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
            "packages/adeu_architecture_compiler/schema/adeu_architecture_conformance_report.v1.json",
        ),
    ),
    _ReleasePathSpec(
        path_label="V40-C",
        evidence_ref="artifacts/agent_harness/v79/evidence_inputs/v40c_architecture_hybrid_evidence_v79.json",
        evidence_schema="v40c_architecture_hybrid_evidence@1",
        closeout_doc_ref="docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS79.md",
        release_surface_refs=(
            "apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json",
            "apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_human_needed_reference.json",
            "apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_oracle_reference.json",
            "apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_ir_delta_v79_reference.json",
            "apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_oracle_request_v79_reference.json",
            "apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_oracle_resolution_v79_reference.json",
            "packages/adeu_architecture_compiler/schema/adeu_architecture_checkpoint_trace.v1.json",
            "packages/adeu_architecture_compiler/schema/adeu_architecture_ir_delta.v1.json",
            "packages/adeu_architecture_compiler/schema/adeu_architecture_oracle_request.v1.json",
            "packages/adeu_architecture_compiler/schema/adeu_architecture_oracle_resolution.v1.json",
        ),
    ),
    _ReleasePathSpec(
        path_label="V40-D",
        evidence_ref="artifacts/agent_harness/v80/evidence_inputs/v40d_architecture_core_ir_lowering_evidence_v80.json",
        evidence_schema="v40d_architecture_core_ir_lowering_evidence@1",
        closeout_doc_ref="docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS80.md",
        release_surface_refs=(
            "apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_blocked_reference.json",
            "apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_ready_reference.json",
            "apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_blocked_reference.json",
            "apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_ready_reference.json",
            "apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json",
            "packages/adeu_architecture_compiler/schema/adeu_architecture_projection_bundle.v1.json",
            "packages/adeu_architecture_compiler/schema/adeu_architecture_projection_manifest.v1.json",
            "packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json",
        ),
    ),
    _ReleasePathSpec(
        path_label="V40-E",
        evidence_ref="artifacts/agent_harness/v81/evidence_inputs/v40e_architecture_ux_domain_packet_compatibility_evidence_v81.json",
        evidence_schema="v40e_architecture_ux_domain_packet_compatibility_evidence@1",
        closeout_doc_ref="docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS81.md",
        release_surface_refs=(
            "apps/api/fixtures/architecture/vnext_plus81/ux_domain_packet_v81_ready_reference.json",
            "packages/adeu_core_ir/schema/ux_domain_packet.v1.json",
        ),
    ),
)
_PATH_SPEC_BY_LABEL = {spec.path_label: spec for spec in _RELEASE_PATH_SPECS}
_ALLOWED_EVIDENCE_REFS = frozenset(spec.evidence_ref for spec in _RELEASE_PATH_SPECS)
_ALLOWED_CLOSEOUT_DOC_REFS = frozenset(spec.closeout_doc_ref for spec in _RELEASE_PATH_SPECS)
_ALLOWED_RELEASE_SURFACE_REFS = frozenset(
    ref for spec in _RELEASE_PATH_SPECS for ref in spec.release_surface_refs
)


def _assert_sha256(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if not _HEX_64_RE.match(normalized):
        raise ValueError(f"{field_name} must be a 64-character lowercase hex sha256")
    return normalized


def _canonical_release_surface_refs(values: list[str]) -> list[str]:
    normalized = _assert_sorted_unique(values, field_name="release_surface_refs", allow_empty=False)
    for value in normalized:
        if value.startswith(_FORMAL_SIDECAR_PREFIXES):
            raise ValueError("formal-sidecar files may not be admitted as family release surfaces")
        if not value.startswith(_SURFACE_ARTIFACT_PREFIXES):
            raise ValueError(
                "release_surface_refs must point only to released "
                "artifact/schema files"
            )
    return normalized


def _family_evidence_hash(payload: dict[str, Any]) -> str:
    without_hash = dict(payload)
    without_hash.pop("family_evidence_hash", None)
    return sha256_canonical_json(without_hash)


class ArchitecturePathReleaseClosure(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    path_label: str
    evidence_ref: str
    evidence_hash: str
    closeout_doc_ref: str
    closeout_doc_hash: str
    release_surface_refs: list[str]
    release_surface_hashes: dict[str, str]

    @model_validator(mode="after")
    def _validate_closure(self, info: ValidationInfo) -> ArchitecturePathReleaseClosure:
        object.__setattr__(
            self, "path_label", _assert_non_empty_text(self.path_label, field_name="path_label")
        )
        if self.path_label not in _PATH_SPEC_BY_LABEL:
            raise ValueError("path_label must be one of the released V40-A through V40-E paths")
        spec = _PATH_SPEC_BY_LABEL[self.path_label]

        normalized_evidence_ref = _normalize_repo_relative_path(
            self.evidence_ref,
            field_name="evidence_ref",
        )
        if normalized_evidence_ref != spec.evidence_ref:
            raise ValueError(
                f"{self.path_label} evidence_ref must match the released "
                "path evidence"
            )
        object.__setattr__(self, "evidence_ref", normalized_evidence_ref)
        object.__setattr__(
            self, "evidence_hash", _assert_sha256(self.evidence_hash, field_name="evidence_hash")
        )

        normalized_closeout_doc_ref = _normalize_repo_relative_path(
            self.closeout_doc_ref,
            field_name="closeout_doc_ref",
        )
        if normalized_closeout_doc_ref != spec.closeout_doc_ref:
            raise ValueError(
                f"{self.path_label} closeout_doc_ref must match the released closeout doc"
            )
        object.__setattr__(self, "closeout_doc_ref", normalized_closeout_doc_ref)
        object.__setattr__(
            self,
            "closeout_doc_hash",
            _assert_sha256(self.closeout_doc_hash, field_name="closeout_doc_hash"),
        )

        normalized_surface_refs = _canonical_release_surface_refs(self.release_surface_refs)
        if normalized_surface_refs != sorted(spec.release_surface_refs):
            raise ValueError(
                f"{self.path_label} release_surface_refs must match the released surface set"
            )
        object.__setattr__(self, "release_surface_refs", normalized_surface_refs)

        release_surface_hashes = {}
        for path, digest in self.release_surface_hashes.items():
            normalized_path = _normalize_repo_relative_path(
                path,
                field_name="release_surface_hashes key",
            )
            release_surface_hashes[normalized_path] = _assert_sha256(
                digest,
                field_name=f"release_surface_hashes[{path}]",
            )
        if set(release_surface_hashes) != set(normalized_surface_refs):
            raise ValueError("release_surface_hashes must cover exactly release_surface_refs")
        object.__setattr__(
            self,
            "release_surface_hashes",
            {path: release_surface_hashes[path] for path in normalized_surface_refs},
        )

        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            evidence_payload = _load_repo_json(
                normalized_evidence_ref,
                repository_root=repository_root,
            )
            if evidence_payload.get("schema") != spec.evidence_schema:
                raise ValueError(
                    f"{self.path_label} evidence_ref must carry schema {spec.evidence_schema}"
                )
            if (
                _sha256_repo_file(normalized_evidence_ref, repository_root=repository_root)
                != self.evidence_hash
            ):
                raise ValueError("evidence_hash must match the referenced evidence_ref contents")
            if (
                _sha256_repo_file(normalized_closeout_doc_ref, repository_root=repository_root)
                != self.closeout_doc_hash
            ):
                raise ValueError("closeout_doc_hash must match the referenced closeout doc")
            for surface_ref in normalized_surface_refs:
                if (
                    _sha256_repo_file(surface_ref, repository_root=repository_root)
                    != self.release_surface_hashes[surface_ref]
                ):
                    raise ValueError(
                        "release_surface_hashes must match the referenced release surface contents"
                    )
        return self


class V40FArchitectureReleaseIntegrationEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema: Literal[V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA] = (
        V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA
    )
    family_label: Literal[V40F_RELEASE_FAMILY] = V40F_RELEASE_FAMILY
    release_arc: Literal[V40F_RELEASE_ARC] = V40F_RELEASE_ARC
    released_paths: list[str]
    per_path_release_closure: dict[str, ArchitecturePathReleaseClosure]
    consumed_arc_evidence_refs: list[str]
    consumed_closeout_doc_refs: list[str]
    family_release_surface_refs: list[str]
    deferred_surface_refs: list[str]
    stop_gate_schema_family: Literal["stop_gate_metrics@1"] = "stop_gate_metrics@1"
    v81_stop_gate_ref: str = V40F_V81_STOP_GATE_REF
    metric_key_cardinality: int
    metric_keys: list[str]
    metric_key_exact_set_equal_v81: bool
    family_evidence_hash: str
    runtime_observability_comparison_ref: str = V40F_RUNTIME_OBSERVABILITY_COMPARISON_REF
    notes: str

    @model_validator(mode="after")
    def _validate_evidence(
        self,
        info: ValidationInfo,
    ) -> V40FArchitectureReleaseIntegrationEvidence:
        released_paths = _assert_sorted_unique(
            self.released_paths,
            field_name="released_paths",
            allow_empty=False,
        )
        if released_paths != list(_RELEASED_PATHS):
            raise ValueError("released_paths must be exactly V40-A through V40-E")
        object.__setattr__(self, "released_paths", released_paths)

        closure_keys = sorted(self.per_path_release_closure)
        if closure_keys != list(_RELEASED_PATHS):
            raise ValueError(
                "per_path_release_closure must provide exact keyed closure "
                "for V40-A..V40-E"
            )
        for key, closure in self.per_path_release_closure.items():
            if key != closure.path_label:
                raise ValueError("per_path_release_closure keys must match path_label")

        expected_evidence_refs = sorted(
            closure.evidence_ref for closure in self.per_path_release_closure.values()
        )
        consumed_arc_evidence_refs = _assert_sorted_unique(
            self.consumed_arc_evidence_refs,
            field_name="consumed_arc_evidence_refs",
            allow_empty=False,
        )
        if set(consumed_arc_evidence_refs) != _ALLOWED_EVIDENCE_REFS:
            raise ValueError(
                "consumed_arc_evidence_refs must match the released "
                "per-path evidence set"
            )
        if consumed_arc_evidence_refs != expected_evidence_refs:
            raise ValueError(
                "consumed_arc_evidence_refs must match the exact "
                "evidence_ref set from per_path_release_closure"
            )
        object.__setattr__(self, "consumed_arc_evidence_refs", consumed_arc_evidence_refs)

        expected_closeout_doc_refs = sorted(
            closure.closeout_doc_ref for closure in self.per_path_release_closure.values()
        )
        consumed_closeout_doc_refs = _assert_sorted_unique(
            self.consumed_closeout_doc_refs,
            field_name="consumed_closeout_doc_refs",
            allow_empty=False,
        )
        if set(consumed_closeout_doc_refs) != _ALLOWED_CLOSEOUT_DOC_REFS:
            raise ValueError(
                "consumed_closeout_doc_refs must match the released per-path closeout doc set"
            )
        if consumed_closeout_doc_refs != expected_closeout_doc_refs:
            raise ValueError(
                "consumed_closeout_doc_refs must match the exact "
                "closeout_doc_ref set from per_path_release_closure"
            )
        object.__setattr__(self, "consumed_closeout_doc_refs", consumed_closeout_doc_refs)

        family_release_surface_refs = _canonical_release_surface_refs(
            self.family_release_surface_refs
        )
        if any(ref not in _ALLOWED_RELEASE_SURFACE_REFS for ref in family_release_surface_refs):
            raise ValueError(
                "family_release_surface_refs may point only to already "
                "released V40-A through V40-E surfaces"
            )
        expected_family_release_surface_refs = sorted(
            {
                ref
                for closure in self.per_path_release_closure.values()
                for ref in closure.release_surface_refs
            }
        )
        if family_release_surface_refs != expected_family_release_surface_refs:
            raise ValueError(
                "family_release_surface_refs must equal the exact union "
                "of per-path release_surface_refs"
            )
        object.__setattr__(self, "family_release_surface_refs", family_release_surface_refs)

        deferred_surface_refs = _assert_sorted_unique(
            self.deferred_surface_refs,
            field_name="deferred_surface_refs",
            allow_empty=False,
        )
        if deferred_surface_refs != sorted(_DEFERRED_SURFACE_REFS):
            raise ValueError(
                "deferred_surface_refs must list the exact deferred surfaces frozen for V40-F"
            )
        object.__setattr__(self, "deferred_surface_refs", deferred_surface_refs)

        normalized_v81_stop_gate_ref = _normalize_repo_relative_path(
            self.v81_stop_gate_ref,
            field_name="v81_stop_gate_ref",
        )
        if normalized_v81_stop_gate_ref != V40F_V81_STOP_GATE_REF:
            raise ValueError("v81_stop_gate_ref must remain the frozen v81 stop-gate source")
        object.__setattr__(self, "v81_stop_gate_ref", normalized_v81_stop_gate_ref)

        metric_keys = _assert_sorted_unique(
            self.metric_keys,
            field_name="metric_keys",
            allow_empty=False,
        )
        object.__setattr__(self, "metric_keys", metric_keys)
        if self.metric_key_cardinality != len(metric_keys):
            raise ValueError("metric_key_cardinality must equal len(metric_keys)")
        if not self.metric_key_exact_set_equal_v81:
            raise ValueError("metric_key_exact_set_equal_v81 must remain true in V40-F")

        normalized_runtime_ref = _normalize_repo_relative_path(
            self.runtime_observability_comparison_ref,
            field_name="runtime_observability_comparison_ref",
        )
        object.__setattr__(
            self,
            "runtime_observability_comparison_ref",
            normalized_runtime_ref,
        )
        object.__setattr__(self, "notes", _assert_non_empty_text(self.notes, field_name="notes"))
        object.__setattr__(
            self,
            "family_evidence_hash",
            _assert_sha256(self.family_evidence_hash, field_name="family_evidence_hash"),
        )

        repository_root = info.context.get("repository_root") if info.context else None
        if repository_root is not None:
            stop_gate_payload = _load_repo_json(
                normalized_v81_stop_gate_ref,
                repository_root=repository_root,
            )
            if stop_gate_payload.get("schema") != self.stop_gate_schema_family:
                raise ValueError("v81_stop_gate_ref must preserve stop_gate_metrics@1")
            metrics = stop_gate_payload.get("metrics")
            if not isinstance(metrics, dict):
                raise ValueError("v81_stop_gate_ref must contain a metrics object")
            stop_gate_metric_keys = sorted(str(key) for key in metrics)
            if metric_keys != stop_gate_metric_keys:
                raise ValueError("metric_keys must match the exact v81 stop-gate metric key set")

            runtime_payload = _load_repo_json(
                normalized_runtime_ref,
                repository_root=repository_root,
            )
            if runtime_payload.get("schema") != "runtime_observability_comparison@1":
                raise ValueError(
                    "runtime_observability_comparison_ref must point to "
                    "runtime_observability_comparison@1"
                )

        expected_hash = _family_evidence_hash(_dump_json_payload(self, exclude_hash=True))
        if self.family_evidence_hash != expected_hash:
            raise ValueError(
                "family_evidence_hash must match the canonical family "
                "evidence payload"
            )
        return self


def _dump_json_payload(
    model: V40FArchitectureReleaseIntegrationEvidence,
    *,
    exclude_hash: bool = False,
) -> dict[str, Any]:
    exclude = {"family_evidence_hash"} if exclude_hash else None
    return model.model_dump(mode="json", exclude=exclude)


def canonicalize_v40f_architecture_release_integration_evidence_payload(
    payload: dict[str, Any],
    *,
    repository_root: Path | None = None,
) -> dict[str, Any]:
    evidence = V40FArchitectureReleaseIntegrationEvidence.model_validate(
        payload,
        context=_validation_context(repository_root),
    )
    return _dump_json_payload(evidence)


def _build_path_closure(
    spec: _ReleasePathSpec,
    *,
    repository_root: Path,
) -> dict[str, Any]:
    return {
        "path_label": spec.path_label,
        "evidence_ref": spec.evidence_ref,
        "evidence_hash": _sha256_repo_file(spec.evidence_ref, repository_root=repository_root),
        "closeout_doc_ref": spec.closeout_doc_ref,
        "closeout_doc_hash": _sha256_repo_file(
            spec.closeout_doc_ref,
            repository_root=repository_root,
        ),
        "release_surface_refs": sorted(spec.release_surface_refs),
        "release_surface_hashes": {
            ref: _sha256_repo_file(ref, repository_root=repository_root)
            for ref in sorted(spec.release_surface_refs)
        },
    }


def derive_v40f_release_integration_evidence(
    *,
    repository_root: Path | None = None,
    runtime_observability_comparison_ref: str = V40F_RUNTIME_OBSERVABILITY_COMPARISON_REF,
    notes: str = _DEFAULT_NOTES,
) -> dict[str, Any]:
    root = _resolve_repository_root(repository_root)
    closure = {
        spec.path_label: _build_path_closure(spec, repository_root=root)
        for spec in _RELEASE_PATH_SPECS
    }
    stop_gate_payload = _load_repo_json(V40F_V81_STOP_GATE_REF, repository_root=root)
    runtime_ref = _normalize_repo_relative_path(
        runtime_observability_comparison_ref,
        field_name="runtime_observability_comparison_ref",
    )
    metric_keys = sorted(str(key) for key in stop_gate_payload["metrics"])
    payload: dict[str, Any] = {
        "schema": V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA,
        "family_label": V40F_RELEASE_FAMILY,
        "release_arc": V40F_RELEASE_ARC,
        "released_paths": list(_RELEASED_PATHS),
        "per_path_release_closure": closure,
        "consumed_arc_evidence_refs": sorted(spec.evidence_ref for spec in _RELEASE_PATH_SPECS),
        "consumed_closeout_doc_refs": sorted(spec.closeout_doc_ref for spec in _RELEASE_PATH_SPECS),
        "family_release_surface_refs": sorted(_ALLOWED_RELEASE_SURFACE_REFS),
        "deferred_surface_refs": sorted(_DEFERRED_SURFACE_REFS),
        "stop_gate_schema_family": "stop_gate_metrics@1",
        "v81_stop_gate_ref": V40F_V81_STOP_GATE_REF,
        "metric_key_cardinality": len(metric_keys),
        "metric_keys": metric_keys,
        "metric_key_exact_set_equal_v81": True,
        "runtime_observability_comparison_ref": runtime_ref,
        "notes": notes,
    }
    payload["family_evidence_hash"] = _family_evidence_hash(payload)
    return canonicalize_v40f_architecture_release_integration_evidence_payload(
        payload,
        repository_root=root,
    )


__all__ = [
    "V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA",
    "V40F_RUNTIME_OBSERVABILITY_COMPARISON_REF",
    "V40F_V81_STOP_GATE_REF",
    "V40F_V82_CONTRACT_SOURCE",
    "V40FArchitectureReleaseIntegrationEvidence",
    "canonicalize_v40f_architecture_release_integration_evidence_payload",
    "derive_v40f_release_integration_evidence",
]
