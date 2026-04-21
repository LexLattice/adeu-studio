from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from typing import Any

from adeu_commitments_ir import (
    AnmDocAuthorityProfile,
    AnmDocClassPolicy,
    AnmMigrationBindingProfile,
    AnmMigrationBindingRow,
    AnmReaderProjectionManifest,
    AnmReaderProjectionRow,
    AnmSemanticDiffChangeRow,
    AnmSemanticDiffReport,
    AnmSourceSetManifest,
    canonicalize_anm_doc_authority_profile_payload,
    canonicalize_anm_doc_class_policy_payload,
    canonicalize_anm_migration_binding_profile_payload,
    canonicalize_anm_reader_projection_manifest_payload,
    canonicalize_anm_source_set_manifest_payload,
    stable_payload_hash,
)
from adeu_ir.repo import repo_root
from adeu_semantic_source import AnmCompileError


@dataclass(frozen=True)
class V66BMigrationResult:
    migration_binding_profile: AnmMigrationBindingProfile
    reader_projection_manifest: AnmReaderProjectionManifest
    semantic_diff_report: AnmSemanticDiffReport


def _repo_root_path(anchor: Path | None = None) -> Path:
    return repo_root(anchor=anchor or Path(__file__)).resolve()


def _load_manifest(
    payload: AnmSourceSetManifest | dict[str, Any],
) -> AnmSourceSetManifest:
    return (
        payload
        if isinstance(payload, AnmSourceSetManifest)
        else AnmSourceSetManifest.model_validate(payload)
    )


def _load_policy(payload: AnmDocClassPolicy | dict[str, Any]) -> AnmDocClassPolicy:
    return (
        payload
        if isinstance(payload, AnmDocClassPolicy)
        else AnmDocClassPolicy.model_validate(payload)
    )


def _load_profiles(
    payloads: list[AnmDocAuthorityProfile | dict[str, Any]],
) -> list[AnmDocAuthorityProfile]:
    profiles = [
        payload
        if isinstance(payload, AnmDocAuthorityProfile)
        else AnmDocAuthorityProfile.model_validate(payload)
        for payload in payloads
    ]
    doc_refs = [item.doc_ref for item in profiles]
    if doc_refs != sorted(doc_refs):
        raise AnmCompileError("authority profiles must be sorted by doc_ref for V66-B")
    if len(doc_refs) != len(set(doc_refs)):
        raise AnmCompileError("authority profiles must not contain duplicate doc_ref values")
    return profiles


def _manifest_ref(manifest: AnmSourceSetManifest) -> str:
    return f"anm_source_set_manifest:{manifest.manifest_id}"


def _policy_ref(policy: AnmDocClassPolicy) -> str:
    return f"anm_doc_class_policy:{policy.policy_id}"


def _profile_ref(profile: AnmDocAuthorityProfile) -> str:
    return f"anm_doc_authority_profile:{profile.doc_id}"


def _basis_hashes(
    *,
    manifest: AnmSourceSetManifest,
    class_policy: AnmDocClassPolicy,
    authority_profiles: list[AnmDocAuthorityProfile],
) -> tuple[str, str, str]:
    manifest_hash = stable_payload_hash(canonicalize_anm_source_set_manifest_payload(manifest))
    policy_hash = stable_payload_hash(canonicalize_anm_doc_class_policy_payload(class_policy))
    profiles_hash = stable_payload_hash(
        [canonicalize_anm_doc_authority_profile_payload(item) for item in authority_profiles]
    )
    return manifest_hash, policy_hash, profiles_hash


def _profile_index(
    profiles: list[AnmDocAuthorityProfile],
) -> tuple[dict[str, AnmDocAuthorityProfile], dict[str, str]]:
    by_doc_ref = {item.doc_ref: item for item in profiles}
    by_profile_ref = {_profile_ref(item): item.doc_ref for item in profiles}
    return by_doc_ref, by_profile_ref


def _manifest_index(manifest: AnmSourceSetManifest) -> dict[str, Any]:
    index = {entry.doc_ref: entry for entry in manifest.source_entries}
    if len(index) != len(manifest.source_entries):
        raise AnmCompileError("manifest source entries must not contain duplicate doc_ref values")
    return index


def _resolve_transition_law(
    *,
    repo_root_path: Path,
    transition_law_ref: str,
    host_doc_ref: str,
    companion_doc_ref: str | None,
    profile_by_doc_ref: dict[str, AnmDocAuthorityProfile],
) -> None:
    doc_ref, _, _anchor = transition_law_ref.partition("#")
    if not doc_ref.startswith("docs/"):
        raise AnmCompileError("transition law refs must resolve under docs/")
    host_profile = profile_by_doc_ref.get(doc_ref)
    if host_profile is None or host_profile.authority_layer != "lock":
        raise AnmCompileError("transition law refs must resolve to lock-authority docs")
    resolved = (repo_root_path / doc_ref).resolve()
    if not resolved.exists():
        raise AnmCompileError(f"transition law ref is unresolved: {transition_law_ref}")
    text = resolved.read_text(encoding="utf-8")
    if host_doc_ref not in text:
        raise AnmCompileError("transition law ref must match host doc ref")
    if companion_doc_ref is not None and companion_doc_ref not in text:
        raise AnmCompileError("transition law ref must match companion doc ref")
    if "supersession" not in text.lower():
        raise AnmCompileError("transition law ref must name supersession scope explicitly")


def _ensure_governed_non_projection_basis(
    *,
    manifest_index: dict[str, Any],
    profile_by_doc_ref: dict[str, AnmDocAuthorityProfile],
) -> None:
    for doc_ref, entry in manifest_index.items():
        if entry.profile_ref_or_none is None:
            raise AnmCompileError(
                "V66-B requires classified governed sources with profile refs; "
                f"missing for {doc_ref}"
            )
        if doc_ref not in profile_by_doc_ref:
            raise AnmCompileError(f"manifest/profile mismatch for governed source {doc_ref}")


def _projection_ref(*, projection_manifest_id: str, projection_doc_ref: str) -> str:
    return f"anm_reader_projection_manifest:{projection_manifest_id}#{projection_doc_ref}"


def _load_projection_hash_if_missing(
    *, repo_root_path: Path, projection_doc_ref: str
) -> str | None:
    projection_path = repo_root_path / projection_doc_ref
    if not projection_path.exists() or not projection_path.is_file():
        return None
    return sha256(projection_path.read_bytes()).hexdigest()


def _require_projection_banner(*, repo_root_path: Path, projection_doc_ref: str) -> None:
    projection_path = repo_root_path / projection_doc_ref
    if not projection_path.exists() or not projection_path.is_file():
        return
    text = projection_path.read_text(encoding="utf-8")
    if "non-authoritative" not in text.lower():
        raise AnmCompileError(
            f"generated projection {projection_doc_ref} is missing a non-authoritative banner"
        )


def build_v66b_reader_projection_manifest(
    *,
    repo_root_path: Path | None = None,
    manifest: AnmSourceSetManifest | dict[str, Any],
    authority_profiles: list[AnmDocAuthorityProfile | dict[str, Any]],
    class_policy: AnmDocClassPolicy | dict[str, Any],
    projection_rows: list[dict[str, Any]],
    projection_manifest_id: str = "projection:v66b-starter",
) -> AnmReaderProjectionManifest:
    root = (repo_root_path or _repo_root_path()).resolve()
    manifest_model = _load_manifest(manifest)
    profiles_model = _load_profiles(authority_profiles)
    class_policy_model = _load_policy(class_policy)
    manifest_hash, policy_hash, profiles_hash = _basis_hashes(
        manifest=manifest_model,
        class_policy=class_policy_model,
        authority_profiles=profiles_model,
    )
    manifest_index = _manifest_index(manifest_model)
    profile_by_doc_ref, _profile_ref_index = _profile_index(profiles_model)
    _ensure_governed_non_projection_basis(
        manifest_index=manifest_index, profile_by_doc_ref=profile_by_doc_ref
    )

    rows: list[AnmReaderProjectionRow] = []
    for raw_row in projection_rows:
        row_payload = dict(raw_row)
        source_doc_ref = row_payload["source_doc_ref"]
        if source_doc_ref not in manifest_index:
            raise AnmCompileError(
                f"projection source {source_doc_ref} is outside the shipped V66-A source set"
            )
        if row_payload["projection_doc_ref"] in manifest_index:
            raise AnmCompileError(
                "generated projections may not be governed ANM source by themselves"
            )
        source_entry = manifest_index[source_doc_ref]
        expected_profile_ref = source_entry.profile_ref_or_none
        if row_payload["source_profile_ref"] != expected_profile_ref:
            raise AnmCompileError(f"projection source_profile_ref mismatch for {source_doc_ref}")
        if row_payload.get("projection_authority_posture") == "invalid_claims_authority":
            raise AnmCompileError(
                f"generated projection {row_payload['projection_doc_ref']} claims authority"
            )
        row_payload["source_content_hash"] = source_entry.content_hash
        row_payload.setdefault("projection_content_hash_or_none", None)
        if row_payload["projection_content_hash_or_none"] is None:
            row_payload["projection_content_hash_or_none"] = _load_projection_hash_if_missing(
                repo_root_path=root,
                projection_doc_ref=row_payload["projection_doc_ref"],
            )
        _require_projection_banner(
            repo_root_path=root,
            projection_doc_ref=row_payload["projection_doc_ref"],
        )
        rows.append(AnmReaderProjectionRow.model_validate(row_payload))

    rows.sort(key=lambda item: item.projection_doc_ref)
    return AnmReaderProjectionManifest(
        projection_manifest_id=projection_manifest_id,
        consumed_source_set_manifest_ref=_manifest_ref(manifest_model),
        consumed_source_set_manifest_hash=manifest_hash,
        consumed_doc_class_policy_ref=_policy_ref(class_policy_model),
        consumed_doc_class_policy_hash=policy_hash,
        consumed_authority_profile_set_ref_or_hash=f"sha256:{profiles_hash}",
        projection_rows=rows,
    )


def build_v66b_migration_binding_profile(
    *,
    repo_root_path: Path | None = None,
    manifest: AnmSourceSetManifest | dict[str, Any],
    authority_profiles: list[AnmDocAuthorityProfile | dict[str, Any]],
    class_policy: AnmDocClassPolicy | dict[str, Any],
    binding_rows: list[dict[str, Any]],
    projection_manifest_id: str = "projection:v66b-starter",
    diff_report_id: str = "diff:v66b-starter",
    migration_binding_profile_id: str = "migration:v66b-starter",
    projection_refs_by_source_doc_ref: dict[str, list[str]] | None = None,
) -> AnmMigrationBindingProfile:
    root = (repo_root_path or _repo_root_path()).resolve()
    manifest_model = _load_manifest(manifest)
    profiles_model = _load_profiles(authority_profiles)
    class_policy_model = _load_policy(class_policy)
    manifest_hash, policy_hash, profiles_hash = _basis_hashes(
        manifest=manifest_model,
        class_policy=class_policy_model,
        authority_profiles=profiles_model,
    )
    manifest_index = _manifest_index(manifest_model)
    profile_by_doc_ref, _profile_ref_index = _profile_index(profiles_model)
    _ensure_governed_non_projection_basis(
        manifest_index=manifest_index, profile_by_doc_ref=profile_by_doc_ref
    )
    planned_diff_ref = f"anm_semantic_diff_report:{diff_report_id}"

    rows: list[AnmMigrationBindingRow] = []
    for raw_row in binding_rows:
        row_payload = dict(raw_row)
        host_doc_ref = row_payload["host_doc_ref"]
        if host_doc_ref not in manifest_index:
            raise AnmCompileError(
                f"binding host {host_doc_ref} is outside the shipped V66-A source set"
            )
        if row_payload["host_profile_ref"] != manifest_index[host_doc_ref].profile_ref_or_none:
            raise AnmCompileError(f"binding host_profile_ref mismatch for {host_doc_ref}")
        companion_doc_ref = row_payload.get("companion_doc_ref_or_none")
        if companion_doc_ref is not None:
            if companion_doc_ref not in manifest_index:
                raise AnmCompileError(
                    f"binding companion {companion_doc_ref} is outside the shipped V66-A source set"
                )
            expected_companion_profile = manifest_index[companion_doc_ref].profile_ref_or_none
            if row_payload.get("companion_profile_ref_or_none") != expected_companion_profile:
                raise AnmCompileError(
                    f"binding companion_profile_ref mismatch for {companion_doc_ref}"
                )
        if row_payload.get("supersession_claim_status") == "claimed_with_explicit_transition_law":
            _resolve_transition_law(
                repo_root_path=root,
                transition_law_ref=row_payload["explicit_transition_law_ref_or_none"],
                host_doc_ref=host_doc_ref,
                companion_doc_ref=companion_doc_ref,
                profile_by_doc_ref=profile_by_doc_ref,
            )
        elif row_payload.get("explicit_transition_law_ref_or_none") is not None:
            raise AnmCompileError(
                "explicit_transition_law_ref_or_none requires claimed_with_explicit_transition_law"
            )
        row_payload.setdefault("generated_reader_projection_refs_or_none", [])
        if not row_payload["generated_reader_projection_refs_or_none"]:
            row_payload["generated_reader_projection_refs_or_none"] = list(
                (projection_refs_by_source_doc_ref or {}).get(host_doc_ref, [])
            )
        row_payload.setdefault("semantic_diff_ref_or_none", planned_diff_ref)
        rows.append(AnmMigrationBindingRow.model_validate(row_payload))

    rows.sort(key=lambda item: item.binding_id)
    return AnmMigrationBindingProfile(
        migration_binding_profile_id=migration_binding_profile_id,
        consumed_source_set_manifest_ref=_manifest_ref(manifest_model),
        consumed_source_set_manifest_hash=manifest_hash,
        consumed_doc_class_policy_ref=_policy_ref(class_policy_model),
        consumed_doc_class_policy_hash=policy_hash,
        consumed_authority_profile_set_ref_or_hash=f"sha256:{profiles_hash}",
        binding_rows=rows,
    )


def _current_surface_rows(
    *,
    manifest: AnmSourceSetManifest,
    authority_profiles: list[AnmDocAuthorityProfile],
    class_policy: AnmDocClassPolicy,
    migration_binding_profile: AnmMigrationBindingProfile,
    reader_projection_manifest: AnmReaderProjectionManifest,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for entry in manifest.source_entries:
        if entry.profile_ref_or_none is None:
            continue
        rows.append(
            {
                "source_doc_ref": entry.doc_ref,
                "current_profile_ref": entry.profile_ref_or_none,
                "surface_kind": "source_set_entry",
                "path_or_axis": f"source_entries.{entry.doc_ref}",
                "value": entry.model_dump(mode="json", exclude_none=True),
            }
        )
    for profile in authority_profiles:
        rows.append(
            {
                "source_doc_ref": profile.doc_ref,
                "current_profile_ref": _profile_ref(profile),
                "surface_kind": "doc_authority_profile",
                "path_or_axis": f"authority_profiles.{profile.doc_ref}",
                "value": canonicalize_anm_doc_authority_profile_payload(profile),
            }
        )
    for row in migration_binding_profile.binding_rows:
        rows.append(
            {
                "source_doc_ref": row.host_doc_ref,
                "current_profile_ref": row.host_profile_ref,
                "surface_kind": "migration_binding",
                "path_or_axis": f"binding_rows.{row.binding_id}",
                "value": row.model_dump(mode="json", exclude_none=True),
            }
        )
    for row in reader_projection_manifest.projection_rows:
        rows.append(
            {
                "source_doc_ref": row.source_doc_ref,
                "current_profile_ref": row.source_profile_ref,
                "surface_kind": "reader_projection_manifest",
                "path_or_axis": f"projection_rows.{row.projection_doc_ref}",
                "value": row.model_dump(mode="json", exclude_none=True),
            }
        )
    for row in class_policy.policy_rows:
        rows.append(
            {
                "source_doc_ref": f"class_policy:{row.doc_class}",
                "current_profile_ref": f"anm_doc_class_policy:{row.doc_class}",
                "surface_kind": "doc_class_policy",
                "path_or_axis": f"policy_rows.{row.doc_class}",
                "value": row.model_dump(mode="json", exclude_none=True),
            }
        )
    return rows


def build_v66b_semantic_diff_report(
    *,
    manifest: AnmSourceSetManifest | dict[str, Any],
    authority_profiles: list[AnmDocAuthorityProfile | dict[str, Any]],
    class_policy: AnmDocClassPolicy | dict[str, Any],
    migration_binding_profile: AnmMigrationBindingProfile | dict[str, Any],
    reader_projection_manifest: AnmReaderProjectionManifest | dict[str, Any],
    baseline_kind: str = "none_initial_report",
    baseline_report: AnmSemanticDiffReport | dict[str, Any] | None = None,
    diff_report_id: str = "diff:v66b-starter",
) -> AnmSemanticDiffReport:
    manifest_model = _load_manifest(manifest)
    profiles_model = _load_profiles(authority_profiles)
    class_policy_model = _load_policy(class_policy)
    migration_model = (
        migration_binding_profile
        if isinstance(migration_binding_profile, AnmMigrationBindingProfile)
        else AnmMigrationBindingProfile.model_validate(migration_binding_profile)
    )
    projection_model = (
        reader_projection_manifest
        if isinstance(reader_projection_manifest, AnmReaderProjectionManifest)
        else AnmReaderProjectionManifest.model_validate(reader_projection_manifest)
    )
    manifest_hash, policy_hash, profiles_hash = _basis_hashes(
        manifest=manifest_model,
        class_policy=class_policy_model,
        authority_profiles=profiles_model,
    )
    current_rows = _current_surface_rows(
        manifest=manifest_model,
        authority_profiles=profiles_model,
        class_policy=class_policy_model,
        migration_binding_profile=migration_model,
        reader_projection_manifest=projection_model,
    )
    current_bundle = {
        "manifest": canonicalize_anm_source_set_manifest_payload(manifest_model),
        "authority_profiles": [
            canonicalize_anm_doc_authority_profile_payload(item) for item in profiles_model
        ],
        "class_policy": canonicalize_anm_doc_class_policy_payload(class_policy_model),
        "migration_binding_profile": canonicalize_anm_migration_binding_profile_payload(
            migration_model
        ),
        "reader_projection_manifest": canonicalize_anm_reader_projection_manifest_payload(
            projection_model
        ),
    }
    current_hash = stable_payload_hash(current_bundle)
    current_ref = f"anm_v66b_bundle:{current_hash}"

    if baseline_kind == "none_initial_report":
        baseline_model = None
        baseline_ref = None
        baseline_hash = None
        baseline_index: dict[tuple[str, str, str], dict[str, Any]] = {}
    else:
        if baseline_report is None:
            raise AnmCompileError("explicit V66-B semantic diff baselines require baseline_report")
        baseline_model = (
            baseline_report
            if isinstance(baseline_report, AnmSemanticDiffReport)
            else AnmSemanticDiffReport.model_validate(baseline_report)
        )
        baseline_ref = baseline_model.current_artifact_ref
        baseline_hash = baseline_model.current_artifact_hash
        baseline_index = {
            (row.source_doc_ref, row.surface_kind, row.path_or_axis): {
                "baseline_profile_ref_or_none": row.baseline_profile_ref_or_none,
                "current_profile_ref": row.current_profile_ref,
                "value": row.current_value_or_none,
            }
            for row in baseline_model.change_rows
        }

    current_index = {
        (row["source_doc_ref"], row["surface_kind"], row["path_or_axis"]): row
        for row in current_rows
    }
    all_keys = sorted(set(current_index) | set(baseline_index))
    diff_rows: list[AnmSemanticDiffChangeRow] = []
    for key in all_keys:
        current = current_index.get(key)
        baseline = baseline_index.get(key)
        source_doc_ref, surface_kind, path_or_axis = key
        if baseline_kind == "none_initial_report":
            change_kind = "initial"
        elif baseline is None:
            change_kind = "added"
        elif current is None:
            change_kind = "removed"
        elif baseline["value"] != current["value"]:
            change_kind = "changed"
        else:
            change_kind = "unchanged"
        authority_effect_kind = "no_authority_minted"
        summary = None
        if surface_kind == "reader_projection_manifest" and current is not None:
            current_value = current["value"]
            if current_value["projection_authority_posture"] == "invalid_claims_authority":
                authority_effect_kind = "invalid_authority_claim_rejected"
                summary = "generated projection claimed authority and was rejected"
        if surface_kind == "migration_binding" and current is not None:
            current_value = current["value"]
            if (
                current_value["supersession_claim_status"]
                == "claimed_without_transition_law_rejected"
            ):
                authority_effect_kind = "invalid_authority_claim_rejected"
                summary = "supersession claim without explicit transition law was rejected"
        diff_rows.append(
            AnmSemanticDiffChangeRow(
                source_doc_ref=source_doc_ref,
                baseline_profile_ref_or_none=(
                    baseline["baseline_profile_ref_or_none"] if baseline is not None else None
                ),
                current_profile_ref=(
                    current["current_profile_ref"]
                    if current is not None
                    else baseline["current_profile_ref"]
                ),
                change_kind=change_kind,
                surface_kind=surface_kind,
                path_or_axis=path_or_axis,
                baseline_value_or_none=(baseline["value"] if baseline is not None else None),
                current_value_or_none=(current["value"] if current is not None else None),
                authority_effect_kind=authority_effect_kind,
                authority_effect_summary_or_none=summary,
            )
        )

    diff_rows.sort(
        key=lambda item: (
            item.source_doc_ref,
            item.surface_kind,
            item.path_or_axis,
            item.change_kind,
        )
    )
    return AnmSemanticDiffReport(
        diff_report_id=diff_report_id,
        consumed_source_set_manifest_ref=_manifest_ref(manifest_model),
        consumed_source_set_manifest_hash=manifest_hash,
        consumed_doc_class_policy_ref=_policy_ref(class_policy_model),
        consumed_doc_class_policy_hash=policy_hash,
        consumed_authority_profile_set_ref_or_hash=f"sha256:{profiles_hash}",
        baseline_kind=baseline_kind,
        baseline_artifact_ref_or_none=baseline_ref,
        baseline_artifact_hash_or_none=baseline_hash,
        current_artifact_ref=current_ref,
        current_artifact_hash=current_hash,
        change_rows=diff_rows,
    )


def check_v66b_anm_migration_projection(
    *,
    repo_root_path: Path | None = None,
    manifest: AnmSourceSetManifest | dict[str, Any],
    authority_profiles: list[AnmDocAuthorityProfile | dict[str, Any]],
    class_policy: AnmDocClassPolicy | dict[str, Any],
    binding_rows: list[dict[str, Any]],
    projection_rows: list[dict[str, Any]],
    baseline_kind: str = "none_initial_report",
    baseline_report: AnmSemanticDiffReport | dict[str, Any] | None = None,
    migration_binding_profile_id: str = "migration:v66b-starter",
    projection_manifest_id: str = "projection:v66b-starter",
    diff_report_id: str = "diff:v66b-starter",
) -> V66BMigrationResult:
    reader_projection_manifest = build_v66b_reader_projection_manifest(
        repo_root_path=repo_root_path,
        manifest=manifest,
        authority_profiles=authority_profiles,
        class_policy=class_policy,
        projection_rows=projection_rows,
        projection_manifest_id=projection_manifest_id,
    )
    projection_refs_by_source_doc_ref: dict[str, list[str]] = {}
    for row in reader_projection_manifest.projection_rows:
        projection_refs_by_source_doc_ref.setdefault(row.source_doc_ref, []).append(
            _projection_ref(
                projection_manifest_id=projection_manifest_id,
                projection_doc_ref=row.projection_doc_ref,
            )
        )
    migration_binding_profile = build_v66b_migration_binding_profile(
        repo_root_path=repo_root_path,
        manifest=manifest,
        authority_profiles=authority_profiles,
        class_policy=class_policy,
        binding_rows=binding_rows,
        projection_manifest_id=projection_manifest_id,
        diff_report_id=diff_report_id,
        migration_binding_profile_id=migration_binding_profile_id,
        projection_refs_by_source_doc_ref=projection_refs_by_source_doc_ref,
    )
    semantic_diff_report = build_v66b_semantic_diff_report(
        manifest=manifest,
        authority_profiles=authority_profiles,
        class_policy=class_policy,
        migration_binding_profile=migration_binding_profile,
        reader_projection_manifest=reader_projection_manifest,
        baseline_kind=baseline_kind,
        baseline_report=baseline_report,
        diff_report_id=diff_report_id,
    )
    return V66BMigrationResult(
        migration_binding_profile=migration_binding_profile,
        reader_projection_manifest=reader_projection_manifest,
        semantic_diff_report=semantic_diff_report,
    )


__all__ = [
    "V66BMigrationResult",
    "build_v66b_migration_binding_profile",
    "build_v66b_reader_projection_manifest",
    "build_v66b_semantic_diff_report",
    "check_v66b_anm_migration_projection",
]
