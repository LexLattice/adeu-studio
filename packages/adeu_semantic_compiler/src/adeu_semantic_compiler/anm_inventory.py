from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from typing import Any

from adeu_commitments_ir import (
    AnmAuthorityLayer,
    AnmDocAuthorityProfile,
    AnmDocClass,
    AnmDocClassPolicy,
    AnmDocClassPolicyRow,
    AnmDocSourcePosture,
    AnmLifecycleStatus,
    AnmSourceSetEntry,
    AnmSourceSetManifest,
)
from adeu_ir.repo import repo_root
from adeu_semantic_source import (
    AnmCompileError,
    build_v66a_doc_authority_profile,
    inspect_v66a_source,
)

_IGNORED_PARTS = {".git", ".venv", "node_modules", "__pycache__"}


@dataclass(frozen=True)
class V66AInventoryResult:
    discovered_doc_inventory: list[str]
    governed_anm_source_set: list[str]
    manifest: AnmSourceSetManifest
    authority_profiles: list[AnmDocAuthorityProfile]
    class_policy: AnmDocClassPolicy


def _repo_root_path(anchor: Path | None = None) -> Path:
    return repo_root(anchor=anchor or Path(__file__)).resolve()


def _should_ignore(path: Path, *, repo_root_path: Path) -> bool:
    relative_parts = path.relative_to(repo_root_path).parts
    return any(part in _IGNORED_PARTS for part in relative_parts)


def _doc_ref(path: Path, *, repo_root_path: Path) -> str:
    return path.relative_to(repo_root_path).as_posix()


def _default_doc_id(doc_ref: str) -> str:
    return "v66a:" + doc_ref.replace("/", ":").replace(" ", "_")


def _infer_source_posture(
    *,
    doc_ref: str,
    inspected: dict[str, Any],
    registered_entry: dict[str, Any] | None,
) -> AnmDocSourcePosture:
    explicit_profile = inspected["explicit_profile"] or {}
    if "source_posture" in explicit_profile:
        return explicit_profile["source_posture"]
    if registered_entry is not None and "source_posture" in registered_entry:
        return registered_entry["source_posture"]
    if "/generated/" in doc_ref:
        return "generated_projection"
    if doc_ref.endswith(".anm.adeu.md") or "/overlays/" in doc_ref:
        return "companion_anm"
    if doc_ref.endswith(".adeu.md"):
        return "standalone_anm"
    if inspected["has_recognized_d1_blocks"] or inspected["explicit_profile"] is not None:
        return "companion_anm"
    return "legacy_markdown"


def _infer_doc_class(doc_ref: str) -> AnmDocClass:
    name = Path(doc_ref).name
    if "/support/" in doc_ref:
        return "support"
    if name.startswith("LOCKED_CONTINUATION_"):
        return "lock"
    if name.startswith("ARCHITECTURE_"):
        return "architecture"
    if name.startswith("DRAFT_") or name.startswith("ASSESSMENT_"):
        return "planning"
    return "planning"


def _infer_authority_layer(doc_class: AnmDocClass) -> AnmAuthorityLayer:
    return "none" if doc_class == "non_governance" else doc_class


def _infer_lifecycle_status(
    *,
    doc_ref: str,
    source_posture: AnmDocSourcePosture,
) -> AnmLifecycleStatus:
    name = Path(doc_ref).name
    lowered = doc_ref.lower()
    if source_posture == "generated_projection" or "/generated/" in doc_ref:
        return "generated"
    if "superseded" in lowered:
        return "superseded"
    if "historical" in lowered:
        return "historical"
    if name.startswith("DRAFT_"):
        return "draft"
    return "living"


def _default_current_markdown_authority_relation(
    source_posture: AnmDocSourcePosture,
) -> str:
    if source_posture == "standalone_anm":
        return "later_lock_required_for_supersession"
    return "current_markdown_controlling"


def _default_profile_contract(doc_class: AnmDocClass) -> dict[str, list[str] | str | bool]:
    base = {
        "allowed_consumers": ["semantic_compiler", "semantic_source"],
        "allowed_authority_blocks": ["adeu.doc_profile@1"],
        "allowed_outputs": ["anm_doc_authority_profile@1"],
        "forbidden_outputs": ["policy_obligation_ledger@1"],
        "requires_transition_law_for_supersession": True,
    }
    if doc_class == "lock":
        return {
            **base,
            "allowed_authority_blocks": ["D@1", "adeu.doc_profile@1"],
            "allowed_consumers": [
                "policy_evaluator",
                "semantic_compiler",
                "semantic_source",
            ],
            "allowed_outputs": [
                "anm_doc_authority_profile@1",
                "checker_fact_bundle@1",
                "d1_normalized_ir@1",
                "policy_evaluation_result_set@1",
                "policy_obligation_ledger@1",
                "predicate_contracts_bootstrap@1",
            ],
            "forbidden_outputs": [],
        }
    if doc_class == "architecture":
        return {
            **base,
            "allowed_authority_blocks": ["D@1", "adeu.doc_profile@1"],
            "allowed_outputs": ["anm_doc_authority_profile@1", "d1_normalized_ir@1"],
        }
    if doc_class == "planning":
        return {
            **base,
            "allowed_authority_blocks": ["D@1", "adeu.doc_profile@1"],
            "allowed_outputs": ["anm_doc_authority_profile@1", "d1_normalized_ir@1"],
        }
    if doc_class == "support":
        return base
    return {
        "allowed_consumers": [],
        "allowed_authority_blocks": [],
        "allowed_outputs": [],
        "forbidden_outputs": [
            "checker_fact_bundle@1",
            "d1_normalized_ir@1",
            "policy_evaluation_result_set@1",
            "policy_obligation_ledger@1",
            "predicate_contracts_bootstrap@1",
        ],
        "requires_transition_law_for_supersession": True,
    }


def build_v66a_doc_class_policy(*, policy_id: str = "policy:v66a-starter") -> AnmDocClassPolicy:
    return AnmDocClassPolicy(
        policy_id=policy_id,
        policy_rows=[
            AnmDocClassPolicyRow(
                doc_class="architecture",
                allowed_authority_layers=["architecture"],
                allowed_source_postures=["companion_anm", "legacy_markdown", "standalone_anm"],
                allowed_authority_blocks=["D@1", "adeu.doc_profile@1"],
                allowed_outputs=["anm_doc_authority_profile@1", "d1_normalized_ir@1"],
                forbidden_outputs=["policy_obligation_ledger@1"],
                hard_gates=[
                    "reject_overpromotion",
                    "reject_supersession_without_transition_law",
                ],
                warning_gates=["warn_profile_inferred_from_manifest"],
            ),
            AnmDocClassPolicyRow(
                doc_class="lock",
                allowed_authority_layers=["lock"],
                allowed_source_postures=["companion_anm", "legacy_markdown", "standalone_anm"],
                allowed_authority_blocks=["D@1", "adeu.doc_profile@1"],
                allowed_outputs=[
                    "anm_doc_authority_profile@1",
                    "checker_fact_bundle@1",
                    "d1_normalized_ir@1",
                    "policy_evaluation_result_set@1",
                    "policy_obligation_ledger@1",
                    "predicate_contracts_bootstrap@1",
                ],
                forbidden_outputs=[],
                hard_gates=[
                    "reject_overpromotion",
                    "reject_supersession_without_transition_law",
                ],
                warning_gates=["warn_profile_inferred_from_manifest"],
            ),
            AnmDocClassPolicyRow(
                doc_class="non_governance",
                allowed_authority_layers=["none"],
                allowed_source_postures=["generated_projection", "legacy_markdown"],
                allowed_authority_blocks=[],
                allowed_outputs=[],
                forbidden_outputs=[
                    "checker_fact_bundle@1",
                    "d1_normalized_ir@1",
                    "policy_evaluation_result_set@1",
                    "policy_obligation_ledger@1",
                    "predicate_contracts_bootstrap@1",
                ],
                hard_gates=["reject_overpromotion"],
                warning_gates=["warn_unknown_requires_registration"],
            ),
            AnmDocClassPolicyRow(
                doc_class="planning",
                allowed_authority_layers=["planning"],
                allowed_source_postures=["companion_anm", "legacy_markdown", "standalone_anm"],
                allowed_authority_blocks=["D@1", "adeu.doc_profile@1"],
                allowed_outputs=["anm_doc_authority_profile@1", "d1_normalized_ir@1"],
                forbidden_outputs=["policy_obligation_ledger@1"],
                hard_gates=[
                    "reject_overpromotion",
                    "reject_supersession_without_transition_law",
                ],
                warning_gates=["warn_profile_inferred_from_manifest"],
            ),
            AnmDocClassPolicyRow(
                doc_class="support",
                allowed_authority_layers=["support"],
                allowed_source_postures=["companion_anm", "legacy_markdown", "standalone_anm"],
                allowed_authority_blocks=["D@1", "adeu.doc_profile@1"],
                allowed_outputs=["anm_doc_authority_profile@1"],
                forbidden_outputs=["policy_obligation_ledger@1"],
                hard_gates=["reject_overpromotion", "reject_unregistered_companion"],
                warning_gates=[
                    "warn_profile_inferred_from_manifest",
                    "warn_unknown_requires_registration",
                ],
            ),
        ],
    )


def _load_registered_entries(
    registered_entries: list[dict[str, Any]] | None,
) -> dict[str, dict[str, Any]]:
    index: dict[str, dict[str, Any]] = {}
    for entry in registered_entries or []:
        doc_ref = entry["doc_ref"]
        if doc_ref in index:
            raise AnmCompileError(f"duplicate registered entry for {doc_ref}")
        index[doc_ref] = dict(entry)
    return index


def inventory_v66a_anm_source_set(
    *,
    repo_root_path: Path | None = None,
    docs_root: str = "docs",
    registered_entries: list[dict[str, Any]] | None = None,
    manifest_id: str = "manifest:v66a-starter",
    policy_id: str = "policy:v66a-starter",
) -> V66AInventoryResult:
    root = (repo_root_path or _repo_root_path()).resolve()
    docs_dir = (root / docs_root).resolve()
    if not docs_dir.exists():
        raise AnmCompileError(f"docs root {docs_root} is unresolved")

    registered_index = _load_registered_entries(registered_entries)
    discovered_paths = sorted(
        path
        for path in docs_dir.rglob("*")
        if path.is_file() and path.suffix == ".md" and not _should_ignore(path, repo_root_path=root)
    )
    discovered_doc_inventory = [_doc_ref(path, repo_root_path=root) for path in discovered_paths]

    manifest_entries: list[AnmSourceSetEntry] = []
    authority_profiles: list[AnmDocAuthorityProfile] = []
    class_policy = build_v66a_doc_class_policy(policy_id=policy_id)
    policy_rows = {row.doc_class: row for row in class_policy.policy_rows}
    governed_doc_refs: list[str] = []

    for path in discovered_paths:
        doc_ref = _doc_ref(path, repo_root_path=root)
        source_text = path.read_text(encoding="utf-8")
        inspected = inspect_v66a_source(source_text=source_text)
        registered_entry = registered_index.get(doc_ref)
        source_posture = _infer_source_posture(
            doc_ref=doc_ref,
            inspected=inspected,
            registered_entry=registered_entry,
        )
        included = (
            doc_ref.endswith(".adeu.md")
            or registered_entry is not None
            or inspected["explicit_profile"] is not None
            or inspected["has_recognized_d1_blocks"]
        )
        if not included:
            continue

        explicit_profile = inspected["explicit_profile"] or {}
        doc_class = explicit_profile.get("doc_class") or (
            registered_entry.get("doc_class") if registered_entry else None
        )
        if doc_class is None:
            doc_class = _infer_doc_class(doc_ref)
        authority_layer = explicit_profile.get("authority_layer") or (
            registered_entry.get("authority_layer") if registered_entry else None
        )
        if authority_layer is None:
            authority_layer = _infer_authority_layer(doc_class)
        lifecycle_status = explicit_profile.get("lifecycle_status") or (
            registered_entry.get("lifecycle_status") if registered_entry else None
        )
        if lifecycle_status is None:
            lifecycle_status = _infer_lifecycle_status(
                doc_ref=doc_ref,
                source_posture=source_posture,
            )
        classification_status = (
            registered_entry.get("classification_status") if registered_entry else None
        )
        if classification_status is None:
            classification_status = (
                "classified"
                if inspected["explicit_profile"] is not None or registered_entry is not None
                else "unknown_requires_registration"
            )
        doc_id = explicit_profile.get("doc_id") or (
            registered_entry.get("doc_id_or_none") if registered_entry else None
        )
        content_hash = sha256(path.read_bytes()).hexdigest()
        companion_registration_status = (
            registered_entry.get("companion_registration_status_or_none")
            if registered_entry
            else None
        )
        host_doc_ref = registered_entry.get("host_doc_ref_or_none") if registered_entry else None
        generated_from_ref = (
            registered_entry.get("generated_from_ref_or_none") if registered_entry else None
        )

        if source_posture == "companion_anm" and companion_registration_status is None:
            raise AnmCompileError(f"unregistered companion posture for {doc_ref}")
        if companion_registration_status == "registered_companion_overlay":
            if host_doc_ref is None:
                raise AnmCompileError(
                    f"registered companion overlay {doc_ref} is missing host_doc_ref"
                )
            if host_doc_ref not in discovered_doc_inventory:
                raise AnmCompileError(
                    "host or companion linkage for "
                    f"{doc_ref} references unresolved host {host_doc_ref}"
                )
        if (
            companion_registration_status == "registered_host_document"
            and source_posture == "companion_anm"
        ):
            raise AnmCompileError(
                f"host or companion linkage for {doc_ref} is contradictory"
            )

        profile_ref = None
        if classification_status == "classified":
            if doc_id is None:
                doc_id = _default_doc_id(doc_ref)
            profile_defaults = _default_profile_contract(doc_class)
            profile = build_v66a_doc_authority_profile(
                source_text=source_text,
                source_doc_ref=doc_ref,
                doc_id=doc_id,
                doc_class=doc_class,
                authority_layer=authority_layer,
                source_posture=source_posture,
                lifecycle_status=lifecycle_status,
                allowed_authority_blocks=(
                    explicit_profile.get("allowed_authority_blocks")
                    or profile_defaults["allowed_authority_blocks"]
                ),
                allowed_outputs=(
                    explicit_profile.get("allowed_outputs")
                    or explicit_profile.get("emits")
                    or profile_defaults["allowed_outputs"]
                ),
                forbidden_outputs=(
                    explicit_profile.get("forbidden_outputs")
                    or explicit_profile.get("does_not_emit")
                    or profile_defaults["forbidden_outputs"]
                ),
                current_markdown_authority_relation=(
                    explicit_profile.get("current_markdown_authority_relation")
                    or _default_current_markdown_authority_relation(source_posture)
                ),
                allowed_consumers=(
                    explicit_profile.get("allowed_consumers")
                    or profile_defaults["allowed_consumers"]
                ),
                requires_transition_law_for_supersession=bool(
                    explicit_profile.get(
                        "requires_transition_law_for_supersession",
                        profile_defaults["requires_transition_law_for_supersession"],
                    )
                ),
            )
            row = policy_rows[doc_class]
            if profile.authority_layer not in row.allowed_authority_layers:
                raise AnmCompileError(
                    "class policy for "
                    f"{doc_class} forbids authority layer {profile.authority_layer}"
                )
            if profile.source_posture not in row.allowed_source_postures:
                raise AnmCompileError(
                    f"class policy for {doc_class} forbids source posture {profile.source_posture}"
                )
            if not set(profile.allowed_authority_blocks).issubset(row.allowed_authority_blocks):
                raise AnmCompileError(
                    f"class policy for {doc_class} forbids allowed_authority_blocks on {doc_ref}"
                )
            if not set(profile.allowed_outputs).issubset(row.allowed_outputs):
                raise AnmCompileError(
                    f"class policy for {doc_class} forbids allowed_outputs on {doc_ref}"
                )
            profile_ref = f"anm_doc_authority_profile:{profile.doc_id}"
            authority_profiles.append(profile)

        manifest_entries.append(
            AnmSourceSetEntry(
                doc_ref=doc_ref,
                doc_id_or_none=doc_id,
                doc_class=doc_class,
                authority_layer=authority_layer,
                source_posture=source_posture,
                lifecycle_status=lifecycle_status,
                classification_status=classification_status,
                content_hash=content_hash,
                profile_ref_or_none=profile_ref,
                host_doc_ref_or_none=host_doc_ref,
                companion_registration_status_or_none=companion_registration_status,
                generated_from_ref_or_none=generated_from_ref,
            )
        )
        governed_doc_refs.append(doc_ref)

    manifest_entries.sort(key=lambda item: item.doc_ref)
    authority_profiles.sort(key=lambda item: item.doc_ref)
    return V66AInventoryResult(
        discovered_doc_inventory=discovered_doc_inventory,
        governed_anm_source_set=governed_doc_refs,
        manifest=AnmSourceSetManifest(
            manifest_id=manifest_id,
            source_entries=manifest_entries,
        ),
        authority_profiles=authority_profiles,
        class_policy=class_policy,
    )


def check_v66a_anm_source_set(
    *,
    repo_root_path: Path | None = None,
    docs_root: str = "docs",
    registered_entries: list[dict[str, Any]] | None = None,
    manifest_id: str = "manifest:v66a-starter",
    policy_id: str = "policy:v66a-starter",
) -> V66AInventoryResult:
    return inventory_v66a_anm_source_set(
        repo_root_path=repo_root_path,
        docs_root=docs_root,
        registered_entries=registered_entries,
        manifest_id=manifest_id,
        policy_id=policy_id,
    )


__all__ = [
    "V66AInventoryResult",
    "build_v66a_doc_class_policy",
    "inventory_v66a_anm_source_set",
    "check_v66a_anm_source_set",
]
