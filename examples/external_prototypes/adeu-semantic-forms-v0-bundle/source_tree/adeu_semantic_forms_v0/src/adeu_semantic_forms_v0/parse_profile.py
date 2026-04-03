from __future__ import annotations

from .models import (
    AnchorAlias,
    PolicyAnchor,
    ScopeAnchor,
    SemanticLexiconEntry,
    SemanticParseProfile,
    WorkerAnchor,
)


def build_reference_repo_policy_work_profile() -> SemanticParseProfile:
    return SemanticParseProfile.model_validate(
        {
            "profile_id": "repo_policy_work_v0.reference_v48a",
            "snapshot_id": "repo_snapshot_be15b89dfafbee994e98b291",
            "snapshot_sha256": "be15b89dfafbee994e98b2917db37160810bc685d7731740b2b56defbfadd1ab",
            "scope_anchors": [
                {
                    "anchor_id": "repo_symbol_catalog",
                    "display_name": "released V45 repo symbol catalog",
                    "resolved_scope_ref": "apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json",
                    "resolved_binding_entry_ref": "apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json#binding_entry_d9b4bd5b1693dea4ec3c09cd",
                    "aliases": [
                        {"alias": "repo symbol catalog"},
                        {"alias": "released symbol catalog"},
                        {"alias": "symbol catalog"},
                        {"alias": "catalog"},
                    ],
                },
                {
                    "anchor_id": "repo_entity_catalog",
                    "display_name": "released V45 repo entity catalog",
                    "resolved_scope_ref": "apps/api/fixtures/repo_description/vnext_plus101/repo_entity_catalog_v101_reference.json",
                    "resolved_binding_entry_ref": "apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json#binding_entry_a24a84cd152f890bb21be04c",
                    "aliases": [
                        {"alias": "repo entity catalog"},
                        {"alias": "released entity catalog"},
                        {"alias": "entity catalog"},
                        {"alias": "catalog"},
                    ],
                },
            ],
            "policy_anchors": [
                {
                    "anchor_id": "release_surface:owner",
                    "display_name": "released V47 owner release-surface policy anchor",
                    "resolved_clause_ref": "release_surface:owner",
                    "resolved_policy_consumer_ref": "packages/adeu_commitments_ir/tests/fixtures/v47e/reference_anm_policy_consumer_binding_profile.json#consumer_rows[0]",
                    "aliases": [
                        {"alias": "release_surface:owner", "alias_kind": "exact_phrase"},
                        {"alias": "owner policy"},
                        {"alias": "owner rule"},
                        {"alias": "release surface owner"},
                    ],
                }
            ],
            "worker_anchors": [
                {
                    "anchor_id": "worker:repo_internal_single_codex_worker:default",
                    "resolved_worker_subject_ref": "worker:repo_internal_single_codex_worker:default",
                    "aliases": [
                        {"alias": "default codex worker"},
                        {"alias": "single codex worker"},
                        {"alias": "default worker"},
                    ],
                }
            ],
            "mutation_lexicon": [
                {
                    "canonical_value": "read_only",
                    "aliases": [
                        {"alias": "read-only"},
                        {"alias": "read only"},
                        {"alias": "readonly"},
                        {"alias": "no writeback"},
                        {"alias": "do not modify repo"},
                        {"alias": "inspection only"},
                    ],
                }
            ],
            "artifact_kind_lexicon": [
                {
                    "canonical_value": "taskpack_binding_spec_seed",
                    "aliases": [
                        {"alias": "taskpack binding seed"},
                        {"alias": "binding seed"},
                        {"alias": "taskpack boundary seed"},
                        {"alias": "taskpack binding request"},
                    ],
                }
            ],
            "effect_lexicon": [
                {
                    "canonical_value": "network_calls",
                    "aliases": [
                        {"alias": "network calls"},
                        {"alias": "network access"},
                        {"alias": "internet"},
                    ],
                },
                {
                    "canonical_value": "multi_worker_topology",
                    "aliases": [
                        {"alias": "multi-worker topology"},
                        {"alias": "multiple workers"},
                        {"alias": "multi worker"},
                    ],
                },
            ],
            "unsupported_patterns": [
                "whatever policy",
                "choose any policy",
                "modify the repo",
                "edit the repo",
                "if",
                "then",
                "or",
            ],
            "semantic_hash": "derived-by-model-validator",
        }
    )
