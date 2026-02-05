from __future__ import annotations

from adeu_api.id_canonicalization import canonicalize_ir_ids
from adeu_ir import AdeuIR


def _sample_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "random_ir",
            "context": {
                "doc_id": "doc:test",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-05T00:00:00Z",
            },
            "O": {
                "entities": [
                    {
                        "id": "party_supplier",
                        "name": "Supplier",
                        "kind": "party",
                        "provenance": {"doc_ref": "doc:test#sec1", "span": {"start": 0, "end": 8}},
                    }
                ],
                "definitions": [
                    {
                        "id": "def_old",
                        "term": "Confidential Information",
                        "meaning": "Non-public information.",
                        "provenance": {
                            "doc_ref": "doc:test#sec2",
                            "span": {"start": 10, "end": 35},
                        },
                    }
                ],
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "stmt_old",
                        "kind": "obligation",
                        "subject": {"ref_type": "entity", "entity_id": "party_supplier"},
                        "action": {
                            "verb": "protect",
                            "object": {"ref_type": "def", "def_id": "def_old"},
                        },
                        "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                        "provenance": {
                            "doc_ref": "doc:test#sec3",
                            "span": {"start": 40, "end": 70},
                        },
                        "condition": {
                            "kind": "predicate",
                            "text": "if defined",
                            "predicate": "(defined def_old)",
                        },
                    }
                ],
                "exceptions": [
                    {
                        "id": "ex_old",
                        "applies_to": ["stmt_old"],
                        "priority": 5,
                        "condition": {
                            "kind": "predicate",
                            "text": "unless public",
                            "predicate": "(and (defined def_old) (not (defined missing_def)))",
                        },
                        "effect": "defeats",
                        "provenance": {
                            "doc_ref": "doc:test#sec4",
                            "span": {"start": 75, "end": 100},
                        },
                    }
                ],
            },
            "bridges": [
                {
                    "id": "bridge_old",
                    "status": "provisional",
                    "from_channel": "U",
                    "to_channel": "D_norm",
                    "bridge_type": "u_to_dnorm",
                    "justification_text": "policy to norm",
                    "authority_ref": "AUTH-1",
                    "provenance": {"doc_ref": "doc:test#sec5", "span": {"start": 101, "end": 110}},
                }
            ],
            "ambiguity": [
                {
                    "id": "amb_old",
                    "span": {"start": 12, "end": 15},
                    "issue": "modality_ambiguity",
                    "options": [
                        {
                            "option_id": "old_opt",
                            "label": "Keep as obligation",
                            "effect": "No change",
                            "patch": [
                                {
                                    "op": "replace",
                                    "path": "/D_norm/statements/0/kind",
                                    "value": "obligation",
                                }
                            ],
                        }
                    ],
                }
            ],
        }
    )


def test_canonicalize_ir_ids_rewrites_refs_and_predicates() -> None:
    ir = _sample_ir()
    canonical = canonicalize_ir_ids(ir)

    assert canonical.ir_id.startswith("ir_")
    assert canonical.O.entities[0].id.startswith("ent_")
    assert canonical.O.definitions[0].id.startswith("def_")
    assert canonical.D_norm.statements[0].id.startswith("dn_")
    assert canonical.D_norm.exceptions[0].id.startswith("ex_")
    assert canonical.bridges[0].id.startswith("br_")
    assert canonical.ambiguity[0].id.startswith("amb_")
    assert canonical.ambiguity[0].options[0].option_id.startswith("opt_")

    stmt = canonical.D_norm.statements[0]
    assert stmt.subject.ref_type == "entity"
    assert stmt.subject.entity_id == canonical.O.entities[0].id
    assert stmt.action.object is not None
    assert stmt.action.object.ref_type == "def"
    assert stmt.action.object.def_id == canonical.O.definitions[0].id
    assert stmt.condition is not None
    assert canonical.O.definitions[0].id in (stmt.condition.predicate or "")
    assert "def_old" not in (stmt.condition.predicate or "")

    exc = canonical.D_norm.exceptions[0]
    assert exc.applies_to == [stmt.id]
    assert exc.condition.predicate is not None
    assert canonical.O.definitions[0].id in exc.condition.predicate
    assert "def_old" not in exc.condition.predicate


def test_canonicalize_ir_ids_is_idempotent() -> None:
    first = canonicalize_ir_ids(_sample_ir())
    second = canonicalize_ir_ids(first)
    assert first.model_dump(mode="json", exclude_none=True) == second.model_dump(
        mode="json", exclude_none=True
    )
