from adeu_kernel import KernelMode, check


def test_parse_ok() -> None:
    report = check(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_test",
            "context": {
                "doc_id": "doc1",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-04T00:00:00Z",
            },
        },
        mode=KernelMode.STRICT,
    )
    assert report.status == "PASS"
    assert report.metrics.num_statements == 0


def test_schema_version_refuse() -> None:
    report = check(
        {"schema_version": "adeu.ir.v999", "ir_id": "x", "context": {}},
        mode=KernelMode.STRICT,
    )
    assert report.status == "REFUSE"
    assert [r.code for r in report.reason_codes] == ["UNSUPPORTED_SCHEMA_VERSION"]


def test_schema_invalid_refuse() -> None:
    report = check({"schema_version": "adeu.ir.v0"}, mode=KernelMode.STRICT)
    assert report.status == "REFUSE"
    assert report.reason_codes[0].code == "SCHEMA_INVALID"


def test_time_unspecified_strict_refuse() -> None:
    report = check(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_time",
            "context": {
                "doc_id": "doc1",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-04T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "dn1",
                        "kind": "obligation",
                        "subject": {"ref_type": "text", "text": "Party A"},
                        "action": {"verb": "deliver"},
                        "scope": {
                            "jurisdiction": "US-CA",
                            "time_about": {"kind": "unspecified"},
                        },
                        "provenance": {"doc_ref": "doc1#clause1"},
                    }
                ]
            },
        },
        mode=KernelMode.STRICT,
    )
    assert report.status == "REFUSE"
    assert any(r.code == "SCOPE_TIME_MISSING" for r in report.reason_codes)


def test_time_unspecified_lax_warn() -> None:
    report = check(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_time_lax",
            "context": {
                "doc_id": "doc1",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-04T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "dn1",
                        "kind": "obligation",
                        "subject": {"ref_type": "text", "text": "Party A"},
                        "action": {"verb": "deliver"},
                        "scope": {
                            "jurisdiction": "US-CA",
                            "time_about": {"kind": "unspecified"},
                        },
                        "provenance": {"doc_ref": "doc1#clause1"},
                    }
                ]
            },
        },
        mode=KernelMode.LAX,
    )
    assert report.status == "WARN"
    reasons = [r for r in report.reason_codes if r.code == "SCOPE_TIME_MISSING"]
    assert reasons and reasons[0].severity == "WARN"


def test_bridge_certified_requires_validator() -> None:
    report = check(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_bridge",
            "context": {
                "doc_id": "doc1",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-04T00:00:00Z",
            },
            "bridges": [
                {
                    "id": "b1",
                    "status": "certified",
                    "from_channel": "U",
                    "to_channel": "D_norm",
                    "bridge_type": "u_to_dnorm",
                    "justification_text": "Bridge justification.",
                    "provenance": {"doc_ref": "doc1#clause1"},
                    "authority_ref": "doc1#authority",
                }
            ],
        },
        mode=KernelMode.STRICT,
    )
    assert report.status == "REFUSE"
    assert any(r.code == "BRIDGE_CERTIFIED_VALIDATOR_MISSING" for r in report.reason_codes)


def test_bridge_u_to_dnorm_requires_authority() -> None:
    report = check(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_bridge2",
            "context": {
                "doc_id": "doc1",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-04T00:00:00Z",
            },
            "bridges": [
                {
                    "id": "b1",
                    "status": "provisional",
                    "from_channel": "U",
                    "to_channel": "D_norm",
                    "bridge_type": "u_to_dnorm",
                    "justification_text": "Bridge justification.",
                    "provenance": {"doc_ref": "doc1#clause1"},
                }
            ],
        },
        mode=KernelMode.STRICT,
    )
    assert report.status == "REFUSE"
    assert any(r.code == "BRIDGE_U_TO_DNORM_AUTHORITY_MISSING" for r in report.reason_codes)


def test_refers_to_doc_uses_docref_refs_inside_ir() -> None:
    report = check(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_docref_predicate",
            "context": {
                "doc_id": "doc1",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-04T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "dn_ob",
                        "kind": "obligation",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {
                            "verb": "deliver",
                            "object": {"ref_type": "doc", "doc_ref": "doc:linked:sec1"},
                        },
                        "scope": {
                            "jurisdiction": "US-CA",
                            "time_about": {
                                "kind": "between",
                                "start": "2026-01-01T00:00:00Z",
                                "end": "2026-12-31T00:00:00Z",
                            },
                        },
                        "provenance": {"doc_ref": "doc1#clause1"},
                    },
                    {
                        "id": "dn_pr",
                        "kind": "prohibition",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {
                            "verb": "deliver",
                            "object": {"ref_type": "doc", "doc_ref": "doc:linked:sec1"},
                        },
                        "scope": {
                            "jurisdiction": "US-CA",
                            "time_about": {
                                "kind": "between",
                                "start": "2026-01-01T00:00:00Z",
                                "end": "2026-12-31T00:00:00Z",
                            },
                        },
                        "provenance": {"doc_ref": "doc1#clause2"},
                    },
                ],
                "exceptions": [
                    {
                        "id": "ex_docref",
                        "applies_to": ["dn_ob"],
                        "priority": 1,
                        "condition": {
                            "kind": "predicate",
                            "text": "if linked doc exists",
                            "predicate": '(refers_to_doc "doc:linked:sec1")',
                        },
                        "effect": "defeats",
                        "provenance": {"doc_ref": "doc1#clause3"},
                    }
                ],
            },
        },
        mode=KernelMode.LAX,
    )
    assert not any(r.code == "CONFLICT_OBLIGATION_VS_PROHIBITION" for r in report.reason_codes)
