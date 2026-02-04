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
