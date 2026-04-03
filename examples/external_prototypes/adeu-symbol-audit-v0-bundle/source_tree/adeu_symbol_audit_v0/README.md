# ADEU Symbol Audit v0 prototype

This prototype accompanies a worked v0 design for a new ADEU-native module that performs:

1. deterministic syntactic symbol census over a bounded Python slice
2. semantic per-symbol audit over that frozen symbol set
3. mechanical coverage / closure reporting

Pilot scope used here:

- `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`

Key grounding notes:

- The repo already has a broader `repo_symbol_catalog@1` extractor in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`, but that surface is not a
  one-audit-per-symbol closure mechanism.
- This prototype narrows the executable-symbol worklist to `class`, `function`, `method`,
  and `local_function`.
- On the pilot slice, the census yields 62 symbols:
  - 31 functions
  - 15 classes
  - 15 methods
  - 1 local_function

Files in this bundle:

- `adeu_symbol_audit/models.py`
- `adeu_symbol_audit/census.py`
- `adeu_symbol_audit/spu.py`
- `adeu_symbol_audit/coverage.py`
- `adeu_symbol_audit/cli.py`
- `sample_symbol_census.json`
- `sample_symbol_semantic_audit.json`
- `sample_symbol_audit_coverage_report.json`

This is intentionally read-only and proposal-oriented.
