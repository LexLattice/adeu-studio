Write set to own:
- packages/adeu_history_semantics/src/adeu_history_semantics/models.py
- packages/adeu_history_semantics/src/adeu_history_semantics/ledger.py
- packages/adeu_history_semantics/src/adeu_history_semantics/export_schema.py
- packages/adeu_history_semantics/src/adeu_history_semantics/__init__.py
- packages/adeu_history_semantics/schema/
- spec/
- packages/adeu_history_semantics/tests/
- packages/adeu_history_semantics/tests/fixtures/v54b/

First two implementation steps:
1. Read the locked continuation and V54-B implementation mapping, then inspect the released V54-A package models, preclassification flow, schema exports, and tests.
2. Add the four V54-B contracts plus ledger, slice, and theme-anchor construction/export paths, then cover the frozen-law regressions with targeted fixtures and tests.
