# V85 Declaration Probe 011 Assessment

Probe 011 tested the first thin harness layer: the resident model emitted only the semantic body, while the harness injected fixed filing fields and validated the assembled artifact.

Result: 8 of 8 assembled filings passed.

Compared with probe 010, this removed the fragile part of prompt-only filing:

- `artifact_kind` is no longer model-authored.
- `schema`, `loop_state`, `probe_case_id`, and `semantic_declaration_session_ref` are no longer model-authored.
- `resident_model_competency_claim_rows[].claim_status` was correct in all 8 bodies.
- All route fields passed exactly after assembly.

This is the first clean evidence for the practical architecture:

```text
harness:
  owns filing identity
  injects fixed fields
  validates closed enums and row shapes
  accepts or remands

resident model:
  fills semantic body
  preserves uncertainty
  avoids forbidden inference
  stops at schema boundary
```

The result is stronger than another prompt improvement. It proves the institutional split works: do not ask the resident model to be the institution; make it produce a bounded filing inside one.

Recommended next run: add intentional bad bodies and a remand artifact so the circuit becomes `body_submitted -> accepted_filing | remand_required` instead of only scoring accepted filings.
