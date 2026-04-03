# Draft Stop-Gate Decision vNext+117

Status: proposed gate for `V49-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS117.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `adeu_semantic_forms` package scaffold exists and is the only live
  package owner for the first semantic substrate slice;
- the first released schema family is selected exactly to:
  `adeu_semantic_parse_profile@1`, `adeu_semantic_statement_core@1`,
  `adeu_semantic_normal_form@1`, `adeu_semantic_parse_result@1`, and
  `adeu_semantic_transform_contract@1`;
- the slice freezes one starter ADEU statement / calculus shape, one operator /
  relation posture, one semantic-kind / lane-tag posture, one canonical semantic
  identity law, and one explicit identity-field versus projection-field split over
  `repo_policy_work`;
- canonical semantic hash behavior is deterministic and clearly excludes
  projection-only or support-only fields from semantic identity;
- the contract-only parse-result outcome vocabulary is frozen exactly to:
  `resolved_singleton`, `typed_alternatives`, `clarification_required`, and
  `rejected_unsupported`;
- committed fixtures prove:
  - projection/support-only field changes do not change semantic hash;
  - identity-field changes do change semantic hash;
  - invalid outcome vocabulary fails closed;
- normalized support fixtures derived from the intake bundle replay deterministically;
- targeted Python tests cover model validation, canonical hash stability, outcome
  vocabulary validation, and fixture replay;
- if committed schema files are added, authoritative and mirrored schema export parity
  remains exact;
- the implementation remains contract-first with no parser behavior, lowering behavior,
  or product-surface widening.

## Do Not Accept If

- the slice quietly imports the external intake tree as live package code;
- the starter semantic unit remains implicit or underdefined;
- the first schema family remains unselected or only planning-level;
- semantic identity and semantic equivalence are described in prose but not frozen in
  the contracts;
- unsupported posture is deferred while parse-result contracts are already shipped;
- parser heuristics, natural-language recovery, or `V48` lowering appear in the same
  slice;
- product surfaces such as CLI, API, or web routes appear in the same slice;
- later consumer assumptions are baked in without an explicit substrate contract.

## Local Gate

- run `make arc-start-check ARC=117`
