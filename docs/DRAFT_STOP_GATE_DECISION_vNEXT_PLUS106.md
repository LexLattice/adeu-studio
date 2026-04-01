# Draft Stop-Gate Decision vNext+106

Status: proposed gate for `V47-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS106.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the bounded ANM / `D@1` source form compiles deterministically into the same accepted
  `d1_normalized_ir@1` on repeated runs;
- authoritative policy semantics are emitted only from explicit `D@1` blocks and no
  prose inference path exists outside them;
- canonical `predicate_contracts_bootstrap@1`, `checker_fact_bundle@1`,
  `policy_evaluation_result_set@1`, and `policy_obligation_ledger@1` surfaces validate
  and export cleanly with authoritative/mirrored parity;
- released fact-kind and provenance-mode enums match the frozen starter vocabularies
  exactly in this slice;
- the tiny accepted reference chain preserves explicit separation between:
  - source markdown;
  - normalized `D-IR`;
  - checker facts;
  - evaluation results;
  - ledger rows;
- `d1_normalized_ir@1` preserves first-class selector refs and clause-to-selector
  linkage rather than hiding selector handling in prose or implementation-only logic;
- `ONLY_IF`, `UNLESS`, selector zero-match, and result-to-ledger mapping behave as
  frozen in the starter contract;
- selector zero-match does not fabricate a first ledger row while `gated_off` remains a
  non-active instantiated row when a subject was resolved;
- clause-scope `unknown_resolution` without a formed `subject_ref` remains a result-only
  blocker rather than a fabricated ledger row;
- result rows support both subject-scoped evaluations and clause-scope blocker rows
  without forcing `subject_ref` universally;
- checker bundles remain fact-only and cannot carry policy verdicts;
- checker fact rows use fact-kind-shaped payloads rather than pretending every fact kind
  carries the same universal `path` / `values` surface;
- the first release stays non-executive and does not mint waiver, deferral, mutation,
  scheduling, or approval authority;
- Python tests cover:
  - parser/compiler validation;
  - committed fixture replay;
  - schema/model validation;
  - authoritative/mirrored export parity;
  - result-to-ledger mapping;
  - fail-closed rejection of prose inference and authority laundering.

## Do Not Accept If

- any part of the policy path depends on implicit prose interpretation outside `D@1`;
- the implementation collapses source, IR, facts, results, and ledger into one mixed
  artifact or evaluator blob;
- source-level `DEFERRED`, imported O-owned selector handles, or imported E-owned
  predicate registries are widened into the first release;
- released fact-kind or provenance-mode enums drift beyond the frozen starter
  vocabularies in this slice;
- result rows require `subject_ref` even for clause-scope blocker posture;
- checker fact rows pretend every fact kind carries one universal payload shape;
- selector handling is left implicit in `D-IR` instead of represented through explicit
  selector refs and clause linkage;
- selector zero-match and `gated_off` become indistinguishable in typed output;
- checker facts carry policy verdicts or ledger rows are treated as self-authorizing
  approvals;
- clause-scope `unknown_resolution` creates ledger rows without resolved subject
  identity;
- coexistence posture is overread as current-markdown override or repo-wide migration;
- the release widens into recursive execution, mutation, scheduling, or approval
  authority.

## Local Gate

- run `make arc-start-check ARC=106` while the bundle remains docs-only;
- run targeted Python checks once implementation starts;
- do not treat this starter bundle as a substitute for the Python lane after source
  code changes begin.
