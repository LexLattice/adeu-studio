# Draft Stop-Gate Decision vNext+149

Status: proposed gate for `V55-A`.

Authority layer: pre-start scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS149.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- `packages/adeu_constitutional_coherence` exists as the sole implementation package
  for the slice;
- one thin script seam exists under `apps/api/scripts/`;
- the checker is warning-only and remains non-gating;
- the checker is deterministic over structured claims only:
  - explicit headers
  - explicit JSON blocks
  - explicit refs
  - explicit witness refs
  - explicit family or descendant declarations;
- the exact six-document admitted seed set is implemented and remains closed for
  `V55-A`;
- admitted support artifacts are read through explicit
  `constitutional_support_admission_record@1` posture only;
- the checker emits:
  - `constitutional_coherence_report@1`
  - `constitutional_unresolved_seam_register@1`
  - `constitutional_coherence_lane_drift_record@1`;
- the selected predicate set is implemented exactly as locked and no broader predicate
  family is silently added;
- malformed designated structured blocks fail closed while malformed non-designated
  prose does not become authoritative input;
- the preferred descendant trial remains support-surface mode only over
  `docs/support/crypto data spec2.md`;
- tests cover:
  - support-admission validation
  - structured-claim extraction
  - closed predicate evaluation
  - warning-only report emission
  - unresolved seam emission
  - fail-closed designated-record handling
  - support-surface descendant trial posture;
- `make check` passes on the implementation branch.

## Do Not Accept If

- any support doc becomes family law or checker law by citation alone;
- the admitted seed set widens by thematic similarity instead of explicit amendment;
- free text becomes the default checker input path;
- the checker behaves like an open-ended reviewer or theorem prover;
- the checker mints runtime/product authority;
- descendant-trial success is treated as descendant release promotion;
- the implementation introduces whole-checker gating or checker-global escalation;
- more than one descendant trial is shipped in `V55-A`.

## Local Gate

- run `make check`
