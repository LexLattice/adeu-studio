# Draft Stop-Gate Decision vNext+107

Status: proposed gate for `V47-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS107.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the released `V47-A` artifact family is hardened without changing its bounded first-
  slice authority posture;
- widened checker fact-kind and provenance-mode vocabularies are explicit, bounded, and
  matched exactly in code, schemas, and accepted examples;
- accepted standalone and companion ANM examples compile deterministically into the full
  released companion chain:
  - normalized `D-IR`;
  - predicate contracts;
  - checker facts;
  - evaluation results;
  - obligation ledger;
- concrete examples cover:
  - zero-match posture with no first ledger row;
  - prior-instantiation then later zero-match reconciliation posture;
  - clause-scope blocker posture without fabricated ledger rows;
- prose docs, authoritative schemas, mirrored exports, and committed examples remain in
  exact parity for all five released typed artifacts;
- checker fact rows remain typed unions and result/ledger mapping remains explicit in
  examples;
- clause-scope blocker rows remain encoded distinctly from subject-scoped result rows in
  accepted examples;
- the hardening lane does not widen into coexistence migration, ownership-transition,
  source-level `DEFERRED`, or execution/approval authority;
- targeted Python tests cover:
  - example replay determinism;
  - schema export parity;
  - hardened enum exactness;
  - reject-fixture fail-closed behavior.

## Do Not Accept If

- the hardening lane silently changes `V47-A` starter semantics instead of hardening
  them explicitly;
- released fact-kind or provenance-mode enums drift beyond the lock without accepted
  example coverage;
- zero-match after prior instantiation silently drops rows instead of using explicit
  reconciliation posture;
- authoritative schemas, mirrored exports, and committed examples drift out of parity;
- example carriers collapse source, IR, facts, results, and ledger into one mixed
  artifact blob;
- clause-scope blocker posture, subject-scoped result rows, or zero-match posture is
  represented only by prose and not by committed typed examples;
- the slice widens into current-markdown override, repo-wide migration, imported
  selector/predicate ownership, source-level `DEFERRED`, or execution authority;
- facts, results, or ledgers are treated as self-authorizing normative outputs.

## Local Gate

- run `make arc-start-check ARC=107` while the bundle remains docs-only;
- run targeted Python checks once implementation starts;
- do not treat this starter bundle as a substitute for the Python lane after source
  code changes begin.
