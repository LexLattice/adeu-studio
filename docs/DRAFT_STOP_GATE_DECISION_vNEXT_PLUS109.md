# Draft Stop-Gate Decision (Pre vNext+109)

This note records the pre-start stop-gate posture for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS109.md`

Status: starter decision scaffold for `V47-D` (April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS109.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v109_start_stop_gate_scaffold",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Starter scaffold only. Closeout evidence, metric continuity, and final gate values are added after implementation merges."
}
```

## Stop-Gate Question

Should `vNext+109` release the bounded `V47-D` selector / predicate
ownership-transition lane over the already released `V47-A` + `V47-B` + `V47-C` stack
without reopening ANM architecture, coexistence doctrine, downstream consumers, or
execution authority?

Current answer: not yet evaluated. This document is the pre-start scaffold only.

## Required Release Shape

To pass stop-gate at closeout, `V47-D` should show:

- one canonical `anm_selector_predicate_ownership_profile@1` with
  authoritative/mirrored schema parity;
- one explicit normalization rule that the `bootstrap` owner-layer term in `V47-D`
  is the same bootstrap term already used by released bootstrap predicate-contract
  surfaces;
- deterministic explicit classification of bootstrap vs owned selector refs;
- deterministic explicit classification of bootstrap vs owned predicate refs;
- explicit selector-row and predicate-row mutual-exclusion invariants so bootstrap and
  imported ref carriers cannot coexist contradictorily inside one row;
- explicit compatibility posture between bootstrap and later owned surfaces;
- one explicit compatibility matrix covering bootstrap/bootstrap, owned/bootstrap,
  bootstrap/owned, and owned/owned combinations;
- explicit bootstrap-retirement posture that does not silently retire bootstrap
  carriers;
- fail-closed imported-ref resolution against declared snapshot, source-scope, and
  declared identity/version bindings;
- fail-closed rejection of implicit ownership promotion, contradictory mixed
  ownership, missing imported refs, and authority laundering;
- explicit retention of backward-compatible bootstrap replay where retirement is not
  yet selected, with no silent reinterpretation into owned semantics.

## Non-Goals

`V47-D` must not be treated as authority to ship:

- repo-wide markdown migration;
- source-level `DEFERRED`;
- downstream policy-bearing consumer doctrine;
- execution, approval, mutation, scheduling, waiver, or deferral authority;
- automatic retirement of bootstrap selectors or predicate contracts by local
  convention alone.

## Expected Evidence At Closeout

Closeout should supply:

- merged PR and green CI evidence;
- one canonical
  `v47d_authoritative_normative_markdown_selector_predicate_ownership_transition_evidence@1`
  input;
- authoritative/mirrored schema parity evidence;
- accepted bootstrap-only, mixed-transition, owned-selector, owned-predicate, and
  compatibility fixtures;
- reject-fixture evidence for implicit promotion, contradictory mixed ownership,
  missing imported refs, dangling/stale/incompatible imported refs,
  snapshot/scope incompatibility, and anti-authority-laundering failures;
- stop-gate continuity artifacts and runtime observability comparison.

## Provisional Release Criteria

`V47-D` should be considered releasable only if:

1. ownership-transition doctrine is explicit rather than code-inferred;
2. bootstrap replay remains backward compatible unless explicit retirement posture says
   otherwise;
3. selector and predicate owner layers use one normalized bootstrap term rather than
   cross-slice drift;
4. selector and predicate rows enforce mutual-exclusion invariants rather than
   carrying contradictory bootstrap/imported ref state;
5. imported owned refs require explicit bindings rather than local-name promotion and
   fail closed when dangling, stale, or identity/version incompatible;
6. same-snapshot identity and artifact-local source-scope compatibility are enforced;
7. bounded ownership vocabularies and compatibility-matrix semantics remain exact;
8. the shipped slice remains non-executive, non-migratory, and non-consumer-binding.
