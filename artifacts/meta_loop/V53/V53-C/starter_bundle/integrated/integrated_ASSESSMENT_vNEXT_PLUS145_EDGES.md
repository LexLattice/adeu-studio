# Assessment vNext+145 Edges

Status: planning-edge assessment for `V53-C` (April 7, 2026 UTC).

Authority layer: planning support.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS145_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Scope

- In scope:
  - repo-owned `adeu_edge_taxonomy_revision_register@1`
  - exact downstream consumption of released `V53-A` taxonomy/applicability and
    released `V53-B` adjudication
  - append-only cumulative lineage/register semantics
  - exact starter decision-shape, same-lineage append, and lineage-parent law
  - exact starter adjudication-support and candidate-successor ref law
  - slice-local starter mapping for what is instantiated here versus deferred
- Out of scope:
  - reopening released `V53-A` taxonomy/applicability law
  - reopening released `V53-B` adjudication law
  - direct `V45-D` test-intent integration
  - probe strategy/test-intent widening
  - live taxonomy mutation helpers
  - repo-wide scope widening or broader reviewer-platform work

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md`
- `docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_EDGE_LEDGER_V53C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS141.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS143.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md`

## Open Edges

### Edge 1: `V53-C` Quietly Reopens Released `V53-B` Adjudication Law

- Risk:
  the revision/register slice could claim to be downstream while actually revising the
  released meaning of adjudication rows or overriding released support laws.
- Response:
  consume one released adjudication ledger as authoritative input, require every
  register entry to keep `supporting_adjudication_ledger_ref` equal to that bound
  ledger ref, and freeze revision support law to explicit row refs over that released
  ledger only.

### Edge 2: The Register Collapses Back Into One-Off Judgments

- Risk:
  the slice could emit only isolated revision judgments again and call the result
  cumulative without preserving prior order, prior refs, or append-only lineage.
- Response:
  require one append-only cumulative register with explicit preservation of prior entry
  order, explicit lineage-parent refs, and same-lineage append frozen to exact reuse of
  the one bound released adjudication-ledger ref.

### Edge 3: Lineage Parent Refs Drift Outside Admitted History

- Risk:
  a starter register could point to unknown, forward, or duplicated parent refs and
  still appear well-formed.
- Response:
  parent refs must resolve only to earlier admitted entries, duplicates must fail
  closed, and cycles must be forbidden.

### Edge 4: Split/Merge History Launders Automatic Taxonomy Mutation

- Risk:
  a typed revision register could silently become a live catalog-rewrite or migration
  helper instead of a bounded evidence register.
- Response:
  keep `V53-C` register-first: split/merge/deprecate history is typed register
  evidence, not automatic catalog execution.

### Edge 5: Candidate Edge-Class Refs Mint Unbounded New Taxonomy Surface

- Risk:
  starter split/merge entries could invent arbitrary new refs without explicit
  containment, turning a bounded register lane into open-ended taxonomy expansion.
- Response:
  keep candidate refs explicit and typed inside register evidence only, require the
  same `edge_class:` ref family as released `V53-A` `edge_class_ref` values, forbid
  duplicates and subject overlap within an entry, and require reject fixtures for
  inadmissible candidate refs; released catalog mutation remains outside `V53-C`.

### Edge 6: Weak Adjudication Support Is Promoted Into Revision Change

- Risk:
  `applicable_unchecked`, `underdetermined`, lexical adjacency, or structural overlap
  could be laundered into revision-register entries.
- Response:
  require every starter register entry to anchor on at least one released adjudication
  row with `witness_found` or `checked_no_witness_found`, allow `deferred` only as
  supplementary context, and forbid soft-evidence or deferred-only promotion by
  itself.

### Edge 7: Append Order and Identity Become Helper-Taste Semantics

- Risk:
  duplicate ids, silent reordering, or collapsed preserved history could make the
  register look cumulative while losing deterministic lineage.
- Response:
  freeze stable append order, unique entry ids, exact preservation of prior history
  when a register is extended, and one exact same-ledger append law so helper taste
  cannot recover cross-lineage history splicing.

### Edge 8: Probe/Test-Intent Integration Reappears Too Early

- Risk:
  the revision lane could try to justify itself by directly consuming released
  `V45-D` test-intent surfaces before the core register semantics are stable.
- Response:
  keep `V53-C` bounded to released adjudication-ledger inputs only and defer direct
  test-intent or broader probe integration explicitly to `V53-D`.

## Current Judgment

- `V53-C` is the right next slice because the strongest remaining blocker cluster after
  released `V53-B` is no longer override constitutionality:
  - cumulative history versus isolated judgments
  - explicit append-only lineage
  - split/merge/deprecate/stabilize representation
  - prevention of taxonomy-mutation laundering
- the proposed starter bundle is directionally correct and properly bounded when read
  against the controlling planning, support-mapping, and intake docs:
  - one new cumulative revision register contract only
  - exact downstream consumption of released `V53-A` and released `V53-B`
  - one explicit append-only lineage law with same-lineage append frozen to one bound
    released adjudication ledger
  - one explicit starter decision-shape law
  - one explicit starter adjudication-support anchor law with `deferred` supplementary
    only
  - one explicit bounded candidate-successor ref law
  - no direct probe/test-intent integration
  - no live catalog mutation
- the main remaining review focus should be whether the starter register-entry law is
  finite and tight enough that implementation cannot recover taxonomy mutation or test
  authority by helper taste.
