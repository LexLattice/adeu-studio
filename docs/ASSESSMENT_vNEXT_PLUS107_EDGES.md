# Assessment vNext+107 Edges

Status: planning-edge assessment for `V47-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS107_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Vocabulary Creep Without Example Discipline

- Risk:
  fact-kind or provenance-mode enums could widen informally, turning the hardening lane
  into open-ended drift.
- Response:
  permit only bounded enum additions that are backed by schema, accepted examples, and
  deterministic replay.

### Edge 2: Example Collapse Across Artifact Boundaries

- Risk:
  concrete examples could be written as mixed evaluator payloads instead of preserving
  source, IR, facts, results, and ledger as distinct surfaces.
- Response:
  keep example families artifact-separated and require compiled companions for each
  released surface.

### Edge 3: Companion-Posture Overreach

- Risk:
  companion examples could be overread as broader coexistence or migration doctrine.
- Response:
  keep `V47-B` to minimal example-backed coexistence only and defer broader doctrine to
  `V47-C`.

### Edge 4: Clause-Scope Blocker Example Thinness

- Risk:
  the family could ship hardened schemas/examples without making clause-scope blocker
  posture legible in accepted examples.
- Response:
  require at least one accepted example that shows clause-scope blocker results without
  fabricated ledger rows.

### Edge 5: Zero-Match Example Thinness

- Risk:
  selector zero-match could remain implementation knowledge rather than committed
  example-backed doctrine.
- Response:
  require at least one accepted example that shows zero-match notice posture with no
  first ledger row.

### Edge 6: Zero-Match Reconciliation Drift After Prior Instantiation

- Risk:
  the later same-scope case could be missed, so a previously instantiated obligation row
  might disappear silently when a later run resolves to zero-match.
- Response:
  require accepted hardening examples that make post-instantiation zero-match
  reconciliation explicit and fail closed rather than silently dropping rows.

### Edge 7: Union-Shape Drift

- Risk:
  fact or result example hardening could flatten typed unions back into universal row
  shapes for convenience.
- Response:
  keep union carriers explicit and reject malformed catch-all example rows.

### Edge 8: Clause-Scope Blocker Row-Shape Drift

- Risk:
  result examples could flatten clause-scope blocker rows and subject-scoped rows into
  one universal encoding, reintroducing ambiguity that `V47-A` explicitly removed.
- Response:
  keep clause-scope blocker rows and subject-scoped result rows visibly distinct in the
  hardened example family and reject flattening drift.

### Edge 9: Schema/Export Parity Drift

- Risk:
  prose docs, authoritative schemas, mirrored exports, and accepted examples could drift
  apart while all still look individually plausible.
- Response:
  require explicit parity across docs, authoritative schema, mirrored schema, and
  committed example payloads for the hardened vocabulary and row-shape grammar.

### Edge 10: Hardening-Lane Authority Laundering

- Risk:
  because `V47-B` is example-oriented, it could accidentally smuggle stronger normative
  authority into facts, results, or ledger examples.
- Response:
  keep all examples bounded to the same non-executive, non-self-authorizing posture as
  released `V47-A`.

### Edge 11: Package-Boundary Drift

- Risk:
  example and schema hardening could sprawl into unrelated packages or adoption docs too
  early.
- Response:
  keep `V47-B` bounded to `adeu_semantic_source` plus `adeu_commitments_ir`.

## Current Judgment

- `V47-B` is the right next move because `V47-A` is now closed on `main` and the next
  obvious gap is not new architecture but example/schema/vocabulary hardening.
- the slice should remain bounded: concrete, typed, example-backed hardening first;
  broader coexistence, ownership transition, and downstream consumer seams later.
