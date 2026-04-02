# Assessment vNext+111 Edges

Status: planning-edge assessment for `V47-F`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS111_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Benchmark-World Scope Drift

- Risk:
  `V47-F` could quietly widen from a bounded benchmark-world consumer seam into a vague
  “any benchmark family” doctrine.
- Response:
  freeze the starter benchmark-world vocabulary to already released `V42` benchmark
  artifacts on `main` and keep `V46` benchmark-family release out of this slice.

### Edge 2: Policy-Source Collapse

- Risk:
  benchmark consumer rows could treat result or ledger refs as if they were the
  authoritative policy source while leaving clause binding semantically vague.
- Response:
  require exactly one bound released `D-IR` clause source per benchmark row and make
  results or ledger refs supporting evidence only.

### Edge 3: Result/Ledger Authority Laundering

- Risk:
  because result and ledger artifacts are already released, they could be overread as
  independent policy authority inside benchmark consumer bindings.
- Response:
  freeze an explicit support-only doctrine for result-set and ledger refs and reject
  result-or-ledger-only benchmark rows, plus fail closed when support surfaces
  contradict each other or the bound policy source, or when they do not cohere to the
  same benchmark target / snapshot / policy-source lineage.

### Edge 4: Local-Eval Authority Overread

- Risk:
  released `adeu_arc_local_eval_record@1` artifacts could be reinterpreted as official
  scorecard, leaderboard, or competition authority.
- Response:
  require local-eval benchmark consumers to preserve released `V42-D` local-only
  posture and fail closed on any stronger authority claim.

### Edge 5: Scorecard Source-Kind Overread

- Risk:
  released `adeu_arc_scorecard_manifest@1` artifacts could be consumed as if typed
  source-kind and authority-limitations posture did not matter.
- Response:
  require benchmark consumers to respect released `V42-E` scorecard source-kind,
  authority, and limitation posture exactly rather than bypassing it through raw ref
  binding.

### Edge 6: Behavior-Evidence Narrative Laundering

- Risk:
  released `adeu_arc_behavior_evidence_bundle@1` artifacts could be consumed as if
  descriptive narrative or inferred claim-posture entries were execution or approval
  authority.
- Response:
  preserve released `V42-G4` authority-boundary and claim-posture doctrine and fail
  closed on stronger interpretation.

### Edge 7: Benchmark World / Ref Invariant Drift

- Risk:
  typed benchmark rows could still carry contradictory posture if world kind and ref
  kind are not frozen together.
- Response:
  require exact invariants between local-eval world and local-eval ref, scorecard
  world and scorecard ref, and behavior-evidence world and behavior-evidence ref.

### Edge 8: Upstream Profile Bypass

- Risk:
  benchmark consumer rows could bind directly to raw refs in a way that ignores
  already released `V47-C`, `V47-D`, and `V47-E` profile doctrine where those
  surfaces remain relevant.
- Response:
  require benchmark consumer binding to respect released upstream ANM profiles rather
  than bypassing them through raw ref resolution alone, and fail closed when the
  required upstream benchmark or ANM doctrine joins are dangling, stale, or unresolved
  against the declared snapshot/source scope.

### Edge 9: Action-Vocabulary Creep

- Risk:
  benchmark consumer rows could claim vague downstream “effects” without freezing which
  constrain-only actions are actually allowed in this bounded slice.
- Response:
  enumerate benchmark consumer actions exactly and require all row action fields to
  draw from the same frozen vocabulary, remain pairwise disjoint, and stay consistent
  with the row's explicit authority relation.

### Edge 10: Benchmark-Family Overreach

- Risk:
  the first benchmark-world consumer seam could quietly act like a partial `V46`
  benchmark-family release.
- Response:
  keep `V47-F` bounded to consumer doctrine over already released benchmark artifacts,
  not family-level benchmark specs, projections, execution contexts, or diagnostics as
  a new released substrate.

### Edge 11: Snapshot / Source-Scope Drift

- Risk:
  benchmark consumer rows could bind together incompatible snapshots or source scopes
  across the released ANM stack and benchmark artifact worlds.
- Response:
  require same snapshot identity and explicit artifact-local source-scope compatibility
  checks.

### Edge 12: Package-Boundary Sprawl

- Risk:
  a benchmark-consumer lane could sprawl into benchmark-domain packages or operator
  systems before the bounded profile surface is stable.
- Response:
  keep `V47-F` bounded to `adeu_semantic_source` plus `adeu_commitments_ir` and treat
  released benchmark artifacts as consumed inputs, not new owning implementation
  domains in this slice.

## Current Judgment

- `V47-F` is worth implementing now because `V47-A` through `V47-E` have already
  released the bounded ANM substrate, hardening layer, coexistence/adoption doctrine,
  ownership-transition doctrine, and descriptive/runtime consumer seam on `main`,
  while typed benchmark-world consumer posture remains the next unclosed gap in this
  family.
- The narrowest safe version of that gap is not a new `V46` benchmark-family release;
  it is one bounded consumer doctrine over already released benchmark artifacts on
  `main`, with exact anti-leakage posture and no execution or approval power.
