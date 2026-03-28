# Assessment vNext+95 Edges

Status: post-closeout edge assessment for `V42-G1` (March 29, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS95_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Puzzle Source Authority Ambiguity

- Risk:
  local puzzle inputs could be pulled from mixed or ambiguous sources while presented as
  one authoritative cohort.
- Response:
  source authority is bounded by typed `source_kind` enum and explicit `source_ref`
  binding with deterministic precedence policy; open-text source-kind drift is rejected.

### Edge 2: Selection Register Drift

- Risk:
  the three-puzzle cohort could be changed after outcomes are observed, creating
  non-auditable demo selection.
- Response:
  `selection_register_id`/`selection_register_hash` and canonical puzzle order are
  enforced; retrospective swap fixtures are fail-closed.

### Edge 3: Deterministic Freeze Instability

- Risk:
  normalization/freeze could produce different bundle identities across runs.
- Response:
  per-puzzle identity hashes and bundle identity hash are computed over canonical order
  and replay deterministically from fixed payload fixtures.

### Edge 4: Provenance Laundering

- Risk:
  puzzle bundle artifacts could carry IDs and hashes without verifiable provenance refs.
- Response:
  provenance refs are required typed fields at bundle and entry levels, with explicit
  rejection coverage for omissions.

### Edge 5: Cohort Integrity Drift (Duplicate Identity)

- Risk:
  a three-entry bundle could hide duplicate puzzle identity and still appear complete.
- Response:
  duplicate puzzle identity hashes are rejected fail-closed in validators and fixtures.

### Edge 6: Premature Lane Widening

- Risk:
  `V42-G1` implementation could silently widen into agent-run execution (`G2`) or
  multi-puzzle harness orchestration (`G3`).
- Response:
  shipped surfaces remain bounded to ingest/freeze only, with no `G2`/`G3`/`G4`
  execution widening in this closeout.

### Edge 7: Released Stack Redefinition Drift

- Risk:
  local ingest work could reopen or reinterpret released `V42-A`..`V42-F` semantics.
- Response:
  v95 consumes released stack doctrine without redefining prior contracts; emitted
  artifact is scoped to `adeu_arc_puzzle_input_bundle@1` only.

### Edge 8: Narrative Overclaim from Ingest Artifacts

- Risk:
  descriptive fields in puzzle bundles could be treated as authoritative performance or
  competition evidence.
- Response:
  narrative surfaces remain explicitly non-authoritative; authority is constrained to
  typed source/selection/hash/provenance fields.

### Edge 9: Live External Fetch Dependence

- Risk:
  replay claims could implicitly depend on changing external fetch behavior.
- Response:
  replay posture is bounded to frozen local payload fixtures and fixed evidence; live
  external fetch determinism claims remain out of scope.

## Current Judgment

- `V42-G1` closeout on `main` resolves the practical local-ingest blocker with bounded,
  typed, and deterministic puzzle bundle semantics.
- Remaining practical widening now belongs to `V42-G2` (reasoning-agent run bridge)
  while preserving the fail-closed authority posture established in `V42-G1`.
