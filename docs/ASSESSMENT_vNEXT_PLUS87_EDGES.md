# Assessment vNext+87 Edges

Status: planning-edge assessment for `V41-E`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS87_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Intended / Observed Collapse

- Risk:
  the alignment lane could reconcile intended and observed into one cleaned-up truth
  surface, erasing the distinction `V41` was created to preserve.
- Response:
  keep intended and observed as separate consumed artifacts and allow the alignment
  report only to classify drift between them, not to rewrite either one; keep the
  request boundary plus settlement frame as the normative driver of intended truth
  and treat observation as a constraining companion input only.

### Edge 2: Lineage Drift Across the Four Upstream Artifacts

- Risk:
  the report could claim to compare released request, settlement, observation, and
  intended artifacts while actually consuming a mixed or drifting repo world.
- Response:
  require exact carry-through of request id/ref, settlement id/ref, observation
  id/ref, intended architecture id/semantic hash, `source_set_hash`, and
  `authority_boundary_policy`, and fail closed on any mismatch.

### Edge 3: Severity / Blocking Laundering

- Risk:
  the report could emit severe drift but still present the overall posture as
  `aligned` or suppress blocking lineage into summary prose.
- Response:
  freeze exact severity and overall posture enums and require blocking findings to be
  surfaced explicitly through `blocking_finding_ids`; also distinguish report-level
  `blocked` from upstream settlement `compile_entitlement = blocked` so the two
  postures cannot be conflated.

### Edge 4: Unresolved-Unknown Disappearance

- Risk:
  unresolved unknowns already visible in released observed or intended posture could
  disappear during comparison, producing a cleaner but dishonest drift report.
- Response:
  require explicit `unresolved_unknown` findings and fixture-visible carry-through of
  at least one unresolved or evidence-gap case.

### Edge 5: Provenance-Light Findings

- Risk:
  the report could emit findings as grounded-sounding prose without stable ids or
  resolvable intended/observed support refs.
- Response:
  require stable finding-id families, explicit `basis_kind`, deterministic
  canonical-id derivation from typed support tuples, and typed finding anchors that
  resolve back to the consumed intended/observed/request/settlement surfaces rather
  than notes or prose-only fields.

### Edge 6: Non-Deterministic Finding Replay

- Risk:
  the same comparison world could yield the same substantive findings with different
  ids, order, or severity counts depending on traversal order or duplicate emission.
- Response:
  collapse duplicate findings on one canonical support tuple, emit findings in
  ascending canonical `finding_id` order, and derive `severity_counts` from that
  deduplicated canonical set only.

### Edge 7: Remediation / Runner Creep

- Risk:
  a first alignment slice could quietly start shipping repair plans, repo mutation
  instructions, or runner state under the cover of “diagnostics.”
- Response:
  keep `V41-E` bounded to comparison only and reject remediation, runner, and
  repo-mutation payloads outright.

### Edge 8: Silent Settlement Reinterpretation

- Risk:
  the alignment lane could quietly downgrade or reinterpret the released settlement
  posture instead of consuming it as historical governing context.
- Response:
  require the first concrete `V41-E` arc to consume the released entitled settlement
  posture as-is and reject local recomputation of settlement authority.

## Current Judgment

- `V41-E` is worth implementing now because `V41-A` already froze the repo world,
  `V41-B` already froze interpretation and entitlement, `V41-C` already froze a
  facts-only observed lane, and `V41-D` already froze repo-grounded intended
  root-family outputs; the next missing layer is exactly the deterministic comparison
  surface that makes drift inspectable without yet widening into runner behavior.
