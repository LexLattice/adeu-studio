# Assessment vNext+171 Edges

Status: post-closeout edge assessment for `V62-B` (April 17, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS171_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Outbound Connector Delivery Could Be Over-Read As Authority

- Risk:
  outbound connector delivery could be over-read as if it already grants bridge
  office, witness closure, continuation mutation, or act authority.
- Response:
  keep egress transport-bounded and non-authorizing.
  - outbound delivery is not authority
  - bridge-office access is not connector permission
  - rewitness posture is not outbound authority
  - raw outbound payload is not witness, charter amendment, continuation mutation,
    bridge office, repo-write authority, execute authority, or dispatch authority
- Closeout Evidence:
  shipped lock/checker/tests preserve explicit non-equivalence constraints for
  `V62-B`.

### Edge 2: Positive Rewitness Could Be Claimed Without Explicit Basis

- Risk:
  positive rewitness posture could be treated as valid without carrying explicit
  witness basis or certificate basis.
- Response:
  keep positive rewitness fail-closed and basis-bearing.
  - positive rewitness requires witness basis ref or certificate ref
  - missing positive basis fails closed
  - egress bridge carries consumed rewitness basis summary directly
- Closeout Evidence:
  shipped checker/tests enforce explicit positive-basis requirements and direct
  basis summary carry-through.

### Edge 3: Optional Bridge/rewitness Refs Could Become Ambient Authority

- Risk:
  optional consumed bridge-office and rewitness refs could be inferred from prior
  capability instead of explicit per-packet selection.
- Response:
  keep optional refs explicit and non-ambient.
  - `none` means not selected and not consumed in this packet
  - absence cannot be inferred from connector availability or prior emission
    capability
- Closeout Evidence:
  shipped `V62-B` lock/checker require explicit optional-ref semantics.

### Edge 4: Egress Lineage Could Drift From Shipped Ingress Interpretation

- Risk:
  a tampered `V61-A` egress packet could carry an interpretation lineage that does
  not match the shipped `V62-A` consumed interpretation basis.
- Response:
  keep interpretation lineage exact and fail-closed.
  - `communication_egress.ingress_interpretation_ref` must match
    `ingress_bridge.consumed_ingress_interpretation_ref`
  - mismatches fail closed
- Closeout Evidence:
  review hardening commit added explicit checker enforcement and regression
  coverage for interpretation mismatches.

### Edge 5: Repo-Local Path Validation Could Permit Lexical Escape

- Risk:
  absolute paths lexically outside repo root could bypass component checks if they
  resolve back into repo space through symlinks.
- Response:
  keep repo-local path checks lexical-first and fail-closed.
  - path must be lexically within repo root
  - symlink component traversal is disallowed
  - resolved path must remain inside repo root
- Closeout Evidence:
  review hardening commit tightened `_assert_v62b_repo_local_input_path(...)` and
  added a regression for lexically-outside symlinked input paths.

### Edge 6: `V62-B` Could Quietly Swallow `V62-C`

- Risk:
  egress bridge success could be over-read as if connector hardening/migration law
  is already selected.
- Response:
  keep `V62-B` egress-only and leave hardening advisory work to `V62-C`.
  - no connector hardening register in `V62-B`
  - no candidate/migration advisory outcomes in `V62-B`
- Closeout Evidence:
  merged slice includes only one new
  `agentic_de_external_assistant_egress_bridge_packet@1` surface.

### Edge 7: External-Assistant Principal Could Blur Into Human-Via-Connector

- Risk:
  connector bridge posture could drift from explicit external-assistant selection
  into implicit human-via-connector semantics.
- Response:
  keep principal typing explicit and singular in this slice.
  - `external_assistant` selected
  - `human_via_connector` not selected
- Closeout Evidence:
  shipped checker/tests preserve explicit principal-class constraints.

### Edge 8: One Connector Path Could Be Over-Read As Broader Trust Law

- Risk:
  one admitted connector path and one successful egress bridge could be treated as
  connector-fleet trust, remote-operator law, or repo/execute authority.
- Response:
  keep path-level non-generalization explicit.
  - one exact connector path only
  - not broader connector-fleet trust law
  - not remote-operator law
  - not repo or execute authority
- Closeout Evidence:
  shipped contract/checker/tests keep explicit path-level non-generalization.

## Current Judgment

- `V62-B` was the right second slice because `V62-A` already closed admitted
  connector path plus ingress law, while outbound bridge posture was still missing.
- the shipped result remained properly bounded:
  - one admitted connector path only
  - one selected principal only
  - one egress bridge packet only
  - consumed shipped `V62-A` admission/ingress lineage
  - consumed shipped `V61-A` egress plus shipped `V61-B` office/rewitness lineage
  - explicit positive rewitness basis carry-through and fail-closed checks
  - no connector hardening advisory layer yet
  - no human-via-connector law
  - no remote/repo/execute/dispatch widening
- `V62-B` is closed on `main`.
- the next move should be `V62-C` as the advisory hardening follow-on rather than
  widening `V62-B` in place.
