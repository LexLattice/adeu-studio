# Assessment vNext+112 Edges

Status: planning-edge assessment for `V48-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS112_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Hidden Policy Composition

- Risk:
  `V48-A` could quietly become a policy-composition algebra instead of a bounded
  single-policy binding seam.
- Response:
  freeze exactly one released `V47-E` policy source and leave policy composition,
  precedence, and conflict resolution unselected in this slice.

### Edge 2: Hidden Scope Union

- Risk:
  the bridge could silently widen from one released scope source into implicit scope
  union, scope widening, or ambient repo discovery.
- Response:
  require exactly one released `V45` scope source plus exactly one released `V45-F`
  admission entry and fail closed on any widening beyond that bounded lineage.

### Edge 3: `V45-F` Bypass

- Risk:
  `V48-A` could bind a descriptive scope surface directly into worker authority
  without respecting the already released descriptive-to-normative admission seam.
- Response:
  require one explicit released `V45-F` binding-entry lineage for every released scope
  source admitted into the binding profile.

### Edge 4: `V47-E` Bypass

- Risk:
  the first bridge slice could bind directly to raw clauses or informal policy prose,
  bypassing the already released downstream policy-bearing surface meant to carry repo
  task posture.
- Response:
  freeze one starter policy-source kind only:
  `released_v47e_policy_consumer_row_ref`.

### Edge 5: `V47-E` Carrier Authority Laundering

- Risk:
  because `V48-A` admits a released `V47-E` row as its starter policy carrier, the row
  itself could be overread as terminal authority rather than a carrier whose bound
  released `D-IR` clause remains upstream authority.
- Response:
  require every admitted `V47-E` row to resolve to exactly one bound released `D-IR`
  clause and forbid authority laundering from the row apart from that clause lineage.

### Edge 6: `V45-F` Admission Overreach

- Risk:
  because `V48-A` also consumes a released `V45-F` binding entry, that entry could be
  overread as if it directly minted execution-envelope authority rather than merely
  admitting later constrained scope consumption.
- Response:
  require every admitted `V45-F` entry to resolve to the same scope surface and
  binding-subject posture and keep it admission-only and non-executive.

### Edge 7: Kernel Redefinition Drift

- Risk:
  a binding-profile slice could silently redefine generic taskpack compiler, runner,
  signing, or provenance semantics before the bridge is stable.
- Response:
  keep `V48-A` bounded to category-level taskpack mapping only and defer manifest /
  bundle / runner / attestation / conformance release to later `V48` paths.

### Edge 8: Prompt Authority Drift

- Risk:
  prompt text, chat prose, or `AGENTS.md` could remain de facto execution authority
  even after a typed boundary exists.
- Response:
  freeze projection-only posture and make prompt-boundary conflict fail closed rather
  than implementation-defined.

### Edge 9: Stale-Lineage Reuse

- Risk:
  a seemingly valid binding profile could reuse stale or dangling released policy /
  scope lineage and still look structurally plausible.
- Response:
  require same snapshot identity, source-scope-compatible lineage resolution, and
  fail-closed rejection for stale or unresolved lineage.

### Edge 10: Projection-Conflict Drift

- Risk:
  because no precedence algebra is selected in `V48-A`, contradictory allowlist /
  forbidden / command / evidence-slot projections could otherwise validate while
  remaining semantically ambiguous.
- Response:
  make contradictory projections invalid and fail closed rather than choosing a local
  winner.

### Edge 11: Mapping-Surface Creep

- Risk:
  the first bridge slice could introduce ad hoc mapping buckets that drift away from
  the released taskpack kernel categories.
- Response:
  freeze the starter mapping categories exactly to allowlist, forbidden, commands, and
  evidence slots.

### Edge 12: Kernel-Shape Drift

- Risk:
  command or evidence-slot projection could quietly turn into prose-shaped “guidance”
  instead of released kernel-shaped carriers.
- Response:
  keep command projection bounded to released command-carrier shape and evidence-slot
  projection bounded to released evidence-slot carrier shape.

### Edge 13: Single-Worker Topology Drift

- Risk:
  a first binding slice could quietly grow worker-count, topology, or decomposition
  semantics before the single-worker boundary is proven.
- Response:
  freeze exactly one worker subject and leave topology and multi-worker handoff to
  later `V48-E`.

### Edge 14: Authority Expansion Through Binding Rows

- Risk:
  because `V48` terminates in execution-envelope carriers, the first slice could be
  overread as granting execution, approval, waiver, or deferral authority directly.
- Response:
  keep the released surface doctrine-first and non-executive, with no authority
  expansion beyond what upstream released policy already allows.

### Edge 15: Package-Boundary Sprawl

- Risk:
  the bridge could sprawl back into `adeu_repo_description`,
  `adeu_semantic_source`, or `adeu_commitments_ir` instead of first stabilizing as a
  harness-owned bridge surface.
- Response:
  keep `V48-A` bounded to `adeu_agent_harness` and consume released `V45` / `V47`
  artifacts as upstream authority inputs only.

## Current Judgment

- `V48-A` is worth implementing now because `V45` already gives released descriptive
  scope, `V47` already gives released normative / consumer posture, and the harness
  already gives released taskpack / runner / provenance carriers, while the typed
  bridge between them remains missing.
- the right first move is not worker orchestration but one narrow binding profile that
  proves ADEU can externalize worker constraints through released artifacts rather than
  prompt prose alone.
