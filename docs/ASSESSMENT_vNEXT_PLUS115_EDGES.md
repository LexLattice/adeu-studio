# Assessment vNext+115 Edges

Status: planning-edge assessment for `V48-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS115_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released `V48-C` Bypass

- Risk:
  the conformance lane could silently bypass the released worker-envelope chain and
  bind directly to raw compiled bindings or raw policy/scope starters.
- Response:
  freeze one starter input shape only:
  exactly one released boundary instance, one released worker execution attestation,
  and one released worker execution provenance.

### Edge 2: Observed-Action Carrier Ambience

- Risk:
  filesystem, command, emitted-artifact, or branch/ref observation could be recovered
  from ambient repo search rather than explicit typed carriers.
- Response:
  require one explicit four-carrier observed-action set, freeze one source-of-truth /
  acquisition rule per carrier kind, and forbid hidden repo search.

### Edge 3: Observed-Action Carrier Widening

- Risk:
  the first conformance slice could quietly widen into arbitrary action traces,
  telemetry streams, or multi-source observation algebra.
- Response:
  freeze the starter observed-action carrier vocabulary exactly to filesystem mutation
  set, command invocation log, emitted artifact set, and branch/ref identity.

### Edge 4: Repo / Task / Worker Identity Drift

- Risk:
  a report could look structurally valid while the observed run no longer matches the
  repo ref, task instance, worker subject, or provider/model/adapter tuple bound by
  the released `V48-C` envelope.
- Response:
  require explicit lineage coherence and fail closed on mismatch.

### Edge 5: Off-Boundary Mutation Underread

- Risk:
  filesystem mutations outside the bound allowlist or inside forbidden paths could be
  underread as informational rather than conformance-breaking.
- Response:
  freeze explicit mutation validation over the bound compiled boundary and fail closed
  on off-boundary mutation.

### Edge 6: Command Drift Underread

- Risk:
  command invocation logs could contain unallowlisted commands or forbidden effects
  while the report still claims conformant posture.
- Response:
  require explicit command validation over the bound command posture and fail closed on
  drift.

### Edge 7: Emitted-Artifact Contradiction

- Risk:
  the observed emitted artifact set could contradict the bound compiled boundary or
  the support-only provenance surface while remaining structurally plausible.
- Response:
  keep observed emitted artifacts distinct from provenance support refs and fail closed
  on contradiction.

### Edge 8: Branch / Ref Identity Ambiguity

- Risk:
  branch/ref identity could remain ambiguous, loose, or drift away from the exact
  execution repository identity already bound in `V48-C`.
- Response:
  require one explicit exact execution-repository identity / branch-ref carrier
  coherent with the bound repo identity and snapshot, not a floating git-label prose
  field.

### Edge 9: Prompt Authority Drift

- Risk:
  prompt text, chat prose, or `AGENTS.md` could still decide conformance even after
  typed lineage and observed-action carriers exist.
- Response:
  keep prose projection-only and make prompt-boundary conflict fail closed.

### Edge 10: Judgment Aggregation Ambiguity

- Risk:
  overall conformance judgment could become a prose choice rather than a deterministic
  function of the frozen check results.
- Response:
  freeze one exact precedence rule and derive supporting diagnostics from the same
  frozen check set.

### Edge 11: Incomplete Evidence Overread

- Risk:
  missing observed-action carriers or unresolved lineage could be silently treated as
  pass or warning rather than explicit incomplete-evidence posture.
- Response:
  freeze `incomplete_evidence` as a first-class judgment and fail closed on missing
  evidence.

### Edge 12: Support vs Observation Collapse

- Risk:
  support-artifact provenance from `V48-C` could be mistaken for the actual observed
  action set, collapsing lineage evidence into conformance evidence.
- Response:
  keep support lineage and observed-action carriers structurally distinct in the first
  conformance slice and forbid provenance/support artifacts from substituting for the
  frozen observed-action carriers.

### Edge 13: Check-Vocabulary Drift

- Risk:
  different implementations could produce semantically different reports while still
  claiming the same top-level contract because `check_family` and per-check judgment
  vocabularies remain loose.
- Response:
  freeze starter `check_family` and per-check `judgment` vocabularies explicitly in
  the lock rather than leaving them implementation-defined.

### Edge 14: Multi-Worker Topology Creep

- Risk:
  the first conformance release could quietly widen into supervisor/worker or
  worker/worker judgment before the single-worker case is stable.
- Response:
  keep topology deferred to `V48-E`.

### Edge 15: Authority Expansion Through Conformance

- Risk:
  because `V48-D` issues pass/fail judgment over real runs, it could be overread as
  minting broader execution or approval authority than the bound compiled boundary
  already allows.
- Response:
  keep the surface constrain-only, non-executive, and non-approving.

## Current Judgment

- `V48-D` is worth implementing now because `V48-A`, `V48-B`, and `V48-C` already
  released the binding, compiled-boundary, and worker-envelope halves of the bridge on
  `main`, while replayable post-run conformance over frozen observed-action carriers
  remains unshipped.
- the right next move is conformance-first rather than topology-first, because ADEU
  should make single-worker judgment explicit and replayable before widening into any
  supervisor/worker or worker/worker handoff doctrine.
