# Assessment vNext+275 Edges

Status: pre-lock edge assessment for `OTB-0-A`.

Authority layer: planning assessment.

This document records pre-implementation edge analysis for `vNext+275`
(`OTB-0-A` phase catalog, bridge contract, transition claim, transition
validation, legal frontier, and guardrail), aligned to
`docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS275_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Scope

In scope:

- phase circuit catalog validation;
- O/E/D/U bridge contract validation;
- typed transition claim validation;
- artifact, evidence, and obligation-transfer row validation;
- transition admissibility diagnostics;
- legal frontier emission;
- non-authority guardrail output;
- canonical hashing and schema export for A surfaces.

Out of scope:

- semantic adjudication;
- domain ontology generation;
- HOB closure recomputation;
- transition closure/readiness aggregation;
- gate execution plans;
- worker baton contracts;
- evidence posture plans;
- operationalization reports;
- transition delta attribution;
- stale object invalidation after observed runs;
- integration handoff;
- probe generation or execution;
- worker dispatch;
- product authority;
- official-eval authority;
- future-family selection.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`
- `docs/ARCHITECTURE_ADEU_ODEU_TRANSITION_BROKER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS274.md`
- `docs/ASSESSMENT_vNEXT_PLUS274_EDGES.md`
- `docs/support/principled_recursive_odeu_meta_program_experimental_v46.md`
- `docs/support/general_program_ontology_derived_v1_7.md`

## Edge Set

### Edge 1: Artifact Presence Becomes An Implied Transition Claim

- Risk:
  implementation infers a claimed transition from artifact presence.
- Guardrail:
  `repo_phase_transition_claim@1` is mandatory. Missing claim fails closed.

### Edge 2: Valid Transition Becomes Action Authority

- Risk:
  `valid` is read as permission to execute the next phase.
- Guardrail:
  A-level validation uses `valid_for_broker_frontier`; frontier rows carry
  `broker_validation_only_not_execution_authority`.

### Edge 3: Bridge Consistency Collapses Into Bridge Completeness

- Risk:
  well-formed but incomplete bridges are promoted.
- Guardrail:
  separate `bridge_consistency_status` and `bridge_completeness_status`; fixture
  covers consistent but incomplete bridge.

### Edge 4: Artifact Identity Is Under-Specified

- Risk:
  one `artifact_hash` hides payload, semantic object, catalog, bridge, evidence,
  or obligation-set drift.
- Guardrail:
  multi-hash identity fields are required and mismatches fail closed.

### Edge 5: Evidence Contamination Is Only Checked Directly

- Risk:
  post-eval or source-tail evidence leaks through a derived summary artifact.
- Guardrail:
  evidence rows include `derived_from_evidence_refs` and contamination is
  checked through ancestry.

### Edge 6: Useful But Overstrong Artifacts Are Only Blocked

- Risk:
  the broker fails to name the maximum supported posture.
- Guardrail:
  unsupported claims emit `posture_downgrade_required` frontier rows with
  `requested_posture`, `maximum_supported_posture`, and revalidation frontier.

### Edge 7: Freshness Is Treated As Timestamp Freshness

- Risk:
  stale objects are reused when object hashes, evidence boundaries, obligation
  sets, target substrate, run topology, or partition changed.
- Guardrail:
  phase-local freshness basis is required and checked against bridge
  requirements.

### Edge 8: OTB Becomes A Semantic Judge

- Risk:
  the broker decides phase content quality or domain meaning.
- Guardrail:
  broker validates row shape, vocabulary, hashes, evidence boundary, and bridge
  transfer only; semantic judgment remains upstream.

### Edge 9: OTB Recomputes HOB Closure

- Risk:
  transition validation reopens HOB inheritance or closure.
- Guardrail:
  HOB outputs may be consumed as artifacts; OTB-A may not recompute HOB
  closure.

### Edge 10: A Leaks Into B/C

- Risk:
  closure summaries, gate plans, baton contracts, or attribution ship in A.
- Guardrail:
  A emits validation reports, legal-frontier rows, and guardrails only.

### Edge 11: Legal Frontier Becomes Worker Dispatch

- Risk:
  frontier rows are treated as taskpacks.
- Guardrail:
  frontier rows name required next actions but deny worker dispatch and
  execution authority.

### Edge 12: Canonical Determinism Is Claimed But Not Tested

- Risk:
  row ordering changes output hashes.
- Guardrail:
  shuffled input fixture must preserve canonical output order and hash.

## Required Guardrails

- Transition-claim lock:
  - no transition validation without `repo_phase_transition_claim@1`.
- Non-action lock:
  - A-level validation never emits execution or implementation authority.
- Consistency/completeness lock:
  - complete and consistent are separate fields.
- Multi-hash identity lock:
  - file, canonical payload, semantic object, catalog, bridge,
    evidence-boundary, and obligation-set hashes are separately represented.
- Evidence ancestry lock:
  - forbidden evidence ancestry fails closed.
- Posture downgrade lock:
  - overstrong claims emit downgrade frontier instead of silent acceptance.
- Freshness lock:
  - stale phase-local basis fails closed.
- Boundary lock:
  - no B/C outputs in A.
- Guardrail lock:
  - non-authority guardrail denies semantic, ontology, HOB closure, probe,
    implementation, worker dispatch, product, official-eval, and future-family
    authority.

## Acceptance Evidence Targets

- New `adeu_transition_broker` package exists.
- Six A-level record shapes are modeled and schema-exported.
- Focused tests cover the required starter fixtures in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS275.md`.
- Canonical hashing is stable under shuffled inputs.
- No closure aggregation, gate planning, baton contracts, delta attribution, or
  handoff APIs are present in A.
- Local verification includes focused pytest, schema export tests, and the repo
  Python gate selected for the implementation PR.

## Implementation Readiness Notes

1. `OTB-0-A` is implementation-ready as a bounded deterministic validation
   slice after starter-bundle acceptance.
2. Highest risks are action-authority overread and evidence-contamination
   ancestry.
3. Recommended implementation order:
   - vocabulary and canonical hashing;
   - record models;
   - catalog/bridge/claim validation;
   - artifact/evidence/obligation validation;
   - transition validation and legal-frontier emission;
   - schema export and focused fixtures.

