# Architecture ADEU UX Ergonomic Instantiation Adjudication Family v0

Status: architecture / decomposition record; `V67` is complete on `main`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V67` downstream of the released Morphic UX governance stack.
The planned `V67-A` / `V67-B` / `V67-C` ladder is now shipped on `main`; any
follow-on should begin from a new planning decision rather than more widening
inside this closed family.

## 1. Family Thesis

`V67` should not be read as “responsive design again” or “layout solving.”

The existing UX governance stack already owns:

- the stable UX object;
- the lawful morph family;
- the released projection / interaction contract;
- diagnostic and conformance posture.

`V67` is the downstream ergonomic adjudication family that asks:

- how should the same lawful UX object become concretely instantiated under a
  specific human + device + task envelope?
- how should that adjudication remain artifact-bound and finite?
- how should it stay strict about authority, provenance, admissibility, and
  ambiguity?

The intended end-state is:

- constitutional invariants remain stable;
- instantiated invariants become explicit for the case at hand;
- free aesthetic variables remain free unless they encode authority, evidence,
  legibility, or gate visibility.

That is not a design-assistant doctrine.
It is a bounded adjudication doctrine.

## 2. Relationship To Existing UX Governance

The current stack remains the owner of:

- `ux_domain_packet@1`
- `ux_morph_ir@1`
- `v36a_first_family_approved_profile_table@1`
- `v36a_same_context_reachability_glossary@1`
- `ux_surface_projection@1`
- `ux_interaction_contract@1`
- `ux_morph_diagnostics@1`
- `ux_conformance_report@1`
- `ux_surface_compiler_variant_manifest@1`

`V67` should consume those released surfaces.
It should not reopen them casually.

So `V67` may constrain:

- ergonomic rule precedence;
- ergonomic component taxonomy;
- visibility and collapse claims;
- case-envelope and measurement admissibility;
- finite candidate projection evaluation.

But it may not mint:

- new semantic regions or lanes by default;
- new action-cluster semantics by default;
- new evidence-before-commit or trust-boundary law by default;
- free-form morph axes by default;
- authority from screenshots;
- layout law from vibe or preference only.

## 3. Core Separation

The family should keep three layers distinct:

1. constitutional invariants
   - sameness law of the UI object
2. instantiated invariants
   - case-specific constraints required here
3. free aesthetic variables
   - cheap later iteration space unless bound to authority, evidence, or
     legibility law.

This distinction is load-bearing.

`V67` should therefore reject:

- aesthetic variables being exported as hard law;
- heuristic utility being exported as constitutional truth;
- user preference being exported as authority to lower hard floors;
- physical or visual-size claims derived from inadmissible measurement chains.

## 4. Authority Stack

The adjudicator should evaluate rules in a fixed stack:

1. constitutional surface invariants
2. repo-local ADEU deontic / ergonomic policy
3. adopted external-standard floors
4. platform presets
5. user-declared upward preferences
6. heuristic utility ranking

Expected force posture:

- ranks 1 through 3 may produce hard blocking or hard floors;
- platform presets may produce default floors or recommended presets unless
  explicitly adopted by repo-local ADEU policy;
- a platform preset does not become hard law merely by being present;
- user preference may inflate but not lower hard floors;
- heuristic utility may rank only after hard checks pass.

The family therefore needs an explicit rule artifact rather than hidden constants.

## 5. Family Surfaces

The family-level starter target set should be:

| Surface | Role |
|---|---|
| `ux_ergonomic_rule_authority_stack@1` | provenance-bearing ergonomic rulebook and precedence stack |
| `ux_component_ergonomic_registry@1` | frozen ergonomic class vocabulary |
| `ux_component_visibility_contract@1` | per-surface mapping from semantic components to ergonomic classes and visibility duties |
| `ux_ergonomic_candidate_projection_profile_table@1` | finite candidate projection set for ergonomic evaluation |
| `ux_ergonomic_case_envelope@1` | user / device / viewport / input / task / measurement envelope |
| `ux_ergonomic_adjudication_request@1` | bounded request over consumed UX artifacts plus candidate set |
| `ux_ergonomic_adjudication_result@1` | blocked candidates, feasible candidates, preference tiers, ambiguity markers, and obligations |

`V67-A` should ship these as bounded minimum-shape surfaces.

Later `V67-C` may add one bounded advisory bridge pair without reopening the
starter set:

- `ux_ergonomic_runtime_measurement_evidence@1`
- `ux_ergonomic_runtime_bridge_report@1`

Those later-C surfaces should remain replayable and advisory only. They should
not mutate `ux_morph_diagnostics@1` or `ux_conformance_report@1`.

## 6. Candidate Projection Posture

The family must keep the existing approved morph-profile table distinct from the
new candidate projection table.

The existing approved morph-profile table asks:

- which morph-axis tuples are approved for the surface family?

The ergonomic candidate projection table asks:

- which finite geometric / visibility projection shapes may the ergonomic
  adjudicator evaluate for this family?

So candidate profiles may reference the released UX governance artifacts, but they
may not introduce:

- new regions;
- new lanes;
- new action clusters;
- new state-surface semantics;
- new authority posture;
- new trust-boundary or evidence-before-commit law;
- new morph axes not present in `ux_morph_ir@1`.

Every candidate profile should also bind explicitly to:

- `approved_profile_id`;
- `source_artifact_refs`;
- `source_artifact_hashes`;
- released `ux_surface_projection@1` region / lane / action refs only; and
- same-context reveal vocabulary admitted by
  `v36a_same_context_reachability_glossary@1`.

`V67` should start with fixed repo-native candidate shapes, not free-form
reasoning-model proposals.

## 7. Ergonomic Registry Posture

The family needs a frozen ergonomic class vocabulary and a per-surface visibility
contract.

The registry answers:

- which ergonomic classes exist at all?

The visibility contract answers:

- how does this specific surface map its semantic parts into those classes, with
  visibility, collapse, reveal, and targetability claims?

The family should therefore reject:

- unknown ergonomic class IDs;
- widget names used as ergonomic class IDs;
- route-local class names masquerading as ergonomic law;
- incomplete mapping for required constitutional evidence, trust, status, or
  commit-bearing components.

## 8. Measurement And Admissibility Posture

This is the family’s epistemic center.

The adjudicator must keep distinct:

- CSS geometry;
- physical-size estimates;
- visual-angle estimates;
- declared user ergonomic preferences;
- runtime conformance evidence.

Every measured or declared datum should therefore carry:

- provenance state;
- source kind / source ref;
- admissibility level;
- ambiguity severity.

The family should explicitly block:

- physical-size or visual-angle reasoning from DPR-only chains;
- pass/fail claims that rely on unknown or inadmissible dependent inputs;
- decimal “confidence” or “preference” scores being exported as if they were real
  measurement precision.

CSS geometry may remain admissible when physical-size and visual-angle chains are
inadmissible. Inadmissible physical reasoning should not automatically invalidate
the whole adjudication unless the claimed result depends on it.

## 9. Family Slices

### 9.1 `V67-A`

Bounded schema-and-validator starter only.

Owns:

- the seven family artifacts above;
- frozen enums and canonicalization helpers;
- schema export to `spec/`;
- reference fixtures and reject fixtures;
- authority-stack, registry, candidate-profile, and admissibility validators;
- source-hash / lineage binding for starter reference fixtures.

Does not own:

- general layout solving;
- runtime measurement collection;
- continuous runtime personalization;
- screenshot-led adjudication.

### 9.2 `V67-B`

Bounded adjudication engine.

Owns:

- deterministic or nearly deterministic candidate evaluation over the finite
  candidate set;
- hard-blocks with reason codes;
- feasible-set and preference-tier output;
- measurement obligations and ambiguity markers.

Still does not own:

- general responsive-layout synthesis;
- arbitrary candidate generation.

### 9.3 `V67-C`

Advisory runtime / conformance hardening.

Owns:

- bridge from adjudication expectations to realized-measurement evidence;
- one typed advisory bridge report over those measurements;
- non-entitling notices about drift, stale measurement, or unresolved ambiguity.

Still does not own:

- sovereign runtime adaptation engines by default.
- mutation of the released UX-governance diagnostics / conformance schemas by
  default.

## 10. Package Ownership

Expected primary ownership:

- `packages/adeu_core_ir`
  - models, enums, canonicalization, and schemas for the ergonomic family
- later likely `packages/adeu_architecture_compiler` or another deterministic
  compiler/orchestrator home
  - bounded adjudication logic once `V67-B` is selected
- `apps/api/fixtures/ux_ergonomics/`
  - family reference fixtures and reject fixtures.

This should remain an extension of the current `ux_governance` lane, not a new
parallel philosophy stack.
