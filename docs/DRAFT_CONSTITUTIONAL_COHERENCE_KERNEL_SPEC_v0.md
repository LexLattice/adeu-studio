# Draft Constitutional Coherence Kernel Spec v0

Status: planning draft for `V55-A`.

Authority layer: planning.

This document defines the bounded first-pass checker role for the `V55` family. It is
not a lock doc and does not authorize runtime behavior, schema release, or CI gating by
itself.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v38.md`
- `docs/ARCHITECTURE_ADEU_DOMAIN_SUBSTRATE_FAMILY_v0.md`
- `docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md`
- `docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md`

## 1. Direct Answer

The first constitutional coherence kernel should be a thin deterministic checker that:

- reads only explicit structured claims from one admitted seed artifact set;
- evaluates one closed predicate set;
- emits warning-level coherence findings and unresolved seams; and
- proves that a small promoted stack can be checked mechanically without pretending
  that support prose alone already governs implementation.

It should not be an open-ended reviewer or meta-reasoner.

## 2. Bounded Role

The kernel owns:

- structured-claim extraction from admitted artifacts;
- admission-record validation;
- closed-predicate evaluation;
- warning-level report emission; and
- unresolved-seam register emission.

The kernel does not own:

- generic prose interpretation;
- descendant runtime behavior;
- automatic promotion of support doctrine;
- general theorem proving; or
- repo-wide gating in `V55-A`.

## 3. Exact Seed Artifact Set

The first admitted seed set is:

- `docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md`
- `docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md`
- `docs/support/ADEU_SCHEMA_META_GRAMMAR.md`
- `docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED.md`
- `docs/support/ODEU_MEMBRANE_ARCHITECTURE.md`
- `docs/support/crypto data spec2.md`

Each admitted artifact must carry or be paired with one admission declaration that
states:

- `constitutional_support_admission_record@1`
- `authority_layer`
- `current_authority_relation`
- `allowed_kernel_use`
- `forbidden_inference`
- `later_promotion_requirement`

## 4. Structured Input Contract

`V55-A` must be deterministic over structured claims only.

The first bounded checker should read only:

- explicit document headers;
- explicit JSON records or blocks;
- explicit refs;
- explicit witness refs; and
- explicit family or descendant declarations.

Free text may explain, but only declared structured surfaces are checker-authoritative.

Malformed designated structured blocks should fail closed into checker findings.
Malformed non-designated free text should not become authoritative input merely because
it resembles one.

## 5. Closed Predicate Set

The initial predicate set is:

- `authority_layer_declared`
- `authority_relation_legal`
- `placement_basis_present_when_required`
- `coverage_scope_present_when_required`
- `dominant_force_band_resolved`
- `promotion_claim_has_witness`
- `descendant_claim_within_parent_entitlement`
- `projection_does_not_mint_authority`
- `support_surface_not_self_promoted`

Starter interpretation posture:

- predicates are closed and named ahead of execution;
- no additional predicate classes are invented at runtime;
- a predicate may emit `pass`, `warn`, or `unresolved`, but not mint new authority;
- predicate expansion beyond this set is deferred to later family selection.

## 6. Output Contract

`V55-A` should emit at least:

- one coherence report shape:
  - `constitutional_coherence_report@1`
- one unresolved seam register:
  - `constitutional_unresolved_seam_register@1`
- one lane handoff/drift record shape for later-lane amendment checks:
  - `constitutional_coherence_lane_drift_record@1`

The coherence report should minimally record:

- checked artifact refs;
- predicate results;
- warning findings;
- unresolved findings; and
- descendant-trial posture when applicable.

The unresolved seam register should minimally record:

- seam id;
- source artifact;
- reason class;
- current posture; and
- later promotion or amendment requirement.

## 7. Descendant Trial Default

The default descendant trial input is:

- `docs/support/crypto data spec2.md`

Trial posture in `V55-A`:

- support-surface mode only;
- no runtime implementation;
- no descendant release promotion by trial success alone.

## 8. Failure And Governance Posture

The kernel should:

- fail closed on malformed designated structured claims;
- remain warning-only in `V55-A`;
- treat unresolved posture explicitly rather than laundering it into pass; and
- remain deterministic under fixed repo state and checker version.

The kernel should not:

- become a CI gate in `V55-A`;
- infer hidden authority from prose;
- treat support artifacts as self-promoting; or
- widen into multi-descendant evaluation in the starter slice.

## 9. `V55-A` Acceptance

`V55-A` should be considered complete only when:

- `packages/adeu_constitutional_coherence` exists;
- one warning-only checker exists;
- the structured-input-only contract is explicit in code and docs;
- the exact seed artifact set is declared;
- one coherence report shape exists;
- one unresolved seam register exists;
- one descendant trial runs in support-surface mode only; and
- no CI gating or autonomous prose interpretation has been introduced.

## 10. Machine-Checkable Seed Summary

```json
{
  "schema": "constitutional_coherence_kernel_spec@1",
  "artifact": "docs/DRAFT_CONSTITUTIONAL_COHERENCE_KERNEL_SPEC_v0.md",
  "status": "draft",
  "authority_layer": "planning",
  "warning_only_checker_required": true,
  "structured_input_only": true,
  "exact_seed_artifact_set_declared": true,
  "closed_predicate_set_declared": true,
  "coherence_report_required": true,
  "unresolved_seam_register_required": true,
  "preferred_descendant_trial": "docs/support/crypto data spec2.md",
  "ci_gating_selected": false,
  "autonomous_prose_interpretation_selected": false
}
```
