# Draft ADEU ANM Native Documentation Practice V66C Implementation Mapping v0

Status: support note for the `V66-C` implementation pass after `V66-B` closure
on `main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a bounded
`V66-C` slice should evaluate the shipped governed ANM source-set, authority,
migration, reader-projection, and semantic-diff lineage for advisory adoption
hardening without mutating source discovery, migration binding, reader
projection authority, semantic-diff baseline law, markdown supersession law, or
`V47` ANM source semantics by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v51.md`
- `docs/ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V47` ANM / `D@1` language, IR, checker, evaluator, and ledger
  substrate
- shipped `V66-A`:
  - `anm_source_set_manifest@1`
  - `anm_doc_authority_profile@1`
  - `anm_doc_class_policy@1`
- shipped `V66-B`:
  - `anm_migration_binding_profile@1`
  - `anm_reader_projection_manifest@1`
  - `anm_semantic_diff_report@1`
- the rule that current markdown remains controlling unless explicit lock-level
  transition law says otherwise
- the rule that generated reader projections remain non-authoritative and
  excluded from governed ANM source by construction
- the rule that semantic diff remains explicit-baseline and non-authoritative
- the rule that prose outside recognized authority blocks does not compile into
  policy by implication

## Re-Author With Repo Alignment

Candidate new advisory surfaces:

- `anm_compile_report@1`
- `anm_prose_boundary_notice_set@1`

Those surfaces should remain advisory-only in this slice.

They should decide only whether the exact shipped `V66-A` / `V66-B` ANM-native
documentation path deserves later migration cleanup, projection refresh,
transition-law clarification, or broader adoption review, while keeping:

- no fresh governed source-set widening
- no fresh source discovery contract
- no fresh authority-profile contract
- no fresh class-policy contract
- no fresh migration-binding authority
- no fresh reader-projection authority
- no fresh semantic-diff baseline law
- no markdown supersession by advisory output
- no generated-reader promotion into source authority
- no prose-to-policy laundering
- no reopening of `V47` language / IR / checker ownership

`V66-C` should keep explicit:

- the selected advisory target is the shipped exact `V66-A` / `V66-B` lineage
  only:
  - one shipped governed source set only
  - one shipped authority-profile set only
  - one shipped class-policy surface only
  - one shipped migration-binding profile only
  - one shipped reader-projection manifest only where selected
  - one shipped semantic-diff report only where selected
- committed lane artifacts outrank narrative prose when the advisory report or
  notice set is derived
- every emitted advisory artifact should carry exact consumed-basis refs and
  hashes for the shipped `V66-A` / `V66-B` lineage
- the compile report carries one explicit frozen-policy anchor:
  - `policy_anchor_ref`
  - `policy_anchor_hash`
  - `policy_anchor_schema_id`
  - `advisory_outcome_reducer_ref`
  - `advisory_outcome_reducer_hash`
  - `notice_detection_policy_ref`
  - `notice_detection_policy_hash`
- the advisory function remains extensional and replayable:
  - same shipped `V66-A` basis
  - same shipped `V66-B` basis
  - same selected prose-boundary evidence
  - same frozen policy anchor
  - same advisory outcome
- evidence basis remains distinct from advisory outcome
- `report_status` remains distinct from `recommended_adoption_posture`:
  - structural invalidity blocks the advisory outcome
  - the recommendation is only meaningful when `report_status == valid`
- generated reader projection and semantic diff remain shaping inputs only:
  - not source authority
  - not migration authority
  - not supersession law
- prose-boundary notices remain evidence-bound:
  - recognized authority blocks stay compiler-recognized only
  - example text, quoted blocks, and reader projections do not become compiled
    policy by tone or proximity
- current markdown remains controlling unless an explicit shipped lock-level
  transition law already says otherwise
- `needs_more_registration`, `needs_projection_refresh`,
  `needs_transition_law_review`, and
  `candidate_for_later_markdown_transition_review` remain non-entitling and
  non-escalating by themselves
- `current_guardrails_sufficient` records negative selection on current evidence

Recommended decision vocabulary:

- allowed:
  - `current_guardrails_sufficient`
  - `needs_more_registration`
  - `needs_projection_refresh`
  - `needs_transition_law_review`
  - `candidate_for_later_markdown_transition_review`
- forbidden:
  - `promote_now`
  - `supersede_now`
  - `authorize_now`
  - `compile_policy_from_prose_now`

Recommended notice vocabulary:

- `normative_tone_without_compiled_authority_block`
- `projection_staleness_visible`
- `generated_projection_authority_overread_risk`
- `transition_law_scope_ambiguity`
- `class_policy_overpromotion_risk`

## Do Not Import

- source-of-truth transition by advisory artifact alone
- generated-reader promotion into governed source
- semantic-diff promotion into lock law
- prose-tone inference as compiled policy
- new `D@1` semantics
- selector or predicate ownership widening
- repo-wide rename pressure as authority by itself

## Starter field-shape direction

Minimum `anm_compile_report@1` direction:

- `schema_id`
- `compile_report_id`
- `report_status`
- `consumed_lineage`
- `policy_anchor`
- `diagnostic_rows`
- `advisory_result`

Minimum `anm_prose_boundary_notice_set@1` direction:

- `schema_id`
- `notice_set_id`
- `report_status`
- `consumed_lineage`
- `policy_anchor`
- `notice_rows`

Required consumed-lineage fields:

- exact `V66-A` source-set ref and hash
- exact `V66-A` authority-profile set ref or hash
- exact `V66-A` doc-class policy ref and hash
- exact `V66-B` migration-binding profile ref and hash
- exact `V66-B` reader-projection manifest ref and hash where selected
- exact `V66-B` semantic-diff report ref and hash where selected

Recommended `report_status` starter enum:

- `valid`
- `invalid_missing_prior_basis`
- `invalid_prior_basis_hash_mismatch`
- `invalid_policy_anchor`
- `invalid_unsupported_schema`
- `invalid_notice_evidence`
- `invalid_authority_claim_rejected`
