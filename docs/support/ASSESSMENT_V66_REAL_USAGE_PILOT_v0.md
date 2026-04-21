# V66 Real-Usage Pilot Assessment v0

Authority layer: support only.

## Purpose

Record a bounded real-usage pilot over shipped `V66-A` / `V66-B` / `V66-C`
entrypoints so GPTPro can review actual emitted artifacts instead of only the
family docs and test fixtures.

## Pilot Setup

The pilot ran in a temporary workspace copied from real repo docs, with only
the minimum extra scaffolding added locally for one companion overlay and two
generated reader projections.

Real-doc cohort:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS184.md`
- `docs/ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v51.md`
- `docs/support/anm.adeu.md`

Added only for the pilot:

- `docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS184.anm.adeu.md`
- `docs/generated/anm_reader/LOCKED_CONTINUATION_vNEXT_PLUS184.reader.md`
- `docs/generated/anm_reader/anm.reader.md`

## What Was Run

The pilot used the shipped library surfaces directly:

- `adeu_semantic_compiler.check_v66a_anm_source_set(...)`
- `adeu_semantic_compiler.check_v66b_anm_migration_projection(...)`
- `adeu_semantic_compiler.check_v66c_anm_adoption_hardening(...)`

No repo files were modified as part of the pilot run.

## Main Outcome

The live pilot executed cleanly and emitted the full `V66` artifact chain:

- `anm_source_set_manifest@1`
- `anm_doc_authority_profile@1`
- `anm_doc_class_policy@1`
- `anm_migration_binding_profile@1`
- `anm_reader_projection_manifest@1`
- `anm_semantic_diff_report@1`
- `anm_prose_boundary_notice_set@1`
- `anm_compile_report@1`

## Assessment

### What looks good

- `V66-A` behaved correctly on real docs.
  - discovered inventory included the copied live docs plus generated reader
    files
  - governed source set excluded generated reader projections
  - class/posture classification came out sane across lock / architecture /
    planning / support and legacy / companion / standalone postures
- `V66-B` behaved correctly on the pilot cohort.
  - one live lock doc carried a bounded non-overriding companion overlay
  - reader-projection rows emitted with explicit status and drift posture
  - semantic diff emitted deterministically across source-set, authority
    profile, class-policy, migration-binding, and reader-projection surfaces
- `V66-C` produced useful advisory output instead of generic noise.
  - `report_status = valid`
  - recommended posture was
    `needs_projection_refresh`
  - reason code was
    `ANM_V66C_NEEDS_PROJECTION_REFRESH`
  - notice kinds were exactly:
    - `normative_tone_without_compiled_authority_block`
    - `projection_staleness_visible`
  - the pilot `example_block` and `quoted_text` samples did not create
    false-positive notice rows

### Practical gaps

- The family is still library-first, not workflow-first.
  - there is no polished repo-facing runner for maintainers to use in daily
    doc work
- The first `V66-B` semantic diff is structurally correct but verbose for human
  review.
  - useful for determinism
  - still heavy as a human-facing review surface
- Direct library execution still emits the known Pydantic `schema` shadow
  warnings from older model families.
  - not a correctness failure here
  - still undesirable if this becomes a routine workflow

## Current Judgment

The family works on live docs, not just on fixtures.

The strongest result is that `V66-C` stayed specific and bounded in a real-doc
pilot:

- it surfaced a stale generated reader projection
- it surfaced one normative-tone warning in plain prose
- it did not overread example or quoted text into policy
- it did not promote advisory output into authority

So the main next question is no longer whether the `V66` family is coherent.
The main next question is whether to productize the workflow with a
maintainer-facing runner and better human review surfaces.
