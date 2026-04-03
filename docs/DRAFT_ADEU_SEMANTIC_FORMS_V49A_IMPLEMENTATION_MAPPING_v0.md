# Draft ADEU Semantic Forms V49A Implementation Mapping v0

Status: support-layer implementation mapping note for `V49-A`.

Authority layer: support only.

This note does not override:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS117.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`
- `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`

It exists to make the implementation move between the imported prototype and the
repo-owned `V49-A` module explicit, so the repo neither copies the prototype blindly
nor ignores useful grounded work.

## Source And Target

Imported source bundle:

- [examples/external_prototypes/adeu-semantic-forms-v0-bundle](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle)

Primary imported source files:

- [models.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/models.py)
- [parse_profile.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/parse_profile.py)
- [parser.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/parser.py)
- [transform_v48_seed.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/transform_v48_seed.py)

Repo-owned target for `V49-A`:

- `packages/adeu_semantic_forms/pyproject.toml`
- `packages/adeu_semantic_forms/src/adeu_semantic_forms/__init__.py`
- `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`
- `packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py`
- `packages/adeu_semantic_forms/tests/`

## Mapping Doctrine

For `V49-A`, implementation should follow four buckets only:

- `carry_forward_nearly_as_is`
- `re_author_with_repo_alignment`
- `defer_to_later_slice`
- `do_not_import`

The prototype remains:

- shaping evidence
- support-only
- `non_precedent`

The repo-owned package remains:

- the only authoritative implementation surface for `V49-A`

## Carry Forward Nearly As-Is

The following prototype decisions are strong enough to preserve with minimal semantic
change in the repo-owned implementation:

1. Starter domain:
   - `repo_policy_work`
2. Parse-result outcome vocabulary:
   - `resolved_singleton`
   - `typed_alternatives`
   - `clarification_required`
   - `rejected_unsupported`
3. Starter relation vocabulary:
   - `bind_scope_anchor`
   - `bind_policy_anchor`
   - `use_worker_subject`
   - `set_mutation_posture`
   - `allow_path`
   - `forbid_path`
   - `forbid_effect`
   - `produce_artifact_kind`
4. Starter lane-tag vocabulary:
   - `scope`
   - `policy`
   - `worker`
   - `mutation`
   - `constraint`
   - `deliverable`
5. Starter object-kind vocabulary:
   - `scope_anchor`
   - `policy_anchor`
   - `worker_subject`
   - `mutation_posture`
   - `repo_rel_path`
   - `effect_tag`
   - `artifact_kind`
6. Canonical normal-form identity basis:
   - semantic identity is driven by `relation_kind` plus `object_value`
   - canonicalization sorts and deduplicates on that basis
   - evidence does not affect semantic identity
7. Core schema-family names already present in the prototype:
   - `adeu_semantic_parse_profile@1`
   - `adeu_semantic_normal_form@1`
   - `adeu_semantic_parse_result@1`
   - `adeu_semantic_transform_contract@1`

## Re-Author With Repo Alignment

The following should be implemented repo-natively, even when grounded strongly in the
prototype:

1. Package identity and layout:
   - rename package ownership from `adeu_semantic_forms_v0` to `adeu_semantic_forms`
   - add repo-owned `pyproject.toml`
   - place code and tests under `packages/adeu_semantic_forms`
2. Starter statement-core contract:
   - split the prototype’s `SemanticClause` concept into the lock-selected contract
     surface `adeu_semantic_statement_core@1`
   - keep its field content grounded in the prototype, but make the statement-core
     contract explicit rather than only nested inside normal form
3. Canonical hash law:
   - preserve the prototype’s identity basis
   - make the identity-field versus projection-field split explicit in the repo-owned
     model and tests
   - document exactly which fields are excluded from semantic identity
4. Semantic-equivalence doctrine:
   - preserve the prototype’s canonicalization direction
   - re-author it in repo-owned code and tests so equivalence is frozen by the module,
     not merely implied by the prototype
5. Parse-profile builders and fixtures:
   - preserve the prototype’s anchor structure and starter-domain shape where valid
   - move accepted examples into repo-owned committed fixtures or fixture builders
   - avoid treating prototype snapshot IDs or refs as permanent authority unless they
     remain valid in the repo
6. Test suite:
   - convert sample-oriented proof into repo-native tests for:
     - model validation
     - canonical hash stability
     - identity-field versus projection-field behavior
     - accepted/reject fixture replay

## Defer To Later Slice

The following prototype content is useful, but should not ship in `V49-A`:

1. [parser.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/parser.py)
   - defer to `V49-B`
   - includes actual `NL -> ADEU` recovery behavior
2. Lowering behavior in [transform_v48_seed.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/transform_v48_seed.py)
   - defer to `V49-C` / `V49-D`
   - includes actual deterministic lowering into a `V48`-adjacent seed
3. `TaskpackBindingSpecSeed`
   - defer to later slice
   - this is already downstream of the substrate contract
4. `SemanticTransformResult`
   - defer to later slice
   - this is behavior/result surface, not `V49-A` contract-only surface
5. Concrete unsupported text-pattern matching behavior
   - defer to `V49-B`
   - `V49-A` freezes unsupported posture and starter out-of-scope constructs, not
     input-text heuristics

## Do Not Import

The following should not be imported into the repo-owned implementation as authority:

1. The entire prototype tree copied wholesale into live package paths.
2. Prototype package naming:
   - `adeu_semantic_forms_v0`
3. Prototype sample files as if they were already accepted repo fixtures without
   review and normalization.
4. Prototype parser heuristics as if they were substrate law.
5. Prototype unsupported-pattern strings as if they were the lock-level unsupported
   doctrine for `V49-A`.
6. Any implied precedent that the prototype’s bundled code or sample outputs are
   authoritative merely because they exist.

## File-Level Mapping

| Imported source | `V49-A` action | Repo-owned target |
|---|---|---|
| `.../models.py` | split and re-author | `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py` |
| `.../parse_profile.py` | preserve structure, re-author builder/fixtures | `packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py` plus tests/fixtures |
| `.../parser.py` | defer | `V49-B` only |
| `.../transform_v48_seed.py` | keep contract concept now, defer lowering behavior | `V49-A` contract subset in `models.py`; lowering to `V49-C/D` |
| `.../samples/*.json` | selectively normalize | `packages/adeu_semantic_forms/tests/fixtures/` |

## Concrete Reuse Decision For `V49-A`

The implementation should preserve nearly as-is:

- the starter domain
- the relation/lane/object vocabularies
- the parse-result outcome vocabulary
- the normal-form identity basis over `relation_kind` and `object_value`

The implementation should re-author:

- package structure
- schema-family ownership
- explicit `statement_core` contract
- explicit hash-law tests
- explicit accepted/reject fixture set

The implementation should defer:

- parser behavior
- input-text unsupported-pattern behavior
- lowering into `V48` seed artifacts
- transform results and blocking results

The implementation should not import:

- the prototype tree wholesale
- the prototype package name
- the prototype samples as unreviewed live fixtures

## Immediate Implementation Use

During `V49-A` implementation, this note should be used as the concrete answer to:

- what we preserve from the prototype
- what we re-author in repo-owned code
- what we intentionally leave for `V49-B`, `V49-C`, and `V49-D`
- what we explicitly refuse to treat as live authority
