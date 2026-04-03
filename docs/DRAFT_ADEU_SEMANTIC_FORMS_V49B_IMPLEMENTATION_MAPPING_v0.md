# Draft ADEU Semantic Forms V49B Implementation Mapping v0

Status: support-layer implementation mapping note for `V49-B`.

Authority layer: support only.

This note does not override:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS118.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS117.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`
- `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`

It exists to make the implementation move between the imported prototype parser lane
and the repo-owned `V49-B` module explicit, so the repo neither copies the prototype
blindly nor discards useful grounded recovery work.

## Source And Target

Imported source bundle:

- [examples/external_prototypes/adeu-semantic-forms-v0-bundle](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle)

Primary imported source files:

- [parser.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/parser.py)
- [models.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/models.py)
- [parse_profile.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/parse_profile.py)
- [sample_semantic_parse_result.json](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/samples/sample_semantic_parse_result.json)
- [sample_semantic_parse_result_ambiguous.json](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/samples/sample_semantic_parse_result_ambiguous.json)
- [sample_semantic_parse_result_unsupported.json](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/samples/sample_semantic_parse_result_unsupported.json)

Repo-owned target for `V49-B`:

- `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py`
- `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`
- `packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py`
- `packages/adeu_semantic_forms/tests/`

## Mapping Doctrine

For `V49-B`, implementation should follow four buckets only:

- `carry_forward_nearly_as_is`
- `re_author_with_repo_alignment`
- `defer_to_later_slice`
- `do_not_import`

The prototype remains:

- shaping evidence
- support-only
- `non_precedent`

The repo-owned package remains:

- the only authoritative implementation surface for `V49-B`

## Carry Forward Nearly As-Is

The following prototype decisions are strong enough to preserve with minimal semantic
change in the repo-owned implementation:

1. Recovery decomposition:
   - normalize input text first;
   - recover only through the admitted parse profile;
   - build candidates only through released `V49-A` normal forms.
2. Outcome family:
   - `resolved_singleton`
   - `typed_alternatives`
   - `clarification_required`
   - `rejected_unsupported`
3. Unsupported-pattern posture:
   - whole-phrase or token-bounded unsupported-pattern detection is preferable to raw
     substring matching.
4. Starter recovery helper families:
   - scope-anchor collection
   - policy-anchor collection
   - worker-anchor collection
   - mutation lexicon collection
   - artifact-kind lexicon collection
   - effect lexicon collection
   - bounded repo-path extraction for `allow_path` hints
5. Sample artifact families:
   - one singleton parse result
   - one ambiguous parse result
   - one rejected unsupported parse result
   - these should remain grounding examples for repo-owned fixtures after
     normalization.

## Re-Author With Repo Alignment

The following should be implemented repo-natively, even when grounded strongly in the
prototype:

1. Parser ownership and imports:
   - use `adeu_semantic_forms`, not `adeu_semantic_forms_v0`;
   - consume the released repo-owned `V49-A` models directly.
2. Candidate distinctness and ordering:
   - dedupe by released `normal_form.semantic_hash` only;
   - sort deduped candidates deterministically by semantic hash before assigning
     `candidate_rank`;
   - do not preserve prototype ordering merely because the prototype used cartesian
     product order.
3. Clarification posture:
   - clarification must emit zero candidates only;
   - unresolved candidate shells are not allowed in repo-owned `V49-B`.
4. Alias / anchor precedence:
   - exact released `anchor_id` or exact-phrase alias before normalized alias;
   - partial matches are support evidence only;
   - equal-strength conflicts must fail closed rather than pick a silent winner.
5. Identity-versus-projection split:
   - preserve the released `V49-A` identity law exactly;
   - keep `evidence_summary`, ambiguity notes, and notices support-only;
   - ensure parser explanations never affect candidate sameness.
6. Diagnostic structure:
   - emit only released ambiguity entries, rejected reason codes, and notices;
   - do not let ad hoc parser internals become new schema.
7. Repo-owned tests and fixtures:
   - normalize prototype sample cases into committed repo fixtures;
   - add explicit regressions for:
     - semantic-hash dedupe
     - deterministic alternative ordering
     - clarification zero-candidate posture
     - alias conflict fail-closed behavior

## Defer To Later Slice

The following prototype content is useful, but should not ship in `V49-B`:

1. [transform_v48_seed.py](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree/adeu_semantic_forms_v0/src/adeu_semantic_forms_v0/transform_v48_seed.py)
   - defer to `V49-C` / `V49-D`
   - this is downstream deterministic lowering, not recovery.
2. `TaskpackBindingSpecSeed`
   - defer to `V49-C` / `V49-D`
   - no `V48` bridge artifact belongs in `V49-B`.
3. Broader scoring or confidence heuristics:
   - defer richer ranking beyond deterministic hash ordering;
   - `V49-B` only needs bounded recovery, not open-ended parser confidence systems.
4. Multi-domain or multi-profile recovery:
   - defer to later family work if ever selected.
5. CLI, API, or web consumers:
   - defer until the parser lane is released and stable.

## Do Not Import

The following should not be imported into the repo-owned implementation as authority:

1. The entire prototype parser tree copied wholesale into live package paths.
2. Prototype package naming:
   - `adeu_semantic_forms_v0`
3. Prototype hard-coded defaults as live authority:
   - default worker subject strings
   - default mutation posture strings
   - default artifact-kind strings
   - these may inform fixtures, but must not silently become repo law without an
     explicit repo-owned decision.
4. Prototype candidate ordering based on incidental generation order.
5. Prototype sample hashes or IDs as if they were already accepted repo fixtures
   without normalization.
6. Any implied precedent that the prototype parser heuristics are authoritative merely
   because they exist.

## File-Level Mapping

| Imported source | `V49-B` action | Repo-owned target |
|---|---|---|
| `.../parser.py` | preserve decomposition, re-author semantics | `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py` |
| `.../models.py` | consume released repo-owned contracts | `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py` |
| `.../parse_profile.py` | consume released repo-owned profile helpers | `packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py` |
| `.../samples/sample_semantic_parse_result*.json` | selectively normalize | `packages/adeu_semantic_forms/tests/fixtures/` |
| `.../transform_v48_seed.py` | defer | `V49-C` / `V49-D` only |

## Concrete Reuse Decision For `V49-B`

The implementation should preserve nearly as-is:

- the profile-bound recovery decomposition
- the four-outcome family
- whole-phrase unsupported-pattern matching posture
- the starter sample families for singleton / ambiguous / unsupported cases

The implementation should re-author:

- parser ownership inside `adeu_semantic_forms`
- candidate distinctness and deterministic ordering
- alias/anchor precedence
- clarification zero-candidate posture
- explicit tests proving support-only fields do not affect candidate identity

The implementation should defer:

- deterministic lowering into `V48` seed artifacts
- richer scoring systems
- multi-domain and multi-profile recovery
- product consumers

The implementation should not import:

- the prototype tree wholesale
- prototype hard-coded defaults as live law
- prototype sample outputs as unreviewed accepted fixtures

## Immediate Implementation Use

During `V49-B` implementation, this note should be used as the concrete answer to:

- what recovery structure we preserve from the prototype
- what we re-author in repo-owned parser code
- what stays deferred to `V49-C` / `V49-D`
- what we explicitly refuse to treat as live parser authority
