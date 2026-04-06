# DRAFT ADEU Edge Ledger Proto v0

## Intent and bounded placement

This draft proposes a bounded **logical edge ledger** proto-module for ADEU Studio.

The proto is intentionally **downstream of the released V45 repo-description substrate and the released V50 symbol-audit substrate**.
It does **not** reopen those contracts.
It consumes their outputs as already-bounded descriptive inputs and adds a new, read-only layer for explicit edge-space accounting.

Selected home:

- `packages/adeu_edge_ledger`

This package is the most repo-native bounded home because:

1. `packages/adeu_repo_description` (`V45`) already owns repo self-description artifacts and test/symbol identity conventions.
2. `packages/adeu_symbol_audit` (`V50-A` through `V50-C`) already owns the bounded pilot scope, symbol census, coverage closure, semantic audit, and helper session family.
3. The new concern is **adjacent but not identical** to symbol audit:
   - symbol audit says *what symbols exist* and *what they appear to do*;
   - edge ledger says *which abstract edge classes apply*, *what status they hold*, and *whether new witnesses expand the taxonomy*.
4. Keeping it in a new adjacent package preserves the release boundary of `V45` and `V50` while still staying close enough to consume their artifacts directly.

The package therefore acts as a **consumer / extender of descriptive substrate**, not as a fork of upstream semantics.

## Problem statement

Current model-based review often finds edge witnesses opportunistically.
That is useful, but it leaves the larger edge space implicit.
Without an explicit ledger, each review resets to latent intuition.

The proto addresses that gap by introducing:

1. an explicit catalog of abstract edge classes;
2. a bounded applicability frame per symbol;
3. a bounded adjudication ledger per symbol;
4. an explicit revision judgment artifact for taxonomy growth.

The main architectural move is:

- **constant layer**: stable edge families, applicability cues, probe archetypes, status vocabularies, and revision doctrine;
- **variable layer**: symbol-local applicability, coverage status, structural safety posture, underdetermination, and revision evidence.

## Relationship to V45 and V50

### V45 relationship

The proto borrows and respects the V45 descriptive posture:

- typed artifacts with stable schema ids;
- canonical hashing / deterministic ids;
- explicit epistemic posture instead of hidden authority claims;
- repo-native identity shapes such as `symbol:` and `test:` refs;
- schema export into both package-local `schema/` and repo-level `spec/` mirrors.

The proto does **not** modify V45 artifact meanings.
It only reuses the same descriptive discipline.

### V50 relationship

The proto treats the released V50 family as upstream input:

- `scope manifest`
- `symbol census`
- `coverage report`
- `semantic audit`
- helper/session conventions as nearby ownership context

The applicability/adjudication flows deliberately require the V50 stack to remain reconciled and `closed_clean` before they proceed.
That keeps edge-ledger derivation bounded to the same admitted scope rather than drifting into unconstrained repo-wide claims.

## Shipped artifact family

The proto introduces five typed artifact families.

### 1. `adeu_edge_class_catalog@1`

The stable starter taxonomy.
This is the constant-layer ledger of known abstract edge classes.

### 2. `adeu_edge_probe_template_catalog@1`

A stable catalog of probe/check archetypes.
This is intentionally not reduced to one testing philosophy.
A probe template can point toward example tests, property-based checks, metamorphic replay, dependency fault injection, or review-only adjudication.

### 3. `adeu_symbol_edge_applicability_frame@1`

A symbol-local frame over the stable taxonomy.
For each archetype edge class, it records:

- `applicable`
- `not_applicable`
- `underdetermined`

plus matched cues, concrete bindings, probe suggestions, and epistemic posture.

### 4. `adeu_symbol_edge_adjudication_ledger@1`

A bounded symbol-local status ledger over the applicability frame.
It distinguishes:

- `not_applicable`
- `applicable_unchecked`
- `covered_by_existing_tests`
- `checked_no_witness_found`
- `bounded_safe_by_structure`
- `witness_found`
- `underdetermined`
- `deferred`

This keeps the output explicitly advisory.
It does **not** claim that “no witness found” means globally safe.

### 5. `adeu_edge_taxonomy_revision_judgment@1`

A first-class artifact for deciding whether a newly found edge:

- is just an instance of an existing class;
- merits a new specialization;
- implies a split;
- requires a new sibling or intermediate node;
- or forces a new top-level family.

This is the compounding mechanism that turns edge review into a cumulative ledger instead of repeated witness sampling.

## Starter taxonomy structure

The shipped starter taxonomy uses **three levels**:

- **family**
- **subfamily**
- **archetype**

Current starter shape:

- 8 families
- 16 subfamilies
- 25 archetypes

### Families

1. `input_domain`
2. `boundary_order`
3. `control_partition`
4. `state_sequence`
5. `canonicalization_representation`
6. `contract_invariant`
7. `dependency_boundary`
8. `failure_path`

### Representative subfamilies and archetypes

Examples include:

- `input_domain / absence_nullability / none_missing_input`
- `input_domain / cardinality_shape / empty_collection_or_text`
- `boundary_order / numeric_interval / inclusive_exclusive_boundary`
- `boundary_order / ordering_permutation / stable_ordering_preservation`
- `control_partition / branch_exhaustiveness / unhandled_variant`
- `control_partition / guard_short_circuit / guard_before_side_effect`
- `state_sequence / mutation_aliasing / shared_reference_aliasing`
- `state_sequence / temporal_reentry / repeat_application_idempotence`
- `canonicalization_representation / normalization_canonical_form / path_or_text_normalization`
- `canonicalization_representation / serialization_identity / round_trip_serialization`
- `contract_invariant / cross_field_binding / source_ref_matches_scope`
- `contract_invariant / vocabulary_order_identity / ordered_unique_sequence_invariant`
- `dependency_boundary / filesystem_external_tool / git_command_failure_surface`
- `dependency_boundary / parse_validation_boundary / schema_validation_rejection`
- `failure_path / rejection_fail_closed / fail_closed_on_mismatch`
- `failure_path / fallback_underdetermination / no_silent_repair`

This taxonomy is not presented as complete software ontology.
It is a **serious starter ledger** intended to compound over time.

## Applicability derivation flow

`packages/adeu_edge_ledger/src/adeu_edge_ledger/applicability.py` derives a symbol-local applicability frame.

Inputs:

- released V50 census / coverage / semantic audit
- verified repo source text for the admitted scope
- starter edge-class catalog
- starter probe-template catalog

Signals are gathered from:

- symbol names and signatures;
- AST features such as comparisons, raises, branches, assignments, IO calls, subprocess calls, normalization calls, hash/id calls;
- annotations and field names;
- V50 semantic-audit features such as `side_effect_profile`, likely canonical family, decorators, and base classes.

Each archetype edge node carries:

- required cue tags;
- supporting cue tags;
- structural-safety cue tags;
- suggested probe templates;
- test-token tags.

The frame does **not** claim complete truth.
It explicitly marks many cases as `underdetermined` when only partial cues are present.

## Adjudication flow

`packages/adeu_edge_ledger/src/adeu_edge_ledger/adjudicate.py` layers bounded status judgment over the applicability frame.

Current shipped adjudication sources are deliberately narrow:

1. the applicability frame itself;
2. package-local test scanning using repo-native `test:` refs;
3. structural-safety cues from the taxonomy;
4. upstream V50 semantic-audit confidence posture;
5. optional explicit probe outcomes supplied by the caller.

The flow is conservative:

- `not_applicable` remains `not_applicable`;
- `underdetermined` remains `underdetermined`;
- applicable + matching package-local tests -> `covered_by_existing_tests`;
- applicable + structural-safety cues + non-low-confidence audit -> `bounded_safe_by_structure`;
- applicable + side-effect / low-confidence posture without covering test -> `deferred`;
- applicable + neither coverage nor structural closure -> `applicable_unchecked`;
- caller-supplied witness -> `witness_found`;
- caller-supplied checked-without-witness -> `checked_no_witness_found`.

This keeps the package read-only and epistemically explicit.
There is no hidden claim that green means globally safe.

## Revision doctrine

`packages/adeu_edge_ledger/src/adeu_edge_ledger/revision.py` implements a first-class revision judgment.

Inputs include:

- nearest existing edge-class refs;
- observed symbol ids;
- applicability cue tags;
- probe signature tags;
- applicability-pattern distinctness;
- probe-pattern distinctness;
- whether the phenomenon is representable without information loss inside the existing ledger;
- reuse posture (`single_symbol`, `multi_symbol_candidate`, `recurrent_pattern`);
- evidence count.

### Core doctrine

The decision tree uses the following criteria:

1. **Representability without information loss**
   - if yes and the distinction is only `same` or `attribute_refinement_only`, the case stays an `instance_of_existing_class`;
   - if yes but the pattern is repeatedly adjacent and probe-distinct, the system may allow `specialize_under_existing_class`.

2. **Applicability/probe-pattern distinctness**
   - `same` or `attribute_refinement_only` argues against taxonomy growth;
   - `distinct` is a strong signal that an existing class is compressing too much.

3. **Reuse across multiple symbols**
   - one-off single-symbol findings default toward `defer_candidate`;
   - multi-symbol or recurrent patterns can justify new nodes.

4. **Topology of nearest refs**
   - same parent -> `new_sibling_under_existing_parent`;
   - same family but more distant common ancestor -> `new_intermediate_node`;
   - one overloaded nearest archetype with strong recurrent distinctness -> `split_existing_class`;
   - multiple independent families -> `new_top_level_family`.

5. **Maturity posture**
   - new classes default to `candidate` unless the evidence is recurrent and stronger;
   - stabilized only when evidence count and reuse posture justify it;
   - split decisions mark lifecycle as `split`.

This is the core compounding doctrine for deciding whether the ledger grows.

## Pilot behavior over released V50 scope

The shipped tests keep the scope intentionally narrow by reusing the released architecture-ir pilot already admitted by V50.

That pilot is sufficient to demonstrate all of the following statuses inside a real repo slice:

- `covered_by_existing_tests`
- `bounded_safe_by_structure`
- `applicable_unchecked`
- `deferred`
- `underdetermined`
- `not_applicable`

This bounded demonstration is important: the proto is real, but it does not pretend to be a whole-repo semantic reviewer platform.

## File map

### Package code

- `packages/adeu_edge_ledger/src/adeu_edge_ledger/models.py`
  - typed artifact family, ids, hashes, status vocabularies
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/taxonomy.py`
  - three-level starter taxonomy and probe template catalog
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/applicability.py`
  - deterministic / heuristic applicability derivation over V50 inputs
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/adjudicate.py`
  - bounded status ledger over applicability frames
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/revision.py`
  - taxonomy expansion doctrine and revision judgments
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/export_schema.py`
  - schema export to package-local `schema/` and repo-level `spec/`

### Schemas

- `packages/adeu_edge_ledger/schema/*.v1.json`
- `spec/adeu_*edge*.schema.json`

### Tests and fixtures

- `packages/adeu_edge_ledger/tests/conftest.py`
- `packages/adeu_edge_ledger/tests/test_edge_ledger_*.py`
- `packages/adeu_edge_ledger/tests/fixtures/v0/*.json`

## Deliberate non-goals and deferrals

This proto deliberately does **not** do the following:

- mutate code;
- claim global edge completeness;
- replace V45 or V50;
- widen CI, API, or runtime surfaces broadly;
- run a broad probe execution platform;
- infer that “no witness found” means safe in general;
- convert underdetermined cases into false certainty.

Deferred areas include:

- richer integration with V45 test-intent matrices;
- explicit witness registries from real probe execution back-ends;
- cross-symbol cluster ledgers;
- taxonomy migration helpers for split/merge execution;
- larger repo scopes beyond the released V50 pilot.

## Residual epistemic limits

The package is intentionally honest about its limits.

- Applicability can still be `underdetermined`.
- Structural safety is only **bounded** structural safety, not proof.
- Test coverage is package-local lexical/AST-backed coverage evidence, not theorem-like adequacy.
- Revision judgments are disciplined and explicit, but still bounded by the observed evidence supplied.

That honesty is part of the design goal.
The proto moves ADEU from magician-style edge witness sampling toward explicit edge-space accounting without overclaiming global certainty.
