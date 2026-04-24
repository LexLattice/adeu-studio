# Draft ARC Series Multilayer Mapping v1

Status: support synthesis draft, empirically hardened from
`docs/DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v0.md`.

Authority layer: support.

This document does not supersede any lock, architecture/decomposition document,
planning selector, closeout decision, schema, fixture, package, or source module. It is
a hardened support map of the ARC series and an empirical stress-test record for the
missing-seam set proposed in v0.

Horizon-sensitive terms follow `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`. A seam
listed as missing here means "not released as a first-class arc-family surface at this
support horizon." It does not mean impossible, permanently forbidden, or absent as
partial support code.

## 1. Experiment Design

The v0 map made three claims that needed stress testing:

- the current ARC line is a unitary harness rather than a flat feature list;
- the six missing seams are minimal for robust recursive self-improvement posture;
- existing repo tools already prove many local claims but do not yet prove whole-series
  cartography or self-improvement adoption law.

The epistemic loop used here was:

1. State the hypothesis from v0.
2. Inventory repo-native reasoning support tools that could falsify, constrain, or
   harden it.
3. Run the promising tools rather than relying on their names.
4. Classify each result as success, bounded success, failure, or non-applicable.
5. Decide whether each v0 seam is retained, split, merged, or removed.

Tool acceptance criteria:

- the tool must have an explicit input/output surface, schema, fixture, lint posture, or
  test surface;
- the tool must emit a failure or typed summary rather than only informal prose;
- the observed output must be interpreted at the authority layer it actually occupies;
- a tool that passes locally may validate its own lane, but does not become a global
  semantic adequacy oracle.

The experiment intentionally avoided treating transcript reasoning as sufficient
evidence. It used scripts, tests, fixtures, schema names, closeout lints, and planning
markers already present in the repo.

## 2. Tool Inventory

Promising tools and surfaces found:

| Tool family | Representative surfaces | Intended support role |
|---|---|---|
| Test selection | `apps/api/scripts/select_tests_v0.py`, `run_selected_tests_v0.py`, `packages/adeu_repo_description/src/adeu_repo_description/test_selection_v0.py` | select relevant tests from changed paths using repo-description evidence |
| Arc bundle lint | `apps/api/scripts/lint_arc_bundle.py` | validate start/closeout arc-bundle artifact shape for a given ARC number |
| Closeout consistency lint | `apps/api/scripts/lint_closeout_consistency.py` | validate deterministic stop-gate and closeout consistency across released docs/artifacts |
| Semantic compiler closeout lint | `apps/api/scripts/lint_semantic_compiler_closeout.py` | validate V32/V41-V42 semantic-compiler closeout wiring |
| Instruction policy view generation | `apps/api/scripts/generate_instruction_policy_views.py --check` | verify generated policy views remain in sync |
| Stop-gate metrics builder | `apps/api/scripts/build_stop_gate_metrics.py` | build metrics from persisted quality/evidence artifacts under deterministic environment constraints |
| Repo description extractors | `packages/adeu_repo_description/src/adeu_repo_description/extract.py` | derive schema/entity/catalog/dependency/test/optimization descriptive artifacts |
| Repo description schemas/fixtures | `packages/adeu_repo_description/schema/*.json`, `apps/api/fixtures/repo_description/*` | bind descriptive artifacts to frozen reference and reject-case behavior |
| V56-V65 agentic scripts | `apps/api/scripts/run_agentic_de_*`, `evaluate_agentic_de_*` | family-local generation/evaluation of resident-agent interaction, local effect, continuity, communication, connector, writable-surface, and delegated-worker artifacts |
| V67 ergonomic surfaces | `packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics*.py`, related schemas/tests | ergonomic adjudication, runtime bridge evidence, and admissibility checks |

The V56-V65 scripts were inventoried as relevant support surfaces but were not all
rerun. Their useful role for this stress test is already mediated by closeout artifacts,
closeout consistency lint, and the current mapped family stack. Rerunning every
historical artifact generator would test reproducibility breadth, not the specific v0
question of missing whole-series seams.

## 3. Empirical Findings

### 3.1 Test Selection

Command:

```bash
.venv/bin/python apps/api/scripts/select_tests_v0.py \
  --changed-path docs/DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v0.md \
  --stdout-format json
```

Observed result:

- emitted `repo_test_selection_plan@2`;
- selected `packages/adeu_semantic_compiler/tests/test_semantic_compiler_guards.py`;
- reported `risk_posture: narrow`;
- reported `full_suite_recommended: false`;
- selected one test and skipped 358;
- emitted Pydantic `schema` shadowing warnings from `adeu_repo_description.models`.

Judgment:

- useful as a repo-native local-check selector;
- validates that support-doc changes have known downstream consumers;
- does not validate semantic completeness of an ARC-series map;
- strengthens the need for `V68`, because local dependency witnesses are not global
  family cartography.

### 3.2 Selected Semantic Compiler Guard Test

Command:

```bash
.venv/bin/python -m pytest \
  packages/adeu_semantic_compiler/tests/test_semantic_compiler_guards.py
```

Observed result:

- `35 passed`;
- warnings included deprecated `discover_repo_root` usage and Pydantic `schema`
  shadowing.

Judgment:

- confirms the selected semantic-compiler guard lane is healthy;
- supports v0's claim that semantic authority machinery is instantiated;
- does not close semantic ingress from raw user utterance into typed operator instances.

### 3.3 Arc Bundle Closeout Lint For Current V67-C Horizon

Command:

```bash
TZ=UTC LC_ALL=C PYTHONHASHSEED=0 \
PYTHONPATH=apps/api/src:packages/urm_runtime/src \
.venv/bin/python apps/api/scripts/lint_arc_bundle.py --arc 187 --phase closeout
```

Observed result:

- emitted `arc_bundle_lint@1`;
- `arc: 187`;
- `phase: closeout`;
- `failures: []`;
- checked V187 evidence inputs, URM event stream, quality dashboard, stop-gate metrics,
  stop-gate reports, assessment, stop-gate decision, and locked continuation docs.

Judgment:

- strong evidence that the V67-C closeout bundle is coherent at its own horizon;
- supports the v0 reading that V67 is a real closure point for ergonomic instantiation
  adjudication;
- does not prove product-wide UI optimization, personalization, or global arc-series
  cartography.

### 3.4 Closeout Consistency Lint

Command:

```bash
TZ=UTC LC_ALL=C PYTHONHASHSEED=0 \
PYTHONPATH=apps/api/src:packages/urm_runtime/src \
.venv/bin/python apps/api/scripts/lint_closeout_consistency.py
```

Observed result:

- emitted `closeout_consistency_lint@1`;
- `failures: []`;
- checked the released stop-gate decision spine across many `vNEXT_PLUS` docs.

Judgment:

- supports using closeout docs as a released-state evidence spine;
- does not classify every arc family, branch posture, deferred seam, package surface,
  or dependency edge;
- therefore supports, rather than removes, `V68`.

### 3.5 Semantic Compiler Closeout And Instruction Policy Checks

Command:

```bash
TZ=UTC LC_ALL=C PYTHONHASHSEED=0 \
PYTHONPATH=apps/api/src:packages/urm_runtime/src \
.venv/bin/python apps/api/scripts/lint_semantic_compiler_closeout.py
.venv/bin/python apps/api/scripts/generate_instruction_policy_views.py --check
```

Observed result:

- semantic lint emitted `semantic_compiler_closeout_lint@1`;
- `failures: []`;
- reported coverage signature
  `9dc4f720e7884d0e8819fa6d4936c074215691557c9d607864f3d09376f06169`;
- instruction policy check verified:
  - `docs/generated/AGENTS_POLICY_VIEW.md`;
  - `docs/generated/SKILLS_POLICY_VIEW.md`.

Judgment:

- confirms released semantic-compiler and instruction-policy generated views are
  internally consistent;
- supports v0's semantic/documentation authority layer;
- does not supply a turn compiler, commit authority law, or self-improvement experiment
  ledger.

### 3.6 Stop-Gate Metrics Builder

Commands:

```bash
.venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --help
```

```bash
TZ=UTC LC_ALL=C PYTHONHASHSEED=0 \
.venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --help
```

Observed result:

- first run failed under the ambient environment:
  `deterministic tooling env conflict: expected LC_ALL=C, got C.UTF-8`;
- deterministic rerun succeeded and displayed metrics-builder options for quality
  dashboards, incident packets, event streams, connector snapshots, validator evidence,
  semantics diagnostics, and `vnext-plus7` through `vnext-plus27` manifests.

Judgment:

- useful as evidence that some repo tools fail closed on deterministic environment
  posture;
- useful for historical stop-gate metric building;
- bounded to persisted evidence/metric construction, not whole-series family synthesis.

### 3.7 Repo Description Extractors

Command:

```bash
.venv/bin/python - <<'PY'
import json
from pathlib import Path
from adeu_repo_description.extract import derive_v45a_repo_description_bundle

root = Path.cwd()
registry, catalog = derive_v45a_repo_description_bundle()
expected_registry = json.loads(
    (root / "apps/api/fixtures/repo_description/vnext_plus99/"
     "repo_schema_family_registry_v99_reference.json").read_text()
)
expected_catalog = json.loads(
    (root / "apps/api/fixtures/repo_description/vnext_plus99/"
     "repo_entity_catalog_v99_reference.json").read_text()
)
print(registry == expected_registry, catalog == expected_catalog)
PY
```

Observed result:

- V45-A registry matched fixture;
- V45-A catalog matched fixture;
- registry schema: `repo_schema_family_registry@1`;
- catalog schema: `repo_entity_catalog@1`;
- schema entry count: 7;
- entity count: 7;
- emitted Pydantic `schema` shadowing warnings.

Command:

```bash
.venv/bin/python - <<'PY'
from adeu_repo_description.extract import derive_v45c_repo_arc_dependency_register
derive_v45c_repo_arc_dependency_register()
PY
```

Observed result:

- current derivation failed:
  `ValueError: v45c corrective extractor requires V45-B to remain the broader selected_next_branch_local path in planning`;
- source inspection showed the extractor tracks only
  `V45-B`, `V45-C`, `V45-D`, `V45-E`, and `V45-F`;
- source inspection showed hard dependencies from `V45-B/C/D/E` to `V45-F`;
- tests for the frozen V45-A/V45-C behavior still passed separately.

Command:

```bash
.venv/bin/python -m pytest \
  packages/adeu_repo_description/tests/test_repo_description_v45a.py \
  packages/adeu_repo_description/tests/test_repo_description_v45c.py
```

Observed result:

- `36 passed`;
- warnings included deprecated repo-root discovery and Pydantic `schema` shadowing.

Judgment:

- V45-A descriptive extraction is alive and fixture-stable;
- V45-C dependency-register behavior is test-stable but current direct derivation is
  planning-marker sensitive;
- the V45-C register is strong evidence for the pattern of a dependency register but
  strong counter-evidence against treating it as whole-series ARC cartography;
- this is the clearest empirical support for keeping `V68`.

### 3.8 V67 Ergonomic Adjudication Tests

Command:

```bash
.venv/bin/python -m pytest \
  packages/adeu_core_ir/tests/test_ux_ergonomics.py \
  packages/adeu_core_ir/tests/test_ux_ergonomic_adjudication.py \
  packages/adeu_core_ir/tests/test_ux_ergonomic_runtime_bridge.py \
  packages/adeu_core_ir/tests/test_ux_ergonomics_export_schema.py \
  packages/adeu_core_ir/tests/test_ux_ergonomics_admissibility.py
```

Observed result:

- `33 passed`;
- warnings were mostly Pydantic `schema` shadowing.

Judgment:

- supports v0's claim that V67 is a concrete implemented ergonomic-instantiation
  family, not just conceptual prose;
- reinforces the boundary: V67 validates ergonomic adjudication artifacts and runtime
  bridge reports, not global UI sovereignty or recursive improvement law.

## 4. Hardened ARC Layer Map

The v0 family map is retained with one empirical refinement: the map should treat
released closeout docs as the best available status spine, but should not treat any
single existing extractor as the whole-series registry.

The hardened layer stack is:

```text
semantic authority and docs
  -> repo/domain self-description
  -> reasoning, assessment, benchmark evidence
  -> governed agent action and orchestration
  -> observed effect, restoration, continuity
  -> communication, connector, remote, writable surfaces
  -> delegated export and reconciliation
  -> native documentation and ergonomic instantiation
```

Empirical support:

- semantic authority and generated policy views passed their closeout/instruction
  checks;
- repo-description extraction is schema-backed and test-backed for V45-A, while V45-C
  shows the danger of stale planning-marker dependence;
- closeout consistency lint confirms the released closeout spine has no detected
  consistency failures;
- V187 arc-bundle lint and V67 tests support the current V67-C closeout horizon;
- test selection works as a local relevance planner, but it is not a global map.

The main negative laws remain:

- transcript is not authority;
- communication is not permission;
- continuity is not standing authority;
- local write ability is not commit/release authority;
- worker output is not native truth without reconciliation;
- benchmark output is not self-improvement proof without experiment/adoption law;
- planning support is not lock-level authorization;
- tool success is not scope expansion beyond the tool's declared surface.

## 5. Hardened Missing Arc Set

The v0 missing set is retained. The experiment did not find a released tool or schema
that makes any member redundant.

### `V68`: Whole-Series Arc Cartography And Seam Register

Empirical basis:

- closeout consistency lint validates a stop-gate spine but does not emit a whole-series
  arc map;
- V45-C proves a dependency-register shape exists but is V45-local and currently
  planning-marker sensitive when directly re-derived;
- test selection can find local downstream tests but does not classify arc-family
  status, branch posture, or deferred seams.

Required shape:

- schema-backed map over `V31`..current plus connected branch-local families;
- explicit authority layer per family/path;
- explicit status vocabulary such as `closed`, `locked_start_bundle`,
  `planned_not_selected_yet`, `deferred_to_later_family`,
  `superseded_by_alternate_surface`, and `not_selected_yet`;
- provenance links to lock docs, closeout decisions, planning docs, packages, fixtures,
  and lints;
- no scheduling, implementation, commit, or merge authority.

### `V69`: Semantic Ingress / Operator Binding / Turn Compiler

Empirical basis:

- semantic compiler and instruction-policy views are healthy, but they do not compile a
  raw user turn into a typed ADEU operator instance;
- V60/V61 can carry continuation and communication once intent artifacts exist, but
  they do not own closed-world operator-family selection from utterance.

Required shape:

- typed operator instance;
- explicit task family, artifact family, authority layer, action class, check posture,
  and evidence obligations;
- no direct execution, commit, or hidden operator invention authority.

### `V70`: Commit, Merge, And Release Authority

Empirical basis:

- V64/V65 surfaces and scripts support bounded writes and delegated reconciliation;
- closeout lints can validate released bundles;
- no observed tool promotes a local diff into commit, PR, merge, or release truth under
  a typed authority law.

Required shape:

- distinguish local mutation, accepted diff, commit intent, PR update, merge action, and
  released truth;
- bind checks actually run and explicitly skipped;
- consume `V64`, `V65`, generated policy docs, and closeout evidence without bypassing
  maintainer authority.

### `V71`: Self-Improvement Experiment Ledger

Empirical basis:

- V44/V46-style assessment and benchmark machinery exist;
- no observed released artifact binds baseline, intervention, evaluation, regression,
  rollback, and adoption posture for harness changes;
- the present task itself had to design this experimental loop as support prose.

Required shape:

- typed experiment packet;
- baseline/intervention/evaluation/regression/rollback/adoption fields;
- explicit non-self-approval rule;
- no benchmark-only authority laundering.

### `V72`: Multi-Agent Review, Adversarial Feedback, And Arbiter Settlement

Empirical basis:

- V35/V48/V65 provide worker boundaries, taskpack binding, and delegated export
  reconciliation;
- no observed released artifact types independent critics, adversarial feedback,
  conflict posture, or arbiter settlement as adoption-relevant phases.

Required shape:

- child-agent role/scope/evidence/independence/conflict records;
- arbiter settlement artifact;
- no majority-vote authority and no child output as native truth.

### `V43`: General Governed Contest Participation

Empirical basis:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md` names V43 as the external governed contest
  participation substrate and lays out `V43-A` through `V43-F`;
- later planning docs repeatedly preserve V43 as connected but not automatically
  superseded;
- V42 remains an ARC-specific specialization, and no observed closeout makes the V43
  general host-world family redundant.

Required shape:

- host-truth packet;
- rule/eval/resource/timeline compilation;
- archetype/leverage map;
- strategy catalog/selection and bounded run evidence only after world compilation.

## 6. Minimality Proof Sketch After Experiment

The empirical pass strengthens the minimality argument rather than expanding the set.

1. `V68` is necessary because existing status evidence is distributed across closeout
   docs, lock docs, fixtures, extractors, tests, and planning records. The one
   dependency-register extractor found is V45-local and current-text sensitive.

2. `V69` is necessary because healthy semantic compiler checks do not turn live user
   utterance into a typed operator instance. Without this seam, the harness would keep
   relying on transcript interpretation at the point of admission.

3. `V70` is necessary because passing tests, lints, and local file writes do not encode
   commit, PR, merge, or release authority. V64/V65 are deliberately below that layer.

4. `V71` is necessary because the present empirical loop had to be invented in support
   space. V44/V46 can measure and diagnose; they do not adopt self-modifications.

5. `V72` is necessary because worker/delegation law is not adversarial review law.
   Multi-agent critique becomes hazardous if its settlement posture remains informal.

6. `V43` is necessary because V42's ARC-specific specialization does not generalize
   host-world law. Later planning records preserve V43 instead of retiring it.

Irreducibility check:

- none of the six can be merged without collapsing distinct authority transitions;
- no existing passing tool observed here already emits the missing artifact family;
- each missing seam blocks one known unlawful shortcut from transcript, local write,
  tool pass, benchmark score, worker output, or planning text into stronger authority.

Completeness check:

- the remaining closed stack already covers semantic documents, repo description,
  practical analysis, structural assessment, benchmarks, live action, local effects,
  continuity, continuation, communication, connectors, remote UX, bounded repo writes,
  delegated reconciliation, documentation practice, and ergonomic adjudication;
- the six missing seams cover the still-open transitions needed for robust recursive
  self-improvement posture:

```text
global map
  -> semantic ingress
  -> operator instance
  -> bounded local change
  -> commit/release posture
  -> self-improvement experiment
  -> adversarial settlement
  -> external-world generalization
```

## 7. Recommended Next Iteration

The next concrete family should remain `V68`.

Starter experiment for `V68`:

- define a draft `arc_series_cartography@1` schema;
- ingest closeout decisions, locked continuations, `DRAFT_NEXT_ARC_OPTIONS_v*` docs,
  relevant package/test/schema surfaces, and known branch-local planning records;
- materialize a JSON artifact and human support report;
- compare the generated map against this v1 synthesis;
- report mismatches as explicit seam rows rather than silently choosing the prose map;
- keep output descriptive and non-authorizing.

Checks for the `V68` starter should include:

- schema validation for the cartography artifact;
- a lint that forbids planning rows from becoming lock facts without lock evidence;
- a lint that every `closed` family has at least one closeout/lock/fixture/test or
  explicitly documented evidence basis;
- a lint that every `deferred` or `not_selected_yet` seam names its controlling
  authority layer.

## 8. Verification Summary For This Support Doc

Commands run during hardening:

- `select_tests_v0.py` over `docs/DRAFT_ARC_SERIES_MULTILAYER_MAPPING_v0.md`;
- selected semantic compiler guard pytest;
- `lint_arc_bundle.py --arc 187 --phase closeout`;
- `lint_closeout_consistency.py`;
- `lint_semantic_compiler_closeout.py`;
- `generate_instruction_policy_views.py --check`;
- `build_stop_gate_metrics.py --help` with and without deterministic environment;
- V45-A/V45-C repo-description targeted tests;
- V45-A direct fixture comparison;
- V45-C direct derivation attempt;
- V67 ergonomic adjudication/runtime/admissibility targeted tests;
- `rg` inventory across docs, scripts, packages, schemas, fixtures, and tests.

Known empirical failures or limits:

- V45-C direct derivation failed against current planning text because it expects an old
  corrective planning marker;
- stop-gate metrics help failed until deterministic environment variables were set;
- repeated warnings show Pydantic `schema` shadowing and deprecated repo-root discovery;
- full `make check` was not run because this is a docs/support-only iteration and the
  targeted empirical loop was more relevant than the whole Python lane for the requested
  reasoning stress test.
