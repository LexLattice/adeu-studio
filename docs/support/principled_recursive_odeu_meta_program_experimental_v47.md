# Principled Recursive ODEU Meta-Program Experimental v47

Authority layer: support / experimental meta-program revision.

This v47 patch extends:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v46.md
docs/support/general_program_ontology_derived_v1_8.md
docs/support/programbench_hob_obligation_catalog_v1.json
docs/support/programbench_revive_v47_causal_story_to_100.md
.codex/review-shell/chatgpt-downloads/revive_v47_causal_story_meta_review_v51.md
```

Core update:

```text
Dense finite catalogs require a distinct saturation contract. A phase can be
OTB-legal while still not catalog-saturated. HOB can import the catalog parent,
but gold posture is blocked until child entries have statuses, evidence posture,
and preservation obligations.

For static analyzers and similar catalog programs, a named rule/check/formatter
is not automatically a terminal leaf. It may be a subprogram with trigger
grammar, safe negatives, argument schema, context requirements, finding row
law, diagnostics, projection, and suppression interactions.

Formatter, API, directive, and filter closure must be downstream of a stable
semantic row universe. Suppression controls cannot close while the unsuppressed
emitters are absent or source-position unstable.

When blind/public catalog descent saturates and the remaining children are
dense, finite, exact, and implementation-owned, source-tail escalation is a
labeled evidence-layer transition, not a failure. Source-derived facts must not
be laundered as clean first-pass evidence.

Shared-owner catalog patches require BRL preservation manifests before they can
be promoted as a new baseline.
```

The `mgechev__revive.201451e` evidence anchor:

```text
catalog baseline:
  456 / 886

rule-family and infrastructure descent:
  low 50s -> high 70s

source-tail catalog extraction:
  high 70s -> 91

file/config/formatter/path compatibility tail:
  91 -> 98

final owner-surface compatibility overlays:
  886 / 886, score 100
```

Interpretation:

```text
catalog parent recognized
  !=
catalog children saturated

accepted rule name
  !=
rule subprogram closed

formatter or directive probe failed
  may mean row-universe or emitter-readiness failure first

source-tail solved the exact catalog tail
  !=
source-tail facts were blind-derivable
```

## 1. `DENSE_FINITE_CATALOG_IMPORT_GATE`

Trigger:

```text
Public task text, help, config, examples, or scout behavior exposes a finite
but large catalog of named rules, checks, commands, modes, plugins, detectors,
validators, transforms, renderers, or formatters.
```

Required outputs:

```yaml
dense_finite_catalog_import:
  catalog_ref: string
  catalog_kind:
    rule_catalog |
    command_catalog |
    mode_catalog |
    formatter_catalog |
    validator_catalog |
    plugin_catalog |
    mixed
  public_entry_count: int | null
  known_entry_refs: []
  unknown_entry_policy:
    none |
    public_scout_required |
    source_tail_required |
    deferred_with_risk
  child_status_table_ref: string
  catalog_completion_posture:
    representative_only |
    scoped_family_matrix |
    public_catalog_completion_attempt |
    source_tail_completion_attempt |
    gold_complete
  gold_posture_allowed: bool
```

Blocking conditions:

```text
parent marked gold while children are representative-only;
catalog entries lack status rows;
uncovered dense entries have no defer/source-tail posture;
the transition handoff omits catalog completion posture.
```

## 2. `CATALOG_ENTRY_SUBPROGRAM_GATE`

Trigger:

```text
A catalog entry has behavior beyond name acceptance, or the model has not proved
that it is shallow.
```

Required row:

```yaml
catalog_entry_subprogram:
  entry_ref: string
  name: string
  aliases: []
  activation_sets: []
  argument_schema: {}
  value_domains: []
  required_context:
    syntax_only: bool
    package_context: bool
    type_info: bool
    file_system: bool
    module_or_import_graph: bool
    generated_code_state: bool
    multi_file_denominator: bool
  trigger_positive_matrix_ref: string | null
  safe_negative_matrix_ref: string | null
  source_position_law_ref: string | null
  diagnostic_metadata_law_ref: string | null
  projection_refs: []
  directive_or_filter_interaction_refs: []
  evidence_posture:
    visible_spec |
    semantic_inference |
    public_scout |
    reference_observation |
    source_tail |
    target_substrate_probe
  closure_status:
    open |
    representative_only |
    family_matrix_partial |
    family_matrix_closed |
    source_tail_equivalent |
    proved_shallow |
    deferred
```

Rule:

```text
Do not implement catalog entries as accepted strings unless the
CATALOG_ENTRY_SUBPROGRAM_GATE has proved them shallow or explicitly deferred
their subprogram obligations.
```

## 3. `CATALOG_SATURATION_TRANSITION_CLAUSE`

OTB transition legality is not saturation. Any transition into implementation
or official-eval posture for a dense catalog must include:

```yaml
catalog_saturation_transition:
  transition_ref: string
  catalog_refs: []
  child_import_status:
    complete |
    representative |
    source_tail_required |
    scoped_deferred |
    blocked
  unresolved_child_count: int
  score_ceiling_if_scoped: known | unknown | not_applicable
  gold_posture_allowed: bool
  blocker_refs: []
```

Blocking rule:

```text
A transition may be structurally legal but not gold-ready. If saturation is
representative/scoped/source-tail-required, the transition must say so and must
not claim gold completion.
```

## 4. `FINDING_ROW_UNIVERSE_BEFORE_FORMATTER_GATE`

Trigger:

```text
The program reports findings, diagnostics, matches, rows, benchmark samples,
lint warnings, validation errors, or other semantic events through one or more
projection formats.
```

Required row:

```yaml
semantic_row_universe_before_projection:
  row_universe_ref: string
  emitter_refs: []
  required_row_fields: []
  stable_identity_fields: []
  source_position_or_denominator_law: string | null
  projection_refs: []
  projection_closure_allowed: bool
  blockers: []
```

Rule:

```text
Projection failures must first be checked against row-universe presence and
identity. Formatter/API/directive closure is blocked while relevant semantic
rows are absent or unstable.
```

## 5. `DIRECTIVE_EMITTER_READINESS_GATE`

Trigger:

```text
The program has directives, suppressions, excludes, disables, filters,
generated-file rules, path filters, or severity/confidence filters.
```

Required row:

```yaml
directive_emitter_readiness:
  directive_or_filter_ref: string
  affected_emitter_refs: []
  unsuppressed_emitters_green: bool
  source_positions_stable: bool
  scope_state_machine_ref: string | null
  projection_refs: []
  closure_allowed: bool
  blocker_refs: []
```

Blocking rule:

```text
If the unsuppressed emitter is missing, directive/filter behavior is not green;
it is blocked pending emitter readiness.
```

## 6. `STATIC_ANALYZER_CONTEXT_AND_TYPEINFO_GATE`

Trigger:

```text
The target analyzes source files, packages, modules, imports, types, generated
files, test files, multi-file groups, or file-system context.
```

Required classification:

```yaml
static_analyzer_context:
  entry_ref: string
  context_kind:
    - syntax_only
    - package_context
    - typechecker_dependent
    - file_system_dependent
    - module_import_dependent
    - generated_code_dependent
    - multi_file_denominator_dependent
    - test_file_dependent
  probe_matrix_ref: string | null
  source_tail_allowed_if_exact_predicate_owned: bool
```

Rule:

```text
Do not route every analyzer rule through one generic AST predicate. Context
requirements change probes, implementation owners, source-tail authorization,
and preservation sentinels.
```

## 7. `CATALOG_SOURCE_TAIL_AUTHORIZATION_GATE`

Trigger:

```text
Residual failures are dense across catalog children;
children have exact implementation-owned predicates;
blind/public probes have low marginal yield;
the owner map is stable.
```

Required row:

```yaml
catalog_source_tail_authorization:
  triggering_run_ref: string
  catalog_refs: []
  remaining_child_count: int
  public_blind_yield:
    high |
    medium |
    low |
    saturated
  exact_predicate_owner:
    source |
    host_library |
    fixture_corpus |
    target_substrate |
    mixed
  prior_gates_preserved: []
  authorization:
    blocked |
    source_tail_authorized |
    fixture_corpus_authorized |
    host_library_authorized |
    target_substrate_required
  non_laundering_statement: string
```

Blocking rule:

```text
Source-tail is not authorized merely because score is below 100. It is
authorized when the catalog tail is localized, finite, exact, and low-yield
under the current evidence layer.
```

## 8. `OWNER_SURFACE_REPLAY_LOCK_GATE`

Trigger:

```text
A patch touches a shared implementation owner that already has green sibling
leaves.
```

Common dense-catalog shared owners:

```text
formatter registry
config loader
catalog activation normalizer
file/package router
directive/suppression engine
generic analyzer fallback
path diagnostic router
library/API adapter
```

Required row:

```yaml
owner_surface_replay_lock:
  patch_ref: string
  touched_owner_nodes: []
  previously_green_sibling_refs: []
  required_brl_manifest_refs: []
  actual_replay_status:
    not_run |
    green |
    blocked |
    regressed
  certificate_ref: string | null
  promotion_allowed: bool
```

Blocking rule:

```text
A shared-owner patch cannot be promoted as the new baseline until the relevant
BRL preservation sentinels pass or the orchestrator records an explicit
regression tradeoff with replacement proof.
```

## 9. `PROBE_YIELD_CURVE_RECORD`

Future ProgramBench closeouts should record probe yield by phase.

Required row:

```yaml
probe_yield_curve:
  phase_ref: string
  new_probe_count: int
  local_gate_green: bool
  official_pass_gain: int | null
  official_regression_count: int | null
  gain_per_probe: float | null
  owner_surface: string
  reason_for_density: string
  next_posture:
    continue_descent |
    saturation_eval |
    source_tail_authorization |
    stop
```

Purpose:

```text
Early probes build ontology and may have low marginal score yield.
Late owner-discriminator probes can have high yield after the owner map is
stable. A low-yield closing pass is still useful as a saturation measurement.
```

## 10. Dense Catalog Phase Ladder

For dense finite catalog tasks, insert this ladder before implementation:

```text
P1  task-native / GPO / utility reciprocal diff
P2  public catalog ledger
P3  catalog posture decision
P4  infrastructure descent
      control plane
      config discovery and normalization
      resource/file/package universe
      semantic row universe
      formatter substrate
      directive substrate readiness
P5  catalog-entry subprogram descent
      trigger positives
      safe negatives
      argument schema
      context requirement
      source-position law
      diagnostic metadata
      projection and suppression interactions
P6  catalog saturation transition check
P7  implementation handoff with owner and BRL sentinels
P8  local gates and BRL replay
P9  official eval or saturation probe
P10 post-eval source-tail authorization if warranted
P11 source-tail witness separation and preservation replay
P12 final compatibility overlay under BRL
```

Batching preference:

```text
Batch by implementation technique and owner, not by test namespace:
  simple syntax rules
  package/context rules
  typechecker-dependent rules
  struct-tag/string-format sublanguages
  control-flow graph rules
  generated-code and file-routing rules
  formatter/API exactness
  directive/filter state machines
```

## 11. Safe Revive Abstraction Boundary

Promote from the revive run:

```text
dense finite catalog import
catalog entry as subprogram
catalog saturation transition clause
semantic row universe before formatter projection
directive emitter readiness
static analyzer context split
catalog source-tail authorization
owner-surface replay lock
probe yield curve recording
```

Do not promote:

```text
exact revive default/all rule sets
exact Go AST predicates
exact revive diagnostics or formatter bytes
exact generated-code strings
exact revivelib behavior
official test names as ontology nodes
```

## 12. Relationship To HOB, OTB, And BRL

```text
HOB:
  imports catalog child obligations once a dense catalog parent applies.

OTB:
  validates phase transition legality, including whether saturation posture is
  sufficient for the intended use.

BRL:
  preserves previously green sibling leaves when shared implementation owners
  are touched.
```

General law:

```text
HOB child import
  + OTB transition legality
  + catalog saturation posture
  + BRL preservation manifest
  -> admissible dense-catalog implementation handoff
```

Without all four, the run may be structurally disciplined but still either
under-saturated or regression-prone.
