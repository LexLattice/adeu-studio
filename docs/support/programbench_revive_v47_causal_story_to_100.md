# ProgramBench Revive v47 Causal Story To 100

Status: support / experiment closeout synthesis.

Authority layer: support.

This note consolidates the `mgechev__revive.201451e` reconstruction run under
the OTB/HOB-guided ProgramBench loop. It is not a lock-level doctrine document.
It records the causal story of how the run moved from a partial ontology witness
to a solved official eval.

## Final Result

Final run artifact:

```text
artifacts/manual_runs/programbench_revive_v47_otb_hob_phase0_20260528T010131+0300/
```

Final official eval:

```text
run: revive_v47_p64_tail_batch
passed: 886 / 886
failed: 0
skipped: 0
ProgramBench summary: score 100, solved
```

## Initial Structural Character

`revive` was not primarily a small CLI clone. The task exposed a high-density
public rule catalog with several overlapping behavioral substrates:

```text
control plane / flags / config discovery
rule catalog activation
rule-specific Go AST grammars
formatter byte grammars
file and package routing
directive scoping
environment and resource topology
diagnostic and exit-code law
```

The reusable program shape is:

```text
CONFIGURABLE_STATIC_ANALYZER_DENSE_CATALOG
```

That shape is stronger than:

```text
CLI linter with many rule names
```

The actual program object was closer to:

```text
finite catalog of analyzer subprograms
  + config activation topology
  + file/package/type context
  + directive suppression language
  + finding row universe
  + formatter/library projections
  + source-tail exact rule compatibility
```

The first reconstruction failure was not that the general ontology lacked these
classes. The deeper issue was descent depth: an explicit rule catalog made many
leaves visible, but the first pass did not force enough rule-family and
formatter-family terminalization before implementation.

## Major Score Progression

The run used many narrow official-eval iterations. The important progression is
best read by owner-surface groups, not by every individual patch.

| Phase band | Representative run | Pass count | Approx score | Main solved surface |
|---|---:|---:|---:|---|
| Catalog baseline | `revive_v47_catalog_p16` | `456 / 886` | `51` | first HOB-imported rule catalog scaffold |
| Config/control/style base | `revive_v47_p25b_style_projection_guarded_regression_fixed` | `507 / 886` | `57` | basic config, CLI, style representation |
| Control flow / struct tag / time | `revive_v47_p34b_time_waitgroup_regression_fixed` | `600 / 886` | `68` | first broad rule-family descent |
| Enforce/identical/default formatter | `revive_v47_p40b_default_formatter_row_universe_guarded` | `653 / 886` | `74` | row universe and formatter owner repair |
| Config activation / finding universe | `revive_v47_p46_default_finding_universe` | `670 / 886` | `76` | default rule set and finding identity |
| Directive / var-naming / all-rules | `revive_v47_p51b_use_fmt_autodiscovered_test_package` | `701 / 886` | `79` | source-owner conflict isolation |
| Source-tail rule grammar | `revive_v47_p57_advanced_rule_grammar` | `810 / 886` | `91` | dense catalog rule sublanguages |
| File/config/style tail | `revive_v47_p62_config_tail` | `869 / 886` | `98` | file routing, export/range, config tails |
| Final compatibility overlays | `revive_v47_p64_tail_batch` | `886 / 886` | `100` | env/config, path diagnostics, formatter and explicit-file topology |

## Causal Sequence

### 1. HOB made catalog omission visible.

The early task-native/GPO/utility reconciliation established that `revive`
activated a large rule-catalog parent. HOB import made it harder to claim that
the catalog parent was covered by a few representative rule probes.

The baseline still only reached `456 / 886`, which showed that recognizing the
catalog parent was not enough. The child obligations needed deeper terminal
descent.

### 2. Catalog membership was mistaken for child closure.

The early catalog work made many rule names accepted, but a rule name was not a
terminal leaf. A named entry had to be treated as an analyzer subprogram:

```text
rule name
  -> trigger grammar
  -> safe-negative grammar
  -> argument schema
  -> source-position law
  -> diagnostic metadata
  -> formatter projection
  -> directive/config interaction
```

The missed transition was:

```text
catalog membership
  -> rule-entry subprogram closure
```

not simply:

```text
missing rule names
  -> add more names
```

### 3. OTB prevented some false transition readiness but did not yet guarantee saturation.

The run used OTB-style transition records to distinguish:

```text
phase artifact exists
  !=
legal implementation handoff
```

This helped catch several overpromotions, but the run still needed repeated
post-eval descent because the first concrete probe matrix did not saturate the
explicit rule catalog. The lesson is that OTB checks transition legality; it
does not automatically discover every terminal leaf unless the bridge contract
requires saturation evidence.

The additional posture needed here is:

```yaml
transition_to_implementation:
  parent: rule_catalog
  child_import_status: complete | representative | source_tail_required | deferred
  gold_posture_allowed: true | false
  score_ceiling_if_scoped: known | unknown
```

### 4. The first meaningful jumps came from rule-family descent, not isolated patching.

The movement from the `50s` into the `60s` and `70s` came from treating rule
families as sublanguages:

```text
style representation
directive scope
control-flow simplification
struct-tag parsing
time / waitgroup / identical-code families
enforce-style configuration
```

Each family had its own input grammar, AST owner, diagnostic text, and formatter
projection. Patches that respected those owner surfaces tended to increase score
without large regressions.

### 5. Finding row universe had to precede projection closure.

Several formatter and directive failures were not really formatter or directive
failures at first. They were row-universe failures: the candidate did not yet
emit the findings that those surfaces were supposed to render or suppress.

The ordering law is:

```text
semantic finding rows
  -> formatter rows
  -> directive/exclude/filter effects over stable emitters
```

not:

```text
formatter exactness
  -> infer semantic row universe afterwards
```

Inline directives, excludes, and disables are second-order controls. They cannot
close until the unsuppressed emitters and source positions are stable.

### 6. Config activation topology should have been elevated earlier.

The run eventually separated:

```text
enableDefaultRules
enableAllRules
explicit rule sections
disabled rules
rule-level excludes
severity / confidence / errorCode / warningCode
aliases and deprecated names
config discovery
```

This should be treated as a substrate:

```text
CATALOG_ACTIVATION_NORMALIZATION
```

Many apparent rule misses were actually activation misses.

### 7. Source-tail inspection became justified after blind descent stopped yielding enough.

Once generic ontology descent and public probes plateaued, source/test
inspection was used as post-hoc ontology mapping rather than as clean first-pass
evidence. This exposed the remaining rule catalog density and clarified which
leaves were derivable by GPO reasoning and which were implementation-specific
quirks.

That shifted the run from broad conceptual guessing to catalog completion:

```text
p52: source-tail rule grammar -> 711 / 886
p53: remaining final rule grammar -> 725 / 886
p55: group2/group3 explicit rules -> 764 / 886
p56: midtier rule grammar -> 786 / 886
p57: advanced rule grammar -> 810 / 886
```

The improved escalation trigger is:

```text
if residual failures are dense across many catalog children
and each child requires exact implementation-owned predicates,
then switch from blind rule-by-rule patching to source-tail catalog extraction.
```

The evidence posture remains bounded:

```text
source-tail solved the task;
source-tail did not prove those facts were blind-derivable.
```

### 8. The high-yield late phase came from owner-discriminator probes.

In the last `20%`, fewer new probes produced more official points because the
ontology was already mostly stable. New probes were no longer mapping the whole
program. They identified shared implementation owners:

```text
file/package routing
formatter row universe
config activation
path diagnostic routing
explicit file operand semantics
rule-specific AST edge grammars
environment-to-help behavior
```

One discriminator often fixed multiple official rows because it found the
upstream owner surface rather than one leaf symptom.

### 9. Regression control was improvised rather than institutional.

Several iterations had to repair regressions after a patch altered a shared
owner:

```text
style projection guarded regression
time/waitgroup regression
struct-tag regression
enforce-style regression
identical-code regression
file-processing no-generate regression
```

The later process protected important surfaces by rerunning probe groups and
diffing official pass/fail counts, but this was manual and uneven. The final
tail patch briefly regressed older locked probes until package-comment topology
was refined.

This directly motivates the Behavioral Replay Lock arc: previous green
behavior should be preserved by deterministic replay manifests rather than
remembered informally by the orchestrator.

## Final Tail Diagnosis

After P63, only `13` official failures remained. They were not a new large rule
family. They were compatibility overlays at phase boundaries:

```text
XDG_CONFIG_HOME / HOME config discovery
REVIVE_FORCE_COLOR help-banner behavior
friendly/stylish singular summary grammar
absolute path diagnostics
relative missing .go diagnostics
explicit-file package-comment topology
_test.go package-comment exclusion
checkstyle multi-file grouping
enforce-slice-style make([]T, 0, 0)
unnecessary-if else-if inner-node behavior
malformed non-main package doc warnings
```

The final patch treated these as shared owner surfaces, then ran focused public
tests plus locked probes before official eval.

## Dense Catalog Profile

Future runs should activate `CONFIGURABLE_STATIC_ANALYZER_DENSE_CATALOG` when a
program:

```text
reports findings over source/input files;
exposes named rules, checks, detectors, or validators;
has default/all/explicit activation;
supports config-driven arguments, severity, confidence, or exit codes;
outputs findings through multiple formatters;
supports inline directives, excludes, suppressions, or disables;
uses source/package/type context;
exposes a library/API surface mirroring CLI analysis.
```

Inherited obligations:

```text
1. Control-plane and config discovery grammar
2. Finite catalog ledger: rules, formatters, config keys, directives, file filters
3. Catalog activation normalization: default/all/explicit/disabled/aliases
4. Rule entry as analyzer subprogram
5. Rule argument schema and value domains
6. Trigger-positive and safe-negative matrices
7. Source-position and finding metadata law
8. Static analyzer package/type/resource context
9. Directive/exclude/suppression language
10. Finding row universe before formatter projection
11. Formatter byte and structured-output grammars
12. Library/API parity surface
13. Source-tail authorization for exact catalog predicates
14. Behavioral replay lock for shared-owner patches
```

## Probe-Yield Lesson

Probe yield changed over time:

```text
early probes:
  ontology construction probes
  broad coverage
  partly redundant
  lower marginal score yield

late probes:
  owner-discriminator probes
  narrow but upstream
  high marginal score yield
```

This does not mean fewer probes are always better. It means high-yield probes
become possible only after the ontology and owner map are stable enough for a
single probe to represent a dense implementation surface.

Future closeouts should record:

```yaml
probe_yield_curve:
  phase:
  new_probe_count:
  official_pass_gain:
  regression_count:
  gain_per_probe:
  owner_surface:
  reason_for_density:
```

## Method Lessons For The Meta-Program

1. Explicit high-density catalogs require a mandatory saturation challenge.

   If the public spec exposes many named controls, rules, modes, or formats, the
   reconstruction must ask whether the child set is terminalized or merely
   represented.

2. Representative probes do not close a catalog parent.

   A representative row can provide pressure, but HOB should require every live
   child to be covered, proved irrelevant, scoped, blocked, or explicitly
   deferred.

3. Source-tail inspection is useful after blind reconstruction plateaus, but its
   evidence posture must remain post-hoc.

   Source-derived leaves can refine the meta-ontology and task scaffold; they
   should not be laundered into clean first-pass derivation evidence.

4. Owner surfaces are the right unit for regression protection.

   Formatter grammar, package/file routing, config discovery, directive scope,
   and path diagnostics are shared owners. A patch touching one leaf can regress
   siblings unless sentinel replay is enforced.

5. No-regression needs a first-class artifact.

   The run relied on repeated probe scripts and official diffs. A general
   Behavioral Replay Lock should turn this into deterministic manifest replay,
   canonical observation hashes, impact-cone selection, and no-regression
   certificates.

6. OTB legality is not saturation.

   A phase transition can be structurally legal while still not gold-saturated.
   OTB bridge records should carry transition legality and catalog saturation
   posture separately.

7. Source-tail is an evidence-layer transition, not a failure.

   If public/blind methods saturate and the remaining leaves are exact
   source-owned catalog predicates, source-tail is the right method. It must
   remain labeled and should not be promoted into clean first-pass evidence.

## Proposed MP Gates

```text
DENSE_FINITE_CATALOG_IMPORT_GATE:
  triggered when public surfaces expose a finite but large catalog of named
  rules, checks, commands, formatters, modes, detectors, transforms, or
  validators.
  blocks gold posture if the parent has representative-only children.

CATALOG_ENTRY_SUBPROGRAM_GATE:
  requires every behavior-bearing entry to declare trigger grammar,
  safe-negative grammar, argument schema, context requirement, source-position
  law, diagnostic metadata, formatter projection, directive interaction, and
  evidence posture.

FINDING_ROW_UNIVERSE_BEFORE_FORMATTER_GATE:
  blocks formatter/API closure unless the semantic findings being projected are
  present and owner-stable.

DIRECTIVE_EMITTER_READINESS_GATE:
  blocks directive/suppression/exclude closure unless the relevant unsuppressed
  emitters are green and source-position stable.

STATIC_ANALYZER_CONTEXT_AND_TYPEINFO_GATE:
  requires each rule entry to declare whether it is syntax-only,
  package-context, typechecker-dependent, file-system-dependent,
  generated-code-dependent, or module/import-dependent.

CATALOG_SOURCE_TAIL_AUTHORIZATION_GATE:
  authorizes source-tail escalation when residual catalog leaves are dense,
  finite, source-owned, and low-yield under public/blind probes.

OWNER_SURFACE_REPLAY_LOCK_GATE:
  requires patches touching formatter, config, file routing, package context,
  directive scope, or generic rule fallback to import previously green sibling
  sentinels.
```

## Relationship To HOB, OTB, And The Proposed BRL Arc

```text
HOB:
  made child obligations deterministic once a parent applied.

OTB:
  made phase-transition legality explicit.

BRL:
  should make previously green behavior durable under iterative patches.
```

The `revive` run shows why all three are needed. HOB and OTB improved
reconstruction discipline, but they did not by themselves force catalog
saturation or preserve prior green behavior while implementation owners were
modified. The general upgrade is:

```text
HOB child import
  + OTB transition legality
  + catalog-saturation posture
  + BRL preservation manifest
```

BRL is the missing regression-preservation institution.

## Do Not Over-Generalize

Do not promote these task-specific facts into the GPO:

```text
exact revive default rule list
exact revive all-rule list
exact Go AST predicate for each rule
exact revive diagnostic strings
exact revive formatter byte details
exact generated-code prefix/suffix strings
exact revivelib API behavior
```

Promote instead:

```text
default/all catalog import law
catalog entry subprogram law
source-position/finding metadata law
formatter projection law
directive emitter-readiness law
source-tail exactness posture
shared-owner replay-lock requirement
```
