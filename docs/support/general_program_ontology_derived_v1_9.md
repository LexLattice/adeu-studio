# General Program Ontology Derived v1.9

Authority layer: `support / synthesis`

Scope: delta over `docs/support/general_program_ontology_derived_v1_8.md`.

Primary source inputs:

```text
docs/support/general_program_ontology_derived_v1_8.md
docs/support/programbench_hob_obligation_catalog_v1_1.json
.codex/review-shell/chatgpt-downloads/updated_mp_gpo_hob_v47_v18_review.md
```

This revision hardens the dense-catalog doctrine after review. The main change
is to separate generic dense catalogs from the static-analyzer overlay, so the
revive-derived analyzer obligations are not inherited by command catalogs,
renderer catalogs, plugin catalogs, or open extension registries unless the
task actually activates analyzer-like behavior.

## 1. Generic Dense Finite Catalog Profile

The generic profile is:

```text
DENSE_FINITE_CATALOG_PROGRAM
```

Trigger when public task material exposes behavior-bearing entries such as:

```text
commands
modes
plugins
rules
checks
detectors
validators
transforms
renderers
formatters
```

Generic inherited obligations:

```text
public catalog ledger
catalog cardinality and extensibility posture
activation/default/alias normalization
entry-as-subprogram or proved-shallow status
child status table and saturation posture
public-matrix adequacy before source-tail escalation
source-tail authorization and non-laundering boundary
shared-owner preservation and probe-yield economics
```

Closure law:

```text
Representative examples do not close a dense catalog parent.
Each behavior-bearing entry must be accounted for by child status, proof,
deferral, source-tail authorization, or explicit open-extension semantics.
```

## 2. Configurable Static Analyzer Dense Catalog Overlay

The analyzer overlay is:

```text
CONFIGURABLE_STATIC_ANALYZER_DENSE_CATALOG
```

It applies only when the catalog entries report findings over source/input
files or expose analyzer-like rule behavior.

Additional inherited obligations:

```text
analyzer finding row universe and metadata law
directive, suppression, exclude, filter, and generated-file language
static analyzer context split and dependency class
formatter/API projection over stable finding rows
package, type, file, module, build, and language-version context matrix
analyzer source-tail exact predicate authorization
```

Static-analyzer leaves are not inherited for ordinary command catalogs,
formatter catalogs, plugin registries, or open extension surfaces unless their
entries emit analyzer findings or analogous row objects.

## 3. Catalog Cardinality And Extensibility Posture

Dense catalog activation must declare cardinality:

```yaml
catalog_cardinality_posture:
  one_of:
    - closed_finite_public
    - closed_finite_reference_observed
    - closed_finite_source_tail_required
    - mixed_builtin_closed_extension_open
    - open_extensible
    - unknown_pending_scout
```

Closure rules:

```text
closed_finite_public:
  import all public children.

closed_finite_reference_observed:
  import all observed children and keep scout/source-tail gaps explicit.

closed_finite_source_tail_required:
  block gold posture until source-tail authorization or explicit deferral.

mixed_builtin_closed_extension_open:
  import built-ins and close extension registry/interface semantics.

open_extensible:
  close registry, discovery, loading, unknown-entry, and extension interface
  semantics; do not require exhaustive import of future user-defined entries.

unknown_pending_scout:
  block catalog gold posture and require public scout or deferral.
```

## 4. Catalog Activation Normalization

Activation is a substrate, not a side flag.

Required axes:

```text
default entries
all entries
explicit entries
disabled entries
aliases and deprecated names
per-entry arguments
severity/confidence/error/warning overlays
config discovery and precedence
environment/config interaction
library/API activation parity
open-extension registry loading when applicable
```

Rule:

```text
An apparent missing entry may be an activation-normalization failure. Check
activation before patching the entry predicate.
```

## 5. Catalog Entry As Subprogram

A catalog entry may be shallow only by proof. Otherwise it has subprogram
obligations.

Required axes:

```text
canonical name and aliases
activation sets
arguments and value domains
required context
trigger-positive matrix
safe-negative matrix
output/row/side-effect law
diagnostic law
projection/renderer interactions
filter/suppression interactions
evidence posture
closure status
```

## 6. Analyzer Finding Row Universe

For analyzer-like tasks, finding rows are the central state object.

Required row fields may include:

```text
rule/check name
severity
confidence
category
warning/error code
file/path identity
package/module denominator
line/column/span
source-position owner
formatter-specific fields
exit-code consequences
directive/filter suppressibility
library/API representation
grouping denominator for multi-file outputs
```

Ordering law:

```text
semantic finding rows
  -> formatter/API projections
  -> directive/exclude/filter effects over stable emitters
```

## 7. Directive, Suppression, And Filter Language

Directive-like controls require:

```text
lexical syntax
invalid directive diagnostics
scope start/end law
file/package/rule binding
source-position binding
generated-file filters
rule-level excludes
severity/confidence filters
formatter projection effects
exit-code consequences
```

Prerequisite:

```text
The unsuppressed emitter and source-position law must be stable before
directive/suppression closure is allowed.
```

## 8. Static Analyzer Context Split v2

Analyzer entries should declare context requirements.

Context classes:

```text
syntax_only
package_context
typechecker_dependent
control_flow_graph_dependent
dataflow_dependent
constant_eval_dependent
file_system_dependent
module_import_dependent
module_metadata_dependent
generated_code_dependent
build_tag_or_conditional_compilation_dependent
language_version_dependent
multi_file_denominator_dependent
test_file_dependent
naming_convention_dependent
```

Context class changes probe shape, implementation owner, source-tail
authorization, and BRL preservation sentinels.

## 9. Formatter And API Projection Over Finding Rows

Projection closure requires stable row ownership.

Required axes:

```text
format selection and defaults
human summary singular/plural grammar
multi-file grouping law
path identity projection
source-position projection
metadata field projection
structured-output schema
library/API representation
stdout/stderr/file routing
final newline and empty-output policy
```

Rule:

```text
Formatter/API repair is premature if the semantic rows are absent or have wrong
identity, grouping, source-position, or metadata.
```

## 10. Source-Tail Adequacy Prerequisite

Source-tail authorization requires evidence that public/blind methods were
adequate for the current layer and then saturated or became low-yield.

Required row:

```yaml
public_matrix_adequacy:
  branch_matrix_complete: bool
  salience_gate_run: bool
  descent_completeness_gate_run: bool
  representative_only_gaps_named: bool
  unresolved_axes: []
  low_yield_interpretable_as_saturation: bool
```

Rule:

```text
Low yield from poor probes is not saturation. Source-tail is authorized only
after adequate public/blind matrix work has run or after the orchestrator
explicitly records why that matrix cannot be made adequate.
```

## 11. Support Catalog

The support-layer HOB catalog for this split is:

```json
{
  "path": "docs/support/programbench_hob_obligation_catalog_v1_1.json",
  "catalog_version": "programbench-hob-v1.1",
  "canonical_catalog_hash": "sha256:a7013a4b34255c78999c8bbfb8e0cd9a2d97da5c462c3c8f06be1e1a74a963d1"
}
```

The catalog hash is the HOB canonical payload hash, not raw file SHA.
