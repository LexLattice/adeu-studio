# General Program Ontology Derived v1.8

Authority layer: `support / synthesis`

Scope: delta over `docs/support/general_program_ontology_derived_v1_7.md`.

Primary source inputs:

```text
docs/support/general_program_ontology_derived_v1_7.md
docs/support/programbench_revive_v47_causal_story_to_100.md
.codex/review-shell/chatgpt-downloads/revive_v47_causal_story_meta_review_v51.md
```

This revision promotes the reusable ontology lessons from the
`mgechev__revive.201451e` reconstruction. It does not promote revive-specific
rule lists, diagnostic strings, Go AST predicates, formatter bytes, generated
code markers, or library API quirks.

The corresponding support-layer HOB catalog is:

```text
docs/support/programbench_hob_obligation_catalog_v1.json
```

## 1. New Program-Class Profile

Add this profile to the ProgramOntology catalog:

```text
CONFIGURABLE_STATIC_ANALYZER_DENSE_CATALOG
```

Trigger when a program:

```text
reports findings over source or input files;
exposes named rules, checks, detectors, validators, or analyzers;
has default, all, explicit, disabled, alias, or deprecated activation paths;
supports config-driven rule arguments, severity, confidence, warning codes, or
  error codes;
outputs findings through multiple human or machine formatters;
supports inline directives, excludes, suppressions, disables, or generated-file
  filtering;
uses source, package, module, import, file-system, or type context;
exposes a library/API surface mirroring CLI analysis.
```

This profile is stronger than a generic CLI profile. The central object is a
finite catalog of analyzer subprograms plus activation, context, row-universe,
projection, and suppression topology.

## 2. Dense Finite Catalog Parent

Add a reusable parent shape:

```text
DENSE_FINITE_CATALOG_PROGRAM
```

It applies beyond static analyzers to programs with behavior-bearing catalogs
of named rules, checks, commands, plugins, modes, detectors, transforms,
validators, renderers, or formatters.

Closure law:

```text
Representative examples do not close a dense catalog parent.
Dense catalog closure requires child import, child status, and evidence-layer
appropriate completion of every behavior-bearing child.
```

Every live catalog child must be:

```text
covered by a child-specific matrix;
proved shallow / pass-through;
proved irrelevant;
blocked pending evidence;
deferred with explicit risk;
or source-tail authorized with non-laundering labels.
```

## 3. Catalog Entry As Subprogram

A named entry is not automatically a terminal leaf. It may denote a subprogram.

Required record:

```yaml
catalog_entry_subprogram:
  catalog_ref: string
  entry_name: string
  aliases: []
  activation_sets:
    - default
    - all
    - explicit
    - disabled
  argument_schema: {}
  value_domains: []
  required_context:
    - syntax_only
    - package_context
    - type_info
    - file_system
    - module_or_import_graph
    - generated_code_state
  trigger_positive_matrix: []
  safe_negative_matrix: []
  source_position_law: string
  diagnostic_metadata_law: string
  formatter_projection_refs: []
  directive_or_filter_interactions: []
  evidence_posture:
    visible_spec |
    semantic_inference |
    public_scout |
    reference_observation |
    source_tail |
    target_substrate_probe
  closure_status:
    representative_only |
    family_matrix_partial |
    family_matrix_closed |
    source_tail_equivalent |
    proved_shallow |
    deferred
```

Rule:

```text
A catalog entry can be treated as a value only after a proof says it is shallow.
Otherwise it inherits subprogram obligations.
```

## 4. Analyzer Finding Row Universe

Add a central state object for analyzer-like programs:

```text
ANALYZER_FINDING_ROW_UNIVERSE
```

Rows are not just messages. A finding row can include:

```text
rule/check name
severity / confidence / category
warning code / error code
file/path identity
line / column / span
source-position owner
package/module/file denominator
formatter-specific fields
exit-code consequences
directive/filter suppressibility
library/API representation
```

Ordering law:

```text
semantic finding rows
  -> formatter/API projections
  -> directive/exclude/filter effects over stable emitters
```

Do not close formatter, SARIF/JSON/checkstyle-like output, or library API
parity before the semantic row universe is present and owner-stable.

## 5. Suppression And Directive As Second-Order Controls

Add this reusable node:

```text
DIRECTIVE_SUPPRESSION_FILTER_LANGUAGE
```

Suppression-like controls include:

```text
inline directives
file excludes
rule-level excludes
disable / enable blocks
generated-code filters
path filters
severity/confidence filters
config disables
```

Closure prerequisite:

```text
The unsuppressed emitter and source-position law for the affected rule family
must be stable before directive/suppression closure can be claimed.
```

If the emitter is absent, directive behavior is uninterpretable rather than
green.

## 6. Static Analyzer Context Split

Analyzer rules should declare the context they require. Generic AST fallback is
not enough.

Context classes:

```text
syntax-only
package-context
typechecker-dependent
file-system-dependent
module/import-dependent
generated-code-dependent
multi-file-denominator-dependent
test-file / non-test-file dependent
```

The context split belongs in the ontology because it changes probe shape,
implementation owner, source-tail authorization, and preservation sentinels.

## 7. Catalog Activation Normalization

Add a substrate node:

```text
CATALOG_ACTIVATION_NORMALIZATION
```

It covers:

```text
default catalog
all catalog
explicit entries
disabled entries
aliases and deprecated names
per-entry arguments
severity / confidence / warning-code / error-code overlays
config discovery and precedence
environment-config interaction
library/API activation parity
```

Many apparent child-entry misses are activation misses. A rule family should not
be patched as absent until activation normalization is checked.

## 8. Formatter Projection Depends On Row Ownership

Extend class `8 Output router, renderer, and byte grammar` with:

```text
finding-row projection law
singular/plural summary grammar
multi-resource grouping law
path identity projection
formatter-specific metadata projection
structured-output schema projection
library/API projection
```

Closure rule:

```text
Projection exactness can close only over a stable row universe. If emitted rows
are missing or have wrong identity, formatter repair is premature.
```

## 9. Catalog Source-Tail Posture

Some dense catalog leaves are exact, finite, and implementation-owned. When
blind/public descent saturates, source-tail may be the correct method.

Required status:

```yaml
catalog_source_tail_posture:
  catalog_ref: string
  remaining_child_count: int
  remaining_children: []
  public_blind_yield: high | medium | low | saturated
  source_owned_predicate_density: low | medium | high
  authorization:
    blocked |
    source_tail_authorized |
    fixture_or_corpus_authorized |
    target_substrate_required
  non_laundering_statement: string
```

Rule:

```text
Source-tail can solve a task and improve future ontology gates, but
source-derived expected facts remain source_tail evidence. They do not become
clean first-pass evidence.
```

## 10. BRL Preservation Hook

Dense catalog tasks often have shared implementation owners:

```text
formatter registry
config loader
catalog activation normalizer
file/package router
directive scope engine
generic analyzer fallback
path diagnostic router
library/API adapter
```

Any patch touching one of these owners should import preservation sentinels for
previously green sibling leaves through Behavioral Replay Lock.

Ontology-level hook:

```yaml
owner_surface_preservation_requirement:
  owner_surface: string
  green_sibling_refs: []
  required_brl_manifest_refs: []
  allowed_delta: none | bounded
  blocker_if_missing: true
```

## 11. Safe Generalization Boundary

Promote:

```text
dense finite catalog closure law
catalog entry subprogram law
catalog activation normalization
finding row universe before formatter projection
directive emitter-readiness law
static analyzer context split
finding metadata law
source-tail exactness posture
shared-owner replay-lock requirement
```

Do not promote:

```text
exact revive default rule list
exact revive all-rule list
exact revive diagnostic strings
exact revive formatter bytes
exact revive generated-code strings
exact Go AST predicate per revive rule
exact revivelib API quirks
```
