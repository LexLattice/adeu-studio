# GPTPro Review Answers to Section 4.3

Source packet reviewed:

- `PROGRAMBENCH_ADEU_META_ONTOLOGY_AND_TASK_ONTOLOGIES_20260519.md`
- `principled_recursive_odeu_meta_program_experimental_v7.md`

This review answers the eight questions in §4.3. It treats the current `tparse` reconstruction as the active target, while keeping the recommendation general enough for a programming-ontology meta-program.

## Executive conclusion

The v7 design is directionally right: it replaces a checklist of task-specific artifacts with a recursive ontology descent whose artifacts are derived views. The key improvement I recommend is to factor the current eleven operators into a smaller kernel algebra, while keeping some of the current specialized gates as derived macros.

The strongest kernel is:

```text
K1 Factor      entity boundary + decomposition
K2 Partition   value/state/error/grammar alternatives
K3 Bind        roles, consumers, subjects, denominators
K4 Transform   semantic computation, reducers, counters, formulas, resource lookup
K5 Sequence    lifecycle, initialization, mutation, ordering
K6 Expose      renderer, route, side effect, stream, byte grammar, exit surface
K7 Compose     interaction, precedence, non-commutation
M0 Warrant     evidence, authority, readiness, conflict labels
```

`Warrant` is not a normal ontology-splitting operator. It is a modal annotation that must attach to every node, probe, observation, and implementation claim.

Under this factoring, the existing v7 operators become:

```text
OP-B + OP-D          -> K1 Factor
OP-L + parts of OP-F -> K2 Partition
OP-R + OP-S          -> K3 Bind
new missing operator -> K4 Transform
OP-T                 -> K5 Sequence
OP-P                 -> K6 Expose
OP-C                 -> K7 Compose
OP-E                 -> M0 Warrant
OP-M                 -> derived MATCHER macro = K2 + K3 + K7 + K6 + M0
```

The main missing primitive is **Transform / semantic computation**. The current documents repeatedly discover computation surfaces — FIGlet smushing/layout, `scc` counting and LOCOMO/COCOMO formula subsystems, `go-mod-outdated` replacement update semantics, and `tparse` stream reducers — but v7 has no first-class operator asking, “what semantic function maps input/state to output state before projection?” This missing operator is why estimator/formula and generated-resource behavior currently appear as postmortem gates rather than normal descent products.

The second improvement is to promote **resource/dependency contract** from a late postmortem ledger into a required macro triggered early by broad resource-like claims. It does not need to be a primitive if `Factor + Partition + Transform + Expose + Warrant` can generate it, but it should be a mandatory macro gate for renderer, classifier, counter, and toolchain/library-dependent programs.

---

## 1. Which program ontology operators are redundant, missing, or badly factored?

### Redundant or overlapping

| Current operator | Issue | Recommendation |
|---|---|---|
| `OP-B Boundary` and `OP-D Decomposition` | These are often inseparable. Boundary says what one thing is; decomposition says what parts it has. In practice, every decomposition also asserts a boundary. | Collapse into `K1 Factor`, but preserve the scheduling rule: boundary before parts. |
| `OP-R Role` and `OP-S Subject / selection / aggregation` | `OP-S` is a specialized role/consumer split for subject ownership and denominator consumers. | Collapse under `K3 Bind`; keep denominator-specific templates because they are high risk. |
| `OP-L Lattice` and `OP-F Failure` | Invalid, malformed, missing, unsupported, late, partial, and contradictory states are value/state partitions. But their observable error surfaces and precedence are projection/sequence issues. | Put the state alternatives in `K2 Partition`; put error precedence in `K5 Sequence + K6 Expose`. |
| `OP-P Projection` including exit code | Exit code is observable, but the exit denominator is not a projection fact. The docs already separate rendered status, package summary, parser failure, side-effect failure, and process exit for `tparse`. | Keep exit surface under `K6 Expose`; keep exit denominator under `K3 Bind`. |
| `OP-M Matcher` | It is necessary, but it is a compound pattern, not a primitive. It combines value grammar, subject binding, scope, comparison, composition, and consumers. | Treat as a required derived macro for matcher-bearing controls/classifiers. Do not remove it from the implementation procedure. |
| `OP-E Evidence` | Essential, but not behavior-splitting in the same way as the other operators. | Reclassify as `M0 Warrant`, a modal annotation layer over every node and transition. |

### Missing

| Missing operator or macro | Why it matters | Examples from the packet |
|---|---|---|
| `K4 Transform / semantic computation` | The current ontology has input, state, role, selection, and projection, but no primitive for the semantic function that computes the middle truth. | FIGlet smushing/layout; `scc` line/comment/complexity counting and LOCOMO/COCOMO; `go-mod-outdated` module replacement semantics; `tparse` lifecycle reducer and status reducer. |
| Resource/dependency contract macro | Broad behavior often depends on generated tables, resource files, parser/formatter libraries, toolchain versions, encoders, width/locale libraries. The export says representative probes are not enough when broad behavior depends on generated resources. | FIGlet font/control resources; `scc` `languages.json`, generated `constants.go`, examples/language; Go stdlib parser/flag/time behavior in `go-mod-outdated`; tablewriter-like output. |
| Initialization/default-source macro | Startup defaults, env/config overlays, cwd/repo discovery, resource search paths, option order, and help precedence are not just lifecycle; they determine the initial state before normal behavior. | lazygit config/repo discovery; FIGlet `-d`, `-f`, `FIGLET_FONTDIR`, `-C`, `-N`; CLI help/version/no-args surfaces. |
| Protocol/grammar macro | Parser token binding, missing-value behavior, greedy next-token capture, structured stream grammar, and public help grammar repeatedly cause failures. | `scc` parser token-binding grammar; `tparse` Go test JSON event stream; `go-mod-outdated` stream of JSON objects rather than array. |
| Fixture-realism / producer-morphology dimension | This should not be a primitive ontology operator, but it must be a mandatory coverage dimension whenever producer-shaped data affects bytes, exit, or side effects. | `tparse` real fixture dialects differed from small synthetic fixtures; v7 requires realistic morphology probes for producer-shaped projections. |

### Badly factored point

The current v7 text alternates between **operators** and **hard gates**. That is okay procedurally, but the meta-program should label them differently:

```text
primitive operator:      small reusable conceptual move
mandatory macro gate:    recurring compound pattern triggered by a program class
artifact projection:     table/report emitted from the tree
readiness state:         modal status of a leaf or packet
```

This prevents future versions from accidentally treating “matcher-policy ledger,” “renderer compatibility table,” or “source-postmortem ledger” as primitives. They are projections or macros produced by applying the kernel.

---

## 2. Can the operators be organized into a smaller algebra that still generates the observed task-specific ontologies?

Yes. Use this smaller algebra:

```text
K1 Factor(node)
  Create entities, boundaries, parts, subresources, records, fields, controls.

K2 Partition(node)
  Split by value, type, presence, grammar, validity, emptiness, conflict, error state.

K3 Bind(node)
  Split by consumer, subject owner, selected row, aggregate denominator, exit denominator.

K4 Transform(node)
  Split by semantic computation: reducers, counters, formula engines, lookup semantics,
  layout algorithms, estimator models, classifier-to-metric transitions.

K5 Sequence(node)
  Split by lifecycle, initialization, mutation, ordering, timing, before/after state.

K6 Expose(node)
  Split by observable surface: stdout, stderr, file, renderer dialect, byte grammar,
  stream, side effect, final newline, exit surface.

K7 Compose(a, b)
  Split when two branches share a surface, state, resource, denominator, lifecycle
  stage, or parser context and may not commute.

M0 Warrant(node_or_edge)
  Attach evidence authority, readiness, deferral, conflict, postmortem status.
```

Derived macros:

```text
MATCHER(node)
  = Partition(value grammar)
  + Bind(subject/scope/consumer)
  + Compose(default/custom/repeated/comma/list interactions)
  + Expose(display/schema/diagnostic/exit consumers)
  + Warrant(boundary evidence)

RESOURCE_CONTRACT(node)
  = Factor(resource inventory)
  + Partition(resource grammar and missing/malformed states)
  + Transform(resource lookup/use)
  + Expose(resource-owned projection/error behavior)
  + Warrant(cardinality and authority)

PROTOCOL_GRAMMAR(node)
  = Factor(tokens/records/messages)
  + Partition accepted/missing/invalid/wrong-type values)
  + Sequence parse/validate/reduce order)
  + Expose parser errors and precedence)

PROJECTION_GRAMMAR(node)
  = Bind(row universe and denominator)
  + Expose headers/body/separators/style/wrapping/stream/file/exit)
  + Compose modes and identity/order interactions)

FORMULA_MODEL(node)
  = Bind variables and presets)
  + Transform formula/rounding/thresholds)
  + Partition fallback/override/invalid states)
  + Expose renderer-specific fields)
```

This algebra still derives all observed task ontologies:

| Task | How the smaller algebra generates the task ontology |
|---|---|
| FIGlet | `Factor` font/control resources and glyphs; `Partition` layout/width/control states; `Transform` smushing/layout; `Sequence` control stack and option order; `Expose` stdout/stderr/exit bytes; `Compose` layout × width × direction × justification. |
| lazygit | `Factor` repo/config/TUI boundary; `Sequence` startup discovery and overlay order; `Partition` missing/bad config/nonrepo/no-TTY; `Expose` bounded help/config/version surfaces; `Compose` env × config × cwd. |
| go-mod-outdated | `Factor` stream records and module/replacement/update nodes; `Partition` JSON/time/nil/malformed cases; `Bind` direct/update/Main filters and CI denominator; `Transform` update-row semantics; `Expose` table/panic/log/error surfaces. |
| tparse | `Factor` event stream, package/test subjects, controls; `Partition` action/output/time/value states; `Bind` output roles and exit denominators; `Sequence` lifecycle and late-error ordering; `Expose` renderers/follow/file/progress; `Compose` trimpath × smallscreen × format, follow × timestamps × late malformed. |
| scc | `Factor` file/resource/classifier/language/cost nodes; `Partition` matcher and identity states; `Bind` language/filter/denominator/consumer roles; `Transform` counting and formula models; `Expose` renderer/router/MCP/debug streams; `Compose` remap/count-as/filter/defaults. |

---

## 3. Best algorithm for instantiating a task ontology from four evidence settings

### A. README/spec only

Goal: produce a **candidate ontology and probe plan**, not implementation truth.

Algorithm:

```text
1. Extract base ontology from README/spec using native semantics:
   program class, inputs, producers, subjects, state, controls, selection,
   aggregation, projections, side effects, errors, runtime, identity, resources.

2. Assign evidence labels:
   visible_spec_explicit, program_class_inference, producer_name_inference,
   probe_required_pending_observation, explicit_deferral.

3. Apply the kernel algebra recursively:
   Factor -> Partition -> Bind -> Transform -> Sequence -> Expose -> Compose,
   with Warrant at every node.

4. Run mandatory class gates:
   help bootstrap, producer schema, multi-consumer payload, row universe,
   projection byte grammar, matcher macro, resource/dependency macro,
   formula/transform macro when triggered.

5. Emit terminal candidates, not locks:
   every high-risk leaf is either probe_required, pass_through_candidate,
   or explicitly_deferred_with_expected_risk.

6. Emit D-predictions:
   expected stdout/stderr/exit/file behavior before observing the reference.
```

Allowed readiness from README/spec only:

```text
ontology_candidate
probe_ready_candidate
not implementation_ready unless the task is intentionally a new design task
not gold_ready unless the visible spec itself is an executable oracle, which is rare
```

### B. README plus executable scout probes

Goal: convert candidate leaves into observed, terminal, scoped-ready or gold-ready leaves.

Algorithm:

```text
1. Build README ontology as above.
2. Run an independent blind scout over public executable surfaces.
3. Collect help/version/usage, invalid flags, missing values, value binding,
   output routes, stdout/stderr/exit/file effects, and minimal fixtures.
4. Keep the scout blind to prior conceptual artifacts and official failures.
5. Run granularity fitness:
   attach each scout surface to a terminal leaf, or record missing/coarse/conflict.
6. Convert observations into locked discriminator probes.
7. Add realistic producer morphology and cross-product probes for high-risk leaves.
8. Require generating-rule ledgers and held-out/metamorphic probes before gold.
```

Allowed readiness:

```text
probe_ready        if the probe has a discriminator, oracle, surface, and fixture
scoped_ready       if reference observation locks the leaf for a bounded branch
gold_ready         only if siblings, realism, cross-products, projection, side effects,
                   exit, public-surface attachment, and anti-replay are closed or deferred
```

### C. README plus source postmortem

Goal: repair the meta-program, not launder source facts into clean evidence.

Algorithm:

```text
1. Start from a local-green / official-red or near-green / materially-red run.
2. Group failures by subsystem and attach each failure to the smallest tree node.
3. If failures show no adequate node, authorize source-postmortem mode.
4. Inspect source only to identify missing generic operators/macros:
   generated resources, alternate entrypoints, cross-flag mutation graphs,
   event-stream grammar, router/renderer layering, formulas, toolchain contracts.
5. Label all such facts postmortem_source_derived.
6. Reclassify affected local-green leaves as scoped_ready_only where needed.
7. Update the generic meta-program so the next clean run can instantiate the
   missing operator from README/spec/scout evidence.
8. Keep source-derived implementation facts separate from clean reconstruction truth.
```

Allowed readiness:

```text
source_postmortem_explained
meta_program_patch_ready
not clean_gold_ready unless a later clean run observes or specifies the same branch
```

### D. Intention-only product description

Goal: produce a **design ontology**, not a reconstruction ontology.

Algorithm:

```text
1. Classify the intended product class and user-facing promise.
2. Create a normative ontology tree with evidence = product_intent.
3. Mark every compatibility behavior as design_choice_required, not observed truth.
4. Apply the same kernel algebra to derive required design decisions.
5. For each leaf, choose one of:
   specified_by_product_intent, design_decision_open, defer_from_mvp,
   reference_required_if_compatibility_target_exists.
6. Generate acceptance probes as product tests, not reference probes.
7. Only promote to implementation-ready after the product owner chooses defaults,
   parser grammar, projection bytes, failure behavior, and side-effect policy.
```

Allowed readiness:

```text
intent_scoped_ready for product design
implementation_ready only for explicitly chosen behavior
never reconstruction_gold_ready without a reference/spec oracle
```

---

## 4. Which scout probes should be mandatory by program class?

### Universal CLI scout

Every CLI-like target should scout:

```text
no args
-h / --help / help aliases
--version / version aliases when plausible
unknown flag
invalid value for typed flag
missing value for value flag
greedy next-token binding
--flag=value versus --flag value
repeated flag behavior for list-like flags
help/version precedence with invalid flags
stdout/stderr/exit split for all above
cwd and executable-name influence on usage text
stdin vs file source precedence when both are plausible
output route/file behavior when any output flag exists
```

### Renderer / serializer / formatter

```text
empty input
single row / multi-row
single line / multi-line body
special characters and trailing newlines
width/wrapping/smallscreen/terminal-width controls
color/ANSI/no-color controls
all declared formats
stdout vs file route
header/body/separator/footer/final-newline bytes
ordering/tie behavior
negative controls for hidden rows and no-row outputs
```

### Structured stream parser / event aggregator

Examples: `tparse`, `go-mod-outdated`.

```text
empty stream
blank lines
malformed record
wrong-shaped record
wrong-typed field
unknown field
missing required identity field
minimal valid record
realistic producer-shaped fixture
mixed valid + invalid stream
duplicate/conflicting terminal events
incomplete EOF lifecycle
output payload with multiple consumer roles
diagnostic morphology payload
aggregation denominator probe
exit denominator probe
raw-follow/side-effect ordering if raw output exists
late error after partial side effect
```

### Filesystem counter / classifier / analyzer

Example: `scc`.

```text
single file by extension
filename-only identity
shebang identity
content-marker identity
shared extension with multiple possible languages
mixed directory with multiple subject classes
ignored/default-excluded path
custom include/exclude/remap/count-as value shape
default-vs-custom composition
binary/unreadable/empty file
nested directory and path normalization
large/generated/minified marker behavior
language/listing public surface if present
all output formats and output routing
debug/trace/verbose event grammar
formula/cost model overrides if present
```

### Resource interpreter / resource-backed renderer

Example: FIGlet.

```text
missing resource
resource search path / env / cwd precedence
malformed resource header
minimal resource
alternate resource packaging or extension
resource comments/metadata count
resource stack append/clear behavior
resource-controlled layout or transformation
resource-dependent error text and exit
```

### Interactive TUI / workflow app

Example: lazygit.

```text
help/version/config-print surfaces
no-TTY startup
bad config file
config env vs CLI precedence
repo/worktree discovery
non-repo startup
terminal initialization failure or bounded TUI entry
external integration stubs when visible
safe timeout behavior
stdout/stderr/exit for noninteractive surfaces
```

### Estimator / formula / metric program

```text
default formula inputs
override controls
invalid numeric values
integer/float rounding
threshold text branches
empty/no-data behavior
format-specific projection fields
fallback/preset selection
```

### API / server / MCP / programmatic entrypoint

```text
method/schema listing
minimal valid request
unknown method
wrong-shaped request
CLI-equivalence or non-equivalence probe
alternate initialization path
projection schema shape
error status and stream behavior
```

For `tparse` specifically, the mandatory scout set should prioritize:

```text
help/version/no-args and flag validation
stdin vs -file and missing file behavior
minimal go-test JSON event stream
wrong type / malformed / mixed stream
package/test identity and lifecycle finalizers
Output role split: raw follow, failure body, diagnostic marker, coverage/no-test/build-like lines
basic/plain/markdown renderers
failure-detail block geometry
follow/follow-output/timestamps/progress side effects
trimpath/smallscreen/sort interactions
exit denominator branches
realistic go test fixture morphology
```

---

## 5. How should readiness states distinguish scoped-ready, probe-ready, implementation-ready, and gold-ready?

Use orthogonal readiness fields, not a single linear status. A leaf can be probe-ready but not scoped-ready; scoped-ready but not implementation-ready; implementation-ready for a scoped experiment but not for gold.

### Recommended readiness schema

```yaml
ontology_status:
  candidate | terminal_candidate | terminal_locked | pass_through | deferred | conflict_isolated

probe_status:
  no_probe_needed | probe_needed | probe_planned | probe_ready | observed_locked | probe_blocked | conflict_probe_needed

scope_status:
  not_scoped_ready | scoped_ready | scoped_blocked_pending_observation | scoped_blocked_by_conflict | scoped_deferred

implementation_status:
  not_ready | scoped_implementation_ready | gold_implementation_ready | blocked_by_projection_gap | blocked_by_replay_risk | blocked_by_conflict

gold_status:
  not_gold_required | not_gold_ready_missing_sibling | not_gold_ready_missing_cross_product | not_gold_ready_synthetic_only | not_gold_ready_projection_open | not_gold_ready_missing_public_surface | not_gold_ready_missing_generative_rule | not_gold_ready_replay_risk_open | gold_ready | explicitly_deferred_from_gold_with_expected_risk
```

### Definitions

| State | Meaning | What it permits |
|---|---|---|
| `probe-ready` | The branch has a named operator split, sibling distinction, fixture or command, oracle authority, observable surface, expected observation, negative/boundary control, and conflict discriminator. | Execute reference/scout/e-probe. No implementation truth yet. |
| `scoped-ready` | The reference/spec has locked behavior for the named branch under a bounded scope, with siblings-not-covered recorded. | Scoped implementation experiment. Not a gold handoff. |
| `implementation-ready` | All leaves required by the declared handoff type have owners, probes, projections, negative controls, and no unresolved conflicts. Must say scoped or gold. | Code work can start against that handoff packet. |
| `gold-ready` | The leaf is terminal and covered across high-risk siblings, cross-products, fixture realism, projection exactness, public-surface attachment, generating rule, anti-replay, side effects, and exit denominators, or explicitly deferred with risk. | Inclusion in the local gold fixture contract and official-eval attempt. |

Important consequence:

```text
observed example != probe-ready
probe-ready != scoped-ready
scoped-ready != implementation-ready
scoped implementation-ready != gold implementation-ready
gold fixture green != clean evidence promotion for post-eval-only branches
```

---

## 6. How can the meta-program avoid over-priming the model with task-specific edge examples while still forcing deep counterfactual descent?

Use **operator-shaped counterfactuals**, not named edge-case lists.

Recommended controls:

1. **Two-worker independence.** The conceptual worker reads README/spec only. The scout worker reads public executable behavior only. The fitness worker attaches scout surfaces to concept leaves. This prevents the conceptual pass from copying scout examples and prevents the scout from confirming the current theory.

2. **Operator prompts instead of edge names.** Ask “does this payload have multiple consumers?” rather than “check panic/race/no-test.” Ask “can raw identity differ from display identity?” rather than “check trimpath.” The `tparse` specifics should emerge from Go-test stream semantics plus the operators.

3. **Abstract role buckets.** It is acceptable to create buckets like `diagnostic marker`, `raw projection`, `metric-like line`, `no-subject marker`, `terminal summary line`. Avoid task-specific labels until visible spec, producer inference, or observation warrants them.

4. **Derivation proof requirement.** Every generated child must state why it derives from the current node and operator. If the only reason is “this happened in a previous task,” the evidence label must be `program_class_inference` or `probe_required_pending_observation`, not locked truth.

5. **Counterfactual templates.** For each operator, generate anonymous sibling contrasts:

```text
absent vs present
empty vs nonempty
valid vs malformed
single vs multiple
raw identity vs display identity
before side effect vs after side effect
selected row vs hidden counted row
stdout vs file route
semantic invalid fallback vs parser error
same value through two renderer dialects
```

6. **Hold out anti-replay probes.** Implementation may see the rule and representative examples, but not every sibling/metamorphic check. This prevents fixture/argv replay from masquerading as semantics.

7. **Evidence hygiene.** Official failures and source-postmortem facts should be attached as pressure or source-derived gaps, not backfilled into the clean first-pass theory.

8. **Rotating exemplars.** If examples are needed for prompt stability, keep them in bookkeeper training or companion docs, not in the generator’s task pass. The generator should receive the algebra and generic macro triggers, not a list of `tparse` edge cases.

---

## 7. What is the right escalation rule for switching from blind probe repair to source-postmortem operator discovery?

Use source-postmortem only after proving that the local probe universe is measuring a deficient theory rather than an implementation transfer bug.

### Escalation rule

Escalate to labeled source-postmortem when all are true:

```text
1. Local probes are green or near-green for the current scaffold.
2. Official evaluation remains materially red, or a public hidden-source risk remains large.
3. Failures cluster by subsystem rather than isolated byte rows.
4. Grouped divergence says missing_conceptual_node, existing_node_badly_split,
   terminalization_gap, probe_under_realism, or public-surface/coarse-parent attachment.
5. A blind public-surface scout and granularity fitness pass have already been run,
   or were impossible and explicitly deferred.
6. Further blind probes are likely to sample the same flawed ontology rather than
   reveal the missing operator.
```

Do **not** escalate yet when failures are:

```text
isolated implementation transfer errors;
narrow final projection sharpening with known parent nodes;
regressions caused by a broad patch before running parent-discriminator probes;
low-density random failures without subsystem clustering;
branches that public scout can still observe legitimately.
```

### What source-postmortem may do

It may discover missing generic operators/macros:

```text
generated resource inventory
alternate entrypoint stratification
cross-flag state mutation graph
event-stream grammar
router/renderer layering
estimator/formula subsystem
toolchain/library contract
```

It may **not** relabel source facts as clean first-pass evidence. The output should be:

```text
postmortem_source_derived gap classification
meta-program patch recommendation
next clean-run operator trigger
reclassification of affected local-green leaves as scoped_ready_only if needed
```

For `tparse`, source-postmortem should be unnecessary if the remaining failures can still be explained by the existing tree: follow raw-output ordering, projection byte grammar, failure-detail geometry, trimpath/sort/smallscreen interaction, panic/build/race fixture morphology, and exit denominator conflicts. Escalation would become justified only if those clusters stay red after reference-first probes and tree-level repair.

---

## 8. Can probe count be compressed by conceptual ownership without losing hidden-source risk coverage?

Yes, but only **after** gold-required leaves are explicit and the anti-replay gate exists. Compression before terminal leaves are known is dangerous because it hides exactly the distinctions the meta-program is trying to discover.

### Safe compression algorithm

```text
1. Build a bipartite graph:
   probes -> terminal leaves they witness.

2. Annotate each probe edge:
   operator witnessed, sibling split, surface, oracle authority, realism tier,
   positive/negative role, interaction role, side-effect/exit role,
   generative-rule coverage, anti-replay role.

3. For each nearest-common-ancestor subtree, select owner probes:
   choose the strongest probe that covers the parent discriminator and the
   required child surfaces.

4. Retain mandatory risk probes:
   negative/boundary controls, side-effect byte probes, exit denominator probes,
   realistic morphology probes, interaction probes, and held-out/metamorphic probes.

5. Mark removable probes only when they share:
   same terminal leaf, same authority layer, same observable surface,
   same realism tier, same rule, and no unique sibling distinction.

6. Re-run the bookkeeper:
   reject compression that collapses distinct consumers, side-effect destinations,
   exit denominators, renderer byte grammars, fixture-realism tiers, authority
   layers, or matcher consumers.
```

### Compression classes

```text
owned_by_existing_probe
requires_new_probe_same_leaf
requires_new_probe_new_leaf
over_granular_but_hidden_source_risk_valid
redundant_and_removable
deferred_until_more_task_evidence
```

### Rule of thumb

Compress probes that are redundant **within the same behavior leaf**. Do not compress probes that witness different sibling branches merely because they share an argv shape or fixture file.

For `tparse`, safe compression might combine several basic renderer row-alignment snapshots if a stronger projection grammar probe already covers the same table body rule. Unsafe compression would merge:

```text
follow stdout vs follow-output file
raw follow before late malformed parse vs normal malformed input
failure-detail body text vs diagnostic classifier marker
rendered row denominator vs exit denominator
trimpath display identity vs grouping identity
synthetic event stream vs realistic go-test fixture morphology
basic/plain/markdown byte grammar
```

Those are separate behavior leaves even if one fixture can exercise several of them.

---

## Recommended v8 patch to the meta-program

1. Replace the eleven current operators with the seven-kernel-plus-warrant algebra:

```text
Factor, Partition, Bind, Transform, Sequence, Expose, Compose, Warrant
```

2. Reclassify current specialized tables as derived views or macro gates:

```text
matcher-policy ledger       -> MATCHER macro
producer-schema table       -> PROTOCOL_GRAMMAR / RESOURCE_CONTRACT macro
renderer-compatibility      -> PROJECTION_GRAMMAR macro
aggregate-denominator table -> Bind view
lifecycle table             -> Sequence view
mode-interaction table      -> Compose view
source-postmortem ledgers   -> Warranted discovery mode, not clean evidence
```

3. Add `Transform / semantic computation` as a first-class operator. This is the biggest missing principle.

4. Add early macro triggers for:

```text
resource/dependency contract
initialization/default-source precedence
protocol/token grammar
formula/model computation
fixture-realism coverage
```

5. Keep `OP-M` behavior, but treat it as a macro. The matcher-policy gate is too important to remove, but it should be derived from the smaller algebra rather than presented as equally primitive.

6. Make readiness a product of four orthogonal ledgers:

```text
probe readiness
scope readiness
gold readiness
implementation handoff readiness
```

7. Preserve the current source-postmortem rule exactly in spirit: source may repair the meta-program and expose missing operators; it must not launder source facts into clean reconstruction evidence.

8. Use conceptual ownership compression only after the local gold fixture universe and anti-replay probes exist.

## One-sentence answer

The current v7 is close, but the principled version should factor the operators into a small kernel algebra, add a missing Transform/computation operator, treat matchers/resources/renderers/formulas as derived macro gates, make readiness orthogonal, and let probes be generated as witnesses for terminal branch distinctions rather than as an expanding list of edge cases.
