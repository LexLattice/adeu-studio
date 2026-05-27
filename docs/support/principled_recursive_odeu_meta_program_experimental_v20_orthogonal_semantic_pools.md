# Principled Recursive ODEU Meta-Program Experimental v20

## Orthogonal Semantic Pool Triangulation

Authority layer: support / experimental meta-program revision.

This v20 patch deepens v19's blind intent / utility branch into a general
triangulation method over multiple orthogonal semantic pools. The goal is not
more prose and not more examples. The goal is to create independent semantic
views of the same latent program object, reconcile them into the numbered HOB
obligation tree, and use their agreements, disagreements, and silences to drive
probe generation and implementation batches.

Evidence boundary:

```text
Semantic pools are discriminator generators and probe-frontier generators.
They are not behavior authority by themselves.

Only reconciled, warranted, HOB-routed obligations can drive implementation.
Only public observation / reference behavior / source-postmortem labels /
visible spec authority can promote an obligation into behavioral truth.
```

## 1. Why v19 worked, and why it was not enough

The Phase 12B second-track audit is the key positive signal. The v19
intent/utility branch produced real new coverage:

```text
phase9 non-passed rows:          450
v19 wins over phase9 failures:    52
phase9 failures still unsolved:  398
v19 regressions over phase9 passes: 361
```

The 52 wins were not random. They clustered around user-job semantics that the
mechanism-first HOB lane had underweighted:

```text
CLI discovery/control as user jobs
input shaping as workflow affordance
structured JSON/JQ values as data
real SQL over resource-bound files
resource identity and path utility
raw output as downstream-consumer format
```

Interpretation:

```text
The second track succeeded because it cut the program along a semantically
orthogonal basis: useful work, not mechanism syntax.
```

But the same audit also shows why v19 is incomplete:

```text
remaining failures stayed in resource ecology, compression/codecs,
input dialect value domains, analyze/discovery, renderer byte grammars,
DB/config/driver substrate, SQL transform breadth, and diagnostics/fatal
precedence.
```

The problem was not that the intent pool was wrong. The problem was that it
stopped at user-job families and did not recursively import the child
obligations implied by those jobs. It produced a strong narrative cut, but not a
closed inherited obligation tree.

So the v20 refinement is:

```text
Do not add one utility branch.
Add a triangulation system over orthogonal semantic pools.
Each pool independently produces affordance / mechanism / risk hypotheses.
Reconciliation compiles their union and conflicts into numbered HOB obligations.
```

## 2. Core v20 invariant

```text
No single semantic pool may close a program parent.

A parent closes only when:
  - every relevant pool has either produced obligations, stayed silent with a
    reason, or been proved irrelevant;
  - pool outputs have been reconciled onto numbered HOB nodes;
  - inherited children have status rows;
  - mechanism, workflow, and negative probes exist where the obligation is
    compositional;
  - regression sentinels protect previously green semantic siblings.
```

Short form:

```text
semantic discovery != closure
convergence != truth
reconciliation != implementation readiness
```

## 3. Definitions

### 3.0 Run mode and evidence horizon

Every v20 run must declare its evidence horizon before any pool executes.

```yaml
v20_run_mode:
  mode:
    blind_reconstruction |
    public_observation_repair |
    source_postmortem_repair |
    post_eval_pressure_repair
  allowed_evidence:
    visible_spec: true | false
    public_reference_observation: true | false
    source_code: true | false
    official_eval_failures: true | false
    prior_candidate_code: true | false
    prior_probe_logs: true | false
  forbidden_evidence:
    - source_code
    - official_eval_failures
    - prior_candidate_code
    - prior_probe_logs
  evidence_label_required: true
```

Rules:

```text
blind_reconstruction:
  Source code, official failures, prior candidate code, and prior probe logs are
  forbidden. Pool outputs may use visible spec, public help/scout if generated
  inside the run, and semantic class inference.

public_observation_repair:
  Public/reference observations may be used, but post-eval failures and source
  code remain forbidden unless separately authorized.

source_postmortem_repair:
  Source-derived behavior must be labeled source_postmortem or
  source_derived_support and cannot be laundered into clean first-pass evidence.

post_eval_pressure_repair:
  Official failures are pressure only. They can locate missing parents,
  frontier branches, and regressions, but do not become behavior truth without
  reference/source/visible-spec warrant.
```

If a pool consumes evidence outside the declared mode, its rows are
`contaminated` and must be excluded from clean-first-pass closure claims.

### 3.1 Semantic pool

A semantic pool is an independent decomposition lens over the same latent
program object.

Each pool has:

```yaml
semantic_pool:
  pool_id: string
  pool_name: string
  primary_question: string
  allowed_inputs: []
  forbidden_inputs: []
  output_kind:
    - candidate_obligation
    - candidate_discriminator
    - user_job
    - mechanism_node
    - risk_surface
    - probe_pressure
    - negative_case
  evidence_boundary: string
  contamination_status: clean | contaminated | unknown
```

A semantic pool does **not** produce implementation truth. It produces structured
pressure.

### 3.2 Pool applicability ledger

Before running pool outputs, the worker must decide which pools apply to the
program class. The decision is a status ledger, not prose.

```yaml
semantic_pool_applicability_row:
  pool_id: P | U | S | R | D | T | O | N | E | H | other
  applicability_status:
    active |
    proved_irrelevant |
    blocked_pending_observation |
    scoped_deferred_with_expected_risk |
    gold_deferred_with_expected_risk
  applicability_basis:
    visible_spec_text: []
    visible_example: []
    public_observation: []
    semantic_class_inference: []
    post_eval_pressure: []
    source_postmortem: []
  irrelevance_or_deferral_proof_ref: string | null
  expected_risk_if_deferred: string | null
```

Rules:

```text
For every pool required by the program-class minima, one applicability row is
required.

An active pool must either emit outputs or record expected_pool_silent with an
irrelevance/blocker proof.

A proved_irrelevant pool cannot be used later as a silent source of closure.

A deferred pool blocks gold-ready posture unless the deferral is explicitly
accepted as gold_deferred_with_expected_risk.
```

### 3.3 Triangulation

Triangulation is the reconciliation process that compares pool outputs.

```text
pool outputs
  -> convergence / parallax / silence / contradiction analysis
  -> numbered HOB nodes
  -> inherited child obligations
  -> probe matrix
  -> bounded implementation batch
```

Triangulation is not majority vote. Public/reference/source authority still
matters. Pools increase semantic recall and expose missing discriminators.

### 3.4 Parallax gap

A parallax gap occurs when two pools appear to discuss the same phenomenon but
land it on different parents.

Example:

```text
Utility pool:
  "user wants to query files by SQL"

Mechanism pool:
  "SQLite executes query text"

Resource pool:
  "file paths must be imported and bound before SQL"

If implementation sends raw file paths into SQLite, the shared parent is not
"SQL syntax" or "file reading". It is:

  RESOURCE_TO_LANGUAGE_BINDER
```

Parallax gaps are high-value. They often identify the missing parent abstraction
that post-hoc audits otherwise find only after many failures.

## 4. Required semantic pools

The exact pool set can be adapted by program class, but v20 requires at least
these pools for CLI/data/transform/render tasks.

### Pool P: Program-mechanism ontology

Primary question:

```text
What kind of executable machine is this program?
```

Typical cuts:

```text
control grammar
public schema
modes
resources
input dialects
embedded language / transform substrate
identity and binding
state and mutation
output routing and byte grammar
diagnostics and exits
runtime substrate
methodological equivalence
```

This is the v17/v18 deterministic HOB lane.

### Pool U: Intent / utility

Primary question:

```text
What useful work is the program promising to let the user perform?
```

Typical cuts:

```text
inspect data
shape input
query resources
join heterogeneous sources
project nested values
convert/export results
debug malformed inputs
compose with downstream tools
recover from wrong commands or missing resources
```

This is v19 Branch U, but v20 requires it to recurse into affordance children,
not merely record workflows.

### Pool S: Public schema / discovery surface

Primary question:

```text
What public controls, modes, formats, examples, and diagnostics does the program
advertise or reveal?
```

Typical cuts:

```text
help/version/no-args
flag inventory
mode families
format names
compression controls
config/db/driver controls
examples
invalid flag/value grammar
stdout/stderr/exit split
```

This pool is observation-driven when a reference executable exists. It is the
main guard against README-only under-scope.

### Pool R: Resource ecology and route topology

Primary question:

```text
Where do resources live, how are they discovered, decoded, imported, emitted,
and cleaned up?
```

Typical cuts:

```text
stdin/stdout
files and paths
paths with spaces
quoted paths
globs
tildes
query files
output files
compressed resources
config files
DB files
DSN / external database resources
locks / temp files / caches
process-owned resources
```

This pool generalizes the jplot C17 observation ecology lesson and the trdsql
resource-backed SQL lesson.

### Pool D: Data dialect and value-domain grammar

Primary question:

```text
What shapes and values can the program ingest, transform, and emit?
```

Typical cuts:

```text
CSV / TSV / PSV / LTSV / JSON / JSONL / YAML / TBLN / WIDTH / TEXT
header / no-header
empty / blank / malformed
scalar / object / array / nested / mixed
null / empty string / numeric / boolean / unicode / invalid UTF-8
duplicate or blank column names
line-ending variants
selector sublanguages
```

This pool prevents named formats from staying labels.

### Pool T: Transform / embedded language substrate

Primary question:

```text
What semantic computation or language is the user relying on?
```

Typical cuts:

```text
SQL expression-only computation
SQL over resource-bound tables
joins / aliases / subqueries / aggregates / functions / ordering
mutation and persistent state
jq / selector transforms
analyze / advice transform
extension inference
compression inference
normalization and type conversion
```

This pool is the v8 Transform operator made into an independent discovery lens.

### Pool O: Output / downstream-consumer projection

Primary question:

```text
What would make the output unusable even when the internal values are plausible?
```

Typical cuts:

```text
renderer byte grammar
headers
column order
field loss
null policy
final newline
quoting / escaping
alignment / wrapping
stdout vs file routing
compression of output
machine-readable downstream format
human-readable diagnostic format
```

This pool caught raw-output wins in v19 and must now force byte-terminalization.

### Pool N: Negative utility / failure-precedence

Primary question:

```text
What is the most dangerous false success for each user job?
```

Typical cuts:

```text
silent empty output
dropped columns
wrong table/resource binding
malformed input treated as data
wrong output format
wrong resource opened
wrong exit code
traceback instead of product diagnostic
late failure after partial side effect
first fatal gate precedence
```

This pool ensures that happy-path workflow probes do not become false closure.

### Pool E: Methodological equivalence / substrate

Primary question:

```text
Which lower-layer equivalences must hold before local observations can transfer?
```

Typical cuts:

```text
candidate artifact == submitted artifact
target interpreter/compiler ABI
packaged entrypoint
runtime dependencies
local probe oracle vs official checker
stdout/stderr/files split
resource/process/test ecology
fixture realism
regression retention
```

This pool generalizes the v14 methodological equivalence invariant and v11
observation ecology.

### Pool H: Historical delta / regression conservation

Primary question:

```text
Which already-green semantic siblings must remain green when this pool drives a
patch?
```

Typical cuts:

```text
previously green HOB nodes
previously green utility jobs
previously green public schema controls
previously green renderer surfaces
previously green resource routes
previously green negative/failure cases
```

This pool is post-eval / support-layer only. It is not clean first-pass
program truth. Its purpose is regression conservation and delta attribution.

## 5. Pool output schema

Every pool output must be structured enough to reconcile.

```yaml
semantic_pool_output_row:
  run_mode_ref: string
  hob_catalog_id: string
  hob_catalog_version: string
  hob_catalog_hash: string
  pool_id: P | U | S | R | D | T | O | N | E | H | other
  output_ref: string
  summary: string
  proposed_program_node: string | null
  proposed_hob_node: string | null
  proposed_parent_class: string | null
  proposed_child_obligations: []
  sibling_axes: []
  required_probe_types:
    - mechanism_probe
    - workflow_probe
    - negative_utility_probe
    - byte_projection_probe
    - resource_ecology_probe
    - equivalence_probe
    - regression_sentinel
  evidence_basis:
    visible_spec_text: []
    visible_example: []
    public_observation: []
    semantic_class_inference: []
    post_eval_pressure: []
    source_postmortem: []
  evidence_boundary:
    candidate_pressure |
    public_schema_observed |
    source_derived_support |
    post_eval_support |
    reference_locked |
    implementation_transfer
  contamination_status: clean | contaminated | unknown
  contamination_reason: string | null
  closure_claim_allowed: false
  notes: string
```

Rule:

```text
No pool output can set closure_claim_allowed = true by itself.
```

Closure is a reconciliation result, not a pool result.

Contamination rule:

```text
clean:
  Row may participate in the current run's allowed closure posture if all other
  warrants hold.

unknown:
  Row may create frontier pressure, but cannot support scoped-ready or
  gold-ready posture until resolved.

contaminated:
  Row may be retained as postmortem pressure only. It cannot be cited as clean
  first-pass evidence and cannot satisfy an inherited child.
```

## 6. Triangulation board

After pools run, create a triangulation board.

```yaml
triangulation_row:
  run_mode_ref: string
  hob_catalog_id: string
  hob_catalog_version: string
  hob_catalog_hash: string
  phenomenon_ref: string
  pool_output_refs: []
  convergence_kind:
    same_node_same_child |
    same_parent_different_children |
    complementary_axes |
    parallax_gap |
    contradiction |
    one_pool_only |
    expected_pool_silent |
    unsupported_user_expectation |
    public_schema_without_utility |
    utility_without_public_or_mechanism_landing
  reconciled_program_node: string | null
  reconciled_hob_node: string | null
  required_hob_children: []
  required_status_for_each_child:
    covered_by_probe |
    blocked_pending_observation |
    proved_irrelevant |
    proved_pass_through |
    scoped_deferred_with_expected_risk |
    gold_deferred_with_expected_risk |
    conflict_isolated
  probe_matrix_refs: []
  regression_sentinel_refs: []
  implementation_batch_candidate: string | null
  handoff_posture:
    discovery_only |
    probe_frontier_ready |
    scoped_implementation_ready |
    gold_blocked |
    gold_ready
  clean_evidence_complete: true | false
  contaminated_rows_excluded_from_closure: true | false
```

### 6.0 Handoff posture rules

```text
discovery_only:
  Pool pressure is structured, but HOB child status is incomplete.

probe_frontier_ready:
  Live children are mapped and statused, but required probes are not yet locked
  or run.

scoped_implementation_ready:
  Batch-local children have locked probes and non-batch children are explicitly
  deferred with expected risk.

gold_blocked:
  At least one required child is blocked, contaminated, unresolved, or missing
  terminal warrant.

gold_ready:
  Every required terminal child has clean evidence or explicitly accepted
  gold_deferred_with_expected_risk; reference/public/source-labeled behavior
  warrant is present where byte/channel/exit/resource behavior is claimed;
  contaminated rows are excluded from closure; regression sentinels for
  previously green siblings pass or are conflict-isolated.
```

Rules:

```text
Semantic convergence cannot create gold_ready.

gold_ready cannot rely on semantic_class_inference alone for terminal behavior.

gold_ready is forbidden if any active required pool is silent without an
irrelevance/defer/blocker proof.

gold_ready is forbidden if the HOB catalog identity is missing or stale.
```

### 6.1 Convergence rules

```text
one_pool_only:
  candidate pressure only; cannot close parent.

same_node_same_child from two blind pools:
  strong candidate obligation; still needs warrant and HOB child status.

complementary_axes:
  create cross-product probes if the utility depends on composition.

parallax_gap:
  ascend to the smallest shared missing parent; do not patch leaves.

contradiction:
  conflict-isolate until public observation/source/warrant resolves it.

expected_pool_silent:
  either prove pool irrelevant or reopen descent.
```

### 6.2 No majority vote

If seven pools infer a behavior but public reference disproves it, the behavior
is not true. The seven pools may still be useful: they explain why the branch was
plausible, what negative probe is needed, or what out-of-scope proof should be
recorded.

## 7. Pool-to-HOB inheritance

v17 already says selected parent classes import child obligations. v20 adds:

```text
A pool that maps to a parent also imports that parent's children.
A utility workflow mapped to a parent cannot be represented by one happy-path
workflow probe while inherited mechanism children vanish.
```

Example:

```text
Utility job:
  query ad hoc local resources with SQL

Mapped parent:
  RESOURCE_BACKED_SQL_SUBSTRATE

Inherited children include at least:
  resource discovery
  resource decoding
  table identity naming
  SQL token binding
  alias handling
  repeated resource references
  joins/subqueries
  diagnostics for missing/malformed resources
  output consumer projection
```

The worker may defer some children, but every child needs a status row.

## 8. Pool-to-probe compiler

Every reconciled obligation gets probes from the relevant pools.

```text
mechanism probe:
  Does the isolated branch behave as predicted?

workflow probe:
  Does the user job succeed when its required mechanisms compose?

negative utility probe:
  Does the program fail in the useful way when the workflow would otherwise
  silently violate the promise?

projection probe:
  Are stdout/stderr/files/bytes/exit exact enough for this surface?

resource ecology probe:
  Does the route/resource lifecycle reach product behavior without masking?

equivalence probe:
  Does the local observation transfer to the target artifact/substrate/oracle?

regression sentinel:
  Does a patch driven by one pool preserve previously green siblings discovered
  by other pools?
```

A utility-dependent branch is not scoped-ready unless it has at least:

```text
one mechanism probe
one workflow probe
one negative utility probe
```

unless a warrant row proves one is irrelevant.

## 9. Regression conservation gate

The Phase 12B audit reports real wins but also large regressions over previous
passes. v20 treats that as a pool coordination failure.

```yaml
regression_conservation_gate:
  patch_batch_ref: string
  driving_pool_refs: []
  affected_hob_nodes: []
  previous_green_sentinel_refs: []
  sentinel_pool_coverage:
    mechanism: present | missing | not_applicable
    utility: present | missing | not_applicable
    public_schema: present | missing | not_applicable
    resource: present | missing | not_applicable
    data: present | missing | not_applicable
    transform: present | missing | not_applicable
    projection: present | missing | not_applicable
    negative: present | missing | not_applicable
    equivalence: present | missing | not_applicable
  allowed_regression_budget: integer
  actual_regressions: integer | unknown
  posture: pass | blocked | scoped_experiment_only
```

Rule:

```text
A patch driven by Pool U must preserve sentinels owned by Pool P/R/D/T/O/N/E,
not only utility examples.
```

This is the robustness fix for the second-track pattern:

```text
orthogonal pool finds real missing branches
  -> implementation follows that pool too aggressively
  -> siblings from other pools regress
```

## 10. Program-class pool minima

### 10.1 Universal CLI minimum

```text
P: invocation and control mechanism
U: user jobs for discovery/help/error use
S: help/no-args/version/unknown flag public schema
O: stdout/stderr/exit projection
N: invalid/missing argument false-success cases
E: packaged artifact and target runtime equivalence
H: regression sentinels after first repair loop
```

### 10.2 Resource-backed transform tool

Add:

```text
R: resource topology and codecs
D: input/output value domains
T: transform language or computation substrate
O: downstream renderer/serializer contracts
N: malformed/misbound/missing-resource failures
```

### 10.3 Renderer-heavy tool

Add:

```text
O: byte grammar and downstream consumer pool
S: public renderer dialect schema
D: value/domain shapes that affect rendering
N: misleading successful-looking output
E: terminal/substrate/equivalence when needed
```

### 10.4 Long-running / interactive / resourceful tool

Add:

```text
R: resource/process/port/PTY topology
E: observation ecology and product-reached predicate
N: early-exit/timeout/teardown false success
H: rerun/parallel/regression sentinels
```

### 10.5 Pool minima execution rule

```text
The program-class minima are not suggestions.

For every minimum pool:
  - emit an applicability row;
  - if active, emit pool output rows or expected-pool-silent blockers;
  - if inactive, provide an irrelevance proof;
  - if deferred, record expected risk and block gold-ready unless explicitly
    gold-deferred.

No worker may omit a minimum pool because it feels unimportant after reading
another pool's outputs.
```

## 11. trdsql-class triangulation scaffold

### 11.1 High-priority triangulation rows

#### Query ad hoc resources with SQL

```text
Pools:
  U: user wants SQL over local files without preloading a DB
  P: embedded SQL substrate
  R: resource route / path / glob / stdin / compression
  T: SQL token binding and DB execution
  N: wrong table/resource binding is dangerous false success
  O: output must preserve selected columns and downstream format

Reconciled parent:
  RESOURCE_BACKED_SQL_SUBSTRATE

Required child obligations:
  resource discovery
  decode/import before SQL
  SQL token binding
  table identity / aliasing
  repeated references
  joins / comma joins / subqueries
  expression-only SQL
  mutation / persistent DB if public schema supports it
  diagnostics for missing/misbound resources
  output consumer projection
```

#### Shape input before querying

```text
Pools:
  U: user shapes dataset via delimiter/header/limit/skip/row number/no-guess
  S: public input flags
  D: dialect grammar and value domain
  T: importer normalization transform
  N: wrong shape silently changes query result

Reconciled parent:
  INPUT_DIALECT_AND_OPTION_OVERLAY

Required child obligations:
  delimiter grammar
  header/no-header
  skip/limit order
  row number collision policy
  explicit no-guess behavior
  null conversion
  malformed dialect diagnostics
```

#### Preserve structured values

```text
Pools:
  U: user has nested/semi-structured data
  D: JSON/YAML/etc. scalar/object/array/nested/mixed/null domains
  T: jq/selector and SQLite JSON functions
  O: output rehydration / escaping / unicode policy
  N: nested value stringified incorrectly but query appears successful

Reconciled parent:
  STRUCTURED_VALUE_DOMAIN_AND_SELECTOR_SUBSTRATE
```

#### Convert/export for downstream consumer

```text
Pools:
  U: user pipes or exports results to another tool
  S: public output format flags
  O: renderer byte grammar and output route
  R: output file / compression route
  N: wrong format or dropped columns is dangerous false success

Reconciled parent:
  OUTPUT_ROUTER_AND_DOWNSTREAM_CONSUMER_CONTRACT
```

#### Inspect/debug unknown data

```text
Pools:
  U: user wants to understand file before querying
  S: analyze/help public schema
  D: type/sample detection
  T: analyze/advice transform
  O: advice/report renderer
  N: bad advice misleads subsequent query

Reconciled parent:
  ANALYZE_MODE_AS_PROGRAM
```

### 11.2 Suggested next batches

Do not run one huge "apply v20" implementation. Use bounded pool-backed batches.

```text
Batch 0: Pool triangulation only
  - Run P/U/S/R/D/T/O/N/E/H ledgers.
  - Build triangulation board.
  - Compile rows into numbered HOB children.
  - Generate probes and regression sentinels.
  - No source patch.

Batch A: RESOURCE_BACKED_SQL_SUBSTRATE
  Pools: U + P + R + T + N + H
  Goal: resource-to-language binder, not renderer exactness.

Batch B: INPUT_DIALECT_AND_OPTION_OVERLAY
  Pools: U + S + D + T + N + H
  Goal: value/domain and option order, not all output formats.

Batch C: OUTPUT_ROUTER_AND_DOWNSTREAM_CONSUMER_CONTRACT
  Pools: U + S + O + R + N + H
  Goal: raw/TBLN/YAML/JSON/etc. byte and route contracts.

Batch D: ANALYZE_CONFIG_DB_MODE_AS_PROGRAM
  Pools: U + S + R + T + O + N + H
  Goal: analyze/config/db as standalone user jobs and modes.

Batch E: exactness and compatibility sharpening
  Pools: O + E + H
  Goal: byte, channel, codec, dependency, and target-substrate exactness.
```

## 12. Worker prompt contract

A v20 worker should not receive only prose like:

```text
Use the utility lane and improve remaining failures.
```

It should receive a contract like:

```text
You are running Batch A only.

Before editing source:
1. Declare run mode, allowed evidence, forbidden evidence, and evidence labels.
2. Record HOB catalog id, version, hash, and authority.
3. Produce pool applicability rows for every required pool.
4. Produce semantic pool ledgers for P/U/R/T/N/E/H for the scoped parent.
5. Build a triangulation board.
6. Map every live pool output to numbered HOB nodes.
7. Import inherited children and mark each child covered, deferred, irrelevant,
   pass-through, blocked, or conflict-isolated.
8. Generate mechanism, workflow, negative, equivalence, and regression probes.
9. Declare which child branches are outside this batch and expected risk.

Only then patch implementation owners for this batch.

After patching:
1. Run batch probes.
2. Run regression sentinels.
3. Report delta by HOB node and semantic pool.
4. Revalidate contamination status and HOB catalog identity.
5. Do not claim parent closure unless all inherited children are closed or
   explicitly deferred.
6. Do not claim gold-ready unless terminal behavior has clean warrant beyond
   semantic convergence.
```

## 13. Bookkeeper additions

Add the following blocking failures:

```text
run_mode_missing
run_mode_evidence_boundary_violation
hob_catalog_identity_missing
hob_catalog_identity_stale
pool_applicability_ledger_missing
required_pool_missing_applicability_row
active_pool_silent_without_board_row
semantic_pool_missing_for_active_program_class
pool_input_contamination
contaminated_pool_row_used_for_clean_closure
unknown_contamination_row_used_for_readiness
pool_output_without_stable_ref
pool_output_claims_behavior_truth
utility_affordance_not_reconciled
pool_mapping_to_parent_without_child_inheritance
triangulation_board_missing
parallax_gap_not_escalated
expected_pool_silent_without_irrelevance_proof
workflow_probe_missing_for_compositional_utility
negative_utility_probe_missing
regression_conservation_gate_missing
single_pool_parent_closure_claim
gold_ready_from_semantic_convergence_only
gold_ready_with_unresolved_terminal_child
gold_ready_with_contaminated_support
pool_delta_not_attributed_by_hob_node
```

## 14. Relation to v19

v19 said:

```text
Run Branch P and Branch U independently.
Reconcile Branch U back to the program ontology.
Only reconciled ontology drives probes and implementation.
```

v20 generalizes:

```text
Run multiple orthogonal semantic pools.
Reconcile every pool output onto the numbered HOB tree.
Use convergence to prioritize, parallax to find missing parents, silence to
force irrelevance/defer proofs, and contradiction to conflict-isolate.
Only reconciled, warranted, HOB-routed obligations drive probes and
implementation.
```

## 15. Bottom line

The second track was valuable because it introduced semantic parallax. It saw
program obligations from the user's job rather than from mechanism syntax. The
next robustness gain comes from making that parallax systematic:

```text
not one mechanism tree
not one utility narrative
but a triangulated obligation tree over independent semantic pools
```

The intended loop becomes:

```text
visible spec
  -> independent semantic pools
  -> triangulation board
  -> numbered HOB inheritance
  -> mechanism/workflow/negative/equivalence/regression probes
  -> bounded implementation batch
  -> delta attribution by pool and HOB node
```

This preserves v19's discovery benefit while preventing the second track from
becoming another representative patch lane.
