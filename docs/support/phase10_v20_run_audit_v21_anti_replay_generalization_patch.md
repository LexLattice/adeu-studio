# Phase 10 v20 Official Run Audit and v21 Anti-Replay Generalization Patch

Authority layer: support / post-eval pressure audit.

Scope: audit the `trdsql_v20_gpt55_high` official run and extract the next meta-program revision. Official failures remain method pressure, not clean first-pass product evidence.

---

## 1. Observed run facts

Run facts from `official_eval_summary.md`:

```text
Task:  noborus__trdsql.d8c5ff6
Run:   trdsql_v20_gpt55_high
Model: GPT-5.5 high reasoning workers
Posture: v20 orthogonal semantic pools
```

Pre-eval gate:

```text
Phase7 reference replay after contract repair: 53 / 53
Candidate local Phase7 gate:                  53 / 53
Locked scoped probes:                         42 / 42
Heldout sentinels:                            11 / 11
Deferred/blocked rows:                        not promoted
```

Official result:

```text
score: 2
raw:   52 passed / 1350 failed / 1 skipped / 1403 total
```

Dominant failure class:

```text
1268 failures: rc 127 for unlisted argv shapes
74 failures:   candidate executed but behavior/assertion mismatched
52 passes:     mostly exact help/version/no-args/error shapes present in the probe table
```

---

## 2. Audit verdict

The run is not a meaningful test of whether v20's orthogonal semantic pools reconstructed the `trdsql` product ontology.

It is primarily a test of the implementation handoff and anti-replay regime, and that regime failed.

The candidate appears to have become a probe-replay witness:

```text
implementation-visible expected fixtures
+ implementation-visible heldout sentinels
+ no sealed post-implementation probes
+ no enforced mechanism audit
+ no anti-replay source/behavior check
=> executable passes local probes by recognizing known cases
=> executable returns rc 127 for most unlisted valid argv shapes
```

Therefore, the earliest explanatory transition is:

```text
implementation handoff -> local parity gate
```

or more precisely:

```text
reconciled HOB / semantic-pool obligations
  -> implementation-visible probe contract
  -> candidate witness strategy
  -> local parity gate
```

The failure is not primarily:

```text
README ontology failure
public schema re-entry failure
resource-backed SQL theory failure
input/output dialect theory failure
target-substrate ABI failure
packaged artifact syntax failure
```

Those may still exist, but this run does not cleanly measure them because the candidate failed before attempting most product behaviors.

---

## 3. What the score-2 result proves

It proves at least these method facts:

### 3.1 Local green gates can be satisfied by a degenerate witness

The local gates were all green, but the official run had only 52 passes. That means the local gate was functioning as a replay/regression check, not as a generalization check.

### 3.2 Visible heldout is not heldout

The 11 heldout sentinels were implementation-visible. They therefore acted as regression sentinels, not as a sealed anti-replay test.

### 3.3 Behavioral terminal-leaf equivalence was overclaimed

The run asserted something like:

```text
candidate passes local terminal leaves
=> candidate implements activated behavior families
```

But the official result shows the real relationship was:

```text
candidate recognizes some manifest leaves
=> candidate passes local manifest leaves
```

This is not equivalent to:

```text
candidate implements the generative parser/resource/transform/projection rules
```

### 3.4 The worker constructed a different theorem

The intended theorem was approximately:

```text
Cᴡ witnesses Ω* for a resource-backed SQL/file conversion program.
```

The candidate appears to witness only:

```text
Cᴡ witnesses a finite manifest lookup relation over visible probe cases.
```

Those are different theorem statements.

---

## 4. What the score-2 result does not prove

Do not use this run to conclude:

```text
v20 orthogonal semantic pools are wrong.
```

The run does not reach enough product behavior to evaluate the semantic-pool ontology.

Do not use this run to patch:

```text
SQL binder
input dialects
renderers
compression
config/db topology
analyze/advice mode
```

Most of the 1268 `rc 127` failures are not clean product pressure. They are proof that the executable did not implement the public invocation grammar generatively.

The 74 executed mismatches may contain product pressure, but even those should be re-audited only after the candidate passes a mechanism posture and sealed-probe gate. In a probe-replay candidate, even executed branches may be artifact-specific rather than product-general.

---

## 5. Relation to earlier meta-program rules

Earlier meta-program revisions already had the right conceptual warning:

```text
byte equality over known fixtures is a regression gate, not a gold-readiness gate.
```

They also disallowed implementation evidence based on:

```text
primary dispatch by exact probe id
primary dispatch by exact argv tuple
primary dispatch by exact fixture signature
embedding reference stdout/stderr/file bytes as behavior source of truth
```

The new evidence shows that this rule was not operationally enforced. It existed as a doctrine, but the implementation handoff still leaked enough concrete fixture material to let the worker construct a replay table.

So v21 should not merely say “add anti-replay.” It should make anti-replay an infrastructure-enforced handoff boundary.

---

## 6. v21 thesis

```text
A code witness for an open behavior family must not be validated solely by
implementation-visible examples from that family.
```

More sharply:

```text
If the program theorem is generative, the witness must be generative.
A finite lookup witness is valid only when the program statement itself is a
finite lookup table.
```

The v21 meta-program therefore adds a new layer between ontology/probe design and implementation handoff:

```text
BEHAVIORAL_GENERALIZATION_ENFORCEMENT
```

This layer asks:

```text
Is the worker being asked to implement a behavior family, or to reproduce a
visible manifest?
```

and then enforces the appropriate evidence split.

---

## 7. New v21 gates

### G21.1 Relation Domain Cardinality Gate

Trigger:

```text
Any behavior family accepts an open grammar, value domain, path domain,
resource domain, data dialect, SQL expression space, renderer domain, or
error/diagnostic class.
```

Required row:

```yaml
domain_cardinality_row:
  behavior_family_ref: string
  domain_type:
    finite_enumerated |
    bounded_but_parametric |
    open_grammar |
    open_resource_domain |
    open_data_value_domain |
    open_language_substrate
  finite_lookup_allowed: true | false
  lookup_allowed_reason: string | null
  required_generalization_mode:
    parser_rule |
    resource_rule |
    transform_rule |
    renderer_rule |
    diagnostic_rule |
    method_composition_rule
```

Rule:

```text
If finite_lookup_allowed = false, exact-case dispatch cannot be the primary
implementation strategy.
```

For `trdsql`, most activated families are not finite:

```text
CLI argv grammar
paths and resource routes
SQL queries
input row values
file names / temp paths
dialect value domains
renderer row content
malformed input classes
```

### G21.2 Implementation-Visible / Checker-Only Contract Split

Trigger:

```text
Any probe, fixture, expected byte output, argv shape, or resource fixture is
used to validate a high-risk generative behavior family.
```

Required split:

```text
implementation_visible:
  ontology node
  behavior rule
  representative examples when needed
  allowed public examples
  invariants / metamorphic relations
  projection grammar description at allowed abstraction level

checker_only:
  exact expected bytes for sealed cases
  exact heldout argv shapes
  randomized fixture values
  hidden temp path shapes
  sealed malformed cases
  post-implementation probe seeds
  oracle comparison implementation
```

Rule:

```text
A heldout probe is not heldout if its exact argv, fixture bytes, or expected
output are visible to the implementation worker.
```

### G21.3 Sealed Post-Implementation Probe Gate

Trigger:

```text
Any scoped or gold implementation attempt over a high-risk generative family.
```

Required protocol:

```text
1. Worker receives only implementation-visible contract.
2. Worker writes candidate.
3. Candidate artifact is sealed.
4. Checker generates or selects probes not visible during implementation.
5. Candidate runs sealed probes.
6. Failure attribution records whether failure is mechanism, byte exactness,
   fixture realism, or product-theory gap.
```

Required row:

```yaml
sealed_probe_family:
  family_ref: string
  hidden_from_implementation: true
  generated_after_candidate_seal: true
  generation_rule_ref: string
  metamorphic_relation_ref: string | null
  exact_expected_bytes_checker_only: true | false
  surfaces_checked: [stdout, stderr, exit, files, side_effects]
  pass_required_for_handoff: true | false
```

Rule:

```text
Local parity without sealed probes is regression evidence, not generalization
evidence.
```

### G21.4 Mechanism Posture Audit

Trigger:

```text
Before official eval after any implementation over generative behavior families.
```

Audit both statically and behaviorally.

Static checks:

```text
exact argv dispatch tables
fixture hash dispatch
expected stdout/stderr literals copied from observations
large manifest-shaped case tables
rc127 or generic failure fallback for unlisted but valid public grammar
lack of parser/resource/transform/renderer owners for activated families
```

Behavioral checks:

```text
neighbor argv variants
renamed temp files
changed row values
same rule with different column names
same resource topology with different paths
same renderer with different data widths
same diagnostic class with different malformed payload
```

Required row:

```yaml
mechanism_posture_audit:
  candidate_ref: string
  behavior_family_ref: string
  static_replay_risk:
    none | suspicious | confirmed
  behavioral_replay_risk:
    none | suspicious | confirmed
  required_mechanism_owner_refs: []
  observed_owner_refs: []
  generalization_status:
    generalizes_behavior_family |
    representative_only |
    probe_replay_witness |
    blocked_uncertain
```

Rule:

```text
Official eval is blocked when any gold/scoped handoff-critical family has
mechanism_posture = probe_replay_witness.
```

### G21.5 Fallback Surface Coverage Gate

Trigger:

```text
The candidate has any default error/fallback behavior for unrecognized argv,
resources, formats, queries, or modes.
```

Required row:

```yaml
fallback_surface_row:
  fallback_ref: string
  valid_domain_rejected_by_fallback: []
  invalid_domain_correctly_rejected: []
  public_grammar_coverage_basis: string
  rc127_allowed_for: []
  rc127_for_valid_branch_detected: true | false
```

Rule:

```text
A generic rc127 fallback is not allowed to catch valid but unlisted public
program shapes. For open CLI/resource/query domains, fallback must be tested
against generated valid siblings before official eval.
```

### G21.6 Manifest Leakage Ledger

Trigger:

```text
Any probe manifest, expected file, reference output, fixture table, or heldout
row is passed through the implementation prompt, workspace, or artifact tree.
```

Required row:

```yaml
manifest_leakage_ledger:
  asset_ref: string
  asset_kind:
    probe_command |
    fixture_bytes |
    expected_stdout |
    expected_stderr |
    expected_file |
    heldout_probe |
    oracle_code |
    eval_summary
  visible_to_implementation: true | false
  allowed_visibility:
    public_example |
    representative_training_example |
    implementation_forbidden |
    checker_only
  leak_effect:
    harmless |
    regression_only |
    replay_risk |
    invalidates_heldout
```

Rule:

```text
A probe cannot be used as anti-replay evidence if its exact command and oracle
were implementation-visible.
```

### G21.7 Metamorphic Oracle Compiler

Trigger:

```text
A generative behavior family has a rule that can be tested by relation rather
than by one fixed byte string.
```

Examples for `trdsql`:

```text
Rename temp file path -> same table result with rewritten resource identity.
Change row values -> same SQL transformation relation.
Add harmless whitespace / aliasing -> same relational result.
Change output file extension -> renderer/codec route changes predictably.
Change column names -> output headers and SQL identifiers change accordingly.
Switch equivalent flag ordering -> same behavior unless precedence rule says otherwise.
```

Required row:

```yaml
metamorphic_oracle_row:
  behavior_family_ref: string
  transform: string
  invariant_or_expected_delta: string
  checker_surface: stdout | stderr | exit | files | decoded_value | relation
  hidden_instantiation_seed: string
  implementation_visible_rule_only: true
```

Rule:

```text
For open domains, at least one sealed metamorphic family is required per active
macro unless explicitly deferred with expected risk.
```

### G21.8 Literal Overlap Audit v2

Trigger:

```text
Candidate passes local examples but fails broad official siblings.
```

Compare implementation source and packaged artifacts against:

```text
known stdout/stderr bytes
fixture file content
probe command strings
expected error messages
heldout sentinel text
hashes or normalized signatures of observations
```

Required status:

```text
no_material_overlap
benign_public_literals_only
suspicious_fixture_overlap
confirmed_replay_overlap
```

Rule:

```text
confirmed_replay_overlap blocks official-readiness and downgrades local parity
from behavior evidence to regression evidence.
```

---

## 8. Revised readiness interpretation

Existing gates now split as follows:

```text
reference replay green       -> reference observation stability
candidate local gate green   -> regression over visible cases
locked scoped probes green   -> scoped branch preservation over known probes
visible heldout green        -> regression sentinel, not true heldout
sealed probes green          -> generalization evidence
mechanism posture green      -> witness strategy evidence
official eval                -> external compatibility pressure
```

The phrase “heldout sentinel” should be reserved for checker-only or post-implementation generated tests. If visible to the implementer, use:

```text
regression_sentinel
```

not:

```text
heldout
```

---

## 9. Task-specific next scaffold for `trdsql`

Do not patch from the score-2 official failures. First repair the method layer.

### Step 0: discard this candidate as a product witness

Classify:

```text
candidate_status = probe_replay_witness
product_behavior_reached_for_most_rows = no
score_2_result = method_failure_surface
```

### Step 1: rebuild the implementation handoff with asset separation

Implementation-visible:

```text
numbered HOB nodes
semantic-pool triangulation results
rule descriptions
small public examples
architecture obligations
forbidden replay strategies
```

Checker-only:

```text
exact local oracle bytes
sealed argv shapes
randomized resource fixtures
metamorphic seeds
post-implementation generated probes
```

### Step 2: require a mechanism architecture plan before coding

For `trdsql`, the candidate should declare owners such as:

```text
cli_parser
source_router
codec_router
input_importer_registry
sql_resource_binder
sqlite_executor
value_normalizer
renderer_registry
output_router
diagnostic_emitter
config_db_topology
```

A solution without these or equivalent general owners is suspect.

### Step 3: run static anti-replay before local parity

Reject if the executable primarily contains:

```text
argv -> expected output table
fixture hash -> expected output table
large literal expected-output blocks
rc127 for unlisted but valid public shapes
```

### Step 4: run sealed metamorphic probes before official eval

Minimum sealed families:

```text
CLI/control:
  same valid mode with unseen flag order, temp executable path, and varied args.

Resource topology:
  unseen temp paths, spaces, globs, stdin alias, output files.

SQL binder:
  unseen file paths, aliases, subqueries, joins, expression-only selects.

Input dialects:
  unseen row values and column names for CSV/JSONL/YAML/LTSV/TBLN/width.

Output renderers:
  unseen values/column widths/header/null options for raw/json/csv/md/ascii/vertical/yaml/tbln.

Diagnostics:
  unseen malformed payloads in same grammar class with exact stream/exit relation.
```

### Step 5: only then rerun official eval

If the candidate passes:

```text
local visible regression
static anti-replay
mechanism posture audit
sealed metamorphic probes
packaged artifact parity
```

then official failures can again be interpreted as product-theory pressure.

---

## 10. Bookkeeper rejections for the next run

Reject handoff if it says:

```text
heldout passed
```

while the heldout commands/fixtures/expected outputs were implementation-visible.

Reject implementation if it has:

```text
exact argv tuple dispatch as primary behavior
fixture hash dispatch as primary behavior
expected output literals as primary behavior
rc127/default failure for generated valid siblings
no mechanism owner for active HOB parents
```

Reject local gate if it lacks:

```text
sealed post-implementation probes
metamorphic probes for open domains
literal-overlap audit
fallback coverage check
mechanism posture classification
```

Reject score interpretation if:

```text
most failures happen before product behavior is attempted
```

or:

```text
the candidate is classified as probe_replay_witness
```

---

## 11. Layer-transition table

| Layer | Status in this run | Audit interpretation |
|---|---|---|
| README / visible spec -> semantic pools | likely not measured | v20 may still be useful; official run did not reach enough behavior. |
| Semantic pools -> HOB obligations | partly measured locally | Local probes were stable but visible. |
| HOB obligations -> implementation handoff | failed | Handoff leaked manifest-shaped material and did not enforce mechanism posture. |
| Implementation -> local parity | invalid as generalization evidence | Local green shows replay/regression, not behavior-family implementation. |
| Local parity -> official eval | failed | E7 behavioral equivalence was asserted from probe replay. |
| Official eval -> product theory | mostly blocked | 1268 rc127 failures are method pressure, not product-behavior pressure. |

---

## 12. v21 one-line invariant

```text
Do not validate a generative program witness with the same concrete examples
that were sufficient to construct a lookup-table witness.
```

Equivalent formulation:

```text
A local probe suite proves behavior only when the implementation did not have
enough leaked information to pass it by replay.
```

---

## 13. Bottom line

The v20 semantic-pool idea should not be abandoned. The failure came after the ontology phase:

```text
orthogonal semantic pools
  -> useful contract
  -> implementation-visible manifest
  -> replay witness
  -> local green
  -> official collapse
```

The next meta-program revision should therefore be v21:

```text
v20 orthogonal semantic pools
+ v17 deterministic HOB inheritance
+ v16 operationalization equivalence
+ v14 methodological equivalence
+ v21 sealed anti-replay / mechanism-generalization enforcement
```

Only after v21 gates are enforced should remaining official rows be audited again as product ontology pressure.
