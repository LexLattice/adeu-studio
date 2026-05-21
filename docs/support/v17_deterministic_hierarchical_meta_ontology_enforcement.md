# V17 Deterministic Hierarchical Meta-Ontology Enforcement

## 0. Purpose

The v16 diagnosis identified the audit-to-worker transfer gap:

```text
post-hoc audit identifies the right parent discriminator
  !=
worker operationalizes the full child branch matrix
```

V17 converts the meta-program from a mostly prose-driven recursive ontology method into a deterministic obligation system over a numbered hierarchy.

The new invariant is:

```text
A parent ontology class selected as relevant imports its child obligations by default.
A child may be removed only by an explicit irrelevance/pass-through proof or by
an explicit scoped deferral that blocks gold readiness.
```

This changes the worker posture from:

```text
Which examples should I fix under this parent?
```

to:

```text
This parent class applies. Therefore all numbered child obligations are live
until each is covered, proved irrelevant, proved pass-through, blocked, or
explicitly deferred with expected risk.
```

The intended effect is to make improvements more robust. A worker cannot claim it has fixed `SQL_RESOURCE_BINDER`, `INPUT_DIALECT_GRAMMAR_MATRIX`, or `OUTPUT_ROUTER_RENDERER_MATRIX` merely by patching a few representative examples. It must fill the inherited tree.

---

## 1. Core distinction: top-down applicability, downward obligation inheritance

V17 separates two phases that were previously blurred.

### Phase 1: Applicability pass

The model reads the README/spec and public schema and decides whether top-level ontology classes apply.

Example top-level classes:

```text
1 Control plane / invocation grammar
2 Public schema and mode family
3 Input resource and route topology
4 Input dialect and value-domain grammar
5 Embedded language / transform substrate
6 Subject, identity, binding, and aggregation
7 State, lifecycle, and mutation
8 Output router, renderer, and byte grammar
9 Diagnostics, fatal gates, and channel contracts
10 Runtime substrate and observation ecology
11 Methodological equivalence and warrant
12 Probe, readiness, and implementation handoff
```

The applicability pass is semantic and model-native. It asks what kind of machine the program is.

### Phase 2: Inherited obligation closure

Once a top-level class applies, its children become obligations automatically.

```text
parent applies
  -> child obligations become inherited_required
  -> each child must receive a terminal status
```

The default child status is not “optional” or “maybe relevant.” The default is:

```text
required_by_parent
```

The worker may exit a child only by producing one of:

```text
covered_terminalized
covered_by_probe_matrix
proved_pass_through
proved_irrelevant
conflict_isolated
scoped_deferred_with_expected_risk
gold_deferred_with_expected_risk
blocked_pending_reference_observation
blocked_pending_methodological_equivalence
```

Only the first four can contribute to gold readiness. Scoped deferral permits a scoped experiment but not a gold handoff.

---

## 2. Why this is needed

The recent trdsql run shows that parent-level diagnosis was approximately right, but operationalization remained partial. The worker reported that `SQL_RESOURCE_BINDER`, `RESOURCE_ROUTE_TOPOLOGY`, `INPUT_DIALECT_GRAMMAR_MATRIX`, `OUTPUT_ROUTER_RENDERER_MATRIX`, `CONFIG_DB_TOPOLOGY`, and `MODE_DIAGNOSTIC_CHANNEL_CONTRACT` were still under-derived, partially terminalized, scoped, or open. It then patched representative branches and improved score from 60 to 68, but left the same families open.

V17 treats that as a structural failure of obligation inheritance:

```text
parent label recognized
  -> representative children patched
  -> unpatched siblings silently remain outside the worker task
```

The fix is:

```text
parent label recognized
  -> full numbered subtree imported
  -> every child row must be closed, deferred, or proved irrelevant
  -> bookkeeper rejects parent claims unless child ledger is complete
```

---

## 3. Node identifier convention

Every node receives a stable dotted numeric path:

```text
5
5.2
5.2.4
5.2.4.3
```

Suggested interpretation:

```text
major.minor.branch.leaf
```

Example:

```text
5 Embedded language / transform substrate
5.2 SQL-like query substrate
5.2.4 Resource reference binding inside query text
5.2.4.3 Resource reference in JOIN / comma join / subquery context
```

A node ID is not just a label. It is an obligation anchor used by:

```text
ontology tree
probe matrix
implementation owner map
readiness ledger
bookkeeper checks
failure attribution
score-delta attribution
```

---

## 4. Required node record

Each numbered node must have a machine-checkable record.

```yaml
node_id: "5.2.4.3"
node_label: "Resource reference binding in join/subquery contexts"
parent_id: "5.2.4"
node_kind: class | macro | branch | terminal_leaf
applicability_status:
  applies | not_applicable_proven | candidate_pending | conflict_isolated
inheritance_status:
  root_selected | inherited_required | locally_triggered | optional_observed | not_inherited
obligation_status:
  open | covered_terminalized | covered_by_probe_matrix | proved_pass_through |
  proved_irrelevant | scoped_deferred_with_expected_risk |
  gold_deferred_with_expected_risk | blocked_pending_observation |
  blocked_pending_equivalence | conflict_isolated
proof_or_warrant:
  authority: visible_spec | public_help | public_reference_probe |
    implementation_observation | post_eval_pressure | source_postmortem |
    methodological_equivalence | none
  proof_text: "..."
  evidence_refs: []
operators:
  Factor: applied | not_applicable | deferred
  Partition: applied | not_applicable | deferred
  Bind: applied | not_applicable | deferred
  Transform: applied | not_applicable | deferred
  Sequence: applied | not_applicable | deferred
  Expose: applied | not_applicable | deferred
  Compose: applied | not_applicable | deferred
  Warrant: applied
macro_refs: []
probe_refs: []
implementation_owner: parser | router | binder | transformer | renderer |
  diagnostics | runtime | harness | none | unknown
readiness:
  scoped: not_ready | scoped_ready | scoped_deferred | blocked
  gold: not_gold_ready | gold_ready | explicitly_deferred | not_gold_required
missing_children: []
expected_risk_if_deferred: "..."
```

A parent can be marked closed only if all children are closed under the same or stronger warrant.

---

## 5. Irrelevance proof

The key to avoiding explosion is a strict proof standard for irrelevant children.

A child can be removed from the active tree only through one of these proof types.

### 5.1 Semantic impossibility proof

```text
The child cannot exist for this program class because the parent semantics rule it out.
```

Example:

```text
A non-interactive pure file formatter has no clocked-source polling loop,
unless public schema reveals watch/interval/follow behavior.
```

### 5.2 Public schema absence proof

```text
A public help/list/schema surface was observed and the child is absent from that
schema, and there is no independent visible-spec or program-class trigger.
```

This is a bounded public-surface proof, not metaphysical certainty. It can support scoped/gold readiness only when the program class does not strongly imply the absent child.

### 5.3 Negative reference behavior proof

```text
A reference probe shows the candidate child input is rejected, ignored, or routed
as a different known branch.
```

Example:

```text
If --unknown-format exits with a typed invalid-format diagnostic, that branch is
not an accepted renderer dialect.
```

### 5.4 Pass-through proof

```text
The child exists syntactically but cannot affect behavior under the relevant
surfaces.
```

Pass-through must state which surfaces are protected:

```text
stdout
stderr
exit
files
state mutation
resource ownership
row universe
aggregation denominator
```

### 5.5 Explicit scoped deferral

This is not an irrelevance proof. It is allowed only for scoped experiments.

```text
The child might matter, but this run excludes it and carries expected risk.
```

A scoped deferral blocks gold readiness.

---

## 6. Parent closure rule

A parent node is closed only when:

```text
all required children are closed;
all child closure statuses are stronger than or equal to the parent handoff type;
all deferred children have expected score risk;
all probe-covered children have negative/boundary siblings where applicable;
all implementation-owned children have an owner;
all observation-sensitive children have split stdout/stderr/exit/file locks;
all resourceful children have methodological equivalence and ecology status.
```

Therefore:

```text
covered representatives != parent closed
```

A parent with unclosed required children must be labelled:

```text
representative_examples_only
```

or:

```text
branch_matrix_partial
```

not `fixed`.

---

## 7. Canonical hierarchical skeleton

The tree below is not task-specific. It is a reusable meta-ontology skeleton. A task activates relevant top-level classes and then inherits the children.

### 1. Control plane / invocation grammar

```text
1.1 Executable identity and version/usage surface
1.2 No-args, help, version, usage, list modes
1.3 Flag grammar: bool, value, enum, list, repeated, equals/separate forms
1.4 Positional grammar and -- separator behavior
1.5 Unknown flag / invalid value / missing value precedence
1.6 Environment/config/default overlay controls
1.7 Exit and channel contract for control-plane branches
1.8 Public-schema re-entry from help/list/usage observations
```

### 2. Public schema and mode family

```text
2.1 Mode inventory from README/spec
2.2 Mode inventory from public help/list/reference observation
2.3 Mode-to-ontology re-entry obligation
2.4 Mode-specific input route effects
2.5 Mode-specific transform effects
2.6 Mode-specific output/diagnostic effects
2.7 Mode readiness and deferral ledger
```

### 3. Input resource and route topology

```text
3.1 Stdin route
3.2 File path route
3.3 Directory route
3.4 Multiple resource route
3.5 Wildcard/glob route
3.6 Tilde/cwd/env/path normalization route
3.7 Compressed/encoded route
3.8 URL/network route
3.9 Output-file-as-resource route
3.10 Config resource route
3.11 Database/DSN/driver resource route
3.12 Missing/malformed/unreadable resource errors
3.13 Resource lifecycle and cleanup
```

### 4. Input dialect and value-domain grammar

```text
4.1 Format detection and explicit format selection
4.2 CSV/TSV/delimited grammar
4.3 JSON grammar
4.4 JSONL grammar
4.5 YAML grammar
4.6 TBLN grammar
4.7 LTSV grammar
4.8 Text/fixed-width grammar
4.9 Header/no-header and column identity
4.10 Null, empty, scalar, array, object, nested value domain
4.11 Type conversion and numeric/string/date policy
4.12 Invalid syntax and row-level error policy
4.13 Dialect-specific stdout/stderr/exit diagnostics
```

### 5. Embedded language / transform substrate

```text
5.1 Expression-only computation
5.2 File/resource-backed computation
5.3 Resource reference discovery inside language text
5.4 Resource-to-table or resource-to-subject binding
5.5 Aliases, quoted names, and naming collisions
5.6 Joins, comma joins, subqueries, repeated references
5.7 Multiple statements and last-result policy
5.8 Mutation statements and persistent state
5.9 Function/operator/type semantics
5.10 Error precedence: parse vs bind vs execute vs render
```

### 6. Subject, identity, binding, and aggregation

```text
6.1 Raw identity vs display identity
6.2 Resource identity vs table/subject identity
6.3 Column/field identity
6.4 Row universe and hidden-row policy
6.5 Selection/filter predicate ownership
6.6 Aggregation denominator
6.7 Exit denominator
6.8 Duplicate/collision policy
6.9 Persistent identity across statements/resources
```

### 7. State, lifecycle, and mutation

```text
7.1 Initialization/default overlay order
7.2 Resource acquisition order
7.3 Parse/validate/import/bind/execute/render order
7.4 Side effect before later failure
7.5 Mutation persistence and rollback/no-rollback
7.6 Teardown and cleanup
7.7 Rerun and cross-row contamination
7.8 Clocked/streaming/interactive lifecycle
```

### 8. Output router, renderer, and byte grammar

```text
8.1 Stdout/stderr/file routing
8.2 Output format selection and route inference
8.3 Raw renderer
8.4 Delimited/CSV renderer and quote policy
8.5 JSON renderer
8.6 JSONL renderer
8.7 YAML renderer
8.8 TBLN renderer
8.9 Markdown/ascii/vertical/table renderers
8.10 Header/no-header/null/final-newline policy
8.11 Width/wrapping/alignment policy
8.12 Output compression/encoding
8.13 File creation/overwrite/error policy
8.14 Renderer diagnostics and exit pairing
```

### 9. Diagnostics, fatal gates, and channel contracts

```text
9.1 Diagnostic mode inventory
9.2 Debug/analyze/list/config diagnostics
9.3 Split stdout/stderr/exit/files observation lock
9.4 Error message grammar
9.5 Fatal gate precedence lattice
9.6 Reachability witness surfaces
9.7 Dynamic fields and canonicalization policy
9.8 Suggestion/unknown-control diagnostics when applicable
```

### 10. Runtime substrate and observation ecology

```text
10.1 Target interpreter/compiler ABI
10.2 Packaged artifact equivalence
10.3 Dependency and optional-library availability
10.4 Filesystem/locale/time/terminal effects
10.5 Ports/sockets/processes/PTYs/signals/shared resources
10.6 Temp/cache/coverage/DB/file-lock ecology
10.7 Reached-product-behavior predicate
10.8 Harness/evaluator side-effect surfaces
10.9 Local-official methodological equivalence
```

### 11. Methodological equivalence and warrant

```text
11.1 Statement equivalence: Ω? / Ω* / Ωg
11.2 Public-interface equivalence
11.3 Probe/oracle equivalence
11.4 Witness-bundle equivalence
11.5 Target-substrate equivalence
11.6 Execution-topology equivalence
11.7 Resource-ecology equivalence
11.8 Behavioral terminal-leaf equivalence
11.9 Warrant/evidence/readiness equivalence
```

### 12. Probe, readiness, and implementation handoff

```text
12.1 Probe matrix compiler
12.2 Reference observation lock
12.3 Candidate comparison lock
12.4 Held-out/metamorphic anti-replay probes
12.5 Scoped-ready ledger
12.6 Gold-ready ledger
12.7 Implementation owner map
12.8 Batch contract and scope boundaries
12.9 Score-delta attribution by node
12.10 Bookkeeper acceptance/rejection gates
```

---

## 8. Deterministic application algorithm

```text
1. Read README/spec.
2. Select top-level classes that apply.
3. For each selected class, import all first-level children as inherited_required.
4. For each child, recursively import its children unless the child is proven irrelevant.
5. For every open child, apply Factor / Partition / Bind / Transform / Sequence / Expose / Compose / Warrant.
6. Trigger macro gates from the numbered tree, not from ad hoc prompt memory.
7. Create a terminal status row for every child.
8. Generate probe matrix rows only from terminal or near-terminal obligations.
9. Before implementation, require a closure ledger for the selected subtree.
10. After implementation, attribute every local/official failure to a numbered node.
11. If failure lands on an unnumbered concept, add a new node under the smallest correct parent and rerun inheritance closure.
```

The bookkeeper checks the shape, not only the prose.

---

## 9. V17 prompt rule

Replace:

```text
Apply the v16 rules and fix the remaining failures.
```

with:

```text
Use the numbered ontology tree.

First mark top-level classes as applies / not_applicable_proven / candidate_pending.
For every class marked applies, import all child obligations.
For every inherited child, produce one of: covered_terminalized,
covered_by_probe_matrix, proved_pass_through, proved_irrelevant,
scoped_deferred_with_expected_risk, blocked_pending_observation, or
conflict_isolated.

Do not patch code until the selected subtree has a child-closure ledger and a
probe matrix. Do not claim a parent macro is fixed unless every inherited child
is closed or explicitly deferred.
```

---

## 10. V17 bookkeeper rejection rules

The bookkeeper rejects a run when:

```text
1. A selected top-level class has missing child rows.
2. A child is omitted without proof of irrelevance.
3. A scoped deferral is represented as a proof of irrelevance.
4. A parent macro is called fixed while descendants are representative-only.
5. A patch is made before the probe matrix for that node exists.
6. A local parity suite remains unchanged after new inherited children are discovered.
7. Score improvement is reported without node-level attribution.
8. Official failures are used as product theory before methodological equivalence and reached-product-behavior are established.
9. Public help/list/schema observations are recorded as text but not re-entered into the numbered tree.
10. Output/input format names are treated as labels rather than dialect grammar subtrees.
```

---

## 11. Application to current trdsql-style task

A trdsql-like program activates at least:

```text
1 Control plane
2 Public schema and mode family
3 Input resource and route topology
4 Input dialect and value-domain grammar
5 Embedded language / transform substrate
6 Subject/identity/binding/aggregation
8 Output router/renderer/byte grammar
9 Diagnostics/channel contracts
10 Runtime substrate and observation ecology
11 Methodological equivalence
12 Probe/readiness/handoff
```

Therefore these are not optional once the class applies:

```text
3.5 wildcard/glob route
3.7 compressed/encoded route
3.10 config resource route
3.11 database/DSN/driver resource route
4.5 YAML grammar
4.6 TBLN grammar
4.8 text/fixed-width grammar
4.10 null/value-domain conversion
5.1 expression-only SQL
5.4 resource-to-table binding
5.6 joins/subqueries/repeated references
5.8 mutation/persistent state
8.3 raw renderer
8.8 TBLN renderer
8.10 header/null/final-newline policy
9.2 analyze/debug/list/config diagnostics
9.3 split stdout/stderr/exit/files lock
10.2 packaged artifact equivalence
10.7 reached-product-behavior predicate
```

The worker may prove some of these irrelevant for a bounded task, but it may not silently skip them. A run that implements gzip CSV, two-file joins, raw multi-column output, output JSON guessing, and invalid config has still not closed the tree unless it also closes or defers sibling routes, dialects, renderers, SQL statement types, diagnostics, and resource topology.

---

## 12. How this improves robustness

V17 forces the missing lowering step:

```text
audit parent discriminator
  -> numbered subtree
  -> inherited child obligations
  -> child closure ledger
  -> probe matrix
  -> bounded implementation batch
  -> node-level score attribution
```

The model is no longer trusted to remember the full meaning of a macro label. The macro label expands deterministically.

This should convert future progress from:

```text
52 -> 60 -> 68 through representative repairs
```

toward:

```text
parent selected
  -> child matrix closed in batches
  -> each batch has measurable frontier reduction
  -> remaining failures are attributed to explicit open nodes
```

---

## 13. Relationship to the constructive-witness frame

The numbered hierarchy is the theorem statement skeleton.

```text
Ω?  = candidate theorem statement from README/spec
TΩ? = numbered obligation tree
Λ   = inherited terminal obligations
Π   = probes/checkers generated from numbered leaves
Cᴡ  = witness bundle
```

The v17 judgment becomes:

```text
W ; Π ; Σ ⊢ Cᴡ : Ω*[TreeScope]
```

where `TreeScope` names exactly which numbered subtree was closed.

A witness is no longer judged against a vague macro such as `resource-backed SQL`. It is judged against a closed subtree such as:

```text
3.1, 3.2, 3.5, 3.7, 4.2, 4.3, 5.1, 5.4, 5.6, 8.3, 8.5, 9.3, 10.2
```

This makes scoped claims precise and prevents accidental promotion.

---

## 14. Immediate next experimental protocol

For the next trdsql run, do not ask the worker to “apply v15/v16.” Ask it to complete one numbered subtree batch.

Recommended batch:

```text
Batch A:
3 Input resource and route topology
5 Embedded language / transform substrate
6 Subject/identity/binding/aggregation
```

Required before editing source:

```text
1. Mark every child under 3, 5, and 6 as inherited_required or proved irrelevant.
2. Produce irrelevance/pass-through proofs where claimed.
3. Generate probe matrix rows for every non-deferred terminal child.
4. Declare which children are deferred and expected official-risk if any.
5. Patch only the children in the declared batch.
6. Report score delta and remaining failures by numbered node.
```

A second batch would then target:

```text
4 Input dialect and value-domain grammar
8 Output router, renderer, and byte grammar
9 Diagnostics, fatal gates, and channel contracts
```

This keeps the worker inside a bounded proof obligation instead of asking it to operationalize the entire meta-program at once.

---

## 15. Compact v17 invariant

```text
Selected parent classes import child obligations.
Child obligations persist until covered, proved irrelevant, proved pass-through,
blocked, or explicitly deferred.
No parent macro is fixed until its inherited subtree is closed at the claimed
readiness level.
```
