# JPlot v11: Resource Ecology as an Early Meta-Program Gate

## 0. Input update integrated

The v10 remaining-failure repair was tested by a 5.5 medium worker. Official eval stayed at:

```text
score: 98
raw:   705 passed / 16 failed / 1 skipped / 722 total
```

The worker classified the residue through C17-C22. Only one branch was treated as implementation-ready:

```text
C19 witness-scope overreach
  -> test_render_failure_with_steps_parameter
```

After the patch, that row no longer failed as protocol/witness overreach. It failed as:

```text
Address already in use
```

This is a useful negative result. It does not falsify v10. It confirms that v10's C19 diagnosis was locally plausible, but it also reveals that the next blocker is upstream:

```text
C17 RESOURCE_ECOLOGY_INTERFERENCE_GRAPH
```

The correct next move is not another local witness tweak. It is a focused P0 resource-ecology pass that identifies why fixed ports or long-lived processes remain occupied across sibling/rerun rows before product behavior is reached.

---

## 1. Revised core diagnosis

The score-98 plateau should now be read as:

```text
v9 repaired parent discriminator errors.
v10 repaired/confirmed witness-scope classification.
The remaining plateau is gated by observation ecology.
```

The most important layer-transition miss is no longer:

```text
field-spec grammar / dashboard graph topology
```

nor even just:

```text
terminal protocol witness scope
```

It is:

```text
observation ecology reaches or blocks product behavior
```

In other words, some rows are failing before they exercise the abstract program obligation they appear to test.

The failure chain is:

```text
program/probe/evaluator uses shared runtime resources
  -> resource is leaked, contested, not released, or order-dependent
  -> later row fails before candidate-specific product behavior is reached
  -> official row appears as a product failure
  -> but the immediate layer miss is observation ecology
```

For jplot, the visible ecology resource is mostly:

```text
fixed ports / HTTP servers / polling loops / process lifetime / PTY horizon
```

For other tasks, the same meta-pattern can be:

```text
temp files
coverage files
caches
file locks
DB files
PTY/tmux sessions
signals
subprocess trees
filesystem side effects
parallel workers
rerun scheduling
```

---

## 2. v11 meta-program patch

### 2.1 Promote C17 from late residue to early mandatory gate

In v10, C17 was a useful residue classifier:

```text
RESOURCE_ECOLOGY_INTERFERENCE_GRAPH
```

In v11, this becomes an early gate whenever the task or its probes use shared runtime resources.

New v11 gate:

```text
G0 OBSERVATION_ECOLOGY_GATE
```

Definition:

```text
OBSERVATION_ECOLOGY_GATE
  = RESOURCE_ECOLOGY_INTERFERENCE_GRAPH
  + REACHES_PRODUCT_BEHAVIOR predicate
  + setup/teardown warrant
  + rerun/parallel/sibling collision model
```

Operator expansion:

```text
RESOURCE_ECOLOGY_INTERFERENCE_GRAPH
  = Factor + Partition + Bind + Sequence + Compose + Expose + Warrant
```

Meaning:

| Kernel operator | Resource-ecology interpretation |
|---|---|
| Factor | Reify ports, sockets, processes, PTYs, files, locks, caches, temp dirs, coverage files, DBs, signal handlers, test workers. |
| Partition | Split available, occupied, leaked, contested, owned-by-candidate, owned-by-probe, owned-by-harness, owned-by-previous-row, owned-by-environment. |
| Bind | Attach each resource to owner, row, process tree, probe, harness, dependency, or evaluator phase. |
| Sequence | Model setup, acquisition, use, fatal exit, signal, teardown, wait, final verification, rerun. |
| Compose | Model cross-row, sibling, rerun, parallel-worker, and scout/eval interference. |
| Expose | Define observable evidence: `Address already in use`, hanging read, missing output due to premature exit, coverage artifact, stale cache, locked file. |
| Warrant | Decide whether the row reached product behavior or should be classified as pre-product resource failure. |

### 2.2 Add a reaches-product-behavior predicate

Every observed failure in a resourceful task should be annotated with:

```text
REACHED_PRODUCT_BEHAVIOR = yes | no | uncertain
```

Definitions:

```text
yes:
  Candidate-specific parser/transform/render/source logic was entered and produced an observable product-domain state.

no:
  Failure happened during resource setup, acquisition, collision, test harness setup, process spawning, port binding, PTY setup, file lock acquisition, or stale side-effect handling.

uncertain:
  The row emitted a product-looking failure, but resource state could have prevented the intended obligation from being reached.
```

Core rule:

```text
If REACHED_PRODUCT_BEHAVIOR != yes,
  do not promote the failure to product-theory evidence.
First assign resource owner, lifecycle state, setup path, teardown path, and collision edge.
```

This is the same discipline as the broader ODEU boundary law: diagnostic or substrate evidence is useful, but it does not automatically promote to readiness or authority; local authority and promotion require the correct owner and evidence layer. The harness matrix explicitly distinguishes diagnostic evidence from readiness promotion and separates provider possibility from harness authority. fileciteturn35file2

---

## 3. Refinements beyond v8/v9/v10

The v8 kernel remains valid:

```text
Factor
Partition
Bind
Transform
Sequence
Expose
Compose
Warrant
```

But several operators need sharper contracts.

### 3.1 Sequence must include cross-row ecology lifecycle

Old Sequence was mostly:

```text
program lifecycle
startup -> parse -> source -> transform -> render -> exit
```

v11 Sequence must also include:

```text
probe lifecycle
preflight -> resource acquire -> run -> fatal/success -> teardown -> wait -> verify-clean -> next row
```

The key point is that lifecycle does not end at candidate process exit. It ends when the resource graph is clean enough for the next row.

### 3.2 Bind must bind resources to owners, not just program roles

Old Bind attached:

```text
consumer / subject / denominator / display role
```

v11 Bind also attaches:

```text
resource -> owner
resource -> row
resource -> process tree
resource -> harness phase
resource -> product phase
resource -> teardown obligation
```

This prevents `Address already in use` from being treated as a generic product error without knowing which actor owns the existing listener.

### 3.3 Compose must model row-order non-commutation

v10 Compose modeled feature interactions inside the product. v11 Compose must also model:

```text
row A passes alone but poisons row B
row B passes alone but poisons row A
A -> B differs from B -> A
rerun differs from fresh run
parallel differs from serial
scout run contaminates official run
```

A row-order-dependent failure is not yet stable product evidence.

### 3.4 Expose must include pre-product observable surfaces

Pre-product surfaces include:

```text
Address already in use
connection refused before product source logic
PTY read/write unavailable before renderer logic
stale temp file found before parser logic
coverage file write before intended assertion
lock timeout before candidate computation
```

These should be classified as ecology surfaces unless there is direct evidence that the product obligation was reached.

### 3.5 Warrant must distinguish product truth from observation truth

Add warrant labels:

```text
product_observed
pre_product_resource_failure
observer_induced_failure
harness_side_effect_surface
candidate_teardown_failure
dependency_teardown_failure
masked_product_obligation
post_eval_support_only
```

A failure can be official and still not be product-theory evidence. Official eval reveals pressure; Warrant decides what kind of pressure it is.

---

## 4. Mandatory trigger rule for OBSERVATION_ECOLOGY_GATE

The gate is mandatory whenever the README/spec, expected behavior, public scout, local tests, or evaluator row touches any of:

```text
ports / sockets / HTTP servers
PTYs / terminals / tmux
subprocesses / child process trees
long-running loops / polling / watchers
signals / Ctrl-C / termination handling
temp files / caches / generated files
coverage files / reports / harness artifacts
locks / DB files / filesystem side effects
parallel test workers / reruns / shared fixtures
network services / browser sessions / external daemons
```

The gate is especially mandatory if any failure says:

```text
Address already in use
connection refused
broken pipe
resource busy
file exists
permission denied on cleanup
read timeout
process did not terminate
leaked process
coverage file missing/present unexpectedly
```

---

## 5. P0 resource-ecology scout pass before any new implementation patch

The next loop should not patch product code until P0 has been run.

### 5.1 P0 goal

P0 answers:

```text
Which resource is contested?
Who owns it?
When was it acquired?
Why was it not released?
Which later row is masked?
Did the masked row reach product behavior?
```

### 5.2 P0 required observations

For each suspicious row or row cluster, record:

```text
row_id
test_name
command / argv
resource_kind
resource_id
pre_state
post_state
owner_pid
owner_cmdline
owner_process_tree
candidate_pid
harness_pid
acquire_time
release_time
exit_status
stdout/stderr
reached_product_behavior
collision_edge
cleanup_result
rerun_result
isolated_result
```

### 5.3 P0 probe matrix

#### P0-A: clean baseline

Run before any jplot candidate row:

```text
record listening ports
record candidate-like processes
record active HTTP servers
record PTY/tmux state where applicable
record temp/cache/coverage artifacts
```

Expected classification:

```text
baseline_clean | baseline_dirty
```

If baseline is dirty, no product probe should run yet.

#### P0-B: isolated failing row

Run each current `Address already in use` row alone from a clean baseline.

Record:

```text
passes alone?
fails alone?
who owns the port before the row?
who owns the port after the row?
```

Interpretation:

```text
fails alone with clean baseline:
  likely candidate/test fixed-port conflict or immediate teardown bug.

passes alone but fails in suite:
  cross-row/rerun ecology issue.
```

#### P0-C: pairwise order probe

For each suspected poisoner row A and masked row B:

```text
run A -> B
run B -> A
run A alone
run B alone
run A -> cleanup-check -> B
```

Classification:

```text
A poisons B
B poisons A
both share resource
external fixture owns resource
candidate leaks resource
harness leaks resource
uncertain
```

#### P0-D: teardown path probe

Run rows that involve polling, intervals, steps, signals, Ctrl-C, timeout, or PTY shutdown.

After each run:

```text
wait bounded interval
check process tree
check listening sockets
check temp/cache/coverage files
send cleanup signal if needed
verify final clean state
```

Important distinction:

```text
process exited but child listener survived
process alive because loop horizon is legitimate
process killed but socket still LISTEN-owned by orphan
TIME_WAIT only, no LISTEN owner
```

`TIME_WAIT` alone should not be conflated with `Address already in use` unless the product or OS binding policy makes it operationally blocking.

#### P0-E: rerun contamination probe

Run the same subset twice without manual cleanup:

```text
subset run 1
immediate subset run 2
resource snapshot before/after each
```

This distinguishes:

```text
single-run leak
rerun-only leak
parallel-worker leak
worker-process cleanup failure
```

#### P0-F: official-like scheduler probe

Mimic the evaluator's sequencing as closely as possible:

```text
same row order
same timeout style
same worker count if known
same environment variables
same PTY/non-PTY profile
```

The goal is not to overfit official. The goal is to reproduce the observation ecology that decides whether product obligations are reached.

---

## 6. JPlot-specific repair scaffold after P0

This is not a patch list. It is a branch ownership scaffold.

### 6.1 JPlot resource graph

```text
JPlotResourceGraph
  ├─ HTTPSourceServer
  │   ├─ fixed port
  │   ├─ test-owned server
  │   ├─ candidate-owned client
  │   ├─ polling loop
  │   └─ status/body/timeout authority
  ├─ ProcessTree
  │   ├─ main candidate process
  │   ├─ polling child/async task if any
  │   ├─ server fixture process if any
  │   └─ signal/timeout kill path
  ├─ TerminalSession
  │   ├─ PTY allocation
  │   ├─ window-size query
  │   ├─ protocol witness emission
  │   └─ observer read horizon
  ├─ HarnessArtifacts
  │   ├─ coverage files
  │   ├─ temp dirs
  │   ├─ stdout/stderr capture files
  │   └─ stale per-row state
  └─ Scheduler
      ├─ isolated row
      ├─ sibling sequence
      ├─ rerun
      └─ parallel worker possibility
```

### 6.2 Branch ownership decisions

After P0, classify each remaining row as one of:

```text
candidate_resource_lifecycle_bug
harness_resource_lifecycle_bug
evaluator_fixture_collision
resourceful_product_behavior
masked_product_obligation
non_resource_product_gap
```

Only the last two categories should feed product ontology repair.

### 6.3 Likely jplot branches to re-open after C17 is neutralized

Once resource ecology is clean, the following branches may need reclassification:

```text
C18 RENDER_TRANSFORM_SUCCESS_CONTRACT
C20 OBSERVER_HORIZON_CONTRACT
C21 CONFLICTED_SUBSTRATE_RULE
C22 HARNESS_SIDE_EFFECT_SURFACE
```

Current score-98 failures in these groups are not all equally trustworthy while `Address already in use` can mask them. P0 should establish which rows are true product misses and which are masked by ecology.

---

## 7. Public scout vs conceptual descent

### 7.1 What conceptual descent should have derived earlier

A better README/spec-only descent should not know exact ports or official order, but it should derive the need for C17 whenever it sees:

```text
URL source
HTTP polling
steps/interval behavior
terminal/PTY behavior
long-running process behavior
signals/Ctrl-C
coverage or side-effect artifacts
```

From those concepts alone, the meta-program should require:

```text
resource owner lattice
setup/teardown lifecycle
observer horizon
rerun/sibling contamination model
pre-product failure label
```

### 7.2 What only a better public scout could discover

A public scout is needed for exact details:

```text
which fixed port is used
which process owns it
whether failures are isolated or order-dependent
whether signal/timeout leaves child processes
whether a row reaches product behavior before failing
whether official-like reruns reproduce collision
whether PTY or terminal setup contaminates later rows
whether coverage/temp artifacts are product surfaces or harness surfaces
```

### 7.3 Revised split

```text
Conceptual descent responsibility:
  derive that observation ecology is mandatory.

Public scout responsibility:
  populate the resource graph and collision edges.

Implementation responsibility:
  patch only the owner/lifecycle branch proven by the graph.
```

---

## 8. Implementation transfer errors vs theory gaps

### 8.1 Theory gaps now confirmed

```text
C17 was too late in the loop.
Resource ecology must be an early gate, not a residue bucket.
Failure rows need REACHED_PRODUCT_BEHAVIOR labels.
Warrant must separate product evidence from observation ecology evidence.
Compose must include row-order/rerun non-commutation.
Sequence must include teardown and post-row cleanup.
```

### 8.2 Likely implementation transfer errors

These become implementation-transfer only after P0 identifies the owner:

```text
candidate process fails to terminate polling loop
candidate leaves child listener/process alive
candidate opens or conflicts with fixed port unexpectedly
candidate ignores signal/timeout cleanup
candidate emits startup witness globally after branch no longer allows it
```

### 8.3 Likely harness/probe ecology errors

```text
local scout leaves server running
worker/evaluator rerun keeps fixed port occupied
test fixture does not tear down on failure
parallel workers share fixed resource
coverage/temp artifact from previous row changes later row
```

### 8.4 Still-mixed branches

```text
render success contract
terminal observer horizon
protocol witness scope
terminal no-source conflict
coverage artifact side effect
```

These should not be called pure product gaps until C17 is neutralized.

---

## 9. Readiness-state changes

Add ecology-specific readiness states:

```text
ecology-unready:
  Task/probes touch shared resources but no resource graph exists.

ecology-probe-ready:
  Resource kinds, suspected owners, commands, and observable probes are declared.

ecology-scoped-ready:
  A bounded resource graph has clean setup/teardown observations for the declared rows.

product-probe-ready:
  The row is known to reach product behavior, so product probes can be trusted.

implementation-ready:
  The owner and lifecycle bug are identified; patch target is not a guess.

gold-ready:
  Product obligations and resource ecology are both closed or explicitly isolated.
```

Important rule:

```text
A product branch cannot be gold-ready while its probe ecology is ecology-unready.
```

---

## 10. Bookkeeper gates for v11

For every task, the bookkeeper must ask:

```text
Does the program or any probe touch shared runtime resources?
If yes, was OBSERVATION_ECOLOGY_GATE activated before product classification?
Are resources factored and owners bound?
Are setup, teardown, and post-row clean checks present?
Are sibling/rerun/parallel collision paths tested or explicitly ruled out?
Does each failure row say whether product behavior was reached?
Were pre-product failures prevented from becoming product-theory evidence?
Did any implementation patch happen before P0 when P0 was required?
Are hidden-source/evaluator failures separated from local scout contamination?
```

If any answer is missing, the task is not implementation-ready for affected rows.

---

## 11. How this moves jplot from 98 toward 100

The next highest-yield move is not another renderer/protocol patch. It is:

```text
P0 resource-ecology pass
  -> identify actual port/process owner
  -> patch owner/lifecycle cleanup or scheduler isolation
  -> rerun score-98 failing subset
  -> reclassify any unmasked product failures
```

Expected value of P0:

```text
It may directly recover rows currently failing as Address already in use.
It will reveal whether C18/C20/C21/C22 are real product misses or masked observations.
It prevents the agent from burning patches on rows that never reached product behavior.
```

This is a general ADEU upgrade:

```text
Observation ecology is part of the proof environment.
If the proof checker is contaminated, failed rows are not yet failures of the program theorem.
They are failures of the witness-checking ecology.
```

In constructive-witness notation:

```text
W ; Π ; Σ ⊢ Cᴡ : Ω*
```

v11 adds that `Π` and `Σ` must be ecology-clean enough for the judgment to mean product satisfaction. If shared resources are dirty, the judgment has not reached the product theorem; it has failed in the checker substrate.

---

## 12. Compact v11 patch summary

Add to the meta-program:

```text
G0 OBSERVATION_ECOLOGY_GATE
  Mandatory for ports, sockets, PTYs, subprocesses, signals, temp files,
  caches, coverage files, locks, DBs, filesystem side effects, parallel workers,
  reruns, and long-running loops.
```

Add to every relevant failure row:

```text
REACHED_PRODUCT_BEHAVIOR = yes | no | uncertain
RESOURCE_OWNER = candidate | harness | fixture | previous-row | environment | unknown
COLLISION_EDGE = none | same-row | sibling | rerun | parallel | scout-to-eval | environment
ECOLOGY_WARRANT = product_observed | pre_product_resource_failure | observer_induced_failure | masked_product_obligation | harness_side_effect_surface
```

Add mandatory pre-patch probe:

```text
P0 RESOURCE_ECOLOGY_INTERFERENCE_GRAPH
```

Do not promote masked rows into product-theory repair until P0 establishes that candidate-specific behavior was reached.
