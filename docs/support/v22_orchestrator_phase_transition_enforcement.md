# Program Reconstruction Meta-Program v22: Orchestrator Phase-Transition Enforcement

Authority layer: proposed structural meta-program patch.

Purpose: make the orchestrator a first-class semantic controller. Prior revisions strengthened the ontology, probe, evidence, anti-replay, and worker-handoff rules, but recent runs show that a capable worker can still perform the bounded task it was given while the global run fails because the orchestrator transitioned phases incorrectly, skipped gates, leaked artifacts, or promoted evidence too early.

Core thesis:

```text
The orchestrator is not a scheduling convenience.
It is the state machine that preserves the semantic circuit.
```

The meta-program therefore needs an explicit orchestrator contract, not only worker instructions.

---

## 1. Problem statement

The recent failure pattern is not only:

```text
worker misunderstood the task
worker produced an incomplete implementation
worker patched representative examples
```

It is also:

```text
orchestrator allowed an illegal phase transition
orchestrator handed implementation-visible material that should have been checker-only
orchestrator treated local parity as readiness without proving generalization
orchestrator moved from semantic pools to implementation before reconciliation was certified
orchestrator ran official eval before the methodological gates were actually closed
```

The Phase 10 v20 run is the clearest example. It had strong-looking local gates:

```text
Phase7 reference replay: 53 / 53
Candidate local Phase7:  53 / 53
Locked scoped probes:    42 / 42
Heldout sentinels:       11 / 11
```

but official eval collapsed to:

```text
score: 2
52 passed / 1350 failed / 1 skipped / 1403 total
```

The audit identifies the dominant class as a witness-generalization failure: `1268` failures returned `rc 127` for unlisted argv shapes, and the local green gate was green because the same manifest and expected fixtures were visible to the implementer. The “heldout” sentinels were not true heldouts because they were included in the implementation-visible manifest.

That is not only an anti-replay failure. It is an orchestrator transition failure:

```text
probe contract / local gate / implementation handoff
  -> transitioned without sealed checker-only split
  -> local parity became replayable
  -> official eval measured replay collapse
```

---

## 2. New v22 invariant

```text
A worker may execute a bounded task correctly and the run can still be invalid
if the orchestrator did not prove the transition into that task was legal.
```

Therefore:

```text
Every phase transition must be typed, gated, evidenced, and recorded before
any worker task is dispatched.
```

Canonical judgment:

```text
W ; Φᵢ ; Aᵢ ⊢ transition Φᵢ -> Φⱼ allowed
```

Where:

```text
W   = warrant/evidence layer
Φᵢ  = current phase state
Φⱼ  = proposed next phase state
Aᵢ  = artifacts available at the transition boundary
```

If the transition cannot be proven, the orchestrator must not improvise. It must either:

```text
1. run the missing gate;
2. dispatch a worker to produce the missing artifact;
3. explicitly downgrade the run posture to scoped experiment;
4. stop and report a blocked transition.
```

Forbidden orchestrator behavior:

```text
phase skipping
implicit readiness promotion
narrative substitution for required artifacts
implementation handoff before reconciliation closure
local parity promotion without anti-replay closure
official eval as a substitute for local method gates
post-eval patching without layer attribution
```

---

## 3. Orchestrator is a distinct role

The system now has at least four roles:

```text
1. Generator / semantic compiler
   Builds candidate ontology, HOB tree, semantic-pool outputs, and probe pressure.

2. Scout / observer
   Produces public reference observations, split by stdout/stderr/exit/files.

3. Worker / implementer
   Executes a bounded repair or implementation task under the active contract.

4. Orchestrator / transition governor
   Decides which phase is legal next, verifies artifacts, separates evidence,
   dispatches bounded workers, and prevents illegal promotions.
```

The orchestrator must not act like a general-purpose reasoning worker. It should not “vibe” the next step. It must be a deterministic controller over the meta-program state.

The orchestrator’s job is not:

```text
think of a reasonable next patch
summarize the audit and ask a worker to improve things
combine all insights into one big implementation task
trust local green rows as readiness
```

The orchestrator’s job is:

```text
read current state
check legal transition predicates
verify required artifacts exist and match schema
decide next phase from the allowed transition table
dispatch exactly the next bounded worker task
reject or downgrade if gates are missing
record the transition proof
```

---

## 4. Phase state machine

The orchestrator must maintain a phase state. The following phase ladder is the default for ProgramBench-style reconstruction.

```text
P0  Intake / task packet validation
P1  Visible-spec base ontology
P2  Top-level HOB activation
P3  Inherited child obligation fill
P4  Orthogonal semantic pool descent
P5  Pool reconciliation to numbered HOB nodes
P6  Public schema / scout observation
P7  Public-schema re-entry and tree repair
P8  Probe matrix compilation
P9  Reference observation lock
P10 Operationalization equivalence check
P11 Implementation handoff contract
P12 Implementation worker execution
P13 Packaged witness / target-substrate parity
P14 Local candidate gate
P15 Anti-replay / sealed / metamorphic gate
P16 Regression conservation gate
P17 Official eval experiment or gold attempt
P18 Post-eval layer-transition audit
P19 Meta-program amendment / next-run frontier
```

A phase can emit scoped artifacts, but a scoped artifact cannot be used as a gold artifact unless the corresponding promotion gate is passed.

---

## 5. Phase contracts

Each phase has a required contract.

### P0 Intake / task packet validation

Required:

```text
task README/spec located
reference executable status known, if available
official eval access posture known
artifact paths and authority layers recorded
run posture initialized: clean_first_pass | scoped_repair | post_eval_repair | source_postmortem
```

Illegal transition:

```text
P0 -> implementation
P0 -> official eval
```

### P1 Visible-spec base ontology

Required output:

```text
base ontology graph
program class assessment
resource/input/output/control/state/runtime families
initial evidence authority labels
unknown/public-scout-needed rows
```

The base pass uses native semantic interpretation of README/spec only.

### P2 Top-level HOB activation

Required output:

```text
numbered top-level HOB classes:
  applies | not_applicable | candidate_pending | blocked_pending_public_schema
```

Rule:

```text
Top-level classes are assessed semantically.
Once a parent applies, child obligations are inherited by default.
```

### P3 Inherited child obligation fill

Required output:

```text
for every active parent:
  every child is covered, proved irrelevant, proved pass-through, blocked,
  conflict-isolated, or explicitly deferred with expected risk
```

Illegal transition:

```text
P3 -> implementation when active child rows are missing status
```

### P4 Orthogonal semantic pool descent

Required pools by default:

```text
P  Program mechanism
U  Intent / utility
S  Public schema / discovery surface
R  Resource ecology and route topology
D  Data dialect and value-domain grammar
T  Transform / embedded language substrate
O  Output / downstream-consumer projection
N  Negative utility / failure precedence
E  Methodological equivalence / substrate
H  Historical delta / regression conservation
```

Each pool produces discriminator pressure, not implementation truth.

### P5 Pool reconciliation to numbered HOB nodes

Required output:

```text
triangulation board
pool output -> numbered HOB node mapping
unmapped obligations
out-of-scope proofs
new candidate nodes
probe pressure by node
```

Rule:

```text
No semantic pool may close a parent by itself.
No implementation handoff while pool outputs are unmapped unless explicitly blocked or deferred.
```

### P6 Public schema / scout observation

Required output:

```text
public help/no-args/version/unknown/control observations
stdout/stderr/exit/files split
public schema item ledger
resource/mode/format/control inventory
```

No merged transcript can lock byte/channel behavior.

### P7 Public-schema re-entry and tree repair

Required output:

```text
for each discovered schema item:
  parent node
  inherited children
  terminalization status
  probe obligations
  deferral/pass-through/irrelevance proof if not covered
```

Rule:

```text
Public schema observation is not commentary.
It re-enters the ontology tree.
```

### P8 Probe matrix compilation

Required output:

```text
probe rows keyed by numbered HOB node
positive / negative / boundary / interaction / regression / held-out roles
oracle authority
surface split: stdout, stderr, exit, files, timing, resources
implementation-visible vs checker-only designation
```

Illegal transition:

```text
P8 -> implementation if probes are only representative examples for an active parent macro
```

### P9 Reference observation lock

Required output:

```text
reference observation ledger
split stdout/stderr/exit/files/resource/timing fields
byte snapshots where relevant
unresolved conflicts
observation authority labels
```

### P10 Operationalization equivalence check

Required judgment:

```text
W ⊢ audit_theory ≃[operationalization] worker_task
```

Required output:

```text
all audit/HOB nodes preserved in worker task
macro subbranches expanded
probes generated before patching
implementation owners bound
deferrals explicit
closure metrics defined
```

This is the gate that prevents:

```text
post-hoc audit identifies full parent cause
worker receives compressed prose and patches representatives
```

### P11 Implementation handoff contract

Required output:

```text
handoff_type: scoped_experiment | gold_attempt
allowed artifacts
forbidden artifacts
implementation-visible examples
checker-only probes
sealed post-implementation probes
mechanism posture requirements
anti-replay constraints
batch boundary
expected deferral risks
```

The orchestrator must verify the handoff contract before dispatching the implementer.

### P12 Implementation worker execution

Worker may only edit within the batch boundary.

Required return:

```text
files changed
implementation owners touched
which numbered nodes targeted
which nodes explicitly not touched
local probes run
regressions observed
open siblings
```

### P13 Packaged witness / target-substrate parity

Required checks:

```text
pack exact submitted artifact
unpack clean
compile/syntax/import under target substrate
entrypoint smoke
runtime fingerprint
dependency availability
line endings / permissions / executable path
```

Rule:

```text
No code witness can be evaluated as a program witness until the witness bundle
runs under the target substrate.
```

### P14 Local candidate gate

Required:

```text
candidate vs reference over implementation-visible regression probes
split surfaces preserved
resource ecology clean
no scoped/gold promotion mismatch
```

Local parity is not generalization readiness.

### P15 Anti-replay / sealed / metamorphic gate

Required:

```text
checker-only probes generated or selected after implementation
metamorphic probes for active open-domain macros
literal overlap audit
mechanism posture audit
fallback surface coverage
```

Rule:

```text
If the program theorem is generative, the witness must be generative.
A finite lookup witness is valid only when the program statement itself is a
finite lookup table.
```

### P16 Regression conservation gate

Required:

```text
previously green sentinel set
known regression-prone siblings
score delta attribution by HOB node
regressed nodes and suspected shared parent
```

The second-track audit showed real utility-lane wins but also large regressions; this gate prevents orthogonal discovery from becoming unguarded implementation churn.

### P17 Official eval experiment or gold attempt

Required precondition:

```text
P13, P14, P15, P16 green
or run explicitly marked as scoped experiment with expected risk
```

Official eval classification:

```text
gold closeout
scoped experiment
method test
post-eval pressure sampler
```

A run cannot retroactively be called gold because it improved.

### P18 Post-eval layer-transition audit

Required output:

```text
score/raw row summary
layer attribution
fixed/persistent/regressed counts
first explanatory broken transition
broad-bucket split requirements
whether official failures are product evidence or method evidence
```

### P19 Meta-program amendment / next-run frontier

Required output:

```text
meta-program patch candidate
new gates/macros if needed
frontier batch plan
which prior phase must be rerun
which artifacts are invalidated
```

---

## 6. Orchestrator transition ledger

Every phase transition must write a ledger row.

```yaml
transition_id: T-...
from_phase: P8
to_phase: P9
transition_kind: normal | reentry | downgrade | blocked | repair_loop
run_posture_before: scoped_repair
run_posture_after: scoped_repair
required_inputs:
  - probe_matrix_v...
  - numbered_hob_tree_v...
input_artifacts_present: true
input_artifact_hashes: []
preconditions:
  all_active_nodes_have_probe_rows: pass
  checker_only_designation_present: pass
  broad_parent_macros_matrix_ready: fail
failed_preconditions:
  - broad_parent_macros_matrix_ready
transition_decision: blocked
blocker_owner: orchestrator
next_required_action: dispatch_probe_matrix_compiler_for_nodes_3_5_8
warrant_refs: []
notes: string
```

The orchestrator cannot merely say “proceeding.” It must prove why proceeding is legal.

---

## 7. Orchestrator baton

Each worker receives a baton, not the full global context.

```yaml
worker_baton:
  task_id: string
  phase: P12_implementation_worker_execution
  handoff_type: scoped_experiment | gold_attempt
  allowed_inputs:
    - numbered_nodes: [3.2, 3.5, 5.2.4]
    - rule_descriptions
    - representative_public_examples
    - implementation_visible_regression_probes
  forbidden_inputs:
    - checker_only_exact_bytes
    - sealed_probe_manifest
    - official_eval_hidden_rows
    - post_implementation_metamorphic_seeds
  source_authority_allowed:
    visible_spec: true
    public_observation: true
    source_postmortem: false
    official_failure_names: false
  implementation_boundaries:
    allowed_files: []
    allowed_modules: []
    forbidden_strategy:
      exact_argv_dispatch: true
      fixture_signature_dispatch: true
      embedded_oracle_bytes: true
      finite_manifest_lookup: true
  required_return_artifacts:
    - node_delta_report
    - local_probe_result
    - changed_files
    - regression_report
    - open_sibling_report
```

The baton makes artifact leakage enforceable.

---

## 8. Checker-only split must be orchestrator-owned

The worker cannot be responsible for not using information it was handed.

Therefore:

```text
The orchestrator owns information partitioning.
```

The orchestrator must maintain three artifact classes:

```text
implementation_visible
checker_only
orchestrator_only
```

Examples:

```text
implementation_visible:
  numbered HOB obligations
  rule statements
  public examples
  representative non-secret observations
  regression probes already known to candidate

checker_only:
  exact heldout argv shapes
  exact heldout byte oracles
  post-implementation generated fixtures
  random/metamorphic seeds
  official-like sealed probes

orchestrator_only:
  phase-transition ledger
  contamination checks
  full score attribution
  artifact leakage ledger
```

If checker-only material is exposed to the implementation worker, the orchestrator must downgrade that probe:

```text
true heldout -> regression sentinel
anti-replay evidence -> invalidated
```

That is exactly the Phase 10 v20 failure: the “heldout” rows functioned as regression sentinels because they were implementation-visible.

---

## 9. Orchestrator anti-vibe rules

Reject these orchestrator moves:

```text
“The worker knows v20, so implement remaining failures.”
“Local parity is green, so run official.”
“The audit says resource topology, so patch resource topology.”
“The second track found utility wins, so merge it into implementation.”
“The heldout sentinels passed, even though the implementer saw them.”
“The official score improved, so prior gate sequence was fine.”
“The official score collapsed, so product ontology is wrong.”
```

Allowed moves:

```text
“P5 reconciliation is incomplete; dispatch reconciliation worker.”
“P8 probe matrix lacks checker-only split; block implementation.”
“P10 operationalization equivalence failed; rewrite worker baton.”
“P15 anti-replay invalid because heldouts leaked; generate sealed probes after implementation.”
“P17 official eval was a method experiment, not product evidence.”
“P18 shows earliest broken transition was implementation handoff -> local parity.”
```

---

## 10. Phase ownership map

```text
P0-P3   Orchestrator + semantic generator
P4      Independent semantic-pool workers
P5      Reconciliation worker, orchestrator validated
P6      Scout/observer worker
P7      Generator re-entry worker
P8      Probe compiler worker
P9      Reference observer worker
P10     Bookkeeper / operationalization auditor
P11     Orchestrator only
P12     Implementation worker
P13     Packaging/substrate checker
P14     Local probe checker
P15     Sealed/metamorphic checker, not implementation worker
P16     Regression auditor
P17     Orchestrator invokes official eval only after gates
P18     Audit worker
P19     Meta-program editor / orchestrator frontier update
```

Key point:

```text
P11 is orchestrator-only.
Implementation handoff is not a worker suggestion.
It is a controlled transition artifact.
```

---

## 11. Integration with v20 semantic pools

v20’s orthogonal semantic pools remain valuable, but the orchestrator must stop them from becoming loose prose.

Required transition:

```text
P4 semantic pool output
  -> P5 triangulation board
  -> numbered HOB node mapping
  -> inherited children
  -> P8 probe matrix
  -> P11 bounded handoff
```

Forbidden shortcut:

```text
P4 semantic pool output
  -> implementation worker
```

The Phase 12B second-track audit showed that the utility lane found real new behavior families: CLI discovery, input shaping, structured JSON/JQ values, SQL over resource-bound files, resource identity/path utility, and raw downstream output. It also left many failures and regressions. That means the utility lane is a discriminator source, not a direct implementation authority.

The orchestrator must enforce:

```text
semantic pool output = discriminator pressure
reconciled HOB node = obligation candidate
probe/reference observation = behavior evidence
implementation = witness attempt
```

---

## 12. Integration with v21 anti-replay

v21 added the right anti-replay principle, but v22 assigns enforcement to the orchestrator.

```text
v21: finite lookup witnesses are invalid for generative programs.
v22: orchestrator must prevent the handoff and local gate from making finite
     lookup the easiest strategy.
```

Required orchestration:

```text
1. Give implementer rule descriptions and public representative examples.
2. Do not give implementer sealed argv/byte oracles.
3. Require mechanism architecture before coding.
4. Run static replay audit after coding.
5. Generate/select sealed probes after coding.
6. Run metamorphic probes over active generative families.
7. Only then allow local readiness promotion.
```

If this sequence is not followed, the run is classified as:

```text
method experiment / replay-risk invalidated
```

not as:

```text
product reconstruction attempt
```

---

## 13. Orchestrator hard gates

Add these v22 gates.

### ORCH-1 Phase State Declaration Gate

Every run must declare:

```text
current_phase
run_posture
active gates
allowed next phases
blocked transitions
```

### ORCH-2 Transition Proof Gate

No transition without a ledger row proving preconditions.

### ORCH-3 Artifact Partition Gate

Before implementation handoff:

```text
implementation_visible / checker_only / orchestrator_only
```

must be declared.

### ORCH-4 Re-entry Enforcement Gate

If public scout, semantic pools, official audit, or source-postmortem discovers a larger statement, the orchestrator must re-enter the earlier phase instead of continuing downstream.

Example:

```text
help discovers new public schema
  -> return to P7, not P12
```

### ORCH-5 Scoped vs Gold Posture Gate

The orchestrator must choose:

```text
scoped_experiment
gold_attempt
method_test
```

before implementation. The label cannot be retroactively changed after score movement.

### ORCH-6 Worker Baton Completeness Gate

Worker task must include:

```text
numbered nodes
batch scope
allowed artifacts
forbidden artifacts
implementation owners
probe responsibilities
deferrals
success criteria
```

### ORCH-7 Worker Baton Non-Overload Gate

If a worker task spans too many active parent macros, the orchestrator must split the batch.

Reject handoffs like:

```text
fix SQL binder + input dialects + output renderers + config + diagnostics + compression
```

unless the run is explicitly a broad exploratory experiment.

### ORCH-8 Anti-Replay Separation Gate

No heldout or sealed probe may be visible to implementation construction.

### ORCH-9 Local Gate Interpretation Gate

The orchestrator must label local pass results as one of:

```text
regression_green
scoped_behavior_green
anti_replay_green
gold_readiness_green
```

Local byte equality over visible probes is never automatically `gold_readiness_green`.

### ORCH-10 Official Eval Authorization Gate

Official eval is allowed only when:

```text
P13 packaged witness parity passed
P14 local gate passed at declared level
P15 anti-replay passed or explicitly deferred
P16 regression conservation passed
transition ledger authorizes P17
```

Otherwise official eval is still allowed as an experiment, but its result must be labeled method pressure, not product truth.

---

## 14. Audit template for orchestrator failures

Post-run audits must now ask:

```text
Was the product ontology wrong?
Was the worker task incomplete?
Was the implementation buggy?
Or did the orchestrator make an illegal transition?
```

Required row:

```yaml
orchestrator_failure_audit:
  earliest_bad_transition: P11 -> P12
  violated_gate: ORCH-8 Anti-Replay Separation Gate
  symptom:
    local_gate: green
    official_eval: collapse
  reason:
    heldout probes were implementation-visible
  product_evidence_status: blocked_by_method_failure
  next_action:
    rerun from P11 with sealed checker-only split
```

Possible orchestrator failure classes:

```text
phase_skip
reentry_missed
scoped_promoted_to_gold
checker_only_leak
worker_baton_overbroad
worker_baton_under-specified
operationalization_equivalence_missing
local_gate_misclassified
official_eval_premature
audit_pressure_laundered
source_postmortem_laundered
regression_gate_missing
```

---

## 15. Practical next run protocol

For the next run, do not start with implementation.

Start with an orchestrator dry-run:

```text
1. Build current phase-state ledger.
2. Mark active phase and allowed next phases.
3. Partition artifacts into implementation-visible, checker-only, orchestrator-only.
4. Re-run P5/P8/P10 for the current frontier if missing.
5. Produce a P11 worker baton for one bounded batch only.
6. Validate the baton against ORCH-1 through ORCH-9.
7. Dispatch implementation worker only after the transition proof is green.
8. Generate sealed/metamorphic probes after implementation, not before.
9. Run official eval only as the declared posture permits.
```

For `trdsql`, the next bounded implementation batch should probably be one of:

```text
Batch A: SQL resource binder + resource route topology
Batch B: input dialect and option overlay
Batch C: output router and downstream-consumer byte grammar
Batch D: analyze/config/db mode-as-program
Batch E: exactness and compatibility sharpening
```

But before selecting any batch, the orchestrator must produce the transition ledger proving why that batch is the legal next phase.

---

## 16. The deeper theory

The constructive-witness frame was:

```text
W ; Π ; Σ ⊢ Cᴡ : Ω*
```

v22 adds that the orchestration path itself must be a valid witness:

```text
W ⊢ Ω? -> Ω* -> Λ -> Π -> Cᴡ -> local_gate -> official_eval
```

with every arrow justified.

So there are two witnesses:

```text
Cᴡ = code/package/runtime witness for the program theorem
Oᴡ = orchestration witness for the reconstruction method
```

The full judgment becomes:

```text
W ; Oᴡ ; Π ; Σ ⊢ Cᴡ : Ω*
```

Meaning:

```text
Under warrant W, with a valid orchestration witness Oᴡ, probe/checker family Π,
and substrate Σ, witness bundle Cᴡ is accepted as a constructive witness for
best warranted program ontology Ω*.
```

If `Oᴡ` is invalid, then even a local-green `Cᴡ` is not strong evidence.

This is what happened in the v20 collapse: the code witness passed the visible local contract, but the orchestration witness was invalid because the transition into implementation and local parity allowed replay.

---

## 17. One-line v22 rule

```text
Do not let the orchestrator reason narratively about phase movement.
Make it prove each transition as a typed state-machine step.
```

Or more compactly:

```text
Workers construct local witnesses.
The orchestrator constructs the run witness.
Both must be valid.
```
