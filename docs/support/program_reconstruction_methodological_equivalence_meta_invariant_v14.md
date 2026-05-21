# Program Reconstruction Methodological Equivalence Meta-Invariant v14

## Status

This is a structural patch to the v13 constructive-witness framing.  v13 added target-substrate and packaged-artifact gates after the `trdsql` score-collapse run.  v14 promotes that lesson into a more general ADEU / ODEU invariant:

```text
No reconstruction result may transfer across two programs, two executions, two substrates,
two observers, or two artifact states unless the relevant equivalence relation has been
named, scoped, and witnessed.
```

The v13 target-substrate failure was therefore not merely a Python-version bug.  It was a methodology failure: the loop assumed an equivalence between the local candidate witness and the official candidate witness that had not been proved.

---

## 1. Core invariant

### METHODOLOGICAL_EQUIVALENCE_META_INVARIANT

```text
Before using behavior observed in object A as evidence about object B, the run must provide
a typed equivalence judgment between A and B at every lower layer on which the inference depends.
```

Equivalence is not global.  It is:

```text
typed      by layer,
scoped     to a branch, interface, substrate, artifact, or observer,
relational over a specified observable signature,
warranted  by probes, manifests, fingerprints, or explicit assumptions,
revocable  when a lower-layer counterexample appears.
```

Canonical judgment:

```text
W ⊢ A ≃[L, S, R] B
```

Meaning:

```text
Under warrant W, object A and object B are equivalent at layer L,
within scope S, under observable relation R.
```

For program reconstruction, the central constructive-witness judgment remains:

```text
W ; Π ; Σ ⊢ Cᴡ : Ω*
```

v14 adds that any transfer of this judgment must also prove:

```text
W ⊢ (Cᴡ₁, Π₁, Σ₁) ≃[transfer, S, R] (Cᴡ₂, Π₂, Σ₂)
```

If that transfer equivalence is missing, a local green result is only local evidence.

---

## 2. Objects that must not be silently identified

A reconstruction loop usually contains several different objects that are easily collapsed:

```text
P_ref        reference / target program whose behavior is being reconstructed
P_cand       candidate program as an abstract source/witness design
Cᴡ_src       source-level witness bundle produced by the worker
Cᴡ_local     locally materialized candidate witness bundle
Cᴡ_eval      packaged/submitted/evaluator-side witness bundle
Σ_ref        reference substrate
Σ_local      local probe substrate
Σ_eval       official/evaluator substrate
Π_ref        reference-observation probes/checkers
Π_local      local candidate probes/checkers
Π_eval       official/evaluator probes/checkers
O_ref        reference observations
O_local      local candidate observations
O_eval       official observations
Ω?           candidate inferred ontology
Ω*           best warranted completion of the visible program statement
Ωg           gold/reference ontology, if later known
```

v14 rule:

```text
None of these pairs are equivalent by default.
```

They can be related only by explicit typed equivalence claims.

---

## 3. Equivalence ladder

The meta-program must distinguish at least these equivalence layers.

### E0 Statement equivalence

```text
Ω? ≃ Ω* ≃ Ωg?
```

Question:

```text
Did we reconstruct the same theorem statement the reference program inhabits?
```

Typical failure:

```text
README-derived ontology misses public help schema, SQL expression-only mode,
format dialects, or hidden renderer obligations.
```

### E1 Public-interface equivalence

```text
P_ref interface ≃ P_cand interface
```

Question:

```text
Does the candidate expose the same CLI/API/control grammar, including help,
unknown flags, modes, aliases, env/config surfaces, entrypoints, and stream routes?
```

### E2 Observation-oracle equivalence

```text
Π_ref / Π_local / Π_eval observe the same surface relation
```

Question:

```text
Are stdout, stderr, exit, files, timing, process lifetime, resources, and dynamic
normalization captured with the same semantics?
```

A merged transcript is not equivalent to a split stdout/stderr/exit/file oracle.

### E3 Witness-bundle equivalence

```text
Cᴡ_src ≃ Cᴡ_local ≃ Cᴡ_eval
```

Question:

```text
Is the exact witness bundle being tested locally the same witness bundle submitted
to the official evaluator?
```

This includes:

```text
source files
configs
entrypoints
build scripts
package metadata
generated resources
dependency pins
runtime assumptions
filesystem layout
submission filters
line endings
shebangs
permissions
```

### E4 Target-substrate / ABI equivalence

```text
Σ_local ≃ Σ_eval
```

Question:

```text
Does the local runtime accept, import, execute, encode, and buffer the witness the
same way as the evaluator runtime?
```

This includes:

```text
language version
stdlib and dependency versions
OS / architecture
shell and argv parsing
locale / timezone
filesystem case/ordering semantics
line endings
PTY / stdio behavior
compiler/interpreter flags
```

### E5 Execution-topology equivalence

```text
run_local(Cᴡ, Σ_local) ≃ run_eval(Cᴡ, Σ_eval)
```

Question:

```text
Are cwd, argv, env, stdin/stdout/stderr, temp dirs, resource paths, scheduler,
timeouts, signals, and cleanup topology equivalent enough for the branch?
```

### E6 Resource/observation-ecology equivalence

```text
resource graph local ≃ resource graph eval
```

Question:

```text
Are ports, sockets, PTYs, subprocesses, temp files, DB files, locks, caches,
coverage artifacts, reruns, and parallel schedules clean and comparable?
```

### E7 Behavioral terminal-leaf equivalence

```text
O_ref(λ) ≃ O_cand(λ)
```

Question:

```text
For each terminal leaf λ, do reference and candidate observations match under the
chosen observable relation?
```

Only E7 is the usual “program behavior matches” claim.  It is invalid if any required lower equivalence is missing or failed.

### E8 Warrant equivalence

```text
W_ref / W_local / W_eval authority levels are compatible
```

Question:

```text
Are we using evidence with the same authority class, or are we laundering scoped,
diagnostic, source-postmortem, or post-eval pressure into gold truth?
```

---

## 4. Dominance rule

```text
A failure is evidence about the earliest unproven or broken equivalence layer that can explain it.
```

If the candidate cannot compile under `Σ_eval`, then official failures are not yet strong evidence about SQL semantics, output formats, input grammars, or renderer byte exactness.  They are evidence about E3/E4:

```text
Cᴡ_local was not proven equivalent to Cᴡ_eval under the target substrate.
```

If an HTTP row fails with `Address already in use` before product behavior is reached, then the row is evidence about E6 resource ecology, not about graph rendering or protocol semantics.

If local observations merged stdout and stderr, then byte/channel mismatches are first evidence about E2 observation-oracle non-equivalence.

---

## 5. Commuting-diagram requirement

For any candidate handoff, the following diagram must commute up to explicitly declared normalization:

```text
             package_local                    run under Πlocal,Σlocal
Cᴡ_src ----------------------> Cᴡ_local ----------------------------> O_local
  |                               |                                      |
  | package_eval                  | E3 witness-bundle equivalence        | E2/E5 observation equivalence
  v                               v                                      v
Cᴡ_eval ----------------------> run under Πeval,Σeval --------------> O_eval
             E4/E5 substrate and execution-topology equivalence
```

If the left vertical arrow changes the artifact, or the lower execution path has a different ABI, entrypoint, dependency, resource, or observer relation, then local evidence does not transfer to official evidence without a new proof.

---

## 6. New macro gate

### METHODOLOGICAL_EQUIVALENCE_GATE

Trigger:

```text
Any time a result, readiness state, probe result, scout observation, implementation
claim, or official eval pressure is transferred across two non-identical objects.
```

Typical transfers:

```text
reference program -> candidate program
README ontology -> public executable behavior
public scout -> implementation obligation
local probe result -> official-readiness claim
source witness -> packaged witness
local runtime -> evaluator runtime
fixture oracle -> generative rule
fork exemplar -> direct-shell support
provider intent -> local authority
diagnostic evidence -> readiness promotion
post-eval pressure -> clean theory
```

Required row shape:

```yaml
equivalence_claim_id: EQ-...
source_object: P_ref | Ω? | Cᴡ_src | Cᴡ_local | Π_local | Σ_local | O_local | other
target_object: P_cand | Ω* | Cᴡ_eval | Π_eval | Σ_eval | O_eval | other
equiv_layer: E0_statement | E1_interface | E2_observation_oracle |
             E3_witness_bundle | E4_target_substrate | E5_execution_topology |
             E6_resource_ecology | E7_behavior_leaf | E8_warrant
scope:
  branch_refs: []
  command_refs: []
  terminal_leaf_refs: []
  artifact_refs: []
observable_relation:
  stdout: exact | normalized | ignored | not_applicable
  stderr: exact | normalized | ignored | not_applicable
  exit: exact | ignored | not_applicable
  files: exact | normalized | ignored | not_applicable
  timing: bounded | ignored | not_applicable
  resources: clean_equivalent | isolated | ignored | not_applicable
required_invariants: []
proof_refs: []
negative_control_refs: []
status: unclaimed | claimed_unproven | probe_ready | scoped_equivalent |
        blocked_counterexample | conflict_isolated | gold_equivalent
promotion_allowed: true | false
if_failed_dominates_layers: []
repair_owner: ontology | probe_contract | witness_packaging | substrate |
              execution_topology | resource_ecology | implementation | warrant
```

Rule:

```text
A handoff may promote behavior only across equivalence rows with status
scoped_equivalent or gold_equivalent for every lower layer on which that behavior depends.
```

---

## 7. Derived gates under the macro

### LOCAL_OFFICIAL_TRANSFER_GATE

```text
= E3 witness-bundle equivalence
+ E4 target-substrate equivalence
+ E5 execution-topology equivalence
+ E2 observation-oracle equivalence
+ E8 warrant equivalence
```

Required before treating local green results as official-readiness evidence.

Minimum probes:

```text
pack exact submitted artifact;
unpack in a clean temp root;
compute manifest/hash of files, permissions, line endings, entrypoint metadata;
run target interpreter/compiler syntax checks;
run import and entrypoint smoke tests;
run no-args/help/one representative data command under evaluator-like argv/env/cwd;
record stdout/stderr/exit separately;
record runtime fingerprint;
record dependency and package-resource availability;
record dynamic fields requiring canonicalization;
record resource cleanliness before and after.
```

### TWO_PROGRAM_BEHAVIORAL_EQUIVALENCE_GATE

```text
= E0/E1 statement and interface equivalence
+ E7 terminal-leaf behavioral equivalence
+ E8 warrant equivalence
```

Required before saying the candidate implements the reference program, rather than only a scoped subprogram.

### PROBE_ORACLE_EQUIVALENCE_GATE

```text
= E2 observation-oracle equivalence
+ E5 execution-topology equivalence
+ E8 warrant equivalence
```

Required before a local probe can stand in for a reference observation or official row.

Hard rule:

```text
A merged stdout/stderr transcript cannot prove a byte-sensitive stdout/stderr leaf.
```

### PACKAGED_WITNESS_EQUIVALENCE_GATE

```text
= E3 witness-bundle equivalence
+ E4 target ABI / runtime syntax validity
```

Required before any candidate source code is evaluated as a constructive witness.

Hard rule:

```text
No code witness can be evaluated as a program witness until the witness bundle is
proven to run under the target substrate.
```

### ARTIFACT_IDENTITY_GATE

```text
= Factor artifact paths, files, generated resources, dependencies, package metadata
+ Bind artifact roles to entrypoint, imports, runtime data, output resources
+ Sequence build -> package -> unpack -> compile -> import -> execute
+ Expose syntax/import/entrypoint/resource errors
+ Warrant artifact parity before local-to-official transfer
```

---

## 8. v14 refinement to the kernel

The v8 kernel remains:

```text
Factor, Partition, Bind, Transform, Sequence, Expose, Compose, Warrant
```

v14 adds a cross-cutting equivalence interpretation:

```text
Factor:
  factor not only program entities, but also program copies, artifact states,
  substrates, observers, and harnesses.

Partition:
  split equivalence into scoped relations, not global sameness.

Bind:
  bind each equivalence claim to the consumers that rely on it.

Transform:
  model packaging, transpilation, compilation, serialization, normalization,
  and dynamic canonicalization as transforms that can change witness identity.

Sequence:
  include build -> package -> unpack -> syntax-check -> import -> run -> observe
  before behavior evidence can be used.

Expose:
  include pre-product failures such as syntax errors, import errors, wrong
  entrypoint, missing resources, environment mismatch, and oracle/channel mismatch.

Compose:
  check non-commutation between local/official substrate, packaging, probes,
  resource ecology, and semantic leaves.

Warrant:
  attach equivalence authority separately from product behavior authority.
```

---

## 9. Readiness additions

Add `equivalence_status` to every handoff, probe family, and implementation claim:

```text
equivalence_unstated
  the run is implicitly transferring evidence without a typed relation.

equivalence_claimed_unproven
  a relation is named but no witness/probe exists.

equivalence_probe_ready
  the relation has a concrete proof plan.

equivalence_scoped_ready
  the relation is proven for a bounded branch/surface/artifact.

equivalence_blocked
  a lower-layer counterexample prevents transfer.

equivalence_conflict_isolated
  evidence conflicts across objects; no global transfer allowed.

equivalence_gold_ready
  all lower equivalence layers required by the handoff are proven or explicitly deferred.
```

New handoff rule:

```text
implementation_ready is impossible while required equivalence_status is
`equivalence_unstated`, `equivalence_claimed_unproven`, or `equivalence_blocked`.
```

---

## 10. Application to the `trdsql` collapse

The v12/v13 `trdsql` result had this shape:

```text
local parity: high / near-green
official eval: score collapse
common official surface: SyntaxError before product behavior
```

v14 classification:

```text
Primary failed layer:
  E4 target-substrate / ABI equivalence

Secondary failed layer:
  E3 witness-bundle parity, because the submitted/evaluated witness was not
  proven to be syntactically valid under the target runtime.

Dominated layers:
  E7 behavioral equivalence for SQL, input formats, output renderers, null
  semantics, diagnostics, and source routing cannot be inferred from that run.
```

Correct repair posture:

```text
Do not first patch SQL semantics or output renderers from the score-3 official rows.
First prove PACKAGED_WITNESS_EQUIVALENCE_GATE and LOCAL_OFFICIAL_TRANSFER_GATE.
Only after product behavior is reached under Σeval do official rows become
product-theory pressure again.
```

This does not erase the earlier score-52 audit.  That audit remains evidence of E0/E1/E2/E7 failures around public schema re-entry, output grammar terminalization, SQL-as-computation, and probe-contract exactness.  The score-3 collapse is a lower-layer transfer failure that blocked those semantic questions from being measured.

---

## 11. Relationship to v11 observation ecology

v11 said:

```text
If a failure happens before candidate-specific behavior is reached, do not treat
it as product-theory evidence. First assign resource owner, lifecycle, setup,
teardown, and collision path.
```

v14 generalizes that:

```text
If a failure happens before the intended equivalence layer is reached, do not
treat it as evidence about higher layers. First identify the broken equivalence
claim and prove or repair it.
```

Resource ecology is one instance of the more general equivalence invariant:

```text
resource clean local ≃ resource clean eval
```

Target ABI is another:

```text
runtime local accepts Cᴡ ≃ runtime eval accepts Cᴡ
```

Observation channels are another:

```text
merged transcript ≄ split stdout/stderr/exit/files
```

Fork/direct capability transfer is another:

```text
fork exemplar ≄ direct-shell support unless explicitly proved
```

Provider/local authority transfer is another:

```text
provider tool intent ≄ local authority unless harness gates accept it
```

---

## 12. Bookkeeper v14 checks

Blocking objections:

```text
equivalence_unstated_for_transfer
local_green_promoted_without_local_official_transfer_gate
source_witness_promoted_without_packaged_witness_parity
runtime_fingerprint_missing_for_target_substrate
syntax_import_entrypoint_smoke_missing
merged_oracle_used_for_split_surface
resource_ecology_unproven_but_product_truth_promoted
post_eval_surface_dominated_by_pre_product_failure
fork_or_provider_evidence_promoted_without direct capability proof
scoped_equivalence_used_as_global_equivalence
equivalence_counterexample_ignored
```

The bookkeeper must ask, for every transfer claim:

```text
Which two objects are being identified?
At what layer?
Under what observable relation?
For which branch/scope?
Which consumers rely on this equivalence?
What witness proves it?
What counterexample would break it?
If it fails, which higher layers are dominated and therefore not interpretable?
```

---

## 13. Generator prompt patch

Add this block before implementation handoff:

```text
Before using any observation or local result as evidence about another program,
artifact, substrate, observer, or official row, emit a METHODOLOGICAL_EQUIVALENCE_GATE row.

Do not assume:
- reference program behavior transfers to candidate behavior;
- local candidate artifact equals official candidate artifact;
- local runtime equals official runtime;
- local probes observe the same surfaces as official probes;
- stdout/stderr merged output can prove split channel behavior;
- fixture byte equality proves a generative rule;
- fork exemplars imply direct-shell support;
- provider/tool intent implies local authority;
- diagnostic evidence implies readiness.

For each transfer, state:
1. source object;
2. target object;
3. equivalence layer;
4. scope;
5. observable relation;
6. proof probes/manifests/fingerprints;
7. promotion status;
8. dominated higher layers if the equivalence fails.

If an official or local failure surface occurs before the product behavior layer,
classify it as an equivalence failure at the earliest explaining layer and block
product-theory repair until the equivalence is proved or repaired.
```

---

## 14. Self-amendment record

```yaml
self_amendment_record:
  candidate_advancement_ref: trdsql_v13_layer_transition_audit_and_patch.md plus user structural-equivalence review
  integration_class: structural_integration
  ontology_delta:
    - target-substrate ABI becomes an instance of a broader typed equivalence calculus
    - program copies, artifact states, substrates, observers, and harnesses become first-class Factor nodes
    - local-to-official transfer requires explicit equivalence ledgers
    - behavior evidence is dominated by lower-layer equivalence failures
  epistemic_delta:
    - evidence transfer is no longer allowed by default
    - official failures are interpreted at the earliest broken equivalence layer
    - local green is local unless local-official equivalence is proven
  deontic_delta:
    - implementation handoff is blocked by missing required equivalence gates
    - product-theory repair is blocked while lower transfer equivalence is broken
  utility_delta:
    - avoids wasting repair cycles on semantic patches when the measured object was not the intended witness
    - unifies target ABI, resource ecology, observation lock, fork/direct support, provider/local authority, and scaffold/gold promotion under one methodology invariant
  governance_preservation_posture: O/E/D/U legibility preserved; capability transfer requires warrant
  ratification_status: experimental_support_revision
```

---

## 15. One-line rule

```text
Never compare two programs, two witnesses, two substrates, or two observations without first saying what kind of sameness is being claimed and how that sameness was proved.
```
