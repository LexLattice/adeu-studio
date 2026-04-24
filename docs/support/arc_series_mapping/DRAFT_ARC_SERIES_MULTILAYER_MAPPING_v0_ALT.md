# Draft ARC Series Multilayer Mapping v0

Status: support synthesis draft.

Authority layer: support.

This document is a non-authorizing synthesis of the `docs/DRAFT_NEXT_ARC_OPTIONS_v*`
series, associated architecture/decomposition docs, and released closeout/lock lineage
visible in the repo as of the `V67-C` closeout horizon. It does not supersede any lock,
planning selector, closeout decision, architecture decomposition, schema, or source
module. It is a map of the arc series as a unitary engineering harness and a seam
analysis for future planning.

Interpretive doctrine:

- lock docs and post-closeout decisions bind released slice facts;
- architecture / decomposition docs bind intended family shape but do not authorize
  implementation by themselves;
- planning docs record candidate selection and family boundaries at their horizon;
- support docs may synthesize and stress-test but may not promote themselves into lock
  authority.

Horizon-sensitive words below follow
`docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`. A statement that a seam is "missing" means
missing at the current support-synthesis horizon, not permanently forbidden or impossible.

## 1. Reading Of The Series

The arc series is not one linear feature roadmap. It is a layered harness that keeps
rebuilding the conditions under which a later agent may reason, act, observe, restore,
communicate, delegate, and document without silently minting authority.

The unitary pattern is:

```text
semantic authority and docs
  -> typed repo / domain self-description
  -> practical analysis and benchmark evidence
  -> governed agent action
  -> observed effect, restoration, continuity
  -> continuation and communication
  -> transport / remote surfaces
  -> bounded writable surface
  -> delegated export and reconciliation
  -> native documentation and ergonomic instantiation
```

The repo already contains concrete schemas, packages, fixtures, closeout artifacts, and
test surfaces across that ladder. The remaining work is not "make a system from prose."
It is to close the few seams where the present stack would otherwise have to infer
authority from transcript, planning text, local writes, worker outputs, or evaluation
claims.

## 2. Family Map

| Family | Layer | Current reading | Structural role |
|---|---|---|---|
| `vNext+1`..`vNext+30` | foundation | historical completed baseline in the next-arc series | governance, runtime, explainability, scaling, semantic depth, and early product/read-surface foundations before named `V31+` family discipline stabilized |
| `V31` | evidence / closeout hygiene | closed historical family | evidence explorer, closeout consistency, worker/route safety, proposer idempotency, repo-root discipline |
| `V32` | semantic compiler | closed | commitments IR, semantic source grammar, compiler passes, surface snapshots, CI/closeout wiring |
| `V33` | agent harness | closed | taskpack/profile contracts, Codex SDK runner, auditor/verifier lane, UX packaging |
| `V34` | packaging / verifier trust | closed | signing, adapter parity, zero-trust recomputation, retry context, attested verification, standalone integrity |
| `V35` | orchestration / delegation | closed | orchestrator state, single-builder delegation, worker visibility, topology/duty map, enforcement hardening |
| `V36` | Morphic UX constitutional substrate | closed | UX domain packet, morph IR, projection / interaction contracts, diagnostics, compiler variants |
| `V37` | recursive meta-loop | closed | meta intent packet, sequence contract, arc-bundle recursive compilation, drift diagnostics, advisory control updates |
| `V38` | brokered reflexive execution | closed starter | bridge between recursive planning and bounded execution posture |
| `V39` | external / synthetic pressure alignment | closed | retrospective external contribution alignment and synthetic mismatch detection / plan / checkpoint surfaces |
| `V40` | architecture semantic IR | closed | ASIR root, deterministic conformance, hybrid checkpoint/oracle, projection, UX compatibility, evidence release |
| `V41` | practical repo analysis loop | closed | request, settlement, observation, intended compile, alignment, runner over one bounded repo world |
| `V42` | ARC-AGI specialization | closed | external challenge packet, observation, hypothesis, rollout, local eval, scorecard, submission, puzzle ingest, run bridge, harness, behavior evidence |
| `V43` | governed contest participation | planned / not released | generalize beyond ARC into host-agnostic contest-world compilation before strategy/execution |
| `V44` | structural reasoning assessment | closed | template probes, structural traces, failure taxonomy, differential diagnosis, probe widening, recursive-depth assessment |
| `V45` | repo self-description | closed | schema registry, entity catalog, arc dependency register, symbol/dependency graph, test intent, optimization register, descriptive-to-normative binding |
| `V46` | applied benchmarking | closed | benchmark family substrate, procedural-depth projection, perturbation/non-regression, cross-subject comparison, advisory consumer |
| `V47` | authoritative normative markdown | closed | `D@1` / ANM substrate, hardening, coexistence, ownership transition, downstream and benchmark consumers |
| `V48` | taskpack / worker bridge | closed | policy-scope binding, compiled taskpack derivation, worker attestation, post-run conformance, supervisor-to-worker topology |
| `V49` | semantic forms substrate | closed | repo-owned semantic forms contracts, recovery, deterministic lowering, bridge to `V48` binding profile |
| `V50` | symbol audit | closed | symbol census, one-audit-per-symbol ledger, read-only audit session helper |
| `V51` | ODEU simulation | closed | bounded simulation kernel, API consumer, browser UI consumer |
| `V52` | paper semantic workbench | closed | paper semantics contracts, mock workbench, worker bridge, spatial visualization |
| `V53` | edge ledger | closed on branch lineage | edge taxonomy, applicability, adjudication, revision register, test-intent bridge |
| `V54` | history semantics | closed on branch lineage | source/preclassification, ledger/slice/theme, O/E/D/U reconstruction, workspace question/snapshot |
| `V55` | constitutional coherence | closed | domain substrate and warning-only coherence / descendant trial / migration decision |
| `V56` | resident-agent interaction governance | closed | packet, proposal, checkpoint, ticket, live gate, harvest/calibration |
| `V57` | local-effect hardening | closed | observed local effect, restoration/replay, hardening decision |
| `V58` | live harness integration | closed | live-turn admission, handoff, reintegration, restoration-state integration |
| `V59` | persistent workspace continuity | closed | continuity region, occupancy, continuity-safe restoration, hardening decision |
| `V60` | continuation / residual intent | closed | seed intent, task charter, residual, loop-state ledger, refresh/reproposal, hardening |
| `V61` | governed communication membrane | closed | communication ingress/egress, bridge office binding, rewitness/message-promotion gate |
| `V62` | connector / external assistant bridge | closed | connector admission, external assistant ingress/egress bridge, provenance hardening |
| `V63` | remote operator UX / phone control | closed | remote session, phone-safe status/ask view, command/control bridge, advisory hardening |
| `V64` | repo-bound writable surface | closed | writable descriptor, lease/admission, restoration/reintegration, advisory hardening |
| `V65` | delegated export / worker reconciliation | closed | export packet, worker reconciliation, delegated hardening over `V48` law |
| `V66` | ANM native documentation practice | closed | source discovery/class policy, migration/reader projection, adoption hardening |
| `V67` | ergonomic instantiation adjudication | closed | ergonomic rule/component/candidate/case/adjudication artifacts, bounded engine, runtime bridge report |

## 3. Layered Reading

### 3.1 Semantic And Documentation Authority

Primary families: `V32`, `V40`, `V47`, `V49`, `V66`.

This layer turns prose, architectural intent, semantic forms, and documentation practice
into typed, replayable artifacts. Its main discipline is that a document can be
authoritative only through declared authority posture, not because it is long, plausible,
or conveniently named.

Closed capability:

- semantic source and compiler discipline exist through `V32`;
- architecture semantic IR and practical projection discipline exist through `V40`;
- ANM / `D@1` normative documentation substrate exists through `V47`;
- semantic forms and deterministic lowering exist through `V49`;
- repo-native ANM documentation practice exists through `V66`.

Residual seam:

- the repo still lacks a single global, current arc-series cartography artifact that
  joins all family status, dependency, branch, lock, and closeout facts beyond the
  intentionally bounded `V45-C` register.

### 3.2 Repo And Domain Self-Description

Primary families: `V45`, `V50`, `V53`, `V54`.

This layer lets the repo describe itself, its symbols, its edge spaces, and its history
without relying on ad hoc file search or imported prototype authority.

Closed capability:

- schema/entity/symbol/test/optimization description exists through `V45`;
- symbol census and audit session support exists through `V50`;
- edge-space accounting exists through `V53`;
- history reconstruction and workspace synthesis exist through `V54`.

Residual seam:

- whole-series arc topology is still support/planning-visible rather than a released
  first-class family registry over `V31`..`V67` and connected branch arcs.

### 3.3 Reasoning, Analysis, And Benchmark Evidence

Primary families: `V41`, `V42`, `V44`, `V46`.

This layer makes reasoning inspectable before any stronger claim is made. It separates
analysis request, settlement, observation, intended compile, alignment, local eval,
scorecard posture, structural probes, and benchmark outputs.

Closed capability:

- practical repo analysis loop exists through `V41`;
- ARC-specific local challenge participation stack exists through `V42`;
- structural reasoning assessment exists through `V44`;
- applied benchmark and advisory consumer stack exists through `V46`.

Residual seam:

- `V43` remains the main unclosed planned branch for general external governed contest
  participation. `V42` is a released specialization, not the host-agnostic family.

### 3.4 Harness, Orchestration, And Delegation

Primary families: `V33`, `V34`, `V35`, `V48`, `V65`.

This layer handles taskpack compilation, runner/verifier discipline, worker visibility,
worker boundaries, and later delegated export.

Closed capability:

- taskpack/harness and verification baselines exist through `V33` / `V34`;
- orchestration and worker visibility exist through `V35`;
- worker-bound taskpack and conformance law exists through `V48`;
- delegated export / reconciliation over a bounded writable lineage exists through
  `V65`.

Residual seam:

- multi-worker adversarial review, arbiter selection, and review-phase settlement remain
  a future family, not an ambient entitlement of the existing single-worker/export stack.

### 3.5 Resident-Agent Runtime Governance

Primary families: `V55` through `V65`.

This is the core "philosophy-engineering harness" for a resident agent. It builds from
constitutional coherence to live action, observed effect, restoration, continuity,
continuation, communication, connector/remote surfaces, writable surface authority, and
delegated reconciliation.

Closed capability:

- constitutional/domain coherence exists through `V55`;
- one live action path can be governed through `V56`;
- one local effect can be observed/restored/hardened through `V57`;
- one real live turn can be admitted and reintegrated through `V58`;
- persistent workspace continuity exists through `V59`;
- residual intent and continuation state exist through `V60`;
- communication membrane and bridge office exist through `V61`;
- connector and remote operator surfaces exist through `V62` / `V63`;
- bounded repo write authority exists through `V64`;
- bounded delegated export and reconciliation exists through `V65`.

Residual seam:

- the stack still needs a released semantic ingress/operator compiler in front of the
  resident runtime. Raw user utterance should not be treated as task law, operator
  family selection, commit policy, or arc-family expansion by itself.

### 3.6 Product And Human Surface Layer

Primary families: `V36`, `V51`, `V52`, `V63`, `V67`.

This layer turns internal law into inspectable and usable surfaces while preserving
authority boundaries.

Closed capability:

- Morphic UX substrate exists through `V36`;
- ODEU simulation API/browser proof exists through `V51`;
- paper semantic workbench proof exists through `V52`;
- remote operator and phone-safe view/control exists through `V63`;
- ergonomic instantiation adjudication exists through `V67`.

Residual seam:

- runtime personalization, broad layout solving, and product-wide surface governance are
  still not selected. That is correct: `V67` proves bounded adjudication, not sovereign
  UI optimization.

## 4. Unitary Dependency Cone

The stable dependency cone now looks like this:

```text
V32/V47/V49/V66  semantic and doc authority
        |
        v
V45/V50/V53/V54  self-description, symbol, edge, history
        |
        v
V40/V41/V42/V44/V46  analysis, external challenge, reasoning, benchmark evidence
        |
        v
V55 -> V56 -> V57 -> V58 -> V59 -> V60 -> V61
                                      |       |
                                      v       v
                                   V64 -> V65
                                      ^
                         V62/V63 transport and operator surfaces
        |
        v
V36/V51/V52/V67  human-facing lawful instantiation and inspection surfaces
```

This diagram is not a strict topological ordering for every historical PR. It is the
current conceptual dependency geometry: what must be kept distinct for the harness to
remain lawful.

The crucial negative laws are:

- transcript is not authority;
- communication is not permission;
- continuity is not standing authority;
- local write ability is not commit/release authority;
- worker output is not native truth without reconciliation;
- benchmark output is not self-improvement proof without experiment and adoption law;
- planning support is not lock-level authorization.

## 5. Missing Arc Set

The optimal missing set is not "all possible follow-ons." It is the smallest set of
families needed to prevent the current closed stack from using an unlawful shortcut in
the path toward recursive self-improvement.

### `V68`: Whole-Series Arc Cartography And Seam Register

Purpose:

- release a first-class, repo-owned arc-series map over `V31`..current and known
  branch families;
- bind family status, authority layer, branch posture, lock/closeout evidence, package
  surfaces, and dependency edges;
- generalize the `V45-C` dependency-register posture beyond the bounded V45 planning
  register without pretending stale planning docs are current truth.

Why missing:

- this support doc can synthesize the map, but it is not a schema-backed artifact;
- `repo_arc_dependency_register@2` intentionally covers a bounded V45 snapshot, not the
  whole series;
- future planning still needs a canonical way to know what is released, branch-local,
  deferred, superseded, or not selected.

Boundary:

- descriptive only;
- may constrain planning;
- may not mint scheduling, implementation, merge, or amendment authority.

### `V69`: Semantic Ingress / Operator Binding / Turn Compiler

Purpose:

- compile raw user utterance, live turn context, and known operator families into a
  typed operator instance;
- bind variables such as arc family, artifact family, review scope, action class,
  commit policy, and evidence obligations through declared registries;
- emit a turn-refresh artifact that can feed `V60` / `V61` / `V64` without treating chat
  text as authority.

Why missing:

- `V60` owns continuation after seed intent exists;
- `V61` owns communication packet law;
- neither owns closed-world semantic ingress, operator-family selection, or variable
  expansion from user speech into repo-native workflow objects.

Boundary:

- no commit authority;
- no direct execution authority;
- no hidden operator invention outside registered families.

### `V70`: Commit, Merge, And Release Authority

Purpose:

- govern promotion from local writable effects and reconciled worker outputs into git
  commit, branch update, PR update, merge, or release-note posture;
- separate local file mutation, accepted diff, commit intent, PR authority, merge
  authority, and release truth;
- bind checks actually run and skipped checks to release posture.

Why missing:

- `V64` governs bounded repo writes;
- `V65` governs delegated export/reconciliation;
- neither is allowed to decide that a local write is commit-worthy, merge-worthy, or
  release-authoritative.

Boundary:

- may consume `V64`, `V65`, `V45`, `V66`, and checks;
- may not bypass maintainer authority or convert passing local checks into merge rights.

### `V71`: Self-Improvement Experiment Ledger

Purpose:

- define a typed experiment around changes to prompts, policies, schemas, harnesses,
  benchmark selectors, or runtime behavior;
- require baseline, intervention, evaluation, regression, rollback, and adoption
  posture;
- consume `V44` / `V46` evidence without letting benchmark deltas alone rewrite policy.

Why missing:

- the repo has benchmark and structural assessment machinery;
- it has local write and delegation machinery;
- it lacks a released artifact that says "this change is a self-improvement candidate,
  here is the evidence, here are regressions, here is adoption/rollback posture."

Boundary:

- no automatic policy mutation;
- no self-approval;
- no benchmark-only authority laundering.

### `V72`: Multi-Agent Review, Adversarial Feedback, And Arbiter Settlement

Purpose:

- make delegated critics, worker proposals, adversarial reviews, and arbiter decisions
  explicit phases rather than transcript commentary;
- type child-agent role, scope, evidence, independence, conflict, and settlement;
- bind outputs back to `V65` reconciliation and `V70` commit/release posture.

Why missing:

- `V35`, `V48`, and `V65` provide orchestration and worker boundaries;
- they do not yet release a general adversarial review / multi-agent adjudication law
  for recursive improvement experiments.

Boundary:

- no hidden majority vote authority;
- no child-agent output as native truth;
- no multi-worker widening beyond explicitly admitted scopes.

### `V43`: General Governed Contest Participation

Purpose:

- close the still-unreleased branch that generalizes from `V42` ARC-AGI specialization
  into host-agnostic contest-world compilation;
- separate host adapter, contest law, evaluation, resource/timeline, archetype, leverage,
  strategy, run evidence, and postmortem.

Why still part of the missing set:

- `V42` proves one external challenge specialization;
- recursive self-improvement will need external world/task intake beyond one benchmark
  family, but that generalization should not be smuggled through `V42` or `V46`.

Boundary:

- world compilation before strategy;
- no autonomous contest execution in the first general family;
- no host text as self-authorizing law.

## 6. Proof Sketch For Minimality

The missing set above is optimal under the current repo doctrine because each member
blocks one otherwise unavoidable authority shortcut, and no listed member is reducible
to an already released family without violating that family's boundary.

1. Whole-series cartography is irreducible.
   `V45-C` proves dependency registers are useful, but its own scope is V45-bound. A
   global arc map cannot be safely inferred from scattered planning prose at runtime.

2. Semantic ingress is irreducible.
   `V60` can carry residual intent only after a task identity exists, and `V61` can
   govern communication only as communication. A turn compiler is the missing adapter
   between human utterance and typed operator instance.

3. Commit/release authority is irreducible.
   `V64` admits local repo writes and `V65` reconciles delegated output. Neither may
   promote a write into git history, PR status, or released truth without a separate
   authority family.

4. Self-improvement experiments are irreducible.
   `V44` and `V46` can assess reasoning and benchmarks, but they do not define adoption
   law for changing the harness itself. `V71` is needed to prevent "metric improved" from
   becoming "policy may change."

5. Multi-agent review is irreducible.
   Existing worker laws make delegation bounded. They do not define adversarial
   critique, independence, conflict, or arbiter settlement as first-class artifacts.
   Recursive self-improvement needs those phases typed before they influence adoption.

6. General contest participation is irreducible.
   `V42` is ARC-specific by design. General external task/contest intake requires its
   own host-world compilation substrate or later external benchmark work will launder
   ARC-specific assumptions into unrelated worlds.

Completeness argument:

- The closed stack already covers semantic documents, repo description, practical
  analysis, structural reasoning, benchmarks, live action, local effects, continuity,
  continuation, communication, connectors, remote UX, writable surfaces, delegated
  reconciliation, documentation practice, and ergonomic adjudication.
- The six missing families above close the remaining transitions between those stacks:
  map -> utterance -> operator -> local change -> release -> experiment adoption ->
  multi-agent critique -> external-world generalization.
- Additional possible families such as broader personalization, large-scale memory,
  multi-repo fleet orchestration, or full autonomous contest execution are valid future
  seams, but they are not minimal prerequisites for a robust recursive
  self-improvement harness. They should remain deferred until the six authority
  shortcuts above are closed.

## 7. Recommended Planning Order

The lowest-risk order is:

1. `V68` whole-series cartography.
2. `V69` semantic ingress / operator binding.
3. `V70` commit / merge / release authority.
4. `V71` self-improvement experiment ledger.
5. `V72` multi-agent review / adversarial settlement.
6. `V43` general contest participation, either before or after `V71` if external task
   intake becomes the immediate priority.

Rationale:

- `V68` gives the later operator compiler a reliable family map.
- `V69` prevents raw user text from directly driving continuation, write, or commit
  posture.
- `V70` must exist before self-improvement experiments can lawfully adopt code changes.
- `V71` then binds evaluation and adoption.
- `V72` hardens the experiment loop with typed adversarial phases.
- `V43` remains the main connected unclosed domain-generalization branch and can proceed
  when external-world intake becomes the selected pressure.

## 8. Closeout Reading

At the current horizon, `V67` is a real closure point for a long resident-agent arc:

```text
constitutional coherence
  -> live act
  -> local effect
  -> live harness
  -> persistent continuity
  -> residual intent
  -> governed communication
  -> connector / remote surfaces
  -> repo writable surface
  -> delegated reconciliation
  -> documentation practice
  -> ergonomic adjudication
```

That stack is strong enough to start treating the repo as a philosophy-engineering
harness. It is not yet strong enough to let the harness recursively modify itself
without the six missing seams above.
