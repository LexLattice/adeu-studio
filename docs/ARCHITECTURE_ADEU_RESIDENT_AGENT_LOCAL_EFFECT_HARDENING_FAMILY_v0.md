# Architecture ADEU Resident-Agent Local-Effect Hardening Family v0

Status: architecture / decomposition draft for `V57`.

Authority layer: architecture / decomposition.

This document defines the bounded family shape for resident-agent local-effect
hardening. It is not a lock doc and does not authorize runtime behavior, schema
release, or CI gating by itself.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v40.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_FAMILY_v0.md`
- `docs/support/ADEU_SCHEMA_META_GRAMMAR.md`
- `docs/support/ODEU_MEMBRANE_ARCHITECTURE.md`

## 1. Direct Answer

The next missing layer is not more abstract governance. It is one bounded family that
captures an actually observed local effect under the shipped `V56` live-gate law.

That family should not reopen packet/contract/checkpoint/ticket authority. It should
externalize the post-effect layer around one already selected live path into typed
artifacts:

- designated local-effect sandbox before effect;
- explicit observation record after effect;
- explicit local-effect conformance after effect;
- later restoration and hardening only after evidence exists.

## 2. Family Role

This family owns:

- designated local-effect target-root selection;
- bounded actual-effect observation over one already selected `V56` live class;
- explicit pre/post effect evidence capture;
- explicit local-effect conformance over observed writes/effects;
- later restoration evidence and later local hardening discussion.

This family does not own:

- packet / contract / proposal / checkpoint law already owned by `V56`;
- delegated worker execution already owned by `V48`;
- constitutional artifact coherence already owned by `V55`; or
- hidden latent inference.

## 3. Core Family Law

The family should make these laws explicit:

1. no actual local effect is allowed here without prior lawful `V56` ticket lineage;
2. actual effect must remain inside one designated local-effect sandbox root;
3. observed effect must remain no broader than shipped `local_write` semantics from
   `V56-B`;
4. the first actual-effect slice must narrow `local_write` to one safe subset while
   restoration remains out of scope;
5. every observed write must bind to one lawful ticket, one selected proposal, and one
   bounded checkpoint-entitled effect scope;
6. negative observation outcomes are first-class evidence and may not be laundered
   into apparent successful effect;
7. one observed effect may constrain later hardening discussion but may not mint
   hardening by itself;
8. restoration and replay remain later slices and may not be silently claimed in the
   starter slice.
9. pre-state, observed write set, and post-state must be explicit rather than implied;

## 4. Artifact Ladder

The bounded family ladder is:

1. `agentic_de_local_effect_observation_record@1`
   - one actual observed bounded local effect with target-root, write-set, and state
     refs
2. `agentic_de_local_effect_conformance_report@1`
   - typed report over ticket lineage, effect boundedness, observed writes, and
     conformance to frozen `local_write` semantics
3. `agentic_de_local_effect_restoration_record@1`
   - later restoration / compensating restore evidence over the same bounded effect
4. `agentic_de_local_effect_hardening_register@1`
   - later advisory decision over whether the observed/restored path deserves stronger
     local hardening

The first slice should instantiate only the first two.

## 5. Relationship To `V56`

`V56` remains the resident-agent runtime-governance family:

- packet;
- contract;
- proposal;
- checkpoint;
- ticket;
- conformance;
- harvest / calibration / migration.

`V57` begins only after those surfaces already exist and remain authoritative.

So the correct ordering is:

- `V56` decides whether a path is lawfully ticketed;
- `V57` records what actually happened when one already ticketed local effect is
  exercised inside a bounded sandbox.

`V57` therefore constrains but does not mint:

- it may constrain later hardening discussion through observed evidence;
- it may not mint new action classes, reinterpret ticket law, or widen effect scope.

## 6. Sandbox Boundary Model

The starter boundary should be:

```text
V56 ticket -> designated local-effect sandbox
          -> pre-state ref
          -> bounded local_write effect
          -> observed write-set
          -> post-state ref
          -> local-effect observation record
          -> local-effect conformance report
```

The designated sandbox should remain local and bounded:

- inside repo-controlled artifacts space;
- outside repo source, lock docs, CI config, secrets, credentials, and dispatch
  surfaces;
- no symlink escape;
- no relative-parent traversal;
- no indirect alias or mount redirection;
- no write-through into authority-bearing surfaces via references inside the sandbox;
- non-networked and non-delegated;
- narrow enough that later restoration can remain inside the same authority envelope.

## 7. Starter Effect Law

The starter selected live class should be exactly:

- `local_write`

The first actual-effect subset should be narrower than the full semantic range of
`local_write` while restoration remains out of scope:

- `create_new`
- `append_only`

Not:

- overwrite
- truncate
- rename or move
- delete
- metadata mutation
- `local_reversible_execute`
- `stronger_execute`
- `delegated_or_external_dispatch`

The operative interpretation of `local_write` should be reused from shipped `V56-B`:

- bounded local artifact write only;
- no lock/doc/CI/secret/dispatch surfaces;
- safe-subset-only in the first actual-effect slice while restoration is still out of
  scope;
- no semantic repartition of the class in the starter slice.

## 7.1 Observation Outcome Algebra

`agentic_de_local_effect_observation_record@1` and
`agentic_de_local_effect_conformance_report@1` should explicitly distinguish at least:

- `bounded_effect_observed`
- `no_effect_observed`
- `out_of_scope_write_observed`
- `mismatched_effect_observed`
- `boundedness_verdict_failed`

The family should not assume that actual effect means successful conformant effect.
Negative outcomes must remain first-class evidence.

## 8. Starter Package Shape

The likely starter implementation home remains:

- `packages/adeu_agentic_de/src/adeu_agentic_de/`
- `packages/adeu_agentic_de/tests/`

One thin script seam may live under:

- `apps/api/scripts/`

Likely starter additions:

- `local_effect.py`
- `local_effect_conformance.py`

## 9. Deferred Seams

Deferred seams should be classified explicitly:

- `instantiated_here`
  - designated sandbox selection
  - local-effect observation
  - local-effect conformance
- `deferred_to_later_family`
  - broader product/runtime use of actual local effect
- `not_selected_yet`
  - restoration record
  - hardening register
  - `local_reversible_execute` actual effect
  - stronger execute
  - delegated/external dispatch

## 10. Do Not Import

- silent widening from bounded local sandbox to general repo write authority
- reinterpretation of shipped `local_write` semantics
- claims of restoration or hardening without typed evidence
- hidden-cognition governance proxies
- automatic promotion from one observed effect to broader runtime entitlement
