# Canonical ADEU Semantic Declaration Meta-Loop

Repository grounding note: all requested files were present in the attached repo zip. I treated the repo as a conceptual substrate, not an implementation target. The most relevant observed anchors are: ANM’s prose / authority-zone / derived-deterministic planes; `D@1` as a bounded normative dialect; fact-only checker outputs; policy result sets and obligation ledgers; schema meta-grammar emphasis on core envelope, authority, evidence, and O/E/D/U realization; operator projection’s “projection is not authority” law; morphic UX governed enactment’s “no silent compensation” discipline; agent-harness binding / attestation / conformance artifacts; and edge-ledger class / probe-template catalogs.

---

## Executive summary

**Observed.** ADEU already has the pieces for deterministic governance: explicit authority zones, typed IR, fact bundles, policy results, obligation ledgers, source-bound projection, worker attestations, and conformance reports. The repo repeatedly rejects hidden authority: prose is not obligation, projection is not authority, checker output is not verdict, ledger state is not waiver authority, and support docs do not mint runtime behavior.

**Inferred.** The missing scalable seam is not “make the model reason harder.” The missing seam is **model-assisted O-binding**:

```text
natural task / code context
  -> typed semantic role/class declaration
```

Once that binding exists, ADEU can stop rediscovering the same review logic stochastically. A class-indexed deterministic layer can expand the declaration into obligations, edge probes, evidence requirements, reviewer tasks, and closeout routing.

**Recommended.** Treat the model’s scalable role as semantic declaration, not sovereign reasoning. The model answers:

```text
What semantic act am I performing this turn?
```

Then the deterministic layer answers:

```text
Given that act, what must exist, what must be evidenced, what must be reviewed,
and what routes are allowed?
```

Compact formula:

```text
natural task
  -> typed semantic declaration
  -> canonical lookup
  -> obligation expansion
  -> bounded execution
  -> evidence-bearing closeout
  -> independent review/audit
  -> deterministic route
```

The key historical unlock is that LLMs can perform robust **semantic class binding** from messy task/code context: “make a runtime picker menu” becomes `CREATE ui.menu@v1`, not “some React code.” Without that O-binding, pattern libraries and checkers remain shallow. With it, review can become repeatable: `ui.menu@v1` always activates lifecycle obligations; `semantic.validator@v1` always activates non-vacuity and branch-witness obligations; `semantic.normalizer@v1` always activates absence/null/empty preservation obligations.

---

## Problem statement

ADEU’s existing doctrine already separates authority, evidence, and projection. The problem is that ordinary agentic work still often begins as an untyped natural-language task:

```text
Make me a runtime picker menu in the composer.
Add a validator.
Normalize imported rows.
Cache this expensive call.
Project runtime state into the UI.
```

A model can often perform the task, but review remains brittle because the system has not first declared what kind of semantic act is happening. The result is stochastic rediscovery:

```text
Does this menu need an outside-click handler?
Does this validator need non-empty evidence refs?
Does this normalizer need to preserve missing vs null vs empty?
Does this projection invent state?
Does this cache need invalidation?
```

These are not one-off reasoning questions. They are class-indexed obligations. ADEU should not ask every worker or reviewer to rediscover them from scratch.

The doctrine gap is therefore:

```text
How does a natural turn ignite the correct deterministic ADEU obligation machinery?
```

The answer is a typed semantic declaration artifact.

---

## Core thesis

The ADEU semantic declaration meta-loop should be deterministic even when some internal offices use stochastic models.

The model’s key scalable role is not to reason freely every turn. Its key scalable role is to bind a natural task or code context to a canonical semantic act:

```text
operator + object/function class + target/context refs + evidence basis
```

Examples:

```text
“create a menu”
  -> CREATE ui.menu@v1

“add a validator”
  -> CREATE semantic.validator@v1

“normalize imported rows”
  -> CREATE/UPDATE semantic.normalizer@v1

“project runtime state into the composer”
  -> PROJECT runtime_state@v1 INTO ui.surface@v1

“cache this expensive call”
  -> CREATE cache.layer@v1

“subscribe to event stream”
  -> CREATE event.subscription@v1
```

Once that typed declaration exists, the deterministic layer performs canonical lookup:

```text
CREATE ui.menu@v1
  -> ephemeral surface lifecycle obligations
  -> visibility owner requirement
  -> death trigger requirement
  -> outside-click or waiver requirement
  -> escape-key or waiver requirement
  -> parent-unmount cleanup requirement
  -> evidence contract
  -> reviewer checklist
  -> closeout witness requirements
```

The declaration is the ignition point. It must be compact, typed, and evidence-bearing. It must not be “menu vibes.”

---

## Deterministic meta-loop model

### Core separation

**Observed ADEU posture.** Existing ANM / D@1 practice already distinguishes readable prose, authority-zone blocks, and derived deterministic artifacts. Existing harness schemas distinguish compiled taskpack bindings, worker execution attestation, and boundary conformance reports. Existing operator projection doctrine distinguishes visibility from authority.

**Recommended meta-loop separation.**

```text
1. Stochastic cognition inside bounded offices/workers.
2. Deterministic transitions between offices.
3. Only typed artifacts have procedural force.
4. The meta-orchestrator checks artifact presence, validity, and table routes.
5. The reviewer/auditor is a separate office, not the meta-orchestrator itself.
```

A model may be used in the declaration office, implementation office, research office, authoring office, or audit office. But its untyped reasoning has no procedural force. The only things that move the loop are typed artifacts accepted by deterministic validators or route tables.

### Resident model competency contract

The resident model does not need to reconstruct the institutional reason for
the loop on every turn. The meaning of the sequence lives in the harness, not
in worker improvisation.

The resident model must obey the current procedural pointer:

```text
- identify the active semantic pointer or declared loop state;
- consume only the declared inputs for that state;
- emit the required artifact shape;
- preserve order, duplicates, refs, and declared uncertainty fields;
- refrain from inventing a different class, obligation, artifact, or transition;
- route ambiguity, unknown pointers, and malformed inputs into declared
  uncertainty / abstain / registry-gap slots;
- stop when the schema or transition table stops.
```

The harness owns sequence meaning. The model owns bounded local judgment and
typed artifact production.

Compact inversion:

```text
Do not put the whole institution inside the model.
Put the model inside the institution.
```

The minimal resident-agent competency is therefore:

```text
semantic pointer obedience
artifact-shape obedience
bounded local judgment
declared uncertainty
no unauthorized transition
```

This is intentionally weaker and safer than asking a model to autonomously
reconstruct the whole philosophy of the process, understand every downstream
implication, self-audit perfectly, and choose the next institutional action.

### Loop shape

```text
Turn ingress
  -> semantic declaration worker
  -> canonical meta-list lookup
  -> obligation expansion
  -> implementation / research / authoring worker
  -> evidence artifact
  -> reviewer / auditor worker
  -> audit artifact
  -> deterministic closeout adjudicator
  -> next state
```

### State transition sketch

```text
turn_ingress_received
  requires: ingress_event@v1
  route: semantic_declaration_required

semantic_declaration_required
  requires: turn_semantic_declaration@v1
  if valid selected binding: canonical_lookup
  if ambiguous: clarification_or_abstain_route
  if unknown pointer: registry_gap_route
  if malformed: blocked_invalid_declaration

canonical_lookup
  requires: canonical_meta_lookup_result@v1
  if exact match: obligation_expansion
  if conflict: blocked_registry_conflict
  if unknown: blocked_unknown_semantic_pointer

obligation_expansion
  requires: obligation_expansion_bundle@v1
  emits: evidence_contract@v1, edge_probe_plan@v1, reviewer_taskpack@v1
  route: bounded_worker_execution

bounded_worker_execution
  requires: compiled_policy_taskpack_binding@v1 or equivalent task boundary
  emits: worker_execution_attestation@v1, evidence_bundle@v1
  route: independent_review

independent_review
  requires: audit_report@v1 or worker_boundary_conformance_report@v1
  route: deterministic_closeout_adjudication

deterministic_closeout_adjudication
  if audit pass + evidence sufficient: closeout_satisfied
  if audit fail: remediation_required
  if incomplete evidence: evidence_reentry
  if unknown resolution: declaration_or_registry_reentry
  if waiver claimed without waiver artifact: blocked_waiver_laundering
  if permanence claimed without permanence scope: blocked_lifecycle_laundering
```

### O/E/D/U separation

This loop should preserve ADEU’s O/E/D/U frame:

| Lane               | Role in the meta-loop                                                                                                                                 |
| ------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------- |
| **O — Ontology**   | The semantic declaration binds the turn to operator/object/class: `CREATE ui.menu@v1`, `VALIDATE readiness.summary@v1`, `NORMALIZE imported_rows@v1`. |
| **E — Epistemics** | Evidence contracts define what witnesses, refs, probes, source spans, attestations, and counterexamples are admissible.                               |
| **D — Deontics**   | Class-indexed obligations define what must, must not, or may happen: lifecycle, non-vacuity, source preservation, capability gates.                   |
| **U — Utility**    | Closeout routing defines whether the turn is useful, complete, blocked, deferred, waived, or ready for next office.                                   |

The important move is that O-binding happens before D/E/U expansion. Without O-binding, the system does not know which obligations matter.

---

## Semantic declaration model

The declaration answers:

```text
What am I doing this turn?
```

It should not answer:

```text
What code do I feel like writing?
What seems probably okay?
What would a reviewer maybe care about?
```

### Minimal declaration shape

Conceptual artifact:

```yaml
schema: turn_semantic_declaration@1
turn_ref: turn:2026-05-04-example
binding_posture: selected        # selected | ambiguous | abstain | registry_gap
source_witnesses:
  - kind: user_turn_text
    ref: ingress:turn_text
    excerpt: "Make me a runtime picker menu in the composer."

selected_acts:
  - act_ref: act:runtime-picker-menu:create
    operator: CREATE
    object_class: ui.menu@v1
    object_id_hint: runtime_picker_menu
    target_context_refs:
      - composer_bottom_band@v1
    modifiers:
      - ephemeral
      - interactive_surface
    binding_basis:
      lexical_cues: ["picker", "menu"]
      context_cues: ["composer"]
      negative_cues_checked:
        - not_modal
        - not_static_text
        - not_page_route

  - act_ref: act:runtime-options:project
    operator: PROJECT
    source_class: runtime_option_set@v1
    object_class: ui.menu@v1
    target_context_refs:
      - runtime_picker_menu
    binding_basis:
      lexical_cues: ["runtime", "provider", "reasoning options"]

  - act_ref: act:composer-band:connect
    operator: CONNECT
    source_class: ui.menu@v1
    target_class: ui.surface@v1
    target_context_refs:
      - composer_bottom_band@v1

declaration_limits:
  implementation_not_claimed: true
  authority_not_minted: true
  requires_canonical_lookup: true
```

This artifact does not say the work is complete. It only says which semantic acts are being performed and what source/context evidence supports the binding.

### Declaration examples

| Natural task                               | Typed semantic declaration                     |
| ------------------------------------------ | ---------------------------------------------- |
| “Create a menu.”                           | `CREATE ui.menu@v1`                            |
| “Add a validator.”                         | `CREATE semantic.validator@v1`                 |
| “Normalize imported rows.”                 | `CREATE/UPDATE semantic.normalizer@v1`         |
| “Project runtime state into the composer.” | `PROJECT runtime_state@v1 INTO ui.surface@v1`  |
| “Cache this expensive call.”               | `CREATE cache.layer@v1`                        |
| “Subscribe to event stream.”               | `CREATE event.subscription@v1`                 |
| “Route failed jobs to retry queue.”        | `ROUTE job.failure_event@v1 TO retry.queue@v1` |
| “Migrate old schema records.”              | `MIGRATE schema.binding@v1`                    |
| “Review this implementation.”              | `REVIEW evidence.bundle@v1`                    |
| “Close this task.”                         | `CLOSEOUT closeout.artifact@v1`                |

### Binding posture

A declaration must be allowed to abstain.

```yaml
binding_posture: abstain
reason: no_matching_canonical_class
observed_task_excerpt: "make it feel more alive"
recommended_route: human_semantic_clarification
```

Unknown class invention must fail closed. The model may propose a candidate class, but only canonical classes trigger deterministic obligations.

---

## Proposed Canonical Meta-List v0

This is not a giant ontology. It is a small compositional list:

```text
operator family
  + object/function class
  + optional modifiers
  -> obligation families
  -> edge probe templates
  -> evidence contract
  -> reviewer taskpack
  -> closeout witness requirements
```

The v0 should be just large enough to bind recurring coding, review, research, and UX work.

### Operator families

Canonical operators should be few, stable, and compositional. Aliases may exist, but deterministic lookup should use the canonical spelling.

| Canonical operator | Scope                                                                                                   |
| ------------------ | ------------------------------------------------------------------------------------------------------- |
| `CREATE`           | Introduce a new object, function, stateful surface, artifact, validator, projection, or support object. |
| `MODIFY`           | Change an existing object while preserving declared identity and lifecycle.                             |
| `REMOVE`           | Delete, unrender, disconnect, deprecate, or retire an object.                                           |
| `CONNECT`          | Bind two objects, surfaces, resources, schemas, or workers.                                             |
| `PROJECT`          | Render or expose source-bound state into another surface without minting authority.                     |
| `VALIDATE`         | Check an object, branch, claim, payload, or readiness state against declared semantics.                 |
| `NORMALIZE`        | Transform inputs into canonical representation while preserving declared distinctions.                  |
| `ROUTE`            | Dispatch or select a path, handler, queue, office, reviewer, or next state.                             |
| `TRANSITION`       | Move state from one declared phase to another under transition law.                                     |
| `AGGREGATE`        | Summarize, reduce, group, merge, or produce readiness/claim summaries.                                  |
| `CACHE`            | Store derived or expensive data for reuse under invalidation law.                                       |
| `SUBSCRIBE`        | Listen to event streams, external changes, or state updates.                                            |
| `PERSIST`          | Store state, records, files, or artifacts durably.                                                      |
| `MIGRATE`          | Move records or schemas between versions while preserving lineage.                                      |
| `GATE`             | Authorize, guard, or restrict capability usage without minting authority locally.                       |
| `REVIEW`           | Inspect evidence, implementation, claims, or conformance as a separate office.                          |
| `RECONCILE`        | Resolve drift, conflict, duplicate records, or inconsistent projections.                                |
| `CLOSEOUT`         | Produce final task/readiness/settlement artifact and route by deterministic table.                      |

### Object/function classes

A minimal v0 should include recurring class families, not every possible application object.

| Class                    | Typical use                                                                   |
| ------------------------ | ----------------------------------------------------------------------------- |
| `ui.menu@v1`             | Ephemeral interactive menu or picker.                                         |
| `ui.modal@v1`            | Blocking or focus-trapping dialog surface.                                    |
| `ui.popover@v1`          | Anchored temporary surface.                                                   |
| `ui.projection@v1`       | Source-bound UI projection of state, evidence, or readiness.                  |
| `ui.surface@v1`          | Named UI region, band, panel, or workbench area.                              |
| `semantic.validator@v1`  | Validation logic with explicit admissible branches and evidence requirements. |
| `semantic.normalizer@v1` | Canonicalization or normalization function.                                   |
| `semantic.classifier@v1` | Branch, class, or label assignment.                                           |
| `semantic.summarizer@v1` | Summary or aggregate claim producer.                                          |
| `state.transition@v1`    | Phase/state movement.                                                         |
| `capability.gate@v1`     | Guard around action, authority, permission, or dispatch.                      |
| `router.dispatcher@v1`   | Path, handler, office, queue, or route selector.                              |
| `cache.layer@v1`         | Cache, memoization, or stored derived call result.                            |
| `event.subscription@v1`  | Listener/subscriber over event stream or state updates.                       |
| `resource.handle@v1`     | External/local resource reference, file handle, connection, or tool binding.  |
| `persistence.store@v1`   | Durable storage surface.                                                      |
| `migration.plan@v1`      | Version/schema/data migration object.                                         |
| `evidence.bundle@v1`     | Evidence package with source witnesses and admissibility posture.             |
| `readiness.summary@v1`   | Readiness or closeout summary over branches and warnings.                     |
| `paper.claim_map@v1`     | Research/paper claim decomposition.                                           |
| `paper.evidence_map@v1`  | Evidence-to-claim mapping.                                                    |
| `schema.binding@v1`      | Binding between schema, artifact, family, or version.                         |
| `worker.taskpack@v1`     | Bounded worker instruction/evidence/gate package.                             |
| `worker.attestation@v1`  | Worker execution attestation or provenance witness.                           |
| `audit.report@v1`        | Independent review/audit output.                                              |
| `closeout.artifact@v1`   | Deterministic closeout payload and routing witness.                           |

### Obligation families

Obligation families are class-indexed. They should not all fire for every act.

| Obligation family                     | Meaning                                                                                                                      |
| ------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| `stateful_lifecycle@v1`               | Any introduced stateful object must declare birth, continuation, and death or explicit permanence scope.                     |
| `birth_continuation_death_algebra@v1` | Birth implies death unless permanence is explicitly declared. Continuation must be distinguishable from creation.            |
| `absence_null_empty_distinction@v1`   | Missing, null, empty, defaulted, and intentionally empty values must not collapse unless irrelevance is explicitly declared. |
| `branch_specific_witness@v1`          | Branch claims require branch-specific evidence witnesses.                                                                    |
| `non_vacuous_validation@v1`           | Validators must not pass merely because empty/default collections make membership checks vacuous.                            |
| `projection_source_integrity@v1`      | Projection must preserve source witnesses and must not invent projected state.                                               |
| `source_witness_preservation@v1`      | Transformations must preserve upstream refs or explicitly declare lossy boundaries.                                          |
| `idempotence_reentry@v1`              | Repeat application, replay, or reentry must not drift semantics unless declared.                                             |
| `rollback_cleanup_teardown@v1`        | Stateful, external, or subscribed objects require cleanup/rollback/teardown posture.                                         |
| `staleness_invalidation@v1`           | Cached or subscribed values require invalidation and freshness boundaries.                                                   |
| `enum_exhaustiveness@v1`              | Declared enum/branch vocabularies require exhaustive handling.                                                               |
| `unknown_case_handling@v1`            | Unknown or future cases must fail closed, route explicitly, or be represented as unknown.                                    |
| `capability_guard@v1`                 | Capability-bearing actions require authority boundary and guard evidence.                                                    |
| `partial_retry_reentry@v1`            | Partial success, retry, and reentry must preserve state and evidence.                                                        |
| `evidence_sufficiency@v1`             | Claims require sufficient direct or admissible evidence.                                                                     |
| `waiver_explicitness@v1`              | Waiver, deferral, or exception must be explicit and traceable.                                                               |
| `cross_field_consistency@v1`          | Related fields, refs, identities, and scopes must agree.                                                                     |
| `failure_path_fail_closed@v1`         | Invalid, malformed, or unresolved states must not silently repair into success.                                              |

### Lifecycle law: birth implies death

Recommended refinement:

```text
Any introduced stateful object must declare:
  - birth condition;
  - continuation condition;
  - death condition OR explicit permanence scope.

Missing death condition is not permanence.

Permanence is an explicit empty death-trigger set within a declared scope.
```

Examples:

```yaml
stateful_object:
  class: ui.menu@v1
  birth_condition: user_clicks_runtime_picker_button
  continuation_condition: menu_visibility_owner == open AND parent_surface_mounted
  death_triggers:
    - option_selected
    - outside_pointer
    - escape_key
    - parent_unmount
  permanence_scope: null
```

Explicit permanence, when lawful, must look more like:

```yaml
stateful_object:
  class: persistence.store@v1
  birth_condition: migration_initializes_store
  continuation_condition: store_schema_version_supported
  death_triggers: []
  permanence_scope:
    scope: project_runtime_storage
    until: schema_family_deprecated_or_migrated
    authority_ref: lock_or_policy_ref
```

An empty death-trigger list without `permanence_scope` is invalid.

### Evidence artifact types

These are artifact roles, not a demand for a broad new schema universe.

| Artifact type                          | Role                                                                                           |
| -------------------------------------- | ---------------------------------------------------------------------------------------------- |
| `turn_semantic_declaration@1`          | Model-assisted O-binding artifact.                                                             |
| `canonical_meta_lookup_result@1`       | Deterministic lookup result for declared operator/object/class bundle.                         |
| `obligation_expansion_bundle@1`        | Expanded obligations, edge probes, evidence contracts, reviewer tasks, and closeout witnesses. |
| `edge_probe_plan@1`                    | Required edge probes selected from class bindings.                                             |
| `evidence_contract@1`                  | What evidence kinds are admissible and required.                                               |
| `source_witness_bundle@1`              | Source refs, spans, payload refs, or code refs that support the work.                          |
| `worker.taskpack@1`                    | Bounded work package, aligned with existing taskpack binding posture.                          |
| `worker.execution_attestation@1`       | Worker execution and provenance witness.                                                       |
| `worker.boundary_conformance_report@1` | Boundary conformance report over actual worker actions.                                        |
| `evidence.bundle@1`                    | Material evidence emitted by worker.                                                           |
| `audit.report@1`                       | Independent reviewer/auditor output.                                                           |
| `closeout.artifact@1`                  | Deterministic closeout and route witness.                                                      |
| `readiness.summary@1`                  | Optional readiness summary when the task requires readiness classification.                    |

---

## Class-indexed obligation examples

### A. UI menu lifecycle bug

**Observed task.**

```text
“Make a menu.”
```

**Semantic declaration.**

```text
CREATE ui.menu@v1
```

**Class-indexed obligations.**

```text
ui.menu@v1
  -> stateful_lifecycle@v1
  -> birth_continuation_death_algebra@v1
  -> visibility_owner_required@v1
  -> death_trigger_required@v1
  -> outside_click_or_waiver@v1
  -> escape_key_or_waiver@v1
  -> parent_unmount_cleanup@v1
```

**Review finding.**

The implementation opens the menu on click, but no close/unrender condition exists. The menu has a birth trigger but no death trigger.

**Useful P2-style comment.**

```text
Lifecycle incomplete for CREATE ui.menu@v1. The menu is born on click, but the
implementation does not declare or implement a death path such as option selection,
outside pointer, Escape, or parent unmount cleanup. Missing death is not permanence;
permanence would require explicit permanence_scope, which is absent.
```

### B. Readiness validator bug

**Observed task.**

```text
Validate readiness, including ready_with_nonblocking_warnings.
```

**Semantic declaration.**

```text
CREATE semantic.validator@v1
VALIDATE readiness.summary@v1
```

**Class-indexed obligations.**

```text
semantic.validator@v1 + readiness.summary@v1
  -> branch_specific_witness@v1
  -> non_vacuous_validation@v1
  -> evidence_sufficiency@v1
  -> absence_null_empty_distinction@v1
  -> enum_exhaustiveness@v1
  -> unknown_case_handling@v1
```

**Failure shape.**

Refs default to empty lists. Membership checks pass vacuously. The `ready_with_nonblocking_warnings` branch is accepted even though required scope, target, warning, or validation links are missing.

**Useful P2-style comment.**

```text
Validator accepts a readiness branch without branch-specific witnesses. For
ready_with_nonblocking_warnings, the readiness claim depends on warning/scope/target
refs, so those refs must be non-empty and source-bound. Defaulting refs to [] makes
the membership checks vacuous and allows a counterexample with missing evidence.
```

### C. Normalizer bug

**Observed task.**

```text
Normalize imported rows.
```

**Semantic declaration.**

```text
CREATE semantic.normalizer@v1
```

**Class-indexed obligations.**

```text
semantic.normalizer@v1
  -> absence_null_empty_distinction@v1
  -> source_witness_preservation@v1
  -> idempotence_reentry@v1
  -> failure_path_fail_closed@v1
  -> round_trip_or_lossy_declaration@v1
```

**Failure shape.**

The normalizer collapses absent, null, and empty into the same value.

**Useful P2-style comment.**

```text
Normalizer collapses semantically distinct input states. Missing evidence, explicit
null, and intentionally empty evidence all normalize to the same representation, so
downstream validation cannot tell whether evidence was absent or intentionally empty.
Preserve the distinction or declare it explicitly irrelevant with a lossy-boundary
witness.
```

### D. Operator projection bug

**Observed task.**

```text
Project runtime state into the composer.
```

**Semantic declaration.**

```text
PROJECT runtime_state@v1 INTO ui.projection@v1
CONNECT ui.projection@v1 TO ui.surface@v1
```

**Class-indexed obligations.**

```text
ui.projection@v1
  -> projection_source_integrity@v1
  -> no_invented_projection_state@v1
  -> source_witness_preservation@v1
  -> authority_non_minting@v1
  -> stale_source_visibility@v1
```

**Useful P2-style comment.**

```text
Projection lacks a source witness for the displayed runtime status. A composer
projection may expose source-bound state, but it may not manufacture readiness or
authority from UI state. Add source refs or render the state as unknown/blocking.
```

This follows the operator-projection doctrine: projection can make state visible, but it cannot become source truth, ratification, runtime permission, or dispatch authority.

---

## Why this matters for edge detection

ADEU’s edge-ledger direction already classifies recurring edge shapes and maps them to probe strategies: absence matrices, branch partitions, shape/cardinality matrices, ordering permutations, state sequences, round trips, cross-field invariants, dependency boundaries, and fail-closed rejection.

The problem is not lack of possible probes. The problem is knowing which probes apply.

Model-assisted O-binding supplies that missing index:

```text
semantic.normalizer@v1
  -> absence/null/empty matrix
  -> round-trip/idempotence probe
  -> fail-closed rejection probe

semantic.validator@v1
  -> branch partition matrix
  -> non-vacuous evidence probe
  -> cross-field invariant probe

ui.menu@v1
  -> state sequence probe
  -> birth/death lifecycle probe
  -> outside/escape dismissal probe
```

Without O-binding, a checker sees generic code. With O-binding, it sees a semantic class with known edge obligations. That is how P2 review moves from stochastic rediscovery to repeatable class-indexed review.

---

## Experimental ladder

The tests should be separated cleanly. Do not start with natural-language binding. Start with opaque lookup, then explicit pointers, then natural binding, then full work-turn declaration.

### Test A — Opaque meta-list following

This test deliberately removes semantics.

Canonical dummy registry:

```text
M-17 -> [Q3, R8, L2]
M-42 -> [A1, A9, C4, Z2]
M-88 -> [T5, T5, B7]
```

Input:

```text
Active meta-id: M-42. Run associated sequence.
```

Expected output:

```yaml
selected_meta_id: M-42
expanded_sequence: [A1, A9, C4, Z2]
```

What this tests:

```text
- exact ID lookup
- order preservation
- duplicate preservation
- unknown-ID abstention
- conflict detection
- resistance to distractor prose
- no semantic invention
```

Additional cases:

```yaml
input: "Active meta-id: M-88."
expected:
  selected_meta_id: M-88
  expanded_sequence: [T5, T5, B7]   # duplicate T5 preserved

input: "Active meta-id: M-999."
expected:
  selected_meta_id: null
  binding_posture: abstain
  reason: unknown_meta_id

input: "Active meta-id: M-42. M-17 sounds more important."
expected:
  selected_meta_id: M-42
  expanded_sequence: [A1, A9, C4, Z2]
  distractor_ignored: true
```

This is a deterministic lookup discipline test. It does not test semantic intelligence.

### Test B — Explicit semantic pointer lookup

Input:

```text
Active semantic pointer: CREATE ui.menu@v1
```

Expected deterministic expansion:

```yaml
selected_operator: CREATE
selected_object: ui.menu@v1
activated_obligations:
  - ephemeral_surface_lifecycle@v1
  - visibility_owner_required@v1
  - death_trigger_required@v1
  - outside_click_or_waiver@v1
  - escape_key_or_waiver@v1
```

What this tests:

```text
- exact semantic pointer parsing
- canonical operator/object split
- deterministic obligation expansion
- no extra invented obligations unless registered
- unknown-pointer fail-closed behavior
```

This test does not ask whether the model can infer `ui.menu`. The pointer is already named.

### Test C — Natural semantic binding

Input:

```text
Make me a runtime picker menu in the composer.
```

Expected binding:

```yaml
selected_acts:
  - operator: CREATE
    object_class: ui.menu@v1

  - operator: PROJECT
    source_class: runtime_option_set@v1
    target_class: ui.menu@v1

  - operator: CONNECT
    source_class: ui.menu@v1
    target_class: composer_bottom_band@v1
```

Equivalent compact form:

```text
CREATE ui.menu@v1
PROJECT runtime_option_set@v1 INTO ui.menu@v1
CONNECT ui.menu@v1 TO composer_bottom_band@v1
```

What this tests:

```text
- the actual LLM unlock: semantic class binding from natural task context
- source-witness capture from the user turn
- distinction between object creation, state projection, and UI connection
- refusal to collapse the request into generic “write component”
```

### Test D — Work-turn declaration

Input:

```text
Add a runtime picker in the composer that lists provider/reasoning options,
validates the selected provider, and caches provider metadata.
```

Expected output is a `TURN_SEMANTIC_DECLARATION`, not an implementation.

Expected declaration:

```yaml
schema: turn_semantic_declaration@1
binding_posture: selected

selected_acts:
  - operator: CREATE
    object_class: ui.menu@v1
    object_id_hint: runtime_picker_menu

  - operator: PROJECT
    source_class: runtime_option_set@v1
    target_class: ui.menu@v1

  - operator: CONNECT
    source_class: ui.menu@v1
    target_class: composer_bottom_band@v1

  - operator: CREATE
    object_class: semantic.validator@v1
    object_id_hint: selected_provider_validator

  - operator: CACHE
    object_class: cache.layer@v1
    object_id_hint: provider_metadata_cache

activated_obligation_families:
  - stateful_lifecycle@v1
  - projection_source_integrity@v1
  - non_vacuous_validation@v1
  - branch_specific_witness@v1
  - staleness_invalidation@v1
  - capability_guard@v1
  - evidence_sufficiency@v1
  - waiver_explicitness@v1

evidence_contract:
  required_witnesses:
    - source refs for runtime/provider option set
    - menu birth/continuation/death trigger evidence
    - validator branch fixtures or counterexamples
    - cache key/invalidation/freshness evidence
    - composer surface connection witness

closeout_witness_requirements:
  - obligation_expansion_bundle@v1 accepted
  - evidence_bundle@v1 emitted
  - independent audit_report@v1 emitted
  - deterministic closeout_artifact@v1 maps result to next state
```

What this tests:

```text
- multi-act declaration
- compositional operator/object binding
- obligation expansion coverage
- evidence contract completeness
- reviewer/auditor task derivation
- closeout witness requirements
```

---

## .adeu.md / ANM integration sketch

### Observed grounding

ANM already provides the right substrate: readable prose remains prose; recognized authority blocks compile to typed artifacts; deterministic outputs include normalized IR, fact bundles, result sets, ledgers, semantic diffs, reader projections, and compile reports.

The semantic declaration should extend this posture. It should not make arbitrary Markdown prose authoritative.

### Recommended integration principle

Natural prose like:

```text
I need to create a menu.
```

should be treated as a semantic act only inside a governed agent procedure where a typed declaration artifact is required.

The prose itself does not ignite obligations. The typed declaration does:

```text
CREATE ui.menu@v1
```

Then deterministic lookup expands the registered class bundle.

### Minimal conceptual block sketch

This is not a full new language design. It is only a grounding sketch for how ANM-style documents could carry the idea.

```markdown
:::O@1 id=runtime-picker-menu-object
CREATE ui.menu runtime_picker_menu

INTENT
  Allow the user to pick runtime/provider/reasoning options from the composer area.

CLASS
  ui.menu@v1

CONTEXT
  parent_surface: composer_bottom_band
  permanence: false
:::
```

The O-block binds the semantic object and class. It does not by itself prove implementation.

A D-style law can then be class-indexed:

```markdown
:::D@1 id=ui-menu-lifecycle-law
ON ui.menu

MUST declare birth_trigger
MUST declare visibility_owner
MUST declare at_least_one death_trigger
MUST handle escape_key dismissal unless explicitly waived
MUST handle outside_pointer dismissal unless explicitly waived
MUST handle parent_unmount cleanup
MUST_NOT treat missing death_trigger as permanence
ONLY_IF permanence_scope is explicit MAY death_trigger_set be empty
:::
```

### O/E/D/U integration

| Lane  | ANM integration posture                                                                                                     |
| ----- | --------------------------------------------------------------------------------------------------------------------------- |
| **O** | Future typed declaration blocks or artifacts bind semantic object/class roles.                                              |
| **E** | Evidence contracts and source witness bundles define admissible proof of implementation, projection, validation, or review. |
| **D** | `D@1`-style laws define class-indexed obligations.                                                                          |
| **U** | Closeout artifacts define readiness, usefulness, blocked status, waiver, deferral, and next route.                          |

The key point is that `.adeu.md` can become the semantic activation substrate without turning all prose into executable law.

---

## Reviewer/auditor role separation

The meta-orchestrator must not become the auditor.

### Meta-orchestrator

The meta-orchestrator is deterministic and table-driven. It checks:

```text
- Is the required typed artifact present?
- Is its schema valid?
- Does the canonical pointer exist?
- Did deterministic lookup produce an expansion?
- Did the worker emit required evidence artifacts?
- Did an independent reviewer/auditor artifact exist?
- What does the closeout route table say?
```

It does not decide substantively whether a menu lifecycle is adequate. It only routes based on accepted artifacts.

### Worker office

The implementation/research/authoring worker may be stochastic. It receives bounded obligations and evidence contracts. It emits evidence, not authority.

Relevant existing ADEU shapes already point this way:

```text
compiled_policy_taskpack_binding@1
worker_execution_attestation@1
worker_boundary_conformance_report@1
```

These make worker scope, provenance, observed action carriers, command/mutation boundaries, and conformance judgments explicit.

### Reviewer/auditor office

The reviewer/auditor is a separate office. It may also use a model, but it receives a different taskpack:

```text
Given declaration + obligation expansion + evidence bundle,
audit whether the evidence satisfies the class-indexed obligations.
```

It emits:

```text
audit.report@1
```

or a conformance artifact with findings such as:

```yaml
overall_judgment: non_conformant
findings:
  - class: ui.menu@v1
    obligation: death_trigger_required@v1
    result: fail
    evidence_basis: "birth trigger found; no death trigger found"
```

The auditor still does not mint final authority. Its audit artifact is consumed by the deterministic closeout adjudicator.

### Closeout adjudicator

The closeout adjudicator maps typed inputs to next state:

| Audit/evidence state                              | Deterministic route              |
| ------------------------------------------------- | -------------------------------- |
| pass + evidence sufficient                        | `closeout_satisfied`             |
| fail                                              | `remediation_required`           |
| incomplete evidence                               | `evidence_reentry`               |
| unknown semantic pointer                          | `registry_gap`                   |
| unknown resolution                                | `declaration_or_binding_reentry` |
| waiver claimed with explicit waiver artifact      | `waived_nonblocking`             |
| waiver claimed without waiver artifact            | `blocked_waiver_laundering`      |
| permanence claimed with explicit permanence scope | `permanence_accepted_with_scope` |
| death trigger missing and no permanence scope     | `blocked_lifecycle_incomplete`   |

This preserves ADEU’s result/ledger doctrine: pass, fail, unknown evidence, unknown resolution, waived, deferred, and gated-off states must not collapse.

---

## Non-goals

This pass should not be read as authorization to:

1. Implement a parser, runtime scheduler, or broad orchestration system now.
2. Replace `D@1` with a large new language.
3. Infer obligations from arbitrary prose.
4. Create a giant universal ontology.
5. Make the model sovereign over obligations, routes, waivers, or authority.
6. Treat projection as source truth or operator visibility as ratification.
7. Treat reviewer output as final authority.
8. Collapse O/E/D/U into one “semantic JSON blob.”
9. Treat missing evidence as pass.
10. Treat missing death condition as permanence.
11. Treat a support-layer note as runtime or release authorization.
12. Require every coding task to formalize every sentence.
13. Make all possible UI/component classes first-class in v0.

The v0 should be small, compositional, and class-indexed.

---

## Failure modes and guardrails

| Failure mode                                           | Guardrail                                                                                                                                                        |
| ------------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Model chooses the wrong semantic class.                | Declaration artifact must include source witnesses, binding basis, negative cues checked, and `ambiguous` / `abstain` posture. Reviewer can challenge O-binding. |
| Model invents a class or obligation.                   | Deterministic lookup only accepts canonical IDs. Unknown IDs route to registry gap, not execution.                                                               |
| Free-form “vibes” replace typed declaration.           | Only `turn_semantic_declaration@1` or equivalent typed artifacts have procedural force.                                                                          |
| The meta-list grows into a giant ontology.             | Keep v0 operator/object/obligation lists small; add classes only when recurring work proves the need.                                                            |
| Deterministic layer starts reasoning semantically.     | It only performs lookup, expansion, schema validation, artifact presence checks, and route-table transitions.                                                    |
| Auditor and implementer collapse into the same office. | Require separate reviewer/auditor artifact with distinct taskpack and evidence basis.                                                                            |
| Auditor mints authority.                               | Audit output is evidence for closeout, not authority by itself.                                                                                                  |
| Waiver laundering.                                     | `waiver_ref` required for waiver posture; source-semantic exception and external waiver remain distinguishable.                                                  |
| Permanence laundering.                                 | Empty death-trigger set valid only with explicit `permanence_scope`. Missing death is not permanence.                                                            |
| Projection laundering.                                 | `PROJECT` activates source witness preservation and no-invented-state obligations.                                                                               |
| Null/default laundering.                               | Normalizers and validators activate absence/null/empty distinction and absence-matrix probes.                                                                    |
| Vacuous validation.                                    | Branch-specific witness obligations require non-empty refs when branch claims depend on them.                                                                    |
| Edge probes applied randomly.                          | Edge probes are selected by class binding, not ad hoc reviewer intuition.                                                                                        |
| Unknown resolution treated like missing evidence.      | Unknown resolution is a harder failure and routes to declaration/registry/toolchain repair.                                                                      |
| Prompt distractors override IDs.                       | Opaque lookup tests require exact ID selection and distractor resistance.                                                                                        |
| Order/duplicates lost in canonical expansion.          | Opaque Test A checks order and duplicate preservation.                                                                                                           |
| Model overstates completion.                           | Declaration is not implementation; evidence and audit artifacts are required before closeout.                                                                    |

---

## Minimal next-slice recommendation

**Recommended narrow slice.** Promote a small doctrine/test bundle, not an implementation arc.

1. Freeze a `canonical_meta_list_v0` support/architecture artifact with:

   * operator families;
   * object/function classes;
   * obligation families;
   * evidence artifact roles;
   * three class bundles: `ui.menu@v1`, `semantic.validator@v1`, `semantic.normalizer@v1`.

2. Define only the conceptual shape of `turn_semantic_declaration@1`:

   * selected acts;
   * source witnesses;
   * binding posture;
   * canonical pointers;
   * abstain/ambiguous behavior.

3. Define deterministic expansion fixtures for:

   * Test A: opaque ID lookup;
   * Test B: explicit semantic pointer lookup;
   * Test C: natural semantic binding;
   * Test D: work-turn declaration.

4. Use existing harness concepts as downstream anchors:

   * compiled taskpack binding;
   * worker execution attestation;
   * worker boundary conformance report;
   * evidence bundle;
   * audit artifact;
   * closeout artifact.

5. Measure only three things:

   * binding accuracy: did the declaration choose the right operator/object classes?
   * expansion accuracy: did deterministic lookup expand exactly the registered obligations?
   * review repeatability: did class-indexed obligations produce the expected menu/validator/normalizer findings?

**Optional later slice.** Add `ui.projection@v1`, `cache.layer@v1`, and `event.subscription@v1` only after the first three bundles prove the doctrine.

The minimal success condition is not a working orchestration product. It is a repeatable proof that:

```text
natural work context
  -> typed O-binding
  -> deterministic obligation expansion
  -> evidence-bearing work
  -> independent audit
  -> deterministic closeout
```

can produce useful review findings without forcing every worker to rediscover the same edge law from scratch.
