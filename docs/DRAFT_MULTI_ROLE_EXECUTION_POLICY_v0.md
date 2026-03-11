# Draft Multi-Role Execution Policy v0

Status: working synthesis only (March 11, 2026 UTC).

This document defines the intended operational split between ADEU and Codex for multi-role
execution.

It is not a lock doc. It does not itself authorize runtime changes, release-scope changes, or
boundary expansion. It records the current recommended jurisdiction model on top of Codex's
existing capability surface.

Canonical precedence:

- [MULTI_ROLE_EXECUTION_CONTRACTS_v0.json](/home/rose/work/LexLattice/odeu/docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json)
  is the canonical contract artifact.
- This policy doc and the lock draft are derived interpretive layers and must not weaken or
  contradict the JSON contract surface.

## Architectural Positioning

This bundle is not another V33/V34-style pipeline contract.

It governs a different axis:

- V33/V34 contracts govern deterministic harness stages such as compile, verify, package,
  sign, parity, attestation, and distribution lanes.
- This bundle governs role authority, write jurisdiction, handoff structure, and acceptance
  boundaries across ADEU-managed multi-agent execution.

That makes it a governance-layer family, not a pipeline-stage family.

Control/execution split:

- ADEU is the control plane.
- Codex is the execution plane.

Current enforcement status:

- design-time contract with post-hoc reconciliation only;
- no runtime enforcement module currently hard-enforces these boundaries.

## Core Rule

ADEU owns governance. Codex provides the execution substrate.

Compressed constitution:

- `main_orchestrator` owns governance authority;
- `builder` holds the current scoped write lease;
- `explorer`, `validator`, and `docs_helper` produce typed non-authoritative outputs unless
  explicitly re-roled;
- all authority changes must be explicit;
- acceptance and closeout never leave `main_orchestrator`.

Authority tiers:

- `main_orchestrator`
- `builder`
- `explorer`, `validator`, `docs_helper`

The support roles are differentiated by function, but equal in authority status within one
shared tier: all remain non-authoritative unless explicitly re-roled.

## Why This Split Exists

Current Codex already provides:

- strong session and turn context;
- real tool execution;
- real sub-agent lifecycle;
- permission and sandbox surfaces;
- practical history and compaction continuity.

Current Codex does not hard-enforce:

- single-writer discipline;
- role authority partitions;
- ADEU-style governance and closeout authority;
- typed acceptance-grade worker handoff as a platform invariant.

So the correct posture is:

- use Codex as the execution plane;
- keep ADEU as the control plane.
- treat worker-reported state as claims until reconciled by the orchestrator.

## Artifact Classes

There are three artifact classes.

These classes are orthogonal to authoritative surface.

- `artifact_class` says whether something is `authoritative`, `advisory`, or `scratch`.
- `artifact_surface` says whether it concerns `implementation`, `governance`, `mixed`, or
  `none`.

### Authoritative

Artifacts that can change implementation truth or ADEU governance truth.

Examples:

- production code;
- tests treated as release gates;
- accepted evidence inputs;
- ADEU lock, assessment, and closeout artifacts.

Default writers:

- `builder` for authoritative implementation artifacts inside leased scope;
- `main_orchestrator` for authoritative governance artifacts.

Authoritative surfaces:

- `implementation`
- `governance`

The same `authoritative` class may appear on either surface, but the owning role differs.

### Advisory

Artifacts that inform judgment but do not by themselves change implementation or governance
truth.

Examples:

- exploration reports;
- validation summaries;
- review notes;
- draft implementation evidence before acceptance;
- non-authoritative documentation drafts.

Default writers:

- `explorer`
- `validator`
- `docs_helper`
- `builder`
- `main_orchestrator`

### Scratch

Ephemeral working artifacts with no authority unless explicitly promoted.

Examples:

- temporary notes;
- local repro logs;
- throwaway scripts;
- intermediate local outputs.

Default writers:

- `main_orchestrator`
- `builder`
- `explorer`
- `validator`
- `docs_helper`

Promotion rule:

- no advisory or scratch artifact becomes authoritative without explicit
  `main_orchestrator` acceptance.

Cross-role execution rule:

- executing an advisory or scratch artifact consumes the authority of the executor, not the
  author;
- if a `builder` executes a support-role script or similar artifact, all resulting mutations
  are attributed to the builder's implementation write lease;
- support roles do not gain implementation authority by proxy through artifact execution.

## Roles

### `main_orchestrator`

Lives in:

- ADEU harness

Authority:

- sole interpreter of user intent, governance state, completion, acceptance, and closeout.

Allowed:

- interpret requests and ADEU governance artifacts;
- decompose work;
- assign role and scope;
- issue, revoke, or transfer write lease;
- spawn and coordinate workers;
- review handoffs;
- accept or reject evidence;
- update ADEU governance artifacts;
- decide PR, merge, and closeout readiness.

Forbidden:

- delegating final acceptance authority;
- delegating closeout authority;
- treating advisory worker output as self-authenticating.

### `builder`

Lives in:

- implementation repo

Authority:

- scoped implementation authority only.

Write lease:

- holds the current exclusive write lease for the assigned scope;
- the lease is bounded by scope, time, and ownership surface;
- transfer or revocation must be explicit through `main_orchestrator`.

Allowed:

- edit implementation code within leased scope;
- edit tests within leased scope;
- run repo-local gates;
- integrate accepted support findings;
- prepare branch, commit, and PR updates;
- emit implementation evidence.

Forbidden:

- modifying ADEU governance artifacts;
- declaring slice accepted or closed;
- expanding scope without approval;
- spawning another writer without approval.

### `explorer`

Lives in:

- implementation repo

Authority:

- informational and advisory only.

Allowed:

- inspect files;
- search symbols and history;
- answer bounded codebase questions;
- identify risks and dependencies;
- emit advisory reports.

Forbidden:

- editing authoritative implementation artifacts by default;
- declaring completion or acceptance;
- self-upgrading into writer.

### `validator`

Lives in:

- implementation repo

Authority:

- evidence authority only, never acceptance authority.

Allowed:

- run tests, lint, build, repro, and targeted checks;
- report pass/fail outcomes;
- report gaps and residual risks;
- emit evidence reports.

Forbidden:

- editing authoritative implementation artifacts by default;
- declaring evidence sufficient for acceptance;
- quietly fixing failures unless explicitly re-roled.

### `docs_helper`

Lives in:

- implementation repo

Authority:

- advisory documentation authority only.

Allowed:

- draft repo-local documentation;
- summarize implementation changes;
- prepare non-authoritative release notes.

Forbidden:

- modifying ADEU governance artifacts by default;
- changing implementation code by default;
- declaring closure or acceptance.

## Write-Lease Model

Single writer is the default for one implementation repo.

Rules:

- there is exactly one exclusive authoritative implementation write lease by default;
- the `builder` holds that lease for assigned scope only;
- support roles may not self-upgrade into lease holders;
- if a support role must edit authoritative implementation artifacts, it must be explicitly
  re-roled and granted a new lease;
- prior advisory output from a re-roled worker remains advisory unless separately accepted.

## Role Transition Protocol

This is where governance drift is prevented.

Rules:

- no role may self-upgrade authority level;
- any transition that changes authoritative write rights requires explicit
  `main_orchestrator` approval;
- every transition must declare:
  - `from_role`
  - `to_role`
  - `authority_level_before`
  - `authority_level_after`
  - `scope_owned`
  - `reason`
  - `effective_time`
  - `granted_by`
- a support role becoming a `builder` is a new lease event, not an implicit continuation;
- a builder losing scope or authority must have the lease explicitly revoked or narrowed.

## Shared Handoff Envelope

Every repo-local role should return the same minimal handoff structure.

Trust model:

- the handoff envelope is a worker self-report until `main_orchestrator` reconciles it against
  observed repo state, command output, and emitted artifacts;
- lease-scope sufficiency must not be accepted from worker self-report alone.

Required fields:

- `role`
- `authority_level`
- `authority_domain`
- `artifact_class`
- `artifact_surface`
- `repo_root`
- `branch_or_head`
- `scope_owned`
- `scope_remaining`
- `files_changed`
- `commands_run`
- `artifacts_produced`
- `evidence_refs`
- `status`
- `blocking_state`
- `blockers`
- `open_risks`
- `escalation_reason`
- `recommended_next_action`

Field rules:

- `authority_level` must reflect actual role contract, not worker self-importance;
- `authority_domain` must be one of `implementation`, `governance`, or `advisory`;
- `artifact_class` must classify output as authoritative, advisory, or scratch;
- `artifact_surface` must identify the relevant surface as `implementation`, `governance`,
  `mixed`, or `none`;
- `evidence_refs` should cite concrete files, logs, or command outputs;
- `blocking_state` should be either `blocking` or `non_blocking` and should reflect urgency
  to orchestration;
- `files_changed`, `commands_run`, and `artifacts_produced` are self-reported until
  reconciled by `main_orchestrator`;
- `escalation_reason` is always present; it must be an empty string when no escalation exists
  and a non-empty explanation when escalation exists.

Minimum reconciliation expected from `main_orchestrator`:

- recompute effective `files_changed` from observed repo diff or equivalent state witness;
- compare claimed `scope_owned` against the observed mutation surface;
- verify `evidence_refs` resolve to actual files, logs, or outputs where applicable;
- reject lease-scope compliance claims based on self-report alone.

## Acceptance Boundary

This line must remain sharp.

- only `main_orchestrator` may decide that evidence is sufficient for acceptance;
- `validator` may report pass, fail, or unresolved gaps, but may not declare acceptance;
- `explorer` may report likely truth, but may not declare acceptance;
- `builder` may report implementation completion within scope, but may not declare slice
  acceptance or closure;
- `docs_helper` may draft explanatory text, but may not generate authoritative closeout
  language.

## Default Operating Topology

Recommended first topology:

- `1` `main_orchestrator`
- `1` `builder`
- `0..n` `explorer`
- `0..n` `validator`
- `0..n` `docs_helper`

Default rules:

- single builder is the default for one implementation repo;
- multiple writers are forbidden unless explicitly authorized by `main_orchestrator`;
- support roles should prefer advisory and evidence output over direct mutation;
- ADEU remains the governance and closeout authority layer.

## Practical Consequence

The intended flow is:

1. `main_orchestrator` interprets scope and assigns ownership.
2. `builder` performs the implementation.
3. `explorer` answers bounded codebase questions when needed.
4. `validator` runs parallel checks when useful.
5. `docs_helper` drafts repo-local docs if requested.
6. `builder` integrates accepted support findings.
7. `main_orchestrator` adjudicates sufficiency, acceptance, and closeout.

That is the highest-coherence structure that fits current Codex capabilities without
pretending the platform already provides governance-grade role enforcement.
