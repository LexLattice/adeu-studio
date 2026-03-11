# Draft Multi-Role Execution Lock v0

Status: draft lock only (March 11, 2026 UTC).

This document formalizes a first ADEU-style lock for multi-role execution on top of current
Codex behavior.

It is a draft. It is not yet an active release lock, and it does not by itself authorize
runtime changes. Its purpose is to state the invariants, failure conditions, and validation
surface required if the repo later promotes this model into an enforced execution contract.

Canonical precedence:

- [MULTI_ROLE_EXECUTION_CONTRACTS_v0.json](/home/rose/work/LexLattice/odeu/docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json)
  is the canonical contract artifact.
- This lock doc and the policy doc are derived interpretive layers and must not weaken or
  contradict the JSON contract surface.

## Architectural Positioning

This bundle governs a different axis from the V33/V34 pipeline-contract family.

- V33/V34 contracts govern deterministic harness stages and trust/distribution lanes.
- This draft governs role authority, write jurisdiction, handoff trust, and acceptance
  boundaries across ADEU-managed multi-agent execution.

Current enforcement status:

- design-time contract with post-hoc reconciliation only;
- no runtime enforcement module in the current repo hard-enforces these rules yet.

## Decision Basis

- Current Codex already provides:
  - explicit session/turn context;
  - runtime policy inheritance across spawned agents;
  - real collaboration tools (`spawn_agent`, `send_input`, `wait`, `close_agent`);
  - a broad implementation tool surface.
- Current Codex does not hard-enforce:
  - single-writer discipline;
  - strong role authority separation;
  - ADEU-style acceptance and closeout governance.
- Therefore the safe baseline is:
  - ADEU remains the control plane;
  - Codex provides the execution plane;
  - exactly one implementation writer exists by default;
  - all support roles remain non-authoritative unless explicitly re-roled.

## Global Locks

- Governance authority remains non-delegable and belongs to `main_orchestrator`.
- Authority tiers are frozen:
  - tier 1: `main_orchestrator`
  - tier 2: `builder`
  - tier 3: `explorer`, `validator`, `docs_helper`
- Tier 3 roles are differentiated by function but remain peer roles within one shared
  non-authoritative support tier unless explicitly re-roled.
- Single-writer default remains frozen:
  - exactly one authoritative implementation write lease is active by default.
- Support roles remain non-authoritative by default:
  - `explorer`
  - `validator`
  - `docs_helper`
- No role may self-upgrade authority level.
- No advisory or scratch artifact may become authoritative without explicit
  `main_orchestrator` acceptance.
- Executing an advisory or scratch artifact consumes the authority of the executor, not the
  author.
- Worker-reported handoff fields remain non-authoritative until reconciled by
  `main_orchestrator`.
- Acceptance, merge readiness, and closeout readiness remain exclusive to
  `main_orchestrator`.

## Role Families

This draft recognizes five role families only:

1. `main_orchestrator`
2. `builder`
3. `explorer`
4. `validator`
5. `docs_helper`

Out of scope:

- symmetric multi-writer execution;
- worker self-promotion into authoritative roles;
- support-role ownership of governance artifacts;
- automated acceptance or closeout.

## Machine-Checkable Core Contract

```json
{
  "schema": "multi_role_execution_lock@1",
  "authority_surface": {
    "governance_authority_owner": "main_orchestrator",
    "acceptance_authority_non_delegable": true,
    "single_writer_default": true,
    "support_roles_non_authoritative": true
  },
  "artifact_class_contract": {
    "classes": [
      "authoritative",
      "advisory",
      "scratch"
    ],
    "promotion_policy": "explicit_main_orchestrator_acceptance_required"
  },
  "cross_role_execution_contract": {
    "execution_consumes_executor_authority": true,
    "support_role_proxy_authority_forbidden": true,
    "builder_execution_of_support_artifact_binds_to_builder_write_lease": true
  },
  "authoritative_surface_contract": {
    "surfaces": [
      "implementation",
      "governance"
    ],
    "builder_authoritative_surface": "implementation",
    "main_orchestrator_authoritative_surface": "governance"
  },
  "write_lease_contract": {
    "exclusive_builder_write_lease_required": true,
    "lease_scope_bound_required": true,
    "lease_transfer_policy": "explicit_main_orchestrator_only",
    "support_role_self_upgrade_forbidden": true
  },
  "role_transition_contract": {
    "explicit_transition_required": true,
    "required_fields": [
      "from_role",
      "to_role",
      "authority_level_before",
      "authority_level_after",
      "scope_owned",
      "reason",
      "effective_time",
      "granted_by"
    ]
  },
  "handoff_contract": {
    "schema": "role_handoff_envelope@1",
    "self_report_trust_policy": "non_authoritative_until_reconciled_by_main_orchestrator",
    "required_fields": [
      "role",
      "authority_level",
      "authority_domain",
      "artifact_class",
      "artifact_surface",
      "repo_root",
      "branch_or_head",
      "scope_owned",
      "scope_remaining",
      "files_changed",
      "commands_run",
      "artifacts_produced",
      "evidence_refs",
      "status",
      "blocking_state",
      "blockers",
      "open_risks",
      "escalation_reason",
      "recommended_next_action"
    ]
  },
  "handoff_reconciliation_contract": {
    "required": true,
    "performed_by": "main_orchestrator",
    "minimum_checks": [
      "recompute_effective_files_changed_from_observed_repo_state",
      "compare_claimed_scope_owned_to_observed_mutation_surface",
      "verify_evidence_refs_resolve_to_actual_outputs",
      "reject_lease_scope_sufficiency_claims_based_on_self_report_alone"
    ]
  }
}
```

## Role Constraints

### `main_orchestrator`

- may interpret governance state;
- may issue, revoke, or transfer write lease;
- may accept or reject evidence;
- may update ADEU governance artifacts.
- is the only role with authoritative governance surface by default.

Fail-closed conditions:

- governance authority delegated to another role;
- closeout or acceptance language accepted from a support role as authoritative.

### `builder`

- holds the exclusive write lease for assigned implementation scope only;
- may mutate authoritative implementation artifacts inside scope;
- may not mutate ADEU governance artifacts.
- is the only role with authoritative implementation surface by default.
- if the builder executes a support-role advisory or scratch artifact, all resulting mutations
  are attributed to the builder's write lease.

Fail-closed conditions:

- builder mutates outside leased scope;
- second authoritative implementation writer appears without explicit lease transition;
- builder claims acceptance or closure.

### `explorer`

- may emit advisory reports only;
- may not mutate authoritative implementation artifacts by default.

Fail-closed conditions:

- explorer output treated as authoritative implementation change;
- explorer self-upgrades into write authority.

### `validator`

- may emit evidence reports only;
- may report pass/fail/gaps;
- may not decide sufficiency for acceptance.

Fail-closed conditions:

- validator output treated as acceptance authority;
- validator silently fixes authoritative implementation artifacts without re-role.

### `docs_helper`

- may emit non-authoritative repo-local doc drafts only;
- may not mutate ADEU governance artifacts by default.

Fail-closed conditions:

- docs helper output treated as authoritative closeout or acceptance language;
- docs helper mutates authoritative implementation or governance artifacts without re-role.

## Failure Conditions

The following conditions are invalid and fail closed:

- `governance_authority_transferred_without_explicit_transition`
- `multiple_authoritative_writers_active_without_explicit_authorization`
- `support_role_output_promoted_without_explicit_acceptance`
- `role_self_upgrade_accepted`
- `write_lease_scope_drift_accepted`
- `builder_acceptance_claim_accepted`
- `validator_acceptance_claim_accepted`
- `explorer_authoritative_change_accepted`
- `docs_helper_governance_mutation_accepted`
- `handoff_envelope_missing_required_fields`
- `blocking_state_invalid_or_missing`
- `escalation_reason_missing_or_non_empty_policy_violated`
- `artifact_class_misclassified_and_accepted`
- `artifact_surface_misclassified_and_accepted`
- `support_role_proxy_authority_gained_via_artifact_execution`
- `self_reported_handoff_accepted_without_reconciliation`
- `lease_scope_violation_hidden_by_self_report`

## Validation Expectations

If this model is later promoted into operational enforcement, the minimum proof surface is:

1. Handoff validation
   - reject worker outputs missing required handoff fields.
   - treat handoff fields as self-reported claims until reconciled.
   - require `escalation_reason` to be always present, with empty string when no escalation
     exists and non-empty explanation when escalation exists.
2. Lease validation
   - reject concurrent authoritative writers in the default topology.
   - attribute executed support-role artifacts to the executor's authority surface.
3. Role-transition validation
   - reject write-authority transfer without explicit transition record.
4. Artifact-class validation
   - reject advisory or scratch artifacts promoted without explicit acceptance.
5. Acceptance-boundary validation
   - reject any non-`main_orchestrator` acceptance or closeout claim as authoritative.
6. Reconciliation validation
   - reject lease-scope sufficiency claims not backed by observed repo diff or equivalent
     state witness.

## Suggested Testable Invariants

- exactly one `builder` write lease is active by default;
- all support-role handoffs carry `authority_level`, `authority_domain`, `artifact_class`,
  `artifact_surface`, and `blocking_state`;
- no support role may write authoritative implementation artifacts without a recorded role
  transition;
- no support-role output may be used as acceptance authority;
- governance artifacts remain owned by `main_orchestrator`.

## Recommended Promotion Path

If this draft becomes active later:

1. formalize the JSON contract as a canonical artifact;
2. enforce handoff-envelope validation at orchestration boundaries;
3. record write-lease and role-transition state explicitly;
4. keep acceptance and closeout adjudication in ADEU, not in worker runtime.

## Bottom Line

This draft encodes one operational principle:

- Codex may execute through multiple roles, but ADEU remains the sole governance authority,
  and only one scoped authoritative implementation writer exists by default.
