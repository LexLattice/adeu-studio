# Governance Ops Deepening Evidence Report (Template)

Source lock: `docs/LOCKED_CONTINUATION_vNEXT_PLUS4.md`

Status: template.

## Report Metadata

- report_id:
- generated_at_utc:
- repo_head_sha:
- ci_workflow:
- ci_run_id:
- scope:
  - `A1` policy explain hardening
  - `A2` profile lifecycle hardening
  - `A3` incident packet hardening
  - `A4` rollout/rollback hardening
  - `A5` docs/scaffold

## Required Inputs (Versioned + Frozen)

- `policy/profiles.v1.json`
- `policy/incident_redaction_allowlist.v1.json`
- `spec/policy_profiles.v1.schema.json`
- `spec/policy_incident_redaction_allowlist.v1.schema.json`
- `spec/policy_explain.schema.json`
- `spec/incident_packet.schema.json`
- `spec/policy_registry.schema.json`
- `spec/policy_activation_log.schema.json`

## Evidence Index

| Claim ID | Artifact Path | Schema / Type | Required Fields |
|---|---|---|---|
| A1-EXPLAIN-DET | `artifacts/governance/a1_policy_explain/determinism_report.json` | `policy_explain@1` summary | `fixture_id`, `policy_hash`, `input_context_hash`, `evaluation_ts`, `json_sha256_first`, `json_sha256_second`, `json_hash_match`, `md_sha256_first`, `md_sha256_second`, `md_hash_match` |
| A1-EXPLAIN-OUT | `artifacts/governance/a1_policy_explain/fixture_<id>.policy_explain.json` | `policy_explain@1` | `schema`, `policy_hash`, `input_context_hash`, `evaluation_ts`, `evidence_refs` |
| A2-PROFILE-REPLAY | `artifacts/governance/a2_profile_lifecycle/profile_replay_report.json` | replay summary | `profile_id`, `profile_version`, `default_policy_hash`, `selected_policy_hash`, `replay_hash_match` |
| A2-PROFILE-EVENTS | `artifacts/governance/a2_profile_lifecycle/profile_events.ndjson` | `urm-events@1` stream | `event`, `stream_id`, `seq`, `detail.profile_id` |
| A3-INCIDENT-DET | `artifacts/governance/a3_incident_packet/incident_repro_report.json` | `incident_packet@1` summary | `packet_sha256_first`, `packet_sha256_second`, `packet_hash_match`, `decision_code_match`, `matched_rule_ids_match` |
| A3-INCIDENT-OUT | `artifacts/governance/a3_incident_packet/incident_packet_<id>.json` | `incident_packet@1` | `schema`, `streams`, `artifact_refs`, `decision_code`, `matched_rule_ids`, `redaction_markers` |
| A4-REGISTRY | `artifacts/governance/a4_policy_activation/policy_registry_snapshot.json` | `policy_registry@1` snapshot | `policy_hash`, `schema_id`, `policy_schema_version`, `policy_ir_version`, `semantic_policy_json`, `materialized_at` |
| A4-ACTIVATION | `artifacts/governance/a4_policy_activation/activation_log.json` | `policy_activation_log@1` | `activation_seq`, `client_request_id`, `request_payload_hash`, `profile_id`, `action`, `target_policy_hash`, `prev_policy_hash`, `activation_ts` |
| A4-IDEMPOTENCY | `artifacts/governance/a4_policy_activation/idempotency_report.json` | replay summary | `client_request_id`, `stored_payload_hash`, `incoming_payload_hash`, `replay_stable`, `restart_replay_stable` |
| A4-STREAM | `artifacts/governance/a4_policy_activation/stream_urm_policy_<profile_id>.ndjson` | `urm-events@1` stream | `event` in `{POLICY_ROLLED_OUT,POLICY_ROLLED_BACK}`, `stream_id` |
| A5-DOCS | `docs/templates/GOVERNANCE_OPS_DEEPENING_EVIDENCE_REPORT_TEMPLATE.md` | markdown | exists |
| A5-DRAFT | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS4.md` | markdown | exists |

## Exit Criteria Mapping

| Exit Criterion | Result | Evidence Reference |
|---|---|---|
| A1-A5 merged with green CI |  | CI run URL + commit SHA |
| `policy_explain@1` determinism = `100%` |  | `A1-EXPLAIN-DET` |
| profile lifecycle replay determinism = `100%` |  | `A2-PROFILE-REPLAY` |
| incident packet reproducibility >= `99%` |  | `A3-INCIDENT-DET` |
| rollout/rollback replay + idempotency = `100%` |  | `A4-IDEMPOTENCY` |
| no solver semantics delta / no trust-lane regression |  | solver/trust regression report path |
| Option B follow-on lock draft ready |  | follow-on draft path |

## A1 Evidence (Policy Explain)

- fixture set path:
- deterministic input mode:
- replay run count:
- summary:
  - json hash match rate:
  - markdown hash match rate:
- issues (`issues[]` codes + contexts):

## A2 Evidence (Profile Lifecycle)

- profile registry path: `policy/profiles.v1.json`
- replay scenario paths:
- child snapshot immutability check evidence:
- profile stream linkage evidence:
- issues (`issues[]` codes + contexts):

## A3 Evidence (Incident Packet)

- allowlist path: `policy/incident_redaction_allowlist.v1.json`
- incident fixture corpus path:
- reconstruction validation evidence:
- secret-leak guard evidence:
- issues (`issues[]` codes + contexts):

## A4 Evidence (Rollout / Rollback)

- policy registry snapshot path:
- activation log path:
- idempotency retry evidence path:
- restart replay evidence path:
- governed stream evidence path (`urm_policy:<profile_id>`):
- issues (`issues[]` codes + contexts):

## Determinism Anchors

- policy hashes:
- context hashes:
- request payload hashes:
- artifact sha256 list:

## Residual Risks

- risk:
  - owner:
  - mitigation:

## Final Gate Summary

- valid:
- all_passed:
- recommendation:
- blocked_by:
