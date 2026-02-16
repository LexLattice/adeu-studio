# Locked Continuation vNext+12 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS11.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS11.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- vNext+11 (`C1`-`C4`) merged on `main` with green CI and stop-gate `all_passed = true`.
- Practical real-paper run surfaced two deterministic quality gaps:
  - raw-PDF abstract candidate extraction selecting metadata/date lines
  - worker parse quality marked degraded by known provider log noise even when output is valid
- This arc is reserved for practical paper-pipeline realism hardening only:
  - raw extraction robustness first
  - deterministic flow selection/reporting second
  - worker log normalization quality signaling third

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS10.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS11.md` remain authoritative for policy/proof/explain/runtime/semantic-depth/conformance semantics.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- Hidden randomness is forbidden in deterministic/replay mode:
  - UUID/random ids must be explicit input, deterministic derivation, or used only behind persisted-artifact determinism boundaries.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)

## Arc Scope (Draft Lock)

This arc proposes only practical paper-pipeline hardening thin slice:

1. `P1` Raw-PDF abstract extraction robustness in `urm_domain_paper`
2. `P2` Deterministic paper flow selection summary contract (`paper_pipeline_summary@1`)
3. `P3` Worker provider-log normalization quality signaling hardening
4. `P4` Deterministic fixture/test closeout for practical paper runs

## P1) Raw-PDF Abstract Extraction Robustness

### Goal

Improve deterministic abstract candidate extraction on real PDF text without introducing semantic/LLM gating.

### Scope

- Harden `paper.extract_abstract_candidate` in `packages/urm_domain_paper/src/urm_domain_paper/adapters.py`.
- Prefer explicit abstract-section extraction when `Abstract` markers are present.
- Add deterministic structural candidate heuristics for fallback paragraph selection.

### Locks

- Extraction remains deterministic and closed-world over provided input text only.
- Structural-only lock is frozen:
  - no LLM/semantic classifier in extraction gating paths.
- Date/header guard lock is frozen:
  - date-only metadata lines may not be selected when a structurally valid abstract-like paragraph exists.
- Extract output additive lock is frozen:
  - additive fields allowed:
    - `sentence_count`
    - `extract_strategy`
  - existing fields remain authoritative:
    - `abstract_text`
    - `word_count`
    - `candidate_hash`

### Acceptance

- Real-paper raw PDF fixtures no longer select metadata/date-only abstract candidates when abstract body is present.
- Existing deterministic extraction fixtures remain stable.

## P2) Deterministic Paper Flow Selection Summary

### Goal

Make pipeline winner selection explicit and reproducible when multiple extraction flows exist.

### Scope

- Add deterministic paper pipeline runner:
  - `apps/api/scripts/run_paper_pipeline.py`
- Add deterministic selection/cleaning helpers:
  - `apps/api/src/adeu_api/paper_pipeline.py`
- Emit explicit summary selection fields.

### Locks

- Summary envelope lock is frozen:
  - `schema = "paper_pipeline_summary@1"`
  - `flows`
  - `selected_flow`
  - `selected_candidate_hash`
  - `selected_artifact_id`
  - `selection_reason`
  - `fallback_used`
  - `parse_degraded_raw`
  - `final_parse_quality`
  - `selected_word_count`
- Selection ranking lock is frozen:
  - deterministic rank key:
    - `(passes, word_count, candidate_hash, label)` ascending with max-selected.
- Selection reasoning lock is frozen:
  - deterministic, ordered, machine-readable reason strings.

### Acceptance

- Re-running the pipeline with identical inputs emits byte-identical summary JSON.
- Winner selection is explicit and stable under replay.

## P3) Worker Provider-Log Normalization

### Goal

Prevent known provider log noise from falsely degrading parse-quality signal.

### Scope

- Harden worker line normalization:
  - `packages/urm_runtime/src/urm_runtime/normalization.py`
- Classify known rollout-state stderr noise as provider log events, not parse errors.

### Locks

- Known-log classification lock is frozen:
  - recognized `codex_core::rollout::list` missing-path lines normalize to:
    - `event = "PROVIDER_LOG"`
    - `event_kind = "provider_log"`
    - `provider_log_kind = "rollout_state_db_missing_path"`
- Parse-degraded signal lock is frozen:
  - `parse_degraded` remains true only when unclassified parse errors occur.
- Raw-line preservation lock is frozen:
  - original line remains persisted in `raw_line`.

### Acceptance

- Worker runs with only known rollout log noise and valid JSON events no longer set `parse_degraded = true`.
- Existing malformed-line fixtures still set `parse_degraded = true`.

## P4) Deterministic Fixture/Test Closeout

### Goal

Freeze reproducible evidence for practical paper pipeline behavior under the above locks.

### Scope

- Add/refresh tests for:
  - paper extraction section/date-header behavior
  - flow-selection determinism
  - worker provider-log normalization behavior

### Locks

- Test inputs remain persisted fixture-based and deterministic.
- No live network dependency in deterministic test paths.

### Acceptance

- Targeted suites are green:
  - `apps/api/tests/test_urm_domain_tools.py`
  - `apps/api/tests/test_urm_worker_runner.py`
  - `apps/api/tests/test_paper_pipeline.py`
- Practical real-paper run demonstrates:
  - raw flow viable candidate extraction
  - explicit selected-flow reporting
  - worker parse-quality signal without false degradation from known rollout log noise

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- No new error-code family is required by default in this arc unless additional fail-closed behavior is introduced.

## Commit Plan (Small Green Commits)

1. `paper: harden abstract extraction heuristics for raw-pdf metadata/date resilience`
2. `paper: add deterministic flow selection summary runner and tests`
3. `runtime: classify known rollout provider logs without parse-degraded regression`
4. `docs: add vnext+11 stop-gate decision closeout and vnext+12 draft lock`

## Exit Criteria (Draft)

- `P1`-`P4` merged with green CI.
- Raw-paper practical extraction avoids date/header false selection on locked fixture run.
- Selected flow/candidate reporting is deterministic across replay reruns.
- Known rollout provider-log noise no longer causes false `parse_degraded` in worker success runs.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing `vNext+6` through `vNext+11` determinism metrics remain at threshold.
