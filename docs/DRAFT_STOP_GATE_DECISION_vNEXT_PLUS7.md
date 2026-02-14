# Draft Stop-Gate Decision (Post vNext+7)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS7.md`

Status: draft decision note.

## Decision Guardrail (Frozen)

- This draft cannot pre-commit `vNext+8` implementation scope before all `vNext+7` thresholds are measured and evidenced.
- Any `vNext+8` recommendation in this document is non-binding until `all_passed = true` for the `vNext+7` exit criteria.

## Evidence Source

- CI workflow: `ci` on `main`
- Run ID: `22019921107`
- Head SHA: `78cfaa76921ded83fd55f8112fbd30af4950a302`
- CI result timestamp window: merge on February 14, 2026 (UTC)
- Deterministic stop-gate artifact outputs (reproducible):
  - JSON: `artifacts/stop_gate/metrics.json`
  - Markdown: `artifacts/stop_gate/report.md`
  - build command:
    - `.venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --out-json artifacts/stop_gate/metrics.json --out-md artifacts/stop_gate/report.md`
- Arc diff evidence (mechanically reproducible):
  - commit range: `c4efa68..78cfaa7`
  - diff command:
    - `git diff --name-status c4efa68..78cfaa7`
- Key artifacts:
  - P1A instruction-kernel policy thin slice + lemma compile boundary:
    - `packages/urm_runtime/src/urm_runtime/instruction_policy.py`
    - `apps/api/tests/test_urm_instruction_policy.py`
    - `apps/api/tests/test_urm_policy_tools.py`
  - P1B policy lineage + lint/conformance hardening:
    - `spec/policy_lineage.schema.json`
    - `packages/urm_runtime/src/urm_runtime/policy_tools.py`
    - `apps/api/tests/test_urm_policy_tools.py`
    - `apps/api/tests/test_urm_events_tools.py`
  - P2A proof evidence packet + lifecycle hardening:
    - `spec/proof_evidence.schema.json`
    - `packages/adeu_kernel/src/adeu_kernel/proof_evidence.py`
    - `packages/adeu_kernel/tests/test_proof_evidence_packet.py`
    - `apps/api/tests/test_proof_evidence_packet_schema.py`
    - `apps/api/tests/test_artifact_trust_labels.py`
  - P2B replay metrics + stop-gate hardening:
    - `apps/api/fixtures/stop_gate/vnext_plus7_manifest.json`
    - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
    - `apps/api/scripts/build_stop_gate_metrics.py`
    - `apps/api/tests/test_urm_stop_gate_tools.py`
  - Merge PRs:
    - `#108` (P1A), `#109` (P1B), `#110` (P2A), `#111` (P2B)

## Exit-Criteria Check (vNext+7)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| P1A-P2B merged with green CI | required | `pass` | CI run `22019921107` (`python=success`, `web=success`) |
| policy lint/reload determinism | `100%` | `pass` | deterministic policy fixtures in `apps/api/tests/test_urm_instruction_policy.py` + `apps/api/tests/test_urm_policy_tools.py`; stop-gate metric `policy_lint_determinism_pct = 100.0` |
| proof evidence replay determinism | `100%` | `pass` | `test_proof_evidence_packet_is_deterministic_for_identical_inputs`; stop-gate metric `proof_replay_determinism_pct = 100.0` |
| policy/proof packet hash stability | `100%` | `pass` | `test_proof_evidence_hash_excludes_proof_id_and_created_at`; stop-gate metric `policy_proof_packet_hash_stability_pct = 100.0` |
| `vNext+7 -> vNext+8` thresholds all pass | required | `pass` | `artifacts/stop_gate/metrics.json` has all three frozen `vNext+7` metrics at `100.0` and `all_passed = true` |
| no solver semantics contract delta | required | `pass` | Arc diff `c4efa68..78cfaa7` is policy/proof operational hardening + reporting/metrics; no intentional solver contract drift |
| no trust-lane regression | required | `pass` | proof trust-promotion guardrails validated in `apps/api/tests/test_artifact_trust_labels.py` |
| all existing `vNext+6` determinism metrics remain at threshold | required | `pass` | `validator_packet_determinism_pct`, `witness_reconstruction_determinism_pct`, `semantics_diagnostics_determinism_pct` remain `100.0` in stop-gate metrics artifact |

Summary:

- `valid = true`
- `all_passed = true`
- `issues = []`

## P-Track Result Summary

- P1A instruction-kernel policy thin slice integration:
  - status: `done`
  - evidence: merged in `#108`; deterministic lemma compilation + identity fixtures in `apps/api/tests/test_urm_instruction_policy.py`
- P1B policy lineage artifact + lint/conformance hardening:
  - status: `done`
  - evidence: merged in `#109`; `policy_lineage@1` schema + deterministic lint mapping/events fixtures in `apps/api/tests/test_urm_policy_tools.py` and `apps/api/tests/test_urm_events_tools.py`
- P2A proof evidence packet + lifecycle hardening:
  - status: `done`
  - evidence: merged in `#110`; `proof_evidence@1` schema/materialization + trust/hash fixtures in kernel/API tests
- P2B replay metrics + stop-gate hardening:
  - status: `done`
  - evidence: merged in `#111`; manifest-driven `vNext+7` metrics fixtures in `apps/api/tests/test_urm_stop_gate_tools.py`

## Open Issues / Residual Risks

- none blocking `vNext+7` closeout.
- residual process risk:
  - severity: low
  - owner: governance/runtime maintainers
  - mitigation: keep `vNext+8` scope contract-first (API/CLI determinism first, UI thin slice second) with frozen schema/hash locks.

## Recommendation (`vNext+8` Gate)

- gate decision:
  - `GO_VNEXT_PLUS8_DRAFT`
- rationale:
  - all `vNext+7` frozen scope items (P1A-P2B) are merged.
  - merge CI is green on `main` for the closeout commit.
  - deterministic stop-gate thresholds pass with `all_passed = true`.
- explicit guard:
  - if `all_passed != true`, decision is `HOLD_VNEXT_PLUS8`.
  - no implementation scope for `vNext+8` is authorized from this note while held.

## Suggested Next Artifacts

1. Refresh `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` to a post-`vNext+7` baseline.
2. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS8.md` for Path 3 thin-slice freeze candidate.
3. Start `vNext+8` PR1 once the `vNext+8` lock is approved.
