# Assessment vNext+25 Edges (Opus Pass)

This note records disposition of the Opus assessment against:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS25.md`

Status: assessment snapshot (February 26, 2026 UTC).

## Summary

- Overall assessment direction is valid: v25 (`S3b`) is the first bounded proposer activation after the v19-v24 read-only arc family.
- Most high-severity concerns are now explicitly locked in the v25 draft.
- Remaining medium-risk expansions are deferred to cleanups to preserve thin-slice scope.

## Accepted In v25 Draft Lock

1. Hard S9 precondition before implementation (`provider parity` baseline metrics at `100.0`), with explicit block-and-remediate behavior.
2. Explicit proposer endpoint/idempotency boundaries (`POST /urm/core-ir/propose`, `client_request_id`, deterministic fail-closed rules).
3. Composite idempotency identity semantics (`surface_id`, `client_request_id`, `provider`) to prevent cross-provider replay ambiguity.
4. Frozen proposer packet contract including:
   - cross-family refs (`core_ir_artifact_ref`, `lane_artifact_refs`, `integrity_artifact_refs`)
   - deterministic `not_produced_reasons`
   - structural `summary` invariants.
5. Frozen parity model as contract-level parity (not semantic equality), with explicit normalized fingerprint projection and excluded volatile/free-text fields.
6. Frozen multi-provider fixture coverage requirements (`mock|openai|codex`) and deterministic replay semantics.
7. Frozen read-only proposer mutation boundary (no canonical artifact writes in this arc).

## Deferred (Intentional) To Follow-up Cleanups

1. Stronger topology/semantic parity checks beyond current contract-level fingerprint.
2. Surface-id naming harmonization review (`adeu_core_ir.propose` vs flatter proposer token families).
3. Optional provider telemetry enrichment (`latency/token` observability) in proposer envelopes/captures.

These are deferred to keep v25 as a strict thin slice and avoid broadening scope beyond locked `Y1`-`Y4`.

