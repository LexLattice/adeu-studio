# Locked Continuation vNext+71

Status: `V38-A` implementation contract.

## V71 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v38a_brokered_reflexive_execution_contract@1",
  "target_arc": "vNext+71",
  "target_path": "V38-A",
  "target_scope": "brokered_reflexive_execution",
  "advisory_only": true
}
```

## Slice

- Arc label: `vNext+71`
- Family label: `V38-A`
- Scope label: brokered reflexive execution payload, compiled plan, and harness exposure

## Objective

Normalize the current ADEU/UDEO master executable payload into a bounded typed
payload and compile it into a deterministic brokered execution plan that the
repo's existing runtime can consume without hidden prompt-only control logic.

## Required Deliverables

1. New typed ADEU core artifacts:
   - `adeu_brokered_reflexive_payload@1`
   - `adeu_brokered_reflexive_execution_plan@1`
   - explicit `source_doc_ref` and `source_doc_sha256` provenance fields
2. Deterministic builders that:
   - select the active inspection order for the declared domain class;
   - derive a hierarchical execution ladder;
   - derive sentinel guardrails and recursive-honesty checks;
   - carry `max_delegation_depth` into the compiled plan and delegated session limits;
   - materialize bounded session packets for:
     - orchestrator,
     - explorer,
     - adversarial review,
     - implementation,
     - code review,
     - gate verification.
3. Harness exposure for:
   - `adeu.compile_brokered_reflexive_execution`
   - policy-gated `POST /urm/reflex/compile`
4. Committed reference fixtures derived from
   `docs/DRAFT_MASTER_EXECUTABLE_PAYLOAD_v0.md`:
   - normalized payload fixture
   - compiled execution-plan fixture
5. Repo-local operator guidance for this experiment's sub-agent model policy.

## Hard Constraints

- No hidden prompt-only route order may substitute for the typed payload/plan.
- No session packet may omit:
  - truth condition,
  - budget directive,
  - allowed evidence scope,
  - forbidden moves,
  - non-authority statement,
  - recommended model,
  - reasoning effort.
- No parallel `adeu_master_executable_payload@1` /
  `adeu_reflexive_governance_packet@1` /
  `adeu_subagent_contract_bundle@1` family is authorized in this slice.
- No raw markdown payload may be executed directly at runtime;
  `docs/DRAFT_MASTER_EXECUTABLE_PAYLOAD_v0.md` must first be normalized into the
  typed payload fixture.
- The normalized payload and compiled plan must carry source-doc provenance
  sufficient to bind the committed fixtures back to the source artifact.
- Recommended sub-agent models must stay within:
  - `gpt-5.4`
  - `gpt-5.3-codex`
  - `gpt-5.4-mini`
- Recommended reasoning effort must remain `xhigh`.
- The active domain class for the committed reference fixture must be
  `soft_reflexive`.
- The committed plan must expose the accepted delegation-depth budget as typed
  plan/session fields.
- The compiled plan must remain advisory-only in the first family.
- The repo must continue to treat hard gates, committed artifacts, and emitted
  evidence as authoritative over prose.

## PR Shape

- Single integrated PR.

Rationale:

- the new typed payload, compiled plan, tool exposure, policy registration,
  fixture, and tests are tightly coupled and would be hard to review
  independently without temporary contract drift.
