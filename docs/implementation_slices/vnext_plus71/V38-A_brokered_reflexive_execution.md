# V38-A Brokered Reflexive Execution

Status: implementation ladder for `vNext+71`.

## Source

- Source artifact: `docs/DRAFT_MASTER_EXECUTABLE_PAYLOAD_v0.md`
- Locked continuation: `docs/LOCKED_CONTINUATION_vNEXT_PLUS71.md`
- Stop gate: `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS71.md`

## Ladder

1. Source payload doc
   - authoritative soft input only
   - no direct runtime execution from markdown
2. Normalized payload fixture
   - schema: `adeu_brokered_reflexive_payload@1`
   - explicit source-doc ref/hash, domain class, approved roles, sentinel doctrine, recursive-honesty refusal law
3. Compiled execution plan
   - schema: `adeu_brokered_reflexive_execution_plan@1`
   - deterministic route order, execution ladder, session packets, acceptance-boundary refs
   - typed `max_delegation_depth` plus delegated session depth limits
4. Brokered delegated phases
   - `orchestrator` -> `gpt-5.4` at `xhigh`
   - `explorer` -> `gpt-5.4-mini` at `xhigh`
   - `adversarial_reviewer` -> `gpt-5.4` at `xhigh`
   - `implementer` -> `gpt-5.3-codex` at `xhigh`
   - `code_reviewer` -> `gpt-5.4` at `xhigh`
   - `gatekeeper` -> `gpt-5.4-mini` at `xhigh`
5. Harness exposure
   - primary tool: `adeu.compile_brokered_reflexive_execution`
   - supporting route: policy-gated `POST /urm/reflex/compile`
6. Policy surfaces
   - capability lattice
   - packaged lattice mirror
   - runtime role allowlist
   - Copilot tool allowlist
7. Verification
   - core schema/export tests
   - committed fixture replay
   - API/URM integration tests
   - `make check`

## Non-Goals

- no generalized autonomous execution system
- no runtime parsing of raw philosophical markdown
- no authority to mutate repo state from the compiled plan
- no parallel `reflexive_governance` family in this slice
