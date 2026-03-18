# Draft Next Arc Options v12

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v11.md`.

This draft proposes the next family after the closed `V37` recursive-compilation
baseline: make the repo's orchestration layer itself legible in ADEU/UDEO terms
through typed payload normalization, brokered execution plans, and recursive-
honesty checks that can be consumed by the existing URM runtime.

## Baseline

- `V37` already established typed intent, module catalog, sequence law,
  executable reference loop, diagnostics, conformance, and control-update
  export on native repo terrain.
- Historical continuity:
  previous `vNext+70` planning used the directive
  `select `V37-E` as the next default candidate`,
  and that target is now fully closed on `main`.
- The repo already has:
  - ADEU/UDEO dimensional vocabulary in typed artifacts;
  - URM runtime delegation, policy, and topology surfaces;
  - docs-first slice workflow and deterministic gates.

## Gap

The missing layer is not raw agent execution. The missing layer is a typed
translation from a high-level ADEU/UDEO source artifact into:

- a normalized `adeu_brokered_reflexive_payload@1`;
- a compiled `adeu_brokered_reflexive_execution_plan@1`;
- explicit source-doc provenance carried through the typed artifacts;
- an active route order for the declared domain;
- brokered session packets with explicit truth conditions and budgets;
- machine-checkable delegation-depth limits instead of prose-only budget claims;
- sentinel guardrails around utility capture and epistemic abuse;
- recursive-honesty self-audit requirements;
- a ladder from philosophical payload to concrete implementation and review.

## Recommended Family

- Family name: `V38`
- Family theme: brokered reflexive execution
- First path: `V38-A`
- Default path selection:
  select `V38-A` as the next default candidate

## Recommended First Path (`V38-A`)

Implement a bounded, repo-native substrate that turns the source artifact
`docs/DRAFT_MASTER_EXECUTABLE_PAYLOAD_v0.md` into:

- `adeu_brokered_reflexive_payload@1`
- `adeu_brokered_reflexive_execution_plan@1`

and exposes the compiled plan through:

- primary execution surface: `adeu.compile_brokered_reflexive_execution`
- supporting route: `POST /urm/reflex/compile`

## Why This Path

- It uses the runtime and governance substrate already released instead of
  inventing a parallel orchestration system.
- It keeps the philosophical payload as a first-class source artifact.
- It gives the repo a typed way to express adversarial review, code review,
  implementation budgeting, recursive-honesty obligations, and a non-authority
  boundary in one deterministic plan family.
- It makes the current experiment native to ADEU Studio rather than remaining a
  one-off terminal ritual.

## First-Slice Boundary

`V38-A` should stay bounded to:

- new typed payload/plan schemas and deterministic compilation;
- one accepted reference payload fixture and one accepted compiled plan fixture
  derived from the current master executable payload doc;
- ADEU domain-tool exposure for plan compilation plus one thin policy-gated
  direct route;
- policy/allowlist registration for the new advisory compile surface;
- test coverage and docs updates needed to treat the experiment as released
  substrate.

It should not attempt a full autonomous planning operating system, generalized
user-modeling engine, open-ended utility rewriting logic, or a second parallel
`reflexive_governance` family.
