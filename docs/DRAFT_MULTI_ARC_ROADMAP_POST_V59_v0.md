# Draft Multi-Arc Roadmap Post V59 v0

Status: planning roadmap after `V59` closed on `main` through `v163`, and after
support-layer review of `docs/support/v60+ plan gptpro.md`.

Authority layer: planning.

This roadmap is a concise planning-layer sequence note. It records the current best
anticipated post-`V59` family shape and likely lane ladder, but it does not freeze
slice contracts, authorize implementation by itself, or replace the canonical
family-selector docs in `docs/DRAFT_NEXT_ARC_OPTIONS_*.md`.

Interpretive doctrine for this planning surface:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`, `deferred`, and
  `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and absence-of-authorization
  statements for this roadmap, not lock-equivalent permanent prohibitions by
  themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`.

## Baseline

- `V55` through `V59` are closed on `main`.
- the repo already has a materially real governed stack:
  - constitutional coherence
  - resident-agent act governance
  - bounded local-effect evidence
  - live harness integration
  - persistent workspace continuity
- `V59` closed bounded persistent continuity for one exact exemplar path.
- `V59` did not close semantic continuation or communication governance.
- the repo also already has materially real runtime and user surfaces:
  - URM resident Codex sessions and control plane
  - web copilot
  - GPT-5.4 desktop workbench
- the strongest remaining gap is no longer continuity or effect hardening in
  isolation; it is:
  - lawful continuation / residual-intent ownership across acts
  - governed communication surfaces that do not mint authority

## Roadmap Thesis

The clean post-`V59` shape is:

1. close the semantic loop first;
2. then govern the communication membrane;
3. then branch from that semantic core into:
   - alternate transport/control surfaces, and
   - later execution widening.

So the roadmap is best read as a branching dependency cone:

- core semantic closure:
  - `V60`: continuation / residual-intent kernel
  - `V61`: governed communication surfaces + resident bridge office
- surface branch after the core:
  - `V62`: connector admission / external assistant bridge
  - `V63`: remote ODEU-governed operator UX / phone control plane
- execution-widening branch after the core:
  - `V64`: repo-bound writable-surface authority
  - `V65`: delegated export / worker reconciliation under `V48`

## Cross-Family Anti-Drift Rules

These lines are the main reasons for the sequence above:

- `V56` tickets remain `single_step_local`; do not widen them into standing
  multi-step authority.
- prior continuity state is context at most, never standing authority.
- communication access is not permission, and transcript is not native witness.
- connector or phone surfaces are transport/control only; they do not own
  communication law.
- repo-bound writable authority should stay deferred until continuation and
  communication law are first-class.
- delegated export should stay deferred until both the continuation kernel and
  communication membrane exist.

## Anticipated Family Shape

| Family | Theme | Likely lane ladder | Current posture |
|---|---|---|---|
| `V60` | continuation / residual-intent kernel | `V60-A` continuation starter; `V60-B` continuation refresh / reproposal / escalation; `V60-C` advisory continuation hardening / migration | next |
| `V61` | governed communication surfaces + resident bridge office | `V61-A` communication packet starter over existing surfaces; `V61-B` office binding / rewitness / message-promotion gate; `V61-C` advisory communication hardening | prepared, not selected |
| `V62` | connector admission / external assistant bridge | `V62-A` connector admission; `V62-B` external assistant ingress / egress bridge; `V62-C` advisory connector hardening / provenance drift | surface branch after `V60` / `V61` core |
| `V63` | remote operator UX / phone control plane | `V63-A` remote operator session starter; `V63-B` governed command/control packet bridge; `V63-C` advisory remote-operator hardening | surface branch after `V60` / `V61` core |
| `V64` | repo-bound writable-surface authority | starter / restoration / hardening ladder over one declared repo-bound work surface | execution-widening branch after `V60` / `V61` core |
| `V65` | delegated export / worker reconciliation under `V48` | export starter / worker reconciliation / advisory delegation hardening | execution-widening branch after `V60` / `V61` core |

These lane names are planning-level anticipations only. They are not lock-level schema
or deliverable commitments yet.

## Family Notes

### `V60`

`V60` should convert seed intent plus reintegration results into lawful continuation
state without executing effects directly. It should own:

- one typed, non-chat-native starter ingress artifact for seed intent in the first
  slice;
- task charterization;
- residual-intent carriage;
- loop-state identity;
- next-posture decision over bounded outputs such as:
  - continue toward a governed act
  - await authority
  - emit governed communication
  - pause blocked
- stop complete
- escalate

It should not own communication packet law, ticket law, or execution widening.

`TaskResidual` should remain a derived continuation artifact, not authored standing
task law.

### `V61`

`V61` should retrofit the existing communication surfaces so they emit and consume
typed, provenance-bearing communication packets rather than acting as semantically
open transcript pipes. It should own:

- governed ingress / egress packets;
- surface classification;
- office binding for resident Codex as bridge;
- explicit message-to-witness promotion gates

It should not mint execution authority.

Its immediate mission is to retrofit the already-real generic send/message surfaces
before any connector or remote-UX widening lands.

### `V62` And `V63`

`V62` and `V63` should consume `V61` communication law rather than invent their own.
Their trust models differ, so they should remain separate families even if they share
underlying packet shapes.

### `V64` And `V65`

`V64` and `V65` should remain explicitly later because they widen execution reach.
They should be revisited only after the repo has:

- a first-class continuation kernel;
- a first-class governed communication membrane; and
- stable transport/control surfaces over that membrane.

## Selection Status

- selected next family to detail canonically: `V60`
- prepared but not yet selected family: `V61`
- deferred but structurally anticipated surface branch: `V62`, `V63`
- explicitly later execution-widening branch: `V64`, `V65`

## Relationship To Canonical Arc Docs

This roadmap should be read together with:

- the support-layer synthesis in `docs/support/v60+ plan gptpro.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_WCPGC_CORE_AND_STRICT_V0_v0.md`
- the current family selector in `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`

Later branch-specific shaping references include:

- `docs/formal/asir/ASIRKernelConnector.md` for connector/gating formalization
- `docs/OPERATOR_REFERENCE_v0.md` for operator-surface practical constraints

The normal concretization path remains:

1. roadmap-level anticipated sequence
2. canonical next-family selector
3. family architecture / mapping docs
4. lane lock docs

So this roadmap clarifies sequence, but the actual next authoritative planning
boundary should still be set by `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`.
