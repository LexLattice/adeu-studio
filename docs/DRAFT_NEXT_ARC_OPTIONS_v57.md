# Draft Next Arc Options v57

Status: planning draft after the closed `V68` family and the `V69` preflight
dogfood test.

Authority layer: planning.

This draft selects the next planning pressure only. It does not authorize
implementation, schema release, recursive candidate adoption, adversarial review
settlement, ratification, integration, product projection, commit / merge /
release authority, or dispatch widening by itself.

The companion `V69-A` / `V69-B` / `V69-C` implementation specs are support inputs
to future slice locks. They are not admitted implementation authority until a
canonical `vNext+191` starter bundle selects a concrete active slice.

## Current Frontier

- `V67` is closed on `main`.
- `V68` is closed on `main` as the ARC series cartography family.
- `vNext+188` / `V68-A` shipped cartography schemas, models, validators, schema
  exports, and reference / reject fixtures.
- `vNext+189` / `V68-B` shipped deterministic cartography derivation-manifest and
  gap-scan support.
- `vNext+190` / `V68-C` shipped tool-run evidence, tool-applicability hardening,
  and deliberate coordinate-posture support.
- The `V69` preflight dogfood test passed against the shipped `V68` surfaces and
  identified candidate intake as the next missing typed layer:
  - `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.json`
- GPTPro review over this planning bundle is captured as support-layer shaping
  evidence:
  - `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECURSIVE_CANDIDATE_INTAKE_V69_PLANNING_v0.md`

## Next Planning Question

Now that `V68` can map ARC-family topology, source status, tool applicability, and
coordinate posture without authorizing future families, should the next family be
`V69` recursive candidate intake: a typed admission layer for internally generated
conceptual candidates, operator-turn candidates, model-output candidates, review
feedback, support docs, and external artifacts?

## Recommended Next Pressure

- family candidate: `V69`
- proposed family name:
  - `V69: recursive candidate intake, operator-ingress binding, candidate
    source-status, and non-adoption guardrails`
- recommended planning posture:
  - treat `V69` as the immediate review target, not a pre-authorized lock
  - bind candidate intake records to explicit sources, origin classes, ODEU lanes,
    admissible roles, forbidden roles, immediate review surfaces, and eventual
    family hints
  - include internally generated ADEU candidates caused by prior reasoning loops,
    not only external papers, repos, or operator prompts
  - keep operator ingress narrow: typed binding of a human/operator turn into a
    candidate record, not a live turn compiler, standing operator profile, runtime
    permission surface, or hidden candidate invention layer
  - require a non-adoption guardrail for every admitted candidate
  - represent missing or unavailable sources as source rows with absence posture,
    never as source-free candidate rows

## Why `V69` Now

`V68` proved that the repo can describe where candidate pressure comes from and
what it must not become. It cannot, and should not, decide the candidate-intake
schema itself.

The `V69` preflight classified six candidate inputs that are already present in the
repo workflow:

- internal conceptual-diff report candidate;
- internal conceptual-diff schema support candidate;
- typed-adjudication product wedge candidate;
- self-evidencing workflow-type emergence candidate;
- `V69` planning-family candidate;
- `V68` substrate-as-evidence candidate.

Those candidates are real enough to track, but not authoritative enough to adopt.
That is precisely the missing `V69` layer.

## Proposed Family Slices

### `V69-A`: Candidate Intake Schema Backbone

Create the first bounded schema/model/validator surface for candidate intake:

- candidate identity;
- source binding;
- source authority layer;
- source presence and integration posture;
- origin class;
- primary ODEU lane and multi-lane ODEU pressure;
- admissible role;
- forbidden role;
- required next review surface;
- eventual family hint;
- non-adoption guardrail.

`V69-A` should use a hand-curated reference fixture seeded from the `V69` preflight
dogfood candidates and negative controls. It should not derive candidates
automatically yet.

### `V69-B`: Deterministic Candidate Derivation And Gap Scan

Add deterministic derivation support over concrete repo sources:

- observed input manifest;
- candidate derivation rows;
- duplicate / equivalence posture;
- missing expected candidate support artifacts;
- stale source references;
- ambiguous origin or authority layer;
- gap severity and recommended follow-up surface.

`V69-B` should make candidate discovery reproducible without granting adoption,
evidence classification, ratification, or implementation authority.

### `V69-C`: Operator-Ingress And Recursive-Residue Hardening

Harden the recursive workflow boundary:

- bind operator turns to candidate records only through explicit source refs;
- represent internally generated reasoning residue as candidate pressure;
- record self-evidencing workflow-type emergence as intake evidence, not
  self-validation;
- prepare a pre-`V70` handoff surface for candidates that need evidence or
  adversarial review.

`V69-C` should close the family by proving that candidate intake can handle
operator-originated and recursively generated candidates without turning transcript,
model output, support docs, or product projection into authority.

## Non-Selection

This draft does not select:

- `V70` evidence classification or adversarial review settlement;
- `V71` ratification;
- `V72` contained integration or commit/release posture;
- `V73` outcome review;
- `V74` operator/product projection;
- `V75` dispatch or multi-worker orchestration;
- `V43` external-world contest participation.

Those remain mapped future families or conditional branches until their own
planning and lock surfaces select them.

## Inputs For Review

Primary support inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v56.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.json`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECURSIVE_CANDIDATE_INTAKE_V69_PLANNING_v0.md`
- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`
- `docs/ARCHITECTURE_ADEU_RECURSIVE_CANDIDATE_INTAKE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69C_IMPLEMENTATION_MAPPING_v0.md`

## Recommended Next Drafting Move

Send this planning bundle for joint review. If accepted, select `V69-A` as the next default candidate and draft the canonical
`vNext+191` starter bundle for `V69-A` only:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS191.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS191.md`
- `docs/ASSESSMENT_vNEXT_PLUS191_EDGES.md`

The `vNext+191` lock should select schema / validator / fixture work only. It
should not select `V69-B`, `V69-C`, `V70`, or any downstream adoption workflow.
