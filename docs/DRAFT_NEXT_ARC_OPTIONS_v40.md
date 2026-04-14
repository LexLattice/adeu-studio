# Draft Next Arc Options v40

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`, updated after the
bounded `V56` family closed on `main` through `V56-A`, `V56-B`, and `V56-C`, and after
the shipped `V56-C` harvest/calibration/migration surfaces identified exactly one
credible later hardening candidate:
the frozen `local_write` path still lacks an actually observed bounded local effect.

Authority layer: planning.

This draft does not automatically supersede the connected planning branches in
`docs/DRAFT_NEXT_ARC_OPTIONS_v26.md` through `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`.
Instead, it records one fifteenth connected candidate family:

how should ADEU own one bounded resident-agent local-effect hardening family so that
the repo can capture an actually observed local effect under the shipped `V56` live
gate without silently widening action classes, relaxing boundary law, or treating one
observed effect as immediate hardening authority?

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

Interpretive doctrine for this planning surface:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`, `deferred`, and
  `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and absence-of-authorization
  statements for this planning draft, not lock-equivalent permanent prohibitions by
  themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`.

## Baseline

- `V48-A` through `V48-E` are closed on `main` and remain the released bounded
  policy-to-taskpack and worker-enforcement bridge recorded in
  `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md`.
- `V51-A` through `V51-C` are closed on `main` and remain the released ODEU
  simulation kernel / API / bounded browser ladder recorded in
  `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md`.
- `V55-A` through `V55-C` are closed on `main` and remain the released constitutional
  coherence starter / descendant-trial hardening / governance-migration ladder
  recorded in `docs/DRAFT_NEXT_ARC_OPTIONS_v38.md`.
- `V56-A` through `V56-C` are closed on `main` and now constitute the released
  resident-agent interaction-governance starter / bounded live gate /
  harvest-calibration-migration ladder recorded in
  `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`.
- the released `V56` family now owns:
  - packet / morph IR / interaction-contract loading;
  - action proposal;
  - membrane checkpoint;
  - bounded action ticketing over:
    - `local_reversible_execute`
    - `local_write`
  - post-action conformance / harvest / governance calibration / migration decision.
- the shipped `V56-C` outputs do not select broad hardening. They specifically say:
  - `local_write` = `needs_more_evidence`
  - `local_reversible_execute` = `not_selected_for_escalation`
  - checkpoint/ticket boundary = `keep_warning_only`
  - hidden-cognition proxy boundary = `keep_warning_only`
  - the only later candidate hardening path is:
    - `local_write_post_effect_observation_path`
- `v154` is the current implementation-arc baseline on `main`.

## Gap

The repo no longer lacks:

- one released resident-agent packet / contract / checkpoint family;
- one released bounded resident-agent live gate over a narrow local subset; or
- one released advisory harvest/calibration/migration layer over those governed
  surfaces.

The repo still lacks:

- one repo-owned family that captures an actually observed bounded local effect under
  the shipped `V56` live-gate law;
- one typed surface that records pre-state, observed write set, post-state, and effect
  boundedness for a live local-write path;
- one typed conformance surface for actual local effect that does not require reopening
  the shipped `V56` dry-run/no-live-effect conformance contract;
- one designated local-effect sandbox law so actual local-write evidence can be
  collected without laundering into general repo write authority; and
- one bounded restoration / hardening path that stays downstream of `V56` rather than
  silently mutating it.

So the repo still lacks the family that would turn the `V56-C` candidate
`local_write_post_effect_observation_path` into typed evidence rather than leaving it
as a justified but still unrealized later-hardening suggestion.

## Relationship To `V48`, `V51`, `V55`, And `V56`

`V55` asks:

- how should a bounded promoted stack be checked for constitutional coherence?

`V56` asks:

- how should the resident agent's externally effective loop be governed through packet,
  contract, proposal, checkpoint, ticket, conformance, and harvest?

This new family asks:

- how should one already selected `V56` local live path produce lawful post-effect
  evidence without reopening `V56` gate law?
- how should ADEU capture actual local-write observation, boundedness, and later
  restoration evidence inside one designated local sandbox?
- how should one observed effect constrain later hardening discussion without minting
  it automatically?

So this family may constrain:

- actual bounded local-effect execution over a shipped `V56` ticket;
- effect target-root selection and path boundedness;
- post-effect observation and conformance;
- later restoration and hardening discussion over the same frozen semantics.

But it may not mint:

- new live action classes;
- reinterpretation of `local_write` or `local_reversible_execute`;
- broader repo write authority;
- delegated or external dispatch authority;
- stronger execute rollout;
- hidden-cognition governance; or
- immediate product/API rollout.

Ordering discipline for this branch:

- `V55` checks constitutional coherence of family surfaces;
- `V56` governs resident proposal / checkpoint / ticket law;
- `V57` governs actual bounded local-effect observation, restoration, and later local
  hardening evidence over one already selected `V56` live path;
- `V48` still governs delegated worker execution after any later lawful dispatch;
- `V51` may shape membrane/effect semantics, but does not own authority here.

## Recommended Family

- Family name: `V57`
- Family theme: ADEU resident-agent local-effect hardening
- Released earlier shaping inputs:
  - released `V56` resident-agent interaction-governance family
  - released `V55` constitutional coherence family
  - released `V48` worker-boundary bridge
- Connected candidate or released families not reopened or superseded here:
  - `V48`
  - `V51`
  - `V55`
  - `V56`
- Recommended architecture reference to draft next:
  - `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_FAMILY_v0.md`
- Recommended family/slice mapping reference to draft next:
  - `docs/DRAFT_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_V57_IMPLEMENTATION_MAPPING_v0.md`
- Recommended next path for this branch:
  - `V57-A`
- Recommended next concrete arc for this branch if selected:
  - `V57-A`
- Default path selection for this branch:
  - one bounded actual-effect observation starter is recommended:
    - reuse the shipped `V56-A`, `V56-B`, and `V56-C` packet / contract / proposal /
      checkpoint / ticket / conformance / harvest surfaces by default
    - keep the operative interpretation of `local_write` frozen from shipped `V56-B`
      and shipped `V56-C`
    - select `local_write` only for actual observed effect in the first slice
    - narrow that selected `local_write` path to one first safe subset only:
      - create-new writes inside the designated sandbox root
      - append-only writes inside the designated sandbox root
    - keep destructive, overwrite, rename, delete, and metadata-mutating writes out of
      the first selected subset
    - add one designated local-effect sandbox root only
    - add one bounded local-effect observation record
    - add one bounded local-effect conformance report
    - keep the new surfaces evidence-bearing only in the first slice
    - no restoration/hardening decision yet
    - no action-class widening
    - no repo-source/doc/CI/secret/dispatch writes
  - if this family is selected, select `V57-A` as the next default candidate

This family/path recommendation is branch-local to the `v40` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected planning
branches from `v26` through `v39` remain in parallel scope.

## Suggested `V57` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V57-A` | bounded post-effect observation starter | one designated local-effect sandbox, one local-effect observation record, one local-effect conformance report over the frozen `local_write` path only | recommended next path |
| `V57-B` | bounded restoration / replay hardening | one local-effect restoration record and one bounded replay/restoration path over the same frozen `local_write` semantics | later lane |
| `V57-C` | local hardening decision | one local-effect hardening register over whether the observed and restored path deserves stronger local hardening later | later lane |

These output names are planning-level candidate names, not lock-level schema
authority.

## Why This Path

- It follows the only real later-hardening candidate that `V56-C` actually surfaced.
- It avoids broadening runtime authority just because tickets now exist.
- It keeps actual live effect bounded to one designated local sandbox rather than the
  whole repo.
- It turns "needs more evidence" into one concrete evidence path rather than another
  abstract governance note.
- It preserves the correct family ordering:
  - `V56` owns boundary-crossing law;
  - `V57` owns bounded post-effect evidence and later hardening over one already
    selected live class.

## Proposed `V57-A` Scope

`V57-A` should be bounded to:

- one existing primary family package:
  - `packages/adeu_agentic_de`
- one existing thin script seam under repo operations;
- one explicit `V56-C` to `V57-A` handoff via:
  - `agentic_de_lane_drift_record@1`
- reuse of the shipped `V56-A`, `V56-B`, and `V56-C` packet / morph IR /
  interaction-contract / action-proposal / membrane-checkpoint / diagnostics /
  conformance / runtime-state / action-ticket / harvest surfaces by default;
- one selected live action class only:
  - `local_write`
- one designated local-effect sandbox root only:
  - `artifacts/agentic_de/v57/local_effect/`
- one first safe local-write subset only:
  - `create_new`
  - `append_only`
- one bounded local-effect observation surface:
  - `agentic_de_local_effect_observation_record@1`
- one bounded local-effect conformance surface:
  - `agentic_de_local_effect_conformance_report@1`
- one actual observed bounded local effect only inside the designated sandbox root;
- one explicit anti-escape sandbox law only:
  - no symlink escape
  - no parent traversal
  - no indirect alias or mount redirection
  - no write-through into authority-bearing surfaces through sandbox references
- one explicit ticket-to-effect binding law only:
  - every observed write must bind to one live ticket
  - one selected action proposal
  - one checkpoint-entitled bounded effect scope
- one explicit negative observation vocabulary only:
  - bounded effect observed
  - no effect observed
  - out-of-scope write observed
  - mismatched effect observed
  - boundedness verdict failed
- no restoration record yet;
- no hardening register yet;
- no class widening;
- no stronger execute rollout;
- no delegated or external dispatch rollout;
- no repo-source / lock-doc / CI / secret / dispatch-surface writes;
- no hidden-cognition governance claim.

## Machine-Checkable Seed Summary

```json
{
  "schema": "next_arc_option_family_summary@1",
  "artifact": "docs/DRAFT_NEXT_ARC_OPTIONS_v40.md",
  "status": "draft",
  "authority_layer": "planning",
  "family_name": "V57",
  "family_theme": "adeu_resident_agent_local_effect_hardening",
  "recommended_next_path": "V57-A",
  "depends_on_closed_v56_family": true,
  "selected_live_action_class_for_v57a": "local_write",
  "selected_live_action_class_interpretation_reused_from_v56b": true,
  "selected_local_write_first_subset_for_v57a": [
    "create_new",
    "append_only"
  ],
  "destructive_or_overwrite_write_kinds_selected_for_v57a": false,
  "designated_local_effect_sandbox_required": true,
  "sandbox_anti_escape_law_required": true,
  "ticket_to_effect_binding_required": true,
  "negative_observation_outcomes_required": true,
  "actual_local_effect_selected_for_v57a": true,
  "restoration_selected_for_v57a": false,
  "hardening_decision_selected_for_v57a": false,
  "governs_hidden_cognition": false
}
```
