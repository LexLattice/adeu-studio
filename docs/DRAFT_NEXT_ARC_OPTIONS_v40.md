# Draft Next Arc Options v40

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`, updated after the
bounded `V57-A` local-effect observation starter closed on `main` through `v155`, and
after the shipped `V57-A` observation/conformance surfaces captured one actually
observed bounded local effect but still left one bounded restoration/replay path
unowned:
the shipped `create_new` local-write exemplar still lacks a compensating-restore
surface inside the same sandbox and authority envelope.

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
- `V57-A` is closed on `main` and now constitutes the released bounded local-effect
  observation starter recorded in this `v40` planning branch.
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
- the shipped `V57-A` outputs now externalize:
  - one designated sandbox-root local-effect observation record
  - one designated sandbox-root local-effect conformance report
  - one actual bounded `create_new` exemplar under the frozen `local_write` class
  - explicit negative observation outcomes
- `v155` is the current implementation-arc baseline on `main`.

## Gap

The repo no longer lacks:

- one released resident-agent packet / contract / checkpoint family;
- one released bounded resident-agent live gate over a narrow local subset; or
- one released advisory harvest/calibration/migration layer over those governed
  surfaces.

The repo still lacks:

- one repo-owned slice that captures bounded restoration / compensating-restore
  evidence over the shipped `V57-A` observed local effect;
- one typed restoration surface that binds one prior observation and one prior
  conformance output to one restoration effect inside the same sandbox root;
- one bounded replay/restoration path that stays inside the same authority envelope
  rather than laundering into broader delete/overwrite repo authority; and
- one later hardening decision seam over the observed/restored path that stays
  downstream of `V56` and `V57-A` rather than silently mutating them.

So the repo still lacks the slice that would turn the shipped `V57-A` observation of
`local_write_post_effect_observation_path` into one lawful bounded restoration path
rather than leaving it as evidence with no repo-owned replay/restore follow-through.

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
  - `V57-B`
- Recommended next concrete arc for this branch if selected:
  - `V57-B`
- Default path selection for this branch:
  - one bounded restoration / replay starter is recommended:
    - reuse the shipped `V56-A`, `V56-B`, `V56-C`, and `V57-A` packet / contract /
      proposal / checkpoint / ticket / conformance / harvest / observation surfaces by
      default
    - keep the operative interpretation of `local_write` frozen from shipped `V56-B`,
      shipped `V56-C`, and shipped `V57-A`
    - define replay here narrowly:
      - bounded recomputation and re-evaluation of the restoration event against the
        prior observed-effect lineage only
      - not general re-execution of arbitrary prior live actions
    - keep the designated local-effect sandbox root from shipped `V57-A`
    - select one restoration / compensating-restore path only over the shipped
      `create_new` exemplar from `V57-A`
    - reuse of the `V57-A` observation subset does not imply restoration eligibility
      for every observed subset member
    - keep append-only restoration out of the first restoration slice
    - restoration does not reuse the original ticket as ambient ongoing authority
    - restoration is lawful only when one explicit bounded compensating scope can be
      derived from the prior observed path and matched fail-closed against the shipped
      ticket / checkpoint lineage
    - keep general delete, overwrite, rename, and broader destructive semantics out of
      the selected live-class interpretation
    - add one bounded local-effect restoration record
    - keep the new restoration surfaces evidence-bearing only in this slice
    - no hardening decision yet
    - no action-class widening
    - no repo-source/doc/CI/secret/dispatch writes
  - if this family is selected, select `V57-B` as the next default candidate

This family/path recommendation is branch-local to the `v40` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected planning
branches from `v26` through `v39` remain in parallel scope.

## Suggested `V57` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V57-A` | bounded post-effect observation starter | one designated local-effect sandbox, one local-effect observation record, one local-effect conformance report over the frozen `local_write` path only | closed on `main` |
| `V57-B` | bounded restoration / replay hardening | one local-effect restoration record and one bounded replay/restoration path first over the shipped `create_new` exemplar inside the same sandbox authority envelope | recommended next path |
| `V57-C` | local hardening decision | one local-effect hardening register over whether the observed and restored path deserves stronger local hardening later | later lane |

These output names are planning-level candidate names, not lock-level schema
authority.

## Why This Path

- It follows the actual bounded local-effect evidence that `V57-A` already shipped on
  `main`.
- It keeps restoration inside the same designated local sandbox rather than laundering
  it into generic destructive repo authority.
- It chooses one compensating-restore exemplar first, which is narrow enough to be
  lawful before append-only replay or broader hardening is even discussed.
- It turns one observed effect into one bounded replay/restore evidence path rather
  than another abstract governance note.
- It preserves the correct family ordering:
  - `V56` owns boundary-crossing law;
  - `V57` owns bounded post-effect evidence, bounded restoration, and later hardening
    over one already selected live class.

## Proposed `V57-B` Scope

`V57-B` should be bounded to:

- one existing primary family package:
  - `packages/adeu_agentic_de`
- one existing thin script seam under repo operations;
- one explicit `V57-A` to `V57-B` handoff via:
  - `agentic_de_lane_drift_record@1`
- reuse of the shipped `V56-A`, `V56-B`, and `V56-C` packet / morph IR /
  interaction-contract / action-proposal / membrane-checkpoint / diagnostics /
  conformance / runtime-state / action-ticket / harvest surfaces by default;
- reuse of the shipped `V57-A` observation / local-effect conformance surfaces by
  default;
- one selected live action class only:
  - `local_write`
- one designated local-effect sandbox root only:
  - `artifacts/agentic_de/v57/local_effect/`
- one bounded local-effect restoration surface:
  - `agentic_de_local_effect_restoration_record@1`
- one bounded restoration / replay path only over the shipped `create_new` exemplar
  from `V57-A`;
- one explicit replay law only:
  - bounded recomputation and re-evaluation of the restoration event against the prior
    observed-effect lineage
  - not general re-execution of arbitrary prior live actions
- one explicit restoration lineage law only:
  - one prior bounded observation outcome only:
    - `bounded_effect_observed`
  - one prior observation ref
  - one prior local-effect conformance ref
  - one live ticket / selected action proposal / checkpoint-entitled effect lineage
    reused from the prior observed path
  - the original ticket is not ambient ongoing authority
  - restoration is lawful only when one bounded compensating scope can be derived and
    matched fail-closed from that lineage
- reuse of the `V57-A` observation subset does not imply restoration eligibility for
  every observed subset member
- one explicit anti-escape sandbox law only:
  - no symlink escape
  - no parent traversal
  - no indirect alias or mount redirection
  - no write-through into authority-bearing surfaces through sandbox references
- one explicit sandbox-region state law only:
  - restoration pre-state and post-state are scoped to the designated sandbox effect
    region only
  - not to repo-global state
- one explicit restoration outcome vocabulary only:
  - restoration effect observed
  - no restoration effect observed
  - restoration out-of-scope write observed
  - restoration mismatched effect observed
  - restoration boundedness verdict failed
- no append-only restoration yet;
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
  "recommended_next_path": "V57-B",
  "depends_on_closed_v56_family": true,
  "selected_live_action_class_for_v57a": "local_write",
  "selected_live_action_class_interpretation_reused_from_v56b": true,
  "selected_local_write_first_subset_for_v57a": [
    "create_new",
    "append_only"
  ],
  "actual_local_effect_selected_for_v57a": true,
  "bounded_restoration_selected_for_v57b": true,
  "selected_restoration_exemplar_for_v57b": "compensating_restore_of_v57a_create_new_artifact_only",
  "replay_mode_for_v57b": "bounded_recomputation_and_re_evaluation_of_the_restoration_event_against_prior_observed_effect_lineage_only",
  "restoration_does_not_reuse_original_ticket_as_ambient_ongoing_authority": true,
  "restoration_requires_explicit_bounded_compensating_scope_match_or_fail_closed": true,
  "observation_subset_reuse_does_not_imply_restoration_eligibility_for_every_member": true,
  "append_only_restoration_selected_for_v57b": false,
  "destructive_or_overwrite_write_kinds_selected_for_v57b": false,
  "designated_local_effect_sandbox_required": true,
  "sandbox_anti_escape_law_required": true,
  "ticket_to_effect_binding_required": true,
  "restoration_state_pair_scoped_to_designated_sandbox_effect_region_only": true,
  "negative_restoration_outcomes_required": true,
  "hardening_decision_selected_for_v57b": false,
  "governs_hidden_cognition": false
}
```
