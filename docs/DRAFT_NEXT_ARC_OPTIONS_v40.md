# Draft Next Arc Options v40

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v39.md`, updated after the
bounded `V57-A` local-effect observation starter closed on `main` through `v155`,
after the bounded `V57-B` local-effect restoration/replay starter closed on `main`
through `v156`, and after the shipped `V57-A`/`V57-B` surfaces captured one actually
observed bounded local effect plus one compensating-restore path but still left one
bounded local hardening decision seam unowned:
the shipped observed/restored `create_new` local-write exemplar still lacks one
repo-owned advisory hardening register over whether that path deserves stronger local
hardening later.

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
- `V57-B` is closed on `main` and now constitutes the released bounded local-effect
  restoration / replay starter recorded in this `v40` planning branch.
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
- the shipped `V57-B` outputs now externalize:
  - one designated sandbox-root local-effect restoration record
  - one bounded compensating-restore path over the shipped `create_new` exemplar only
  - one explicit restoration-entitlement law tied to the same observation / ticket /
    checkpoint lineage
  - explicit negative restoration outcomes
- `v156` is the current implementation-arc baseline on `main`.

## Gap

The repo no longer lacks:

- one released resident-agent packet / contract / checkpoint family;
- one released bounded resident-agent live gate over a narrow local subset; or
- one released advisory harvest/calibration/migration layer over those governed
  surfaces.

The repo still lacks:

- one repo-owned local hardening decision seam over the shipped observed/restored
  local-write path;
- one typed hardening register that consumes the shipped observation / conformance /
  restoration lineage rather than narrative interpretation alone;
- one bounded advisory decision surface over whether the observed/restored
  `create_new` exemplar deserves stronger local hardening later; and
- one later migration posture over that path that stays downstream of `V56`, `V57-A`,
  and `V57-B` rather than silently mutating live behavior.

So the repo still lacks the slice that would turn the shipped `V57-A` observation plus
the shipped `V57-B` restoration of `local_write_post_effect_observation_path` into
one lawful bounded hardening-decision surface rather than leaving the observed and
restored evidence with no repo-owned local hardening judgment.

## Relationship To `V48`, `V51`, `V55`, And `V56`

`V55` asks:

- how should a bounded promoted stack be checked for constitutional coherence?

`V56` asks:

- how should the resident agent's externally effective loop be governed through packet,
  contract, proposal, checkpoint, ticket, conformance, and harvest?

This new family asks:

- how should one already selected `V56` local live path produce lawful post-effect
  evidence without reopening `V56` gate law?
- how should ADEU capture actual local-write observation, boundedness, and bounded
  restoration evidence inside one designated local sandbox?
- how should one observed and restored effect constrain later hardening discussion
  without minting it automatically?

So this family may constrain:

- actual bounded local-effect execution over a shipped `V56` ticket;
- effect target-root selection and path boundedness;
- post-effect observation and conformance;
- bounded restoration / replay over the same frozen semantics;
- later local hardening discussion over the same observed/restored path.

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
  - `V57-C`
- Recommended next concrete arc for this branch if selected:
  - `V57-C`
- Default path selection for this branch:
  - one bounded local hardening decision starter is recommended:
    - reuse the shipped `V56-A`, `V56-B`, `V56-C`, and `V57-A` packet / contract /
      proposal / checkpoint / ticket / conformance / harvest / observation surfaces by
      default
    - reuse the shipped `V57-B` restoration surface by default
    - keep the operative interpretation of `local_write` frozen from shipped `V56-B`,
      shipped `V56-C`, shipped `V57-A`, and shipped `V57-B`
    - keep the operative interpretation of the shipped `V57-B` restoration exemplar
      frozen:
      - compensating restore of the shipped `create_new` artifact only
    - keep the designated local-effect sandbox root from shipped `V57-A`
    - select one bounded local hardening register only over the shipped observed and
      restored `create_new` exemplar
    - keep the hardening-decision seam advisory-only in this slice
    - keep committed fixtures, observation/conformance/restoration outputs, lane-drift
      records, and closeout evidence higher-ranked than narrative interpretation
    - keep one observed/restored effect from minting checkpoint, ticket, sandbox, or
      class changes by default
    - no action-class widening
    - no restoration-exemplar reinterpretation
    - no repo-source/doc/CI/secret/dispatch writes
    - no checkpoint/ticket mutation
    - no restoration-law widening
  - if this family is selected, select `V57-C` as the next default candidate

This family/path recommendation is branch-local to the `v40` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected planning
branches from `v26` through `v39` remain in parallel scope.

## Suggested `V57` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V57-A` | bounded post-effect observation starter | one designated local-effect sandbox, one local-effect observation record, one local-effect conformance report over the frozen `local_write` path only | closed on `main` |
| `V57-B` | bounded restoration / replay hardening | one local-effect restoration record and one bounded replay/restoration path first over the shipped `create_new` exemplar inside the same sandbox authority envelope | closed on `main` |
| `V57-C` | local hardening decision | one local-effect hardening register over whether the observed and restored path deserves stronger local hardening later | recommended next path |

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

## Proposed `V57-C` Scope

`V57-C` should be bounded to:

- one existing primary family package:
  - `packages/adeu_agentic_de`
- one existing thin script seam under repo operations;
- one explicit `V57-B` to `V57-C` handoff via:
  - `agentic_de_lane_drift_record@1`
- reuse of the shipped `V56-A`, `V56-B`, and `V56-C` packet / morph IR /
  interaction-contract / action-proposal / membrane-checkpoint / diagnostics /
  conformance / runtime-state / action-ticket / harvest surfaces by default;
- reuse of the shipped `V57-A` observation / local-effect conformance surfaces by
  default;
- reuse of the shipped `V57-B` restoration surface by default;
- one selected live action class only:
  - `local_write`
- one designated local-effect sandbox root only:
  - `artifacts/agentic_de/v57/local_effect/`
- one bounded local hardening decision surface:
  - `agentic_de_local_effect_hardening_register@1`
- one selected hardening target only:
  - the shipped observed and restored `create_new` exemplar inside the same sandbox
    authority envelope
- one explicit no-generalization law only:
  - exemplar evidence may not be generalized by default into class-level conclusions
    about `local_write`
  - exemplar evidence may not be generalized by default into restoration-family law
- one explicit evidence-consumption law only:
  - committed observation / conformance / restoration fixtures
  - committed lane-drift record
  - committed closeout evidence
  - outrank narrative interpretation by default
- one explicit hardening-decision law only:
  - advisory-only in this slice
  - candidate-only for any later local hardening selection
  - path-level advisory only:
    - not a family-wide migration surface
  - may assess the shipped path but may not mutate live checkpoint, ticket,
    observation, conformance, or restoration behavior by default
- one explicit hardening-evidence chain only:
  - ticket ref
  - action proposal ref
  - checkpoint ref
  - observation ref
  - local-effect conformance ref
  - restoration ref
  - observation boundedness verdict
  - restoration boundedness verdict
  - selected hardening target surface
  - recommended outcome
  - evidence refs / reason codes
- one explicit allowed outcome vocabulary only:
  - `keep_warning_only`
  - `needs_more_evidence`
  - `candidate_for_later_local_hardening`
  - `not_selected_for_escalation`
- one explicit forbidden outcome vocabulary only:
  - `gate_now`
  - `sandbox_widen_now`
  - `broader_write_now`
  - `restoration_generalize_now`
  - `dispatch_now`
  - `ci_required_now`
- one explicit anti-laundering law only:
  - one observed/restored effect does not by itself nominate checkpoint, ticket,
    class, sandbox, or entitlement changes
  - restoration evidence does not by itself become hardening authority
  - `candidate_for_later_local_hardening` nominates only one later bounded evaluation
    target and does not identify later hardening scope unless a later lock types and
    selects that scope
- no class widening;
- no restoration-exemplar reinterpretation;
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
  "recommended_next_path": "V57-C",
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
  "bounded_local_hardening_selected_for_v57c": true,
  "selected_hardening_target_for_v57c": "observed_and_restored_v57a_create_new_exemplar_only",
  "local_effect_hardening_register_selected_for_v57c": true,
  "advisory_only_hardening_outputs_in_v57c": true,
  "committed_lane_artifacts_outrank_narrative_docs_for_v57c": true,
  "hardening_may_not_change_live_behavior_by_default": true,
  "hardening_decision_selected_for_v57b": false,
  "governs_hidden_cognition": false
}
```
