# ProgramBench HOB Application Protocol v5

Authority layer: support.

This note is a support-layer overlay on
`docs/support/programbench_hob_application_protocol_v4.md`. It incorporates the
`revive` v47 lesson: dense finite catalogs require explicit saturation posture
before implementation handoff or gold attempts.

## Controlling Artifacts

```text
base protocol:
  docs/support/programbench_hob_application_protocol_v0.md

cross-run / tail protocol:
  docs/support/programbench_hob_application_protocol_v4.md

dense catalog catalog version:
  docs/support/programbench_hob_obligation_catalog_v1.json

dense catalog GPO and meta-program revisions:
  docs/support/general_program_ontology_derived_v1_8.md
  docs/support/principled_recursive_odeu_meta_program_experimental_v47.md

revive causal story:
  docs/support/programbench_revive_v47_causal_story_to_100.md
  .codex/review-shell/chatgpt-downloads/revive_v47_causal_story_meta_review_v51.md
```

## V5 Hardening Summary

V4 prevents scoped-green tails from being promoted after high-score method
gains. V5 adds a pre-handoff dense-catalog saturation gate.

The new failure mode is:

```text
catalog parent recognized
  -> representative catalog children green
  -> implementation handoff or gold attempt promoted
  -> many catalog subprogram leaves remain open
```

The correction is:

```text
dense catalog parent
  -> finite catalog ledger
  -> child status table
  -> catalog-entry subprogram rows
  -> saturation posture
  -> owner-linked BRL sentinels
  -> implementation handoff
```

## V1 Catalog Identity

Use this catalog when the dense-catalog route is active:

```json
{
  "catalog_id": "programbench-odeu-meta-program-obligations",
  "catalog_version": "programbench-hob-v1",
  "catalog_hash": "sha256:bfdb783dbab486bd4967ea1bb6ee38762ba893c96209a0aeafbc3fbf1fd0571e",
  "path": "docs/support/programbench_hob_obligation_catalog_v1.json"
}
```

The v1 catalog extends `programbench-hob-v0`; it does not invalidate the v0
catalog for older run artifacts. New dense-catalog runs should bind activation
and inherited-obligation rows to v1 so stale-ledger checks can distinguish the
new child obligations.

## Dense Catalog Trigger

The protocol must activate the dense-catalog route when public material exposes
a finite but large catalog of behavior-bearing entries:

```text
rules
checks
detectors
commands
modes
plugins
validators
formatters
transforms
```

For static analyzers, the specialized profile is:

```text
CONFIGURABLE_STATIC_ANALYZER_DENSE_CATALOG
```

## Required HOB Rows

Before implementation handoff, the orchestrator must produce:

```text
dense_finite_catalog_import
catalog_child_status_table
catalog_saturation_transition
catalog_entry_subprogram rows for non-shallow entries
semantic_row_universe_before_projection where entries emit rows/findings
directive_emitter_readiness where filters/suppressions apply
owner_surface_replay_lock rows for shared-owner patch areas
```

Each catalog child must be in exactly one explicit state:

```text
matrix_closed
representative_only
source_tail_required
proved_shallow
proved_irrelevant
deferred_with_risk
blocked_pending_observation
blocked_pending_equivalence
```

## Catalog Saturation Readiness

Add readiness state:

```text
catalog_representative_scoped
```

Meaning:

```text
The run has useful representative coverage of a dense catalog, but the catalog
parent is not gold-ready because live child entries remain unsaturated.
```

Promotion rule:

```text
catalog_representative_scoped cannot become gold_ready merely by passing the
representative matrix. Promotion requires child expansion, source-tail
authorization, conflict isolation, or explicit deferral with expected risk.
```

## Row Universe Ordering Rule

For finding/reporting programs:

```text
semantic row universe
  before formatter/API closure
  before directive/filter closure
```

Blocking failures:

```text
formatter_closed_before_row_universe
directive_closed_before_emitter_ready
catalog_child_marked_green_by_name_acceptance
catalog_activation_missing_before_rule_patch
```

## Source-Tail Authorization

Dense catalog exactness can be too numerous and implementation-owned for blind
derivation. Source-tail is authorized only when:

```text
catalog children are finite and localized;
remaining predicates are exact/source-owned or host-library-owned;
blind/public probe yield is low or saturated;
prior gates are preserved;
the output remains labeled source_tail.
```

Forbidden promotion:

```text
source-tail catalog facts -> clean first-pass evidence
```

Allowed backport:

```text
source-tail catalog facts -> future method gate / owner map / findability rule
```

## Worker Handoff Additions

For a dense-catalog implementation batch, the worker baton must name:

```text
catalog refs
child entries in scope
entry subprogram rows
activation states covered
semantic row universe owner
projection owners
directive/filter dependencies
shared implementation owners touched
BRL preservation sentinels
source-tail or deferral posture for out-of-scope children
```

The baton must not ask the worker to:

```text
implement the catalog
fix the linter
add missing rules
make formatters exact
```

without a child-status table, owner map, and saturation posture.

## Additional Blocking Failures

```text
dense_catalog_parent_without_child_status_table
catalog_parent_gold_with_representative_children
catalog_entry_treated_as_string_without_shallow_proof
catalog_activation_not_normalized
catalog_source_tail_used_without_authorization
source_tail_facts_laundered_as_blind_evidence
shared_catalog_owner_patch_without_brl_sentinels
catalog_transition_missing_saturation_posture
```

## Bottom Line

```text
Dense catalog parents do not close by representative examples.
They close through child import, child status, evidence-layer-appropriate
completion, and preservation of previously green shared-owner leaves.
```
