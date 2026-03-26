# Draft Next Arc Options v23

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v22.md`, updated after
`vNext+88` closeout and released `V41-A` + `V41-B` + `V41-C` + `V41-D` + `V41-E` +
`V41-F` practical-analysis baselines on `main`.

This draft no longer selects another seam inside `V41`.

Its role is now to record that the bounded practical-analysis family is complete on
`main` and to keep the closure boundary explicit until the repo chooses a new family.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A`, `V41-B`, `V41-C`, `V41-D`, `V41-E`, and `V41-F` are now closed on
  `main`.
- `vNext+88` is the current baseline implementation state.
- The released practical-analysis substrate now includes:
  - canonical `adeu_architecture_analysis_request@1`;
  - deterministic repo-root-relative scope selection;
  - `committed_tree` / `materialized_snapshot` request discipline;
  - per-item plus aggregate `source_set` hashing;
  - exact brief/doc reference closure;
  - explicit request-bound authority-boundary policy pinning;
  - canonical `adeu_architecture_analysis_settlement_frame@1`;
  - explicit interpretation register plus chosen interpretation;
  - explicit deontic typing, affordance decisions, claim posture, escalation policy,
    and fail-closed `compile_entitlement` over the released request boundary;
  - canonical `adeu_architecture_observation_frame@1`;
  - exact request + settlement consumption in the observed lane;
  - facts-only observed implementation extraction with direct-vs-derived marking,
    unresolved observations, and blocked-settlement carry-through;
  - canonical repo-grounded intended compile over the released request, settlement,
    and observation boundary;
  - deterministic materialization of released `V40-A` root-family artifacts over one
    bounded repo slice;
  - canonical `adeu_architecture_alignment_report@1` with stable finding ids,
    deterministic dedup/order, severity/blocking posture, and unresolved-unknown
    carry-through;
  - canonical `adeu_architecture_analysis_run_manifest@1` with deterministic
    `run_id`, canonical stage ledger, exact sequencing over the released practical
    stack, authoritative blocked-run stop witness, and no remediation/repo-mutation
    widening.

## Family Result

`V41` is complete at its intentionally bounded baseline.

It now provides one end-to-end practical loop over one bounded repo world:

```text
repo scope + maintainer brief + accepted docs
    -> canonical analysis request and source_set
    -> analysis settlement / entitlement frame
    -> observed implementation frame
    -> intended architecture semantic IR
    -> deterministic alignment / drift report
    -> habitual CLI-first run manifest
```

This is the first released repo-native practical-analysis loop in the ADEU
architecture lane.

## Closed Current Paths (`V41-A` through `V41-F`)

Solved:

- one canonical analysis-request artifact over one deterministic repo world;
- one canonical settlement / entitlement artifact that externalizes interpretation
  rather than leaving it implicit;
- one canonical observed implementation artifact grounded in the released repo world;
- one canonical intended repo-grounded semantic compile lane that keeps observation as
  constraining evidence rather than a hidden source of intended truth;
- one canonical deterministic alignment lane that compares intended and observed
  without reconciling them into one artifact;
- one canonical practical runner / orchestration lane that makes the released stack
  habitual and replayable without widening into remediation or mutation authority.

## What `V41` Did Not Solve

The bounded practical-analysis family did not attempt to solve:

- remediation planning;
- repo mutation or code-edit authority;
- merged-truth reconciliation between intended and observed lanes;
- API or web workbench release for the practical-analysis loop;
- multi-repo fleet orchestration;
- practical checkpoint/projection/UX reruns inside the runner;
- direct prompt-to-code generation.

Those are not missing slices inside `V41`.

They are candidates for later family-selection work outside the bounded
practical-analysis baseline.

## Remaining Path Inside `V41`

There are no remaining default paths inside `V41`.

The family is complete on `main` at its intentionally bounded scope.

## Planning Boundary

- no reopening of the released `V41-A` request / `source_set` contract is authorized
  by this planning draft;
- no widening of `V41-B` settlement authority is authorized by this planning draft;
- no widening of `V41-C` observed extraction, `V41-D` intended compile, `V41-E`
  alignment, or `V41-F` runner orchestration is authorized by this planning draft;
- no remediation, repo mutation, merged-truth reconciliation, API/web workbench
  release, or direct prompt-to-code generation is authorized by this planning draft;
- no next family is selected by this document.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v22.md",
  "baseline_arc": "vNext+88",
  "closed_prior_family": "V40",
  "closed_prior_paths": [
    "V40-A",
    "V40-B",
    "V40-C",
    "V40-D",
    "V40-E",
    "V40-F"
  ],
  "active_family": "V41",
  "active_family_status": "closed_complete_on_main",
  "closed_current_family_paths": [
    "V41-A",
    "V41-B",
    "V41-C",
    "V41-D",
    "V41-E",
    "V41-F"
  ],
  "default_next_arc_candidate": null,
  "default_next_concrete_arc_candidate": null,
  "family_decomposition_doc": "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md",
  "analysis_request_artifact": "adeu_architecture_analysis_request@1",
  "analysis_settlement_artifact": "adeu_architecture_analysis_settlement_frame@1",
  "analysis_settlement_package": "packages/adeu_architecture_ir",
  "observed_lane_artifact": "adeu_architecture_observation_frame@1",
  "observed_lane_package": "packages/adeu_architecture_compiler",
  "intended_lane_artifact": "adeu_architecture_semantic_ir@1",
  "alignment_artifact": "adeu_architecture_alignment_report@1",
  "alignment_package": "packages/adeu_architecture_compiler",
  "alignment_authoritative_intended_surface": "adeu_architecture_semantic_ir@1",
  "practical_runner_artifact": "adeu_architecture_analysis_run_manifest@1",
  "practical_runner_package": "packages/adeu_architecture_compiler",
  "intended_observed_lane_separation_required": true,
  "alignment_requires_distinct_intended_and_observed_artifacts": true,
  "precompile_settlement_required": true,
  "settlement_entitlement_gate_required": true,
  "settlement_entry_grounding_required": true,
  "settlement_blocking_lineage_required": true,
  "alignment_blocked_distinct_from_settlement_blocked": true,
  "runner_blocked_distinct_from_alignment_blocked": true,
  "run_manifest_emitted_on_blocked_run": true,
  "run_id_deterministic": true,
  "stage_ledger_required": true,
  "settlement_notes_authoritative": false,
  "formal_sidecar_authoritative": false,
  "cli_first_practical_runner": true,
  "remaining_default_paths_in_family": [],
  "v41_family_complete_on_main": true,
  "next_family_selection_required": true
}
```
