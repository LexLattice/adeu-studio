# Draft Next Arc Options v68

Status: planning handoff after `vNext+217` / `V77-C` merged on `main`, after
the `V77` family closeout pass, and after the combined `V68` through `V77`
dogfood probe.

Authority layer: planning.

This draft records the post-`V77` frontier. It does not authorize command
execution, tool invocation, runtime dispatch, product authorization, external
branch activation, PR creation, commit, merge, release, benchmark truth,
global model selection, living-memory authority, recursive policy amendment,
or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v67.md`, which selected the `V77`
runtime-permission review and action-effect envelope family. `vNext+215`,
`vNext+216`, and `vNext+217` then closed `V77-A`, `V77-B`, and `V77-C`
without creating additional family selector versions.

## Current Frontier

- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- `V73` is closed on `main` as the candidate outcome-review family.
- `V74` is closed on `main` as the operator-projection family.
- `V75` is closed on `main` as the dispatch-review family.
- `V76` is closed on `main` as the reconciliation / arbiter review family.
- `V77` is closed on `main` as the runtime-permission review family.
- latest closed implementation arc: `vNext+217`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v67.md`
- next planning obligation: select and review `V78` as the next family outside
  closed `V77`.

The combined `V68` through `V77` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V77` closed runtime-permission review without granting runtime permission,
executing commands, authorizing tool use, productizing, activating external
branches, or selecting `V78`. It also records two carry-forward findings:

- `V77` closes runtime-permission review over command intent, effect,
  telemetry, rollback, authority, summary, and handoff pressure without
  granting runtime permission or executing commands;
- `V77-C` carries product pressure to future product review and runtime /
  tool-use pressure to future authority review, but it does not select `V78`
  or runtime / product / external authority.

## Next Planning Question

Now that `V77` can make runtime-permission review requests, command preflight,
effect envelopes, telemetry requirements, rollback requirements, authority
posture, summaries, and handoffs reviewable without granting permission, should
the next family be `V78`: runtime execution authority, tool-use permission
envelopes, command-scope authorization boundaries, and pre-execution-review
handoff?

## Recommended Next Pressure

- family: `V78`
- proposed family name:
  - `V78: runtime execution authority, tool-use permission envelopes,
    command-scope authorization boundaries, and pre-execution-review handoff`
- recommended planning posture:
  - select `V78` as the next family;
  - select `V78-A` as the next default candidate for `vNext+218`;
  - consume `V77-C` authority posture, runtime review summaries,
    post-runtime-permission-review handoffs, and family closeout alignment as
    immediate source substrate;
  - consume `V77-B` command preflight, action-effect, telemetry, and rollback
    rows as scope / evidence / rollback requirements;
  - define source-bound runtime execution authority requests, authority source
    indexing, and non-action guardrails before any authority decision or
    permission envelope is represented.

`V78` should type the question "who or what can grant, deny, defer, or scope a
bounded later execution review?" It must not run commands, invoke tools,
dispatch workers, productize, activate external branches, or claim release
authority.

## Proposed Family Decomposition

`V78` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V78-A` | runtime execution authority request, runtime authority source index, and non-action guardrail over released `V77-C` handoff / closeout substrate |
| `V78-B` | runtime execution authority decision, tool-use permission envelope, command-scope authorization boundary, and runtime authority exception register |
| `V78-C` | runtime authority readiness summary, pre-execution-review handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V78-A` should be the first active slice. Candidate starter surfaces:

- `repo_runtime_execution_authority_request@1`
- `repo_runtime_authority_source_index@1`
- `repo_runtime_authority_non_action_guardrail@1`

Recommendation: select `V78-A` as the next default candidate after this
selector, with `vNext+218` as the canonical starter bundle if no intervening
arc claims that number.

Later `V78` surfaces should remain planning-layer until their own starter
locks:

- `repo_runtime_execution_authority_decision@1`
- `repo_tool_use_permission_envelope@1`
- `repo_command_scope_authorization_boundary@1`
- `repo_runtime_authority_exception_register@1`
- `repo_runtime_authority_readiness_summary@1`
- `repo_pre_execution_authority_review_handoff@1`
- `repo_runtime_execution_authority_family_closeout_alignment@1`

Post-`V78-A` continuation posture: after `vNext+218` closes on `main`, select
`V78-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V78` family and does not
create a new next-arc-options selector version.

Post-`V78-B` continuation posture: after the `V78-B` slice closes on `main`,
select `V78-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V78` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- command execution;
- actual tool invocation;
- runtime worker dispatch;
- worker assignment;
- dispatch execution;
- product launch, product-market validation, or product authorization;
- external branch activation or `V43` contest participation;
- PR creation, commit, merge, release, or released-truth authority;
- relation settlement, claim truth, or benchmark truth;
- global model selection;
- living decision graph authority;
- recursive policy amendment;
- self-improvement experiment authority.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`V78` is selector-ready because the post-`V77` substrate can cite concrete
released rows showing:

- `V77-C` handoff and closeout records preserve runtime / tool-use authority
  pressure without granting runtime permission or executing commands;
- `V77-C` keeps product pressure blocked by later authority and
  self-evidencing pressure blocked by required runtime / tool-use authority;
- `V77-B` command preflight, effect, telemetry, and rollback rows already
  separate command intent from execution, effect envelope from accepted effect,
  telemetry requirement from observed telemetry, and rollback requirement from
  rollback verification;
- the combined dogfood confirms that no runtime permission has been granted
  and no downstream family has been selected.

`V78` must not be used if the only evidence is:

- an operator desire to run a command;
- a model suggestion that a command would be useful;
- a passing local tool run being treated as authority;
- a `V77` authority posture being treated as an authority grant;
- a command preflight row being treated as command execution;
- a tool applicability or requested tool-use row being treated as tool-use
  permission;
- a product-pressure case being treated as runtime authority;
- an unbounded glob target being treated as a command-scope authorization
  boundary;
- a telemetry or rollback requirement being treated as satisfied evidence.

## Inputs For Starter Drafting

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v67.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_RUNTIME_EXECUTION_AUTHORITY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v217/evidence_inputs/v77_family_closeout_alignment_v217.json`
- `artifacts/agent_harness/v217/evidence_inputs/v77c_runtime_permission_closeout_evidence_v217.json`
- `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_authority_posture_v217_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_review_summary_v217_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus217/repo_post_runtime_permission_review_handoff_v217_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_family_closeout_alignment_v217_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus216/repo_command_preflight_contract_v216_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus216/repo_action_effect_envelope_v216_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus216/repo_runtime_telemetry_requirement_v216_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus216/repo_runtime_rollback_contract_v216_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

## Lock Readiness Note

The future `vNext+218` starter lock should consume committed `V68` through
`V77` closeouts, the combined dogfood artifacts, `vNext+217` evidence inputs,
and released `V77-C` authority / summary / handoff / closeout fixtures as
concrete source rows. If any expected source is missing at lock time, the
`V78-A` runtime execution authority surface should record that absence
explicitly with source-presence or source-status posture.
