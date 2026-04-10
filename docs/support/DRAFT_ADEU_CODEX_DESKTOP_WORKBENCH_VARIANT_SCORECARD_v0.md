# Draft ADEU Codex Desktop Workbench Variant Scorecard v0

Status: working comparison matrix for parallel implementation assessment.

Authority layer: support.

This document defines the comparison rubric for parallel implementations assessed
against `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md`.
It is meant to be used alongside
`docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md`.
It does not mint shipping authorization by itself.

## Run Stance

- `task_mode`: `review`
- `execution_mode`: `governed_enactment`
- `grounding_status`: `repo_grounded`
- `implementation_inspection_status`: `implementation_inspected`

## Purpose

The comparison should not collapse into "which app looks nicest" or "which codebase is
largest".

The target question is:

- which variant is most constitutionally faithful to the governed workbench draft
- which variant is most truthful about real versus unavailable capability
- which variant best balances bounded adoption against overbuilding
- which variant improves most effectively across checkpoint iterations

## Assessment Structure

The scorecard has three layers:

1. hard gates
2. scored dimensions
3. progression tracking

Hard gates are pass/fail. They should not be softened into point totals.
Scored dimensions compare quality among variants that pass enough of the gate layer to
be meaningfully comparable.
Progression tracking records how well each variant responds to review over time.

## Hard Gates

These are mandatory comparison gates.

### Gate Definitions

| Gate | Meaning |
|---|---|
| `build_clean` | local build command passes |
| `launch_clean` | local Electron launch works in the repo environment |
| `truthful_unavailable_state` | unavailable backend/runtime surfaces are rendered truthfully rather than faked |
| `bounded_filesystem_posture` | filesystem access is contained to the intended workspace root |
| `bounded_terminal_posture` | terminal exposure is explicitly bounded, not silently terminal-first or authority-leaking |
| `no_fake_review_or_workflow_success` | review/workflow actions do not counterfeit successful remote execution |

### Gate Result Legend

- `pass`
- `partial`
- `fail`
- `not_checked`

## Scored Dimensions

Score each scored dimension on a `0-4` scale.

### Score Anchors

| Score | Meaning |
|---|---|
| `0` | absent, broken, or directly contrary to the governing draft |
| `1` | mostly representational or weakly aligned |
| `2` | partial and materially incomplete |
| `3` | solid and mostly correct |
| `4` | strong, verified, and well-bounded |

### Dimensions

| Dimension | Weight | What It Measures |
|---|---:|---|
| `constitutional_fidelity` | 25 | chat-first posture, explicit handoff boundaries, advisory versus authoritative discipline, same-context evidence reachability |
| `grounding_honesty` | 20 | truthful distinction between real wiring, unavailable backend, projected behavior, and uninspected facts |
| `interaction_contract_completeness` | 20 | session controls, file/diff/git/terminal artifacts, review dispatch, workflow dock, evidence attachment |
| `bounded_implementation_judgment` | 10 | adherence to the minimalist bounded workbench brief rather than IDE sprawl or terminal-first drift |
| `host_owned_semantics_discipline` | 15 | ADEU semantics remain governed in the host/workbench rather than outsourced to decorative widgets or imported modules |
| `progression_quality` | 10 | quality of iterative improvement across review checkpoints |

### Weighted Score Formula

For each dimension:

- `dimension_points = (score / 4) * weight`

Then:

- `weighted_total = sum(all dimension_points)`

The final weighted total is out of `100`.

## Sidecar Dimension

This should be recorded, but not folded into the weighted total.

| Sidecar | Meaning |
|---|---|
| `tool_discovery_value` | what missing-tool ontology, reusable artifact concepts, or burden-discovered support surfaces the variant exposed |

## Variant Ledger

Use one row per variant for the current latest checkpoint.

| Variant | Latest Checkpoint | Gates Summary | Weighted Total | Current Verdict | Review Anchor |
|---|---|---|---:|---|---|
| `gemini-codex-workbench` | `checkpoint_4` | `build_clean: pass`, `launch_clean: pass`, `truthful_unavailable_state: pass`, `bounded_filesystem_posture: pass`, `bounded_terminal_posture: pass`, `no_fake_review_or_workflow_success: pass` | `77.5` | `near_spec` | `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md` |
| `opus-codex-workbench` | `checkpoint_4` | `build_clean: pass`, `launch_clean: pass`, `truthful_unavailable_state: pass`, `bounded_filesystem_posture: pass`, `bounded_terminal_posture: pass`, `no_fake_review_or_workflow_success: pass` | `90.0` | `near_spec` | `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md` |
| `gptpro-codex-workbench` | `checkpoint_2` | `build_clean: pass`, `launch_clean: fail`, `truthful_unavailable_state: pass`, `bounded_filesystem_posture: pass`, `bounded_terminal_posture: pass`, `no_fake_review_or_workflow_success: pass` | `62.5` | `intermediate` | `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md` |
| `gpt54-codex-workbench` | `checkpoint_3` | `build_clean: pass`, `launch_clean: pass`, `truthful_unavailable_state: pass`, `bounded_filesystem_posture: pass`, `bounded_terminal_posture: pass`, `no_fake_review_or_workflow_success: pass` | `100.0` | `leading_candidate` | `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md` |

## Per-Variant Score Sheet

Copy this block once per variant once final comparison begins.

### Variant: `name_here`

#### Latest Checkpoint

- `checkpoint_id`:
- `review_anchor`:
- `implementation_root`:

#### Hard Gates

| Gate | Result | Notes |
|---|---|---|
| `build_clean` | `tbd` | |
| `launch_clean` | `tbd` | |
| `truthful_unavailable_state` | `tbd` | |
| `bounded_filesystem_posture` | `tbd` | |
| `bounded_terminal_posture` | `tbd` | |
| `no_fake_review_or_workflow_success` | `tbd` | |

#### Scored Dimensions

| Dimension | Weight | Score `0-4` | Notes |
|---|---:|---:|---|
| `constitutional_fidelity` | 25 | `tbd` | |
| `grounding_honesty` | 20 | `tbd` | |
| `interaction_contract_completeness` | 20 | `tbd` | |
| `bounded_implementation_judgment` | 10 | `tbd` | |
| `host_owned_semantics_discipline` | 15 | `tbd` | |
| `progression_quality` | 10 | `tbd` | |

#### Weighted Total

- `weighted_total`: `tbd / 100`

#### Sidecar

- `tool_discovery_value`:

#### Current Verdict

- `preliminary_verdict`:
- `residual_gaps`:

## Gemini Score Sheet

### Variant: `gemini-codex-workbench`

#### Latest Checkpoint

- `checkpoint_id`: `checkpoint_4`
- `review_anchor`: `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md`
- `implementation_root`: `apps/gemini-codex-workbench`

#### Hard Gates

| Gate | Result | Notes |
|---|---|---|
| `build_clean` | `pass` | `npm run build` passed at the reviewed follow-up checkpoint. |
| `launch_clean` | `pass` | `npm run electron:dev` launched successfully after the dedicated launcher removed `ELECTRON_RUN_AS_NODE`. |
| `truthful_unavailable_state` | `pass` | unavailable backend/profile state is now rendered as unavailable or unconfigured instead of fabricated success |
| `bounded_filesystem_posture` | `pass` | Electron file access is now contained to the repo root through resolved-path containment checks |
| `bounded_terminal_posture` | `pass` | terminal trust posture is explicit, write toggling no longer respawns the PTY, and the preload bridge now exposes listener cleanup for dev remounts |
| `no_fake_review_or_workflow_success` | `pass` | review/workflow surfaces are incomplete, but they do not presently counterfeit successful remote execution |

#### Scored Dimensions

| Dimension | Weight | Score `0-4` | Notes |
|---|---:|---:|---|
| `constitutional_fidelity` | 25 | `3` | chat-first posture, same-context evidence reachability, and explicit review/workflow handoff surfaces are now mostly in place, though the harness/profile lane and workspace lane still remain only partially closed |
| `grounding_honesty` | 20 | `3` | backend absence remains truthfully rendered and no fake execution success is presented, though some labels still compress unavailable state into broad placeholders such as `Unknown` |
| `interaction_contract_completeness` | 20 | `3` | transcript/file/diff review dispatch, workflow request state, session/status fields, and artifact reachability are now present, but build/profile selection, workspace/session selection surfaces, and status-origin typing remain incomplete |
| `bounded_implementation_judgment` | 10 | `3` | the app remains well bounded and avoids IDE sprawl while preserving the governed workbench posture |
| `host_owned_semantics_discipline` | 15 | `3` | review/workflow/session state is now much more concretely expressed in the workbench, though review target identity is still compressed to an unconfigured placeholder and one exposed request path still misstates provenance |
| `progression_quality` | 10 | `4` | the fourth checkpoint closed the previously targeted workflow/review/listener gaps cleanly and improved state truth without overbuilding, though narrow residual gaps still remain |

#### Weighted Total

- `weighted_total`: `77.5 / 100`

#### Sidecar

- `tool_discovery_value`: `medium`; the attempt surfaced concrete missing surfaces around launch guarding, filesystem containment, git artifact truth, session-control completeness, and governed review/workflow handoff state.

#### Current Verdict

- `preliminary_verdict`: `near_spec`
- `residual_gaps`: `Git Status review provenance is typed as diff`, `review target identity is still compressed to [Unconfigured Backend]`, `custom build/profile selection surface is still absent`, `workspace lane still lacks workspace/project selection and tree-level review entry`, `recent sessions remain an unavailable-state note rather than a concrete empty-state list`

## Opus Score Sheet

### Variant: `opus-codex-workbench`

#### Latest Checkpoint

- `checkpoint_id`: `checkpoint_4`
- `review_anchor`: `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md`
- `implementation_root`: `apps/opus-codex-workbench`

#### Hard Gates

| Gate | Result | Notes |
|---|---|---|
| `build_clean` | `pass` | `npm run build` passed at the reviewed follow-up checkpoint. |
| `launch_clean` | `pass` | `npm run electron:dev` launched Vite and Electron successfully in this repo shell after the dedicated launcher scrubbed `ELECTRON_RUN_AS_NODE`. |
| `truthful_unavailable_state` | `pass` | ADEU backend absence, provider/build/config unavailability, local-only review/workflow request state, and lack of evidence return are all rendered explicitly rather than faked as success. |
| `bounded_filesystem_posture` | `pass` | the Electron host now binds the workspace root to the `odeu` repo root and keeps reads inside that boundary through resolved-path containment checks. |
| `bounded_terminal_posture` | `pass` | the terminal is PTY-backed, clearly secondary, and explicitly gated between read-only and interactive modes with visible trust treatment. |
| `no_fake_review_or_workflow_success` | `pass` | review/workflow surfaces record only local `not_executed` request state and do not counterfeit external execution. |

#### Scored Dimensions

| Dimension | Weight | Score `0-4` | Notes |
|---|---:|---:|---|
| `constitutional_fidelity` | 25 | `3` | chat stays primary, explicit handoff boundaries remain visible, and the previously missing profile/sidebar/tree review surfaces are now present, though workspace switching remains intentionally single-root rather than multi-root |
| `grounding_honesty` | 20 | `4` | unavailable backend/runtime state, local-only request ledgers, and provider/build/config absence are now rendered plainly without counterfeit execution claims |
| `interaction_contract_completeness` | 20 | `4` | the Electron host, session controls, file/diff/git/terminal surfaces, review routing, workflow dock, profile intent surface, recent-session lane, tree review entry, and relaunch-surviving request history are all now concretely present |
| `bounded_implementation_judgment` | 10 | `4` | the app now stays squarely inside the bounded desktop-workbench brief and no longer drifts into browser-only mock posture or IDE sprawl |
| `host_owned_semantics_discipline` | 15 | `3` | filesystem, git, terminal, and truthful local-only review/workflow semantics remain well governed, and profile/app-server/config treatment is now explicit, but profile intent and relaunch history persistence still stay in local workbench state rather than host-owned archival semantics |
| `progression_quality` | 10 | `4` | this follow-up closed most of the prior checkpoint findings cleanly, and the remaining omissions look like an interrupted closure pass rather than regressions |

#### Weighted Total

- `weighted_total`: `90.0 / 100`

#### Sidecar

- `tool_discovery_value`: `medium_high`; this pass surfaced how far the bounded desktop variant could be closed through truthful local intent surfaces, relaunch-surviving request state, and same-context tree/sidebar affordances without widening into IDE-style multi-root behavior.

#### Current Verdict

- `preliminary_verdict`: `near_spec`
- `residual_gaps`: `workspace switching remains intentionally disabled under the single-root host posture`, `request-history persistence is renderer-local rather than host-archived`

## GPTPro Score Sheet

### Variant: `gptpro-codex-workbench`

#### Latest Checkpoint

- `checkpoint_id`: `checkpoint_2`
- `review_anchor`: `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md`
- `implementation_root`: `apps/gptpro-codex-workbench` (vendored from imported `adeu-studio-main/apps/web`)

#### Hard Gates

| Gate | Result | Notes |
|---|---|---|
| `build_clean` | `pass` | `npm run build` now passes in the unpacked working tree after the repo-access typing fix. |
| `launch_clean` | `fail` | the route now launches cleanly as a web app on `127.0.0.1:3101` against API `127.0.0.1:8101`, but there is still no Electron/native desktop host shell. |
| `truthful_unavailable_state` | `pass` | review/workflow/session surfaces call real backend paths and fail visibly instead of fabricating success when the backend is unavailable |
| `bounded_filesystem_posture` | `pass` | repo file access is contained to repo-relative paths via explicit normalization and containment checks |
| `bounded_terminal_posture` | `pass` | the terminal lane is a bounded read-only snapshot surface with an allowlisted command set |
| `no_fake_review_or_workflow_success` | `pass` | review/workflow flows call real backend tools and record failure when execution or evidence return does not succeed |

#### Scored Dimensions

| Dimension | Weight | Score `0-4` | Notes |
|---|---:|---:|---|
| `constitutional_fidelity` | 25 | `2` | chat-first posture and explicit handoff boundaries are present, but file/diff evidence attachment is still partial and the workbench is web-primary rather than desktop-native |
| `grounding_honesty` | 20 | `4` | the variant is now materially truthful not just in contract shape but in verified runtime behavior: the chat lane renders real SSE replies, backend calls remain visible, and completion state is no longer overstated or left blank |
| `interaction_contract_completeness` | 20 | `3` | session controls, a functioning chat lane, harness/config inspection, file/diff/git/terminal artifacts, review routing, and workflow dock are all substantially implemented, though target execution binding and inline evidence return still remain incomplete |
| `bounded_implementation_judgment` | 10 | `1` | implementing the workbench as a web route plus public desktop-style HTTP endpoints is a major drift from the desktop-native bounded-host brief |
| `host_owned_semantics_discipline` | 15 | `2` | there is real host-owned contract and repo-access logic, but review target selection is only partially executable and the chosen host boundary is wrong |
| `progression_quality` | 10 | `2` | this second checkpoint closed a real runtime defect and verified the full web build, though the core host-boundary problems remain unchanged |

#### Weighted Total

- `weighted_total`: `62.5 / 100`

#### Sidecar

- `tool_discovery_value`: `medium_high`; the variant surfaced reusable artifacts around review packet construction, bounded repo access, harness/config inspection, and read-only terminal snapshots, even though the host boundary choice is wrong.

#### Current Verdict

- `preliminary_verdict`: `intermediate`
- `residual_gaps`: `web-primary instead of desktop-native`, `desktop routes expose repo and harness/config state over HTTP`, `review target profile is not truly routed as backend execution target`, `same-context evidence is still partial for file/diff origins`, `default contract-test script still omits codex-workbench contract coverage`

## GPT-5.4 Codex Score Sheet

### Variant: `gpt54-codex-workbench`

#### Latest Checkpoint

- `checkpoint_id`: `checkpoint_3`
- `review_anchor`: `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_ATTEMPT_REVIEWS_v0.md`
- `implementation_root`: `apps/gpt54-codex-workbench`

#### Hard Gates

| Gate | Result | Notes |
|---|---|---|
| `build_clean` | `pass` | `npm run check` passed in the implementation root. |
| `launch_clean` | `pass` | `npm run smoke` launched Electron successfully in this repo shell after the dedicated launcher removed `ELECTRON_RUN_AS_NODE`. |
| `truthful_unavailable_state` | `pass` | observed runtime state, host-declared launch metadata, and advisory review/workflow surfaces remain explicitly separated; missing runtime data is rendered as unknown/error rather than fabricated success |
| `bounded_filesystem_posture` | `pass` | workspace selection is explicit and file access is contained through resolved-path checks under the chosen workspace root |
| `bounded_terminal_posture` | `pass` | the terminal surface is a read-only allowlisted preset lane with no free-form shell path |
| `no_fake_review_or_workflow_success` | `pass` | review and workflow actions call real ADEU tool paths and surface errors rather than counterfeiting successful remote execution |

#### Scored Dimensions

| Dimension | Weight | Score `0-4` | Notes |
|---|---:|---:|---|
| `constitutional_fidelity` | 25 | `4` | transcript-first posture, explicit handoff boundaries, advisory-vs-authoritative distinction, and same-context evidence reachability are now all strong and verified |
| `grounding_honesty` | 20 | `4` | target routing truth, failed-record persistence, and post-dispatch evidence-load labeling are now all explicit and execution-truthful |
| `interaction_contract_completeness` | 20 | `4` | session controls, launch-profile selection, workspace/file/diff/git/terminal surfaces, workflow dock, review routing, inline origin markers, evidence loading, and recent sessions are now all present and materially connected |
| `bounded_implementation_judgment` | 10 | `4` | the app stays tightly inside the governed desktop-workbench brief and avoids both IDE sprawl and terminal-first drift |
| `host_owned_semantics_discipline` | 15 | `4` | bounded filesystem, read-only terminal presets, session/writes/profile control, and runtime/tool/evidence bridges are all held in the host/workbench layer rather than outsourced to decorative helpers |
| `progression_quality` | 10 | `4` | the third checkpoint fixed the last reviewed phase-truth defect without widening the app or regressing the verified desktop posture |

#### Weighted Total

- `weighted_total`: `100.0 / 100`

#### Sidecar

- `tool_discovery_value`: `high`; this variant surfaced a concrete artifact set for host-declared launch metadata, observed runtime truth, bounded read-only terminal presets, review dispatch records, workflow/evidence docks, and separated trust-boundary notices.

#### Current Verdict

- `preliminary_verdict`: `leading_candidate`
- `residual_gaps`: `none observed within the current review matrix`

## Progression Tracking

This section is mandatory for final assessment.
Variants should be judged not only by current state, but by how they responded to
review over time.

### Progression Fields

| Field | Meaning |
|---|---|
| `checkpoint_id` | ordinal checkpoint label |
| `starting_posture` | what state the variant started that checkpoint in |
| `closed_findings` | which prior findings were actually closed |
| `partial_closures` | findings improved but not fully closed |
| `new_regressions` | issues introduced during the follow-up |
| `overclaim_reduction` | whether the variant became more truthful about what is real versus unavailable |
| `net_progress_judgment` | concise summary of the checkpoint delta |

### Progression Log Template

#### Variant: `name_here`

| Checkpoint | Starting Posture | Closed Findings | Partial Closures | New Regressions | Overclaim Reduction | Net Progress Judgment |
|---|---|---|---|---|---|---|
| `checkpoint_1` | `tbd` | `tbd` | `tbd` | `tbd` | `tbd` | `tbd` |
| `checkpoint_2` | `tbd` | `tbd` | `tbd` | `tbd` | `tbd` | `tbd` |
| `checkpoint_3` | `tbd` | `tbd` | `tbd` | `tbd` | `tbd` | `tbd` |

## Gemini Progression Seed

This seed reflects current observed history and should be refined as the final
cross-variant assessment is assembled.

| Checkpoint | Starting Posture | Closed Findings | Partial Closures | New Regressions | Overclaim Reduction | Net Progress Judgment |
|---|---|---|---|---|---|---|
| `checkpoint_1` | initial implementation with real file tree and PTY but heavy placeholder posture | `none` | `n/a` | `runtime launch fragility`, `unbounded filesystem`, `build/lint failures`, `representational review/workflow` | `low` | useful intermediate checkpoint, not spec-faithful |
| `checkpoint_2` | follow-up after directed review | `launch guard`, `filesystem containment`, `git status/diff`, `build clean`, `lint clean`, `README replaced` | `truthful unavailable posture`, `terminal trust posture` | `terminal listener/respawn bug` | `medium_high` | materially improved, still intermediate because governed handoff/session surfaces remain incomplete |
| `checkpoint_3` | second follow-up after narrowed review | `write-toggle respawn bug`, `inline origin review attachment`, `quick-peek overlay`, `visible session controls` | `review routing surface`, `session boundary truth`, `same-context evidence reachability` | `none observed beyond remaining lifecycle cleanup gap` | `medium_high` | strongest Gemini checkpoint so far, but still intermediate because workflow and multi-origin review contract remain incomplete |
| `checkpoint_4` | third follow-up after targeted closure pass | `workflow request state`, `tri-origin review dispatch`, `origin-linked file/diff review pills`, `terminal listener cleanup` | `session boundary completeness`, `workspace lane coverage`, `review target truth` | `none observed; the remaining issues are residual surface-contract omissions rather than fresh regressions` | `high` | near-spec checkpoint: most governed surfaces are now present and truthful, but the harness/profile lane, workspace lane, and review target/provenance semantics are still not fully closed |

## Opus Progression Seed

This seed reflects the observed Opus checkpoints to date.

| Checkpoint | Starting Posture | Closed Findings | Partial Closures | New Regressions | Overclaim Reduction | Net Progress Judgment |
|---|---|---|---|---|---|---|
| `checkpoint_1` | initial delivered variant | `visual topology reproduction`, `build clean` | `peek overlay`, `review/workflow lane visibility`, `trust notice presentation` | `web-only instead of desktop host`, `counterfeit ADEU runtime`, `blocked session start path`, `flattened file provenance`, `simulated terminal` | `low` | polished browser prototype with governed-shape cues, but not a spec-faithful desktop workbench |
| `checkpoint_2` | follow-up after first review | `desktop host shell`, `launch guard`, `truthful unavailable posture`, `file-path provenance`, `real PTY terminal`, `build clean` | `review/workflow governed request state`, `session boundary truth`, `same-context evidence reachability` | `none observed beyond remaining root-scope and control-binding issues` | `high` | major correction pass: now a real desktop checkpoint and no longer a counterfeit browser mock, but still intermediate because boundary binding and origin-return details remain incomplete |
| `checkpoint_3` | follow-up after narrowed review with quota interruption | `workspace root identity`, `terminal write-scope truth`, `git changed-file load path`, `provider/build/config unavailable fields`, `reply/file/diff origin review markers` | `harness/profile surface`, `sidebar recent-session and workspace-switch contract`, `tree-level review entry` | `none observed` | `high` | substantial closure pass: the variant is now near-spec, and the remaining omissions read more like an interrupted finish than like unresolved host-boundary confusion |
| `checkpoint_4` | closure pass after the interrupted checkpoint | `profile/app-server/config intent surface`, `recent-session sidebar`, `bounded workspace-switch disclosure`, `tree-level review entry`, `current-session review markers`, `relaunch-surviving request history` | `single-root workspace switching remains intentionally disabled`, `history persistence remains renderer-local rather than host-archived` | `none observed` | `high` | near-spec closure checkpoint: the prior residual set is now closed cleanly inside the bounded desktop posture, and the remaining distinctions are implementation-weight choices rather than open correctness defects |

## GPTPro Progression Seed

This seed reflects the current observed imported-snapshot checkpoints.

| Checkpoint | Starting Posture | Closed Findings | Partial Closures | New Regressions | Overclaim Reduction | Net Progress Judgment |
|---|---|---|---|---|---|---|
| `checkpoint_1` | imported cloud-built snapshot reviewed against its own baseline zip | `chat-first topology`, `real repo-access layer`, `session/profile controls`, `review and workflow record surfaces`, `gen:types fallback` | `same-context evidence reachability`, `desktop-native posture` | `web-primary instead of desktop host`, `public desktop API trust-boundary collapse`, `review target selection not fully executable` | `medium` | comparatively complete imported web variant, but still intermediate because the host and trust boundary are materially wrong for the draft |
| `checkpoint_2` | verification/fix follow-up in the unpacked working tree | `actual SSE chat rendering`, `assistant completion replacement`, `hydration mismatch removal`, `full next build verification` | `working web runtime on the codex-workbench route` | `none observed beyond the existing web-host boundary mismatch` | `medium_high` | stronger imported checkpoint: the variant still fails the desktop-host brief, but it now builds cleanly and the chat lane actually works in its chosen web posture |

## GPT-5.4 Codex Progression Seed

This seed reflects the current observed first-pass checkpoint.

| Checkpoint | Starting Posture | Closed Findings | Partial Closures | New Regressions | Overclaim Reduction | Net Progress Judgment |
|---|---|---|---|---|---|---|
| `checkpoint_1` | initial delivered standalone Electron implementation | `desktop host shell`, `launch guard`, `bounded filesystem access`, `read-only terminal presets`, `session/profile/write controls`, `review/workflow/evidence surfaces`, `recent-session surface`, `real ADEU tool wiring` | `origin-linked evidence attachment`, `review target execution binding`, `negative-path request persistence` | `none observed` | `high` | strongest reviewed variant so far: a near-spec desktop workbench with only narrow handoff/provenance gaps remaining |
| `checkpoint_2` | follow-up after targeted residual-gap review | `inline origin review attachment`, `failed handoff persistence`, `review target execution truth` | `failure phase truth remains slightly compressed when evidence load fails after successful dispatch` | `none observed` | `high` | strongest checkpoint across all variants so far: the app remains bounded, build-clean, and desktop-native while closing the prior review gaps with only one narrow phase-labeling defect remaining |
| `checkpoint_3` | follow-up after the phase-truth review | `evidence-load failure labeling`, `automatic evidence-load issue recording`, `successful retry clearing of evidence-load issue state` | `none` | `none observed` | `medium_high` | review-clean against the current support matrix: the app stays desktop-native, bounded, and build-verified while clearing the last scored defect from checkpoint_2 |

## Comparison Notes

- A variant can improve substantially and still remain `intermediate`.
- A variant should not receive high marks for `grounding_honesty` if it overclaims
  backend integration or review/workflow execution that is not actually present.
- `progression_quality` should reward closing the right issues, not merely adding more
  code.
- `tool_discovery_value` should capture any missing-tool ontology or reusable artifact
  boundaries revealed by the implementation, even if the variant itself is not the
  strongest overall.
