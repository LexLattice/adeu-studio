# Draft ADEU Codex Desktop Workbench v0

Status: working design draft for skill enactment.

Authority layer: support.

This document is a Morphic UX design artifact. It does not authorize implementation,
runtime behavior, or artifact adoption by itself.

## Run Stance

- `task_mode`: `design`
- `execution_mode`: `governed_enactment`
- `grounding_status`: `artifact_grounded_repo_incomplete`
- `implementation_inspection_status`: `implementation_not_inspected`

Reason for stance:

- the repo contains grounded Codex and UX reference surfaces;
- the repo does not yet contain the target standalone desktop application;
- design judgments below are therefore grounded against current repo doctrine and current
  reachable Codex-related surfaces, but still inferred for the new desktop workbench.

## Source Grounding

Primary grounding used for this design:

- `apps/web/src/app/artifact-inspector/reference-surface.ts`
- `.agents/skills/morphic-ux-frontend/references/source-grounding.md`
- `.agents/skills/morphic-ux-frontend/references/frontend-delivery-checklist.md`
- `.agents/skills/morphic-ux-frontend/references/artifact-oriented-design.md`
- `apps/web/src/app/copilot/page.tsx`

Repo-grounded facts relevant to this workbench:

- the current repo already exposes Codex-oriented session and workflow surfaces in the
  copilot route, including:
  - `adeu.get_app_state`
  - `adeu.list_templates`
  - `adeu.run_workflow`
  - `adeu.compile_brokered_reflexive_execution`
  - `adeu.read_evidence`
  - `urm.spawn_worker`
  - `urm.set_mode`
- the current Morphic UX reference family is a bounded desktop workbench with explicit
  evidence/status lanes and same-context reachability discipline;
- the target ADEU Codex desktop workbench does not exist yet, so desktop layout,
  native menuing, and local-host behavior are design-time projections rather than
  inspected implementation facts.

## Purpose

Design a standalone ADEU Codex UI/DE that is:

- minimalist
- chat-first
- Codex-wired from the start
- desktop-native rather than web-primary
- able to expose custom Codex harness and `config.toml` wiring cleanly
- able to dispatch selected replies or files into external review workflows
- able to surface ADEU-specific workflows as first-class bounded artifacts

This is not a full IDE brief.

## Non-Goals

This draft does not target:

- full VS Code replacement behavior
- in-place code editing as the primary work mode
- terminal-first interaction posture
- free-form widget sprawl
- review outputs becoming authoritative automatically
- detached multi-window complexity as a default interaction mode

## UX Domain Packet

### User Archetype

- `primary_user_archetype`: expert operator using Codex as the main execution engine
- `secondary_user_archetype`: ADEU maintainer orchestrating review and workflow runs

### Risk And Trust

- `risk_level`: high
- `trust_sensitivity`: authority-and-evidence-sensitive
- `interaction_mode`: analysis-then-dispatch

### Utility Ranking

1. operator speed in the main chat loop
2. truthful visibility of session/build/config state
3. low-friction access to secondary artifacts without losing conversation context
4. explicit review and workflow dispatch boundaries
5. stable same-context access to evidence, status, and returned review outputs

### Required Evidence Visibility

- active Codex provider/build/config identity
- session status, write posture, and app-server reachability
- review request target, scope, and returned status
- workflow launch target, template, and run state
- file or diff provenance when dispatched for review

## Invariants

- chat transcript remains the semantic center of gravity
- the surface may express authority, but may not mint authority
- `writes enabled` and other capability-changing states stay explicit
- review dispatch is visible as a handoff boundary, not a silent side effect
- workflow launch is visible as a handoff boundary, not a background magic action
- evidence for review/workflow actions remains same-context reachable
- advisory review results are rendered as advisory, not as authoritative merge truth
- terminal, diff, git, and file artifacts remain secondary bounded artifacts
- no route change is required to inspect status or evidence relevant to the current
  conversation action

## Morphable Choices

- whether the file tree lives as a narrow persistent lane or a collapsible lane
- whether secondary artifacts open docked in the side context region or as bounded peek
  overlays
- whether ADEU workflows are shown as a lower shelf or a right-pane tab
- whether terminal and diff share one tabbed artifact pane or have separate buttons with
  remembered docking targets

## Proposed Lawful Morph Profile

This workbench needs a new profile inside the repo-native morph axis vocabulary.

- `profile_id`: `adeu_codex_desktop_reference`
- `density`: `medium_high`
- `navigation_mode`: `split_pane`
- `information_posture`: `conversation_first_with_same_context_evidence`
- `interaction_tempo`: `expert_fast_path`
- `salience_posture`: `conversation_and_status_prominent`
- `state_exposure`: `full_explicit`
- `command_posture`: `dual_lane`

Interpretation:

- the transcript is primary, but status and evidence remain visibly attached;
- expert operators should be able to reveal terminal, diff, git, or file context with a
  single bounded focus shift;
- authoritative side effects such as enabling writes, launching workflows, or sending
  external review remain visually distinct from ordinary conversation actions.

## Artifact Inventory

### `desktop_host_shell`

- class: support artifact
- plan: `import_and_align`
- role: native application shell for local processes, native menus, context menus, file
  system access, and bounded child-process wiring
- host-owned meta-properties:
  - authority posture
  - session/build identity interpretation
  - review dispatch semantics
  - workflow dispatch semantics

### `conversation_workbench`

- class: surface artifact
- plan: `build`
- role: primary transcript, composer, response controls, and session-centered operator loop
- host-owned meta-properties:
  - truth posture of replies
  - distinction between local message actions and external dispatch
  - attachment of review/workflow evidence to transcript items

### `session_control_surface`

- class: surface artifact
- plan: `build`
- role: start/stop/restart session, show provider/build/config identity, show write mode,
  show app-server reachability, and expose custom build selection
- host-owned meta-properties:
  - capability truth
  - gating semantics
  - config provenance

### `file_tree_surface`

- class: surface artifact
- plan: `import_and_align`
- role: read-only project tree with selection, quick preview entry, and send-for-review
  entry
- host-owned meta-properties:
  - file selection does not imply edit entitlement
  - review dispatch scope and provenance
  - current-session relevance markers

### `file_quick_viewer`

- class: surface artifact
- plan: `compose_or_import`
- role: read-only file viewing in two lawful modes:
  - bounded peek overlay
  - docked reader tab in the context region
- host-owned meta-properties:
  - read-only posture
  - dispatch scope selection
  - returned review attachment surface

### `terminal_surface`

- class: surface artifact
- plan: `import_and_align`
- role: bounded terminal lane opened by explicit action button
- host-owned meta-properties:
  - session binding
  - read-only vs interactive posture
  - warning and trust treatment
  - no semantic authority leakage from terminal colors or status text

### `diff_surface`

- class: surface artifact
- plan: `import_and_align`
- role: read-only diff inspection, selection, and dispatch-for-review source
- host-owned meta-properties:
  - advisory posture
  - diff provenance
  - dispatch scope truth

### `git_status_surface`

- class: surface artifact
- plan: `compose`
- role: bounded branch/status/log summary rather than full Git client complexity
- host-owned meta-properties:
  - truthful status rendering
  - relation to current session and current diff scope
  - review dispatch integration

### `review_routing_surface`

- class: surface artifact
- plan: `build`
- role: typed dispatch for `Send For Review` from transcript items, files, or diffs
- host-owned meta-properties:
  - advisory-only result posture by default
  - target identity
  - scope identity
  - request provenance
  - return status and evidence rendering

### `workflow_dock`

- class: surface artifact
- plan: `build`
- role: first-class ADEU workflow launcher and run-state surface using existing repo
  workflow semantics
- host-owned meta-properties:
  - template identity
  - launch intent
  - run status truth
  - returned evidence placement

### `workbench_layout_engine`

- class: support artifact
- plan: `import_or_compose`
- role: keep the transcript primary while allowing secondary artifacts to appear in
  docked or peek form without ad hoc layout trial-and-error
- host-owned meta-properties:
  - main conversation width floor
  - context pane bounds
  - non-overlap rules
  - same-context reachability guarantees

## Host-Owned Semantic Rules

Even when secondary artifacts are imported from OSS later, the ADEU host still owns:

- what counts as authoritative vs advisory
- what counts as a handoff or dispatch boundary
- how custom Codex build identity is rendered
- how `config.toml` provenance and effective profile are rendered
- how review returns are classified
- how workflow returns are classified
- where evidence appears before side-effect-bearing actions

## Workbench Topology

### Workbench Root

- `bounded_workbench_id`: `adeu_codex_desktop_workbench`

### Regions

- `workspace_region`
  - session list and bounded project tree
- `primary_conversation_region`
  - transcript and composer
- `context_artifact_region`
  - docked file, diff, terminal, git, review, and workflow detail surfaces
- `status_boundary_region`
  - provider/build/config/write posture and operational status
- `transient_overlay_region`
  - quick file peek, quick diff peek, bounded review-target picker

### Lanes

- `workspace_lane`
  - recent sessions
  - workspace/project selector
  - compact file tree
- `conversation_lane`
  - transcript
  - message actions
- `composer_lane`
  - prompt entry
  - attach/select context
- `artifact_action_lane`
  - terminal
  - diff
  - git
  - file explorer
  - review inbox
  - workflow dock
- `context_artifact_lane`
  - docked secondary artifact tabs
- `workflow_lane`
  - ADEU-specific workflows and run status
- `status_boundary_lane`
  - provider/build/config/write posture
  - session health
  - review/workflow dispatch status
- `trust_boundary_lane`
  - explicit notices for write enablement, external review dispatch, and workflow launch

### Action Clusters

- `conversation_actions`
  - resend
  - copy
  - send_for_review
- `artifact_toggle_actions`
  - open_file_tree
  - open_terminal
  - open_diff
  - open_git
- `session_actions`
  - start_session
  - stop_session
  - restart_with_profile
  - toggle_writes
- `workflow_actions`
  - open_workflow_dock
  - run_adeu_workflow
- `dispatch_actions`
  - send_message_for_review
  - send_file_for_review
  - send_diff_for_review

### State Surfaces

- `codex_runtime_state_surface`
- `config_profile_state_surface`
- `review_dispatch_state_surface`
- `workflow_run_state_surface`
- `file_selection_state_surface`
- `artifact_visibility_state_surface`
- `trust_warning_state_surface`

### Explicit Handoff Boundaries

The primary handoff boundaries are:

- enabling writes
- dispatching content to external review targets
- launching ADEU workflows that perform side effects or cross-process execution

These should never look like ordinary transcript-local buttons.

## Same-Context Reachability Rules

Allowed same-context reveals:

- open terminal in the docked context region
- open diff in the docked context region
- open file reader in the docked context region
- open file quick peek as bounded overlay
- open review target picker as bounded overlay
- open workflow dock in the docked context region

Forbidden context breaks for v0:

- route changes to separate terminal/diff/review pages
- detached secondary windows as the default way to inspect evidence
- losing transcript visibility when opening file, diff, review, or workflow surfaces

## Key Interaction Contracts

### 1. Start Or Restart Session With Custom Build

Goal:

- use a custom Codex build and selected `config.toml` profile explicitly

Preconditions:

- selected build identity is known
- selected config path/profile is known

Visible consequences:

- active provider/build/config surface updates immediately
- session id and reachability state become visible
- any mismatch between configured profile and effective runtime state stays visible in
  the status boundary region

### 2. File Tree To Quick Peek Or Docked Reader

Goal:

- inspect code or config context without making file editing primary

Preconditions:

- file selected from tree, search, or transcript reference

Visible consequences:

- `peek` opens bounded overlay for short inspection
- `open in context pane` docks the file reader as a standard secondary artifact
- transcript remains visible

### 3. Artifact Buttons For Terminal / Diff / Git

Goal:

- preserve a Codex-like minimalist shell while keeping secondary operator tools one step
  away

Preconditions:

- none beyond session/workspace availability for the artifact

Visible consequences:

- artifact opens in the context region or remembered docking target
- status boundary region reflects whether the artifact is connected, stale, unavailable,
  or read-only

### 4. Right-Click `Send For Review` On Reply

Goal:

- dispatch one reply or reply selection to an external reviewer or workflow

Preconditions:

- review target selected
- scope bundle generated from the chosen transcript item

Visible consequences:

- request appears in `review_dispatch_state_surface`
- target identity, request id, and status are visible
- returned review attaches back to the originating reply as advisory evidence

### 5. Right-Click `Send For Review` On File Or Diff

Goal:

- dispatch one file or diff selection for external review

Preconditions:

- file or diff scope is explicit
- provenance is attached

Visible consequences:

- dispatch summary appears in the status boundary region and review surface
- returned review is same-context reachable from the file/diff tab and from the origin
  point that launched it

### 6. ADEU Workflow Launch

Goal:

- launch repo-native workflows already reachable via the Codex wiring

Grounded current examples:

- `adeu.run_workflow`
- `adeu.compile_brokered_reflexive_execution`
- `adeu.read_evidence`

Preconditions:

- workflow template or action chosen
- input payload made explicit

Visible consequences:

- workflow run appears in the workflow dock
- status, evidence, and returned artifacts stay same-context reachable

## Harness And Config Surface

This workbench must include one explicit surface for custom Codex build wiring.

It should show:

- active Codex binary/build identity
- active provider identity
- active config path
- active profile label if one exists
- write posture
- app-server availability
- session id

It should allow:

- selecting a saved launch profile
- revealing effective config values
- restarting with a different build/profile combination

It should not default to:

- raw free-form `TOML` editing in the main conversation lane

Better v0 posture:

- structured profile picker
- effective-config preview
- optional raw config inspector in a secondary reader

## Review Routing Contract

The review system should be modeled as a bounded artifact, not a loose context-menu
gimmick.

Each review dispatch should bind:

- `origin_kind`
  - reply
  - file
  - diff
- `origin_ref`
- `target_profile`
  - external model or workflow identity
- `payload_scope`
  - exact message/file/diff selection
- `request_id`
- `status`
- `returned_artifact_refs`

Default truth posture:

- returned reviews are `advisory`
- they may inform operator judgment
- they may not silently override local session authority

## Wireframe

```text
+--------------------------------------------------------------------------------------+
| Session / Build / Config / Writes / App Server / Review+Workflow Status              |
+----------------------+-------------------------------------------+---------------------+
| Sessions + Project   | Transcript                                | Context Artifacts   |
|                      |                                           |                     |
| - recent chats       | [reply bubble]  (...) Send For Review     | [Files] [Diff]      |
| - workspace switch   | [reply bubble]  (...) Send For Review     | [Terminal] [Git]    |
| - compact file tree  |                                           | [Review] [Workflow] |
|   (...) review       |                                           |                     |
|                      |-------------------------------------------| file / diff / term  |
|                      | Composer                                  | review / workflow   |
|                      | [ prompt input......................... ] | detail surface      |
|                      | [attach] [tree] [diff] [term] [git]      |                     |
|                      | [workflow] [send]                         |                     |
+----------------------+-------------------------------------------+---------------------+
| Trust Boundary Notices: enable writes / external review dispatch / workflow handoff   |
+--------------------------------------------------------------------------------------+
```

## Future OSS Hunter Brief

The later artifact hunter should search against these requirement shapes, not against
raw names only.

### `desktop_host_shell`

- native context menu support
- local child-process bridge
- native filesystem access
- robust PTY compatibility
- bounded dock/overlay integration

### `file_tree_surface`

- read-only explorer posture
- context-menu hooks
- lazy loading
- selection callbacks

### `file_quick_viewer`

- read-only syntax-aware rendering
- bounded overlay mode
- docked mode
- provenance hooks for review dispatch

### `terminal_surface`

- PTY-backed
- theme-neutral semantic host wrapping
- selection and copy support
- session-binding hooks

### `diff_surface`

- unified and side-by-side modes
- read-only posture
- selection hooks
- file provenance hooks

## Governed Enactment Burdens

This design run exposed recurring support-surface needs.

### `lawful_required`

- `harness_profile_surface`
  - without one explicit surface for build/config/write posture, the operator would have
    to infer which Codex build and config are actually active
- `review_dispatch_packet_builder`
  - without one bounded dispatch artifact, `Send For Review` becomes hidden side-effect
    glue rather than lawful explicit handoff

### `reliable_required`

- `context_action_bus`
  - transcript replies, files, and diffs all need one consistent context-action grammar
    for review dispatch and artifact opening
- `artifact_visibility_router`
  - the workbench needs a stable rule for peek vs docked artifact opening so same-context
    reachability does not drift ad hoc

### `performance_only`

- `layout_constraint_engine`
  - useful for keeping the conversation lane primary while bounding the context region,
    but not required for lawful design reasoning

## Closeout

This design keeps the workbench minimalist and Codex-centered, but it does not let the
chat lane swallow the actual ADEU operator needs.

The transcript stays primary.

The secondary artifacts stay bounded.

The custom build/config surface stays explicit.

Review dispatch and ADEU workflows become first-class governed artifacts instead of
ambient side channels.
