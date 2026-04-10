# Draft ADEU Codex Desktop Workbench Attempt Reviews v0

Status: working review bundle for parallel implementation assessment.

Authority layer: support.

This document assesses parallel implementation attempts against
`docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md`.
It records observed checkpoint quality and spec alignment. It does not mint shipping
authorization by itself.

## Run Stance

- `task_mode`: `review`
- `execution_mode`: `governed_enactment`
- `grounding_status`: `repo_grounded`
- `implementation_inspection_status`: `implementation_inspected`

## Review Method

- inspect the governing draft and the realized implementation together
- distinguish real host/runtime wiring from hard-coded placeholder posture
- prefer findings that affect truthful state rendering, authority boundaries, and
  same-context evidence reachability
- treat checkpoint reviews as supersedable by later follow-up revisions

## Attempt Register

1. `gemini-codex-workbench`: reviewed at initial checkpoint and three follow-up checkpoints
2. `opus-codex-workbench`: reviewed at initial checkpoint and three follow-up checkpoints
3. `gptpro-codex-workbench`: reviewed from imported baseline and modified zip snapshots plus one verification/fix follow-up
4. `gpt54-codex-workbench`: reviewed at initial checkpoint and two follow-up checkpoints

## Gemini Review

Assessment summary:

- this is an intermediate checkpoint rather than a spec-complete implementation
- the attempt does contain real Electron host wiring for file reads, directory reads,
  and a PTY-backed terminal
- it does not yet satisfy the governing ADEU desktop workbench draft because the
  truthful session boundary, typed review/workflow surfaces, and bounded trust posture
  are still missing or replaced by placeholders

### Findings

1. `critical`: the core ADEU review/workflow contract is still absent, so the attempt
   does not implement the spec's primary dispatch surfaces.
   Evidence:
   `apps/gemini-codex-workbench/electron/preload.js:3-11` exposes only `readDir`,
   `readFile`, and terminal IPC.
   `apps/gemini-codex-workbench/src/App.tsx:215-260` seeds the transcript with fixed
   placeholder messages and provides a composer/send row that is not wired into a live
   operator loop.
   `apps/gemini-codex-workbench/src/App.tsx:228-260` renders a `Send For Review`
   button and a send button, but neither is connected to typed review routing,
   workflow launch, returned evidence, or run-state surfaces.
   `apps/gemini-codex-workbench/src/App.tsx:266-309` offers only `Terminal`,
   `Diff Viewer`, and `File Preview` tabs, with no git surface and only placeholder
   diff content.
   Spec references:
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:237-259`,
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:448-503`.

2. `critical`: the status boundary counterfeits runtime truth instead of binding to
   actual provider, config, session, write, or app-server state.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:145-190` keeps write posture in local
   React state and hard-codes `Profile: gemini-3.1-pro-high` plus
   `App Server: Connecting...`.
   `apps/gemini-codex-workbench/src/App.tsx:205-239` hard-codes a recent session id
   and transcript messages rather than reflecting live session state or returned
   evidence.
   No ADEU/Codex state calls such as `adeu.get_app_state`, policy selection, session
   start/stop, or config/build identity appear anywhere in the attempt.
   Spec references:
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:172-181`,
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:504-520`,
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:564-579`.

3. `high`: the terminal surface is wired as an ungated full interactive shell, which
   conflicts with the draft's bounded trust posture and explicit handoff discipline.
   Evidence:
   `apps/gemini-codex-workbench/electron/main.js:84-123` spawns a PTY-backed shell in
   the repo root and forwards raw input/output with no visible read-only vs
   interactive posture, no session binding, and no trust warning.
   `apps/gemini-codex-workbench/src/App.tsx:68-119` mounts the terminal directly once
   the tab is opened.
   `apps/gemini-codex-workbench/src/App.tsx:249-255` treats terminal opening as an
   ordinary composer-adjacent toggle rather than a clearly bounded secondary artifact.
   Spec references:
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:205-213`,
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:368-387`,
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:609-614`.

4. `high`: the advertised launch path is not robust in the current repo environment,
   so the attempt does not presently satisfy its own "`npm run electron:dev` gives you
   a fully functional skeleton" claim.
   Evidence:
   `apps/gemini-codex-workbench/package.json:12-13` launches Electron directly.
   `apps/gemini-codex-workbench/electron/main.js:1` imports named exports from
   `electron` without guarding against the repo shell's `ELECTRON_RUN_AS_NODE=1`
   environment.
   In this workspace, `npm run electron:dev` fails with:
   `SyntaxError: The requested module 'electron' does not provide an export named 'BrowserWindow'`.
   The app does boot under `env -u ELECTRON_RUN_AS_NODE xvfb-run -a npm run electron:dev`,
   which shows the missing launcher guard is the concrete issue.

5. `medium`: the filesystem bridge is not actually bounded to the workspace root.
   Evidence:
   `apps/gemini-codex-workbench/electron/main.js:55-78` joins user-provided paths onto
   `ROOT_DIR` with no normalization or escape check, so `..` traversal can escape the
   intended repo root.
   This is materially weaker than the draft's read-only project tree posture and makes
   the file viewer broader than the claimed bounded artifact surface.
   Spec references:
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:183-200`,
   `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md:595-607`.

6. `medium`: the attempt is not build-clean yet, which reinforces that this is a
   checkpoint rather than a shippable pass.
   Evidence:
   `npm run build` fails because `apps/gemini-codex-workbench/src/App.tsx:1` imports
   `React` but never uses it.
   `npm run lint` fails on `apps/gemini-codex-workbench/src/App.tsx:11`,
   `apps/gemini-codex-workbench/src/App.tsx:21`,
   `apps/gemini-codex-workbench/src/App.tsx:23`,
   `apps/gemini-codex-workbench/src/App.tsx:32`,
   `apps/gemini-codex-workbench/src/App.tsx:108`, and
   `apps/gemini-codex-workbench/src/App.tsx:148` due to `any`, unused variables, and
   empty catch blocks.

7. `low`: the handoff/docs claim is incomplete.
   Evidence:
   `apps/gemini-codex-workbench/README.md:1-73` is still the default Vite template,
   and no walkthrough document exists in the repo at this checkpoint.

### Checks Run

- `npm run build`
  Result: failed with a TypeScript unused-import error in `src/App.tsx`.
- `npm run lint`
  Result: failed with 8 lint errors in `src/App.tsx`.
- `timeout 20s xvfb-run -a npm run electron:dev`
  Result: failed in this repo shell because the Electron launch path does not guard
  against `ELECTRON_RUN_AS_NODE=1`.
- `timeout 18s env -u ELECTRON_RUN_AS_NODE xvfb-run -a npm run electron:dev`
  Result: Electron booted and stayed alive until the timeout kill, which confirms the
  app has a real host shell but an unguarded launch path.

### Suggested Follow-Up For Gemini

1. replace all hard-coded status boundary and transcript/session placeholders with live
   ADEU/Codex state wiring
2. add the missing `review_routing_surface` and `workflow_dock`, including target
   identity, request id, status, evidence, and advisory-only return posture
3. bound the terminal artifact explicitly by trust posture, session binding, and visible
   warnings instead of exposing an unqualified repo shell
4. guard the Electron launch path against `ELECTRON_RUN_AS_NODE` in the same way a
   robust desktop app here now must
5. constrain filesystem reads to the selected workspace root and keep the viewer in
   clear read-only posture
6. make the attempt build-clean and lint-clean before the next review pass

## Gemini Review Update

Assessment summary:

- the follow-up materially improves the attempt
- `npm run lint` now passes
- `npm run build` now passes
- `npm run electron:dev` now launches correctly in this repo shell through the dedicated
  Electron launcher
- path containment and basic git artifact surfaces are now real
- despite that progress, the implementation still stops short of the draft's required
  governed review/workflow and session-control surfaces

### Findings

1. `high`: the review/workflow surfaces are still representational rather than real
   governed handoff surfaces.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:263-266` handles `Send For Review` by only
   switching tabs and logging to the console.
   `apps/gemini-codex-workbench/src/App.tsx:332-339` renders the review action as an
   active advisory button even though no review target picker, target identity, request
   id, scope summary, provenance, or returned evidence exists.
   `apps/gemini-codex-workbench/src/App.tsx:419-436` renders review/workflow tabs as
   unavailable placeholders rather than request/state surfaces.
   This is more truthful than the first checkpoint, but it still misses the draft's
   explicit review-routing and workflow-dock contract.

2. `high`: the session-control surface remains incomplete against the draft.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:272-297` exposes only profile
   unconfigured/unavailable state plus a local terminal-write toggle.
   `apps/gemini-codex-workbench/src/App.tsx:311-315` shows only a static note in the
   session area.
   The draft requires start/stop/restart session controls plus visible provider/build/
   config identity, session id, write posture, and app-server availability. The update
   improves truthfulness, but those required surfaces still are not present.

3. `medium`: the terminal integration has a real runtime bug: toggling write mode
   re-creates the PTY bridge and leaks output listeners.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:93-146` mounts the terminal effect on
   `interactiveEnabled`, so changing write mode triggers `spawnPty()` again.
   `apps/gemini-codex-workbench/electron/preload.js:8-10` registers terminal listeners
   but exposes no unsubscribe path.
   Together, that means write-mode toggles can reset shell state and accumulate duplicate
   terminal output handlers over time.

4. `medium`: the workspace and same-context evidence surfaces are still only partially
   implemented.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:302-316` has a tree and a session note, but
   no workspace selector or current-session relevance markers.
   `apps/gemini-codex-workbench/src/App.tsx:151-173` implements only a docked file
   reader, with no bounded quick-peek overlay mode.
   `apps/gemini-codex-workbench/src/App.tsx:419-436` does not attach review/workflow
   evidence back to origin points because no request artifacts exist yet.

### Resolved Since Prior Review

- Electron launch is now guarded against `ELECTRON_RUN_AS_NODE` via
  `apps/gemini-codex-workbench/scripts/launch-electron.js`.
- filesystem reads are now bounded to the repo root via the containment check in
  `apps/gemini-codex-workbench/electron/main.js`
- git status and diff are now wired through the Electron host bridge
- the attempt is now lint-clean and build-clean
- the README is no longer the default Vite template

### Checks Run

- `npm run lint`
  Result: passed.
- `npm run build`
  Result: passed.
- `timeout 18s xvfb-run -a npm run electron:dev`
  Result: launched successfully in this repo shell; the final timeout kill produced the
  expected process-shutdown noise, but startup itself succeeded.

## Gemini Review Update 2

Assessment summary:

- this is the strongest Gemini checkpoint so far
- the follow-up closes the previous write-toggle remount bug, adds local review request
  artifacts, attaches review state back to transcript origin messages, and adds a
  bounded quick-peek file overlay
- `npm run lint`, `npm run build`, and `npm run electron:dev` all still succeed
- despite that progress, the app is still not spec-faithful overall because the
  workflow dock remains mostly absent and review dispatch is still materially narrower
  than the governing draft

### Findings

1. `high`: the workflow dock still is not a real governed handoff surface.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:554-560` renders only a static unavailable
   note plus a disabled button.
   There is still no workflow template identity, launch request token, launch intent
   summary, run-state surface, or returned evidence placement.
   The draft requires a first-class workflow launcher and run-state surface even when
   unavailable state must be rendered truthfully.

2. `high`: review routing is improved but still materially narrower than the draft's
   typed dispatch contract.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:317-326` only creates local review request
   artifacts from `ChatMessage` origins.
   `apps/gemini-codex-workbench/src/App.tsx:434-441` wires `Send For Review` only from
   transcript system messages.
   No file-surface or diff-surface review dispatch entry exists anywhere in the app.
   `apps/gemini-codex-workbench/src/App.tsx:250-255` stores only `id`, `originId`,
   `scope`, `status`, and `createdAt`, while `apps/gemini-codex-workbench/src/App.tsx:536-542`
   renders target and posture as fixed display text rather than request-owned fields.
   This is a meaningful step forward from the last checkpoint, but it still falls short
   of a typed handoff surface from transcript, files, and diffs.

3. `medium`: the session-control surface is now visible, but still only partially
   truthful against the draft.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:334-349` shows disabled start/stop/restart
   controls plus profile and app-server unavailable state, but it still omits session
   id, session status, build identity, and config identity.
   `apps/gemini-codex-workbench/src/App.tsx:375-379` keeps the recent-session area as a
   static unavailable note rather than a session-boundary surface.

4. `medium`: the prior write-toggle respawn bug is fixed, but terminal listener cleanup
   remains incomplete in development.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:114-172` no longer remounts the terminal
   effect on `interactiveEnabled`, which resolves the previously reviewed toggle bug.
   However, `apps/gemini-codex-workbench/electron/preload.js:9-10` still registers
   terminal listeners without any unsubscribe path, and
   `apps/gemini-codex-workbench/src/main.tsx:6-8` runs the app in React `StrictMode`
   during development.
   Inference:
   that combination can still duplicate renderer-side terminal listeners on initial dev
   remounts, so the lifecycle hardening is improved but not fully complete.

### Resolved Since Prior Review

- local review request artifacts now carry request ids and status rather than just
  switching tabs
- review state is now attached back to transcript origin messages through inline pills
- the file tree now supports bounded quick-peek overlays without route changes
- the write-toggle no longer re-spawns the PTY on each change
- session controls are now visibly present, even though backend-driven state remains
  unavailable

### Checks Run

- `npm run lint`
  Result: passed.
- `npm run build`
  Result: passed.
- `timeout 20s xvfb-run -a npm run electron:dev`
  Result: launched successfully in this repo shell; the timeout kill ended the run and
  produced expected shutdown noise, but startup itself succeeded.

## Gemini Review Update 3

Assessment summary:

- this checkpoint closes almost all of the previously targeted review gaps
- workflow requests now have real local request state
- review dispatch now exists from transcript, file, and diff/status artifact surfaces
- terminal listener cleanup now exists in the preload bridge and renderer teardown
- `npm run lint`, `npm run build`, and `npm run electron:dev` all still succeed
- despite that progress, I am not marking the variant fully spec-faithful yet because
  one exposed review action still misstates provenance and the session boundary still
  omits the draft's custom build/profile selection surface

### Findings

1. `medium`: the exposed Git Status review action counterfeits request provenance by
   recording status-origin reviews as `diff` requests.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:300-308` limits `ReviewRequest.originKind`
   to `transcript`, `file`, or `diff`.
   `apps/gemini-codex-workbench/src/App.tsx:276-283` uses `GitViewer` for both
   `status` and `diff`, but always dispatches `onRequestReview('diff', originId, ...)`.
   `apps/gemini-codex-workbench/src/App.tsx:276-277` also filters attachments only on
   `originKind === 'diff'`.
   The status review button is real and useful, but once exposed it should not mislabel
   provenance.

2. `medium`: the session boundary is now much more complete, but it still does not
   expose the custom build/profile selection surface called for by the draft.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:416-451` shows disabled start/stop/restart
   controls plus labels for session id, session status, profile, build/config, and
   app-server state.
   However, there is still no visible selector or bounded control for custom build /
   profile choice, and the recent-session area remains an unavailable-state note rather
   than a concrete empty-state session list in
   `apps/gemini-codex-workbench/src/App.tsx:466-475`.

### Resolved Since Prior Review

- review dispatch now exists from transcript, file, and git/diff artifact surfaces
- request artifacts now carry `originKind`, `originId`, `target`, `posture`, and status
- workflow dock now creates local workflow request records with ids, template identity,
  intent, status, and explicit not-executed posture
- terminal listener cleanup is now exposed in
  `apps/gemini-codex-workbench/electron/preload.js`
- terminal write-toggle behavior remains stable without PTY respawn on toggle

### Checks Run

- `npm run lint && npm run build`
  Result: passed.
- `timeout 20s xvfb-run -a npm run electron:dev`
  Result: launched successfully in this repo shell; timeout shutdown produced expected
  Electron close noise, but startup itself succeeded.

## Gemini Review Update 4

Assessment summary:

- this pass was a direct source-and-check sync after the hot-context sub-agent repro
- the hard gates still hold: `npm run lint`, `npm run build`, and `npm run electron:dev`
  all still pass
- however, the current review bundle had drifted slightly optimistic on residual scope
- I am keeping Gemini at `checkpoint_4` and `near_spec`, but the remaining gaps are
  broader than one provenance bug plus one selector omission

### Findings

1. `medium`: the harness/profile surface is still materially incomplete against the
   draft.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:416-451` shows disabled
   start/stop/restart controls plus passive `Session ID`, `Session Status`, `Profile`,
   `Build/Config`, and `App Server` labels.
   However, there is still no explicit provider field, no config-path or
   effective-config preview, no saved profile picker, and no bounded
   `restart_with_profile` style surface. The status lane is truthful, but still too
   passive relative to the draft's launch/config contract.

2. `medium`: the workspace lane is still only partially closed against the draft.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:36-97` gives the tree selection and quick
   peek affordances, and `apps/gemini-codex-workbench/src/App.tsx:457-475` shows the
   workspace tree plus a recent-session note.
   But there is still no workspace/project selector, no current-session relevance
   treatment in the tree, no concrete empty-state recent-session list, and no direct
   tree-level `Send For Review` entry.

3. `medium`: review dispatch still compresses target and provenance semantics more than
   the draft allows.
   Evidence:
   `apps/gemini-codex-workbench/src/App.tsx:382-393` records every review request with
   the fixed target `[Unconfigured Backend]` and no bounded target-selection step.
   `apps/gemini-codex-workbench/src/App.tsx:250-283` still routes Git Status review
   launches through `originKind: 'diff'`, and
   `apps/gemini-codex-workbench/src/App.tsx:300-309` still limits
   `ReviewRequest.originKind` to `transcript`, `file`, or `diff`.
   So the surface is truthful about backend unavailability, but it still compresses
   both target identity and status-origin provenance.

### Checks Run

- `npm run lint`
  Result: passed.
- `npm run build`
  Result: passed.
- `timeout 20s xvfb-run -a npm run electron:dev`
  Result: launched successfully in this repo shell; timeout shutdown produced the
  expected Electron close noise after successful startup.

## Opus Review

Assessment summary:

- this is a polished web prototype rather than a desktop-native ADEU workbench
- it reproduces much of the desired visual topology
- it does not satisfy the governing draft because the host shell, session/runtime
  surfaces, and artifact behaviors are simulated rather than grounded

### Findings

1. `critical`: this variant is not a standalone desktop application at all.
   Evidence:
   `apps/opus-codex-workbench/package.json:7-10` exposes only `vite` dev/build/preview
   scripts and has no Electron or native host runtime.
   `apps/opus-codex-workbench/index.html:1-40` is a browser page booting
   `apps/opus-codex-workbench/src/main.js`.
   `apps/opus-codex-workbench/src/main.js:25-124` is pure DOM bootstrap code with no native
   host bridge, preload, IPC, filesystem access, or child-process wiring.
   This misses the draft's `desktop_host_shell` requirement.

2. `critical`: the implementation counterfeits real runtime behavior across the core
   ADEU surfaces.
   Evidence:
   `apps/opus-codex-workbench/src/mock-api.js:1-6` explicitly states the API layer simulates
   the Codex/ADEU calls.
   `apps/opus-codex-workbench/src/mock-api.js:20-44` fabricates session start and runtime
   connection state.
   `apps/opus-codex-workbench/src/mock-api.js:103-125` fabricates `adeu.get_app_state`.
   `apps/opus-codex-workbench/src/mock-api.js:176-245` fabricates workflow execution and
   evidence bundles.
   `apps/opus-codex-workbench/src/mock-api.js:249-279` fabricates assistant responses.
   `apps/opus-codex-workbench/src/mock-api.js:283-326` fabricates review dispatch completion.
   The draft requires truthful state rendering and explicit unavailable posture rather
   than simulated success for these governed surfaces.

3. `high`: the main chat loop is functionally blocked because there is no wired
   session-control surface despite the draft requiring one.
   Evidence:
   `apps/opus-codex-workbench/src/components/conversation.js:39-60` only enables send when
   `sessionStatus === 'running'`.
   `apps/opus-codex-workbench/src/state.js:15` initializes `sessionStatus` to `idle`.
   `apps/opus-codex-workbench/src/components/status-boundary.js:29-89` renders only status
   indicators plus a writes toggle; there are no start/stop/restart controls.
   `apps/opus-codex-workbench/src/mock-api.js:20-44` defines `startSession()`, but no UI
   path invokes it.
   That means the transcript starts with a welcome message but the operator cannot
   actually begin a live session from the surface.

4. `high`: file provenance and same-context evidence reachability are materially broken
   by the flattened mock file model.
   Evidence:
   `apps/opus-codex-workbench/src/components/workspace-sidebar.js:47-74` collapses each node
   path to `node.name`, discarding parent directories.
   `apps/opus-codex-workbench/src/components/workspace-sidebar.js:88-115` then stores only
   that flattened name in `selectedFile` and `peekFile`.
   `apps/opus-codex-workbench/src/mock-api.js:392-399` only contains content mappings for a
   handful of top-level filenames and returns generic placeholder text for most nested
   files.
   This loses required file provenance and makes review dispatch from files weaker than
   the draft requires.

5. `high`: review and workflow evidence are not attached back to the origin surfaces in
   the way the draft requires.
   Evidence:
   `apps/opus-codex-workbench/src/components/conversation.js:83-89` has a provision to render
   `msg.reviewReturn`, but no code ever sets it.
   `apps/opus-codex-workbench/src/components/review-routing.js:36-77` renders separate
   dispatch history only.
   `apps/opus-codex-workbench/src/components/file-viewer.js:49-58` and
   `apps/opus-codex-workbench/src/components/diff-surface.js:44-50` can launch review, but
   returned review is not made same-context reachable from the origin file/diff surface.
   `apps/opus-codex-workbench/src/components/workflow-dock.js:90-130` renders evidence detail
   only inside the workflow tab rather than attaching it back to launch origin surfaces.

6. `medium`: the terminal surface is only a simulated terminal and overstates its
   relation to the host/runtime.
   Evidence:
   `apps/opus-codex-workbench/src/components/terminal-surface.js:7-16` seeds fixed terminal
   lines.
   `apps/opus-codex-workbench/src/components/terminal-surface.js:63-75` returns canned
   command responses or a `"simulated command (mock terminal)"` string.
   The draft permits bounded terminals, but not counterfeit PTY-backed host behavior
   presented as if it were real.

### Checks Run

- `npm run build`
  Result: passed.
- `timeout 15s npm run dev -- --host 127.0.0.1`
  Result: Vite served successfully in the browser environment.

### Current Verdict

- `preliminary_verdict`: `intermediate`
- note:
  the variant is visually coherent and topology-aware, but it should currently be
  treated as a browser mock/prototype rather than a spec-faithful desktop workbench

## Opus Review Update

Assessment summary:

- this follow-up is a major improvement over the original Opus browser mock
- the variant is now a real Electron desktop app with a preload bridge, real
  filesystem/git/terminal wiring, and truthful unavailable posture for ADEU backend
  surfaces
- `npm run build` and `npm run electron:dev` now work in this repo environment
- despite that progress, it remains intermediate because one trust-boundary bug and a
  few contract gaps still keep it below the leading implementations

### Findings

1. `high`: the filesystem boundary is still scoped to the wrong root, so the new
   containment logic is broader than the intended repo workspace.
   Evidence:
   `apps/opus-codex-workbench/electron/main.js:30-31` sets `WORKSPACE_ROOT` to
   `path.resolve(__dirname, '../../..')`, which resolves to the parent `LexLattice`
   directory rather than the current repo root `odeu`.
   `apps/opus-codex-workbench/electron/main.js:90-100` then enforces containment relative
   to that broader root.
   This is materially better than the original unbounded mock, but it still means the
   file and git surfaces are bounded to the wrong workspace.

2. `medium`: the write-posture control in the status boundary still mints a misleading
   global capability signal.
   Evidence:
   `apps/opus-codex-workbench/src/components/status-boundary.js:101-136` toggles
   `writesAllowed` and emits a trust notice claiming file modifications are permitted.
   But the only real side-effectful surface is the terminal, and its actual write mode
   is separately controlled in
   `apps/opus-codex-workbench/src/components/terminal-surface.js:64-117`.
   The result is two different write signals, with the status-boundary toggle not
   actually governing the PTY or any other host-side mutation path.

3. `medium`: same-context origin attachment is still only partial.
   Evidence:
   `apps/opus-codex-workbench/src/components/conversation.js:77-96` has a slot for
   `msg.reviewRequestId`, but no code path sets it when a review request is created.
   `apps/opus-codex-workbench/src/host-bridge.js:292-313` records review requests only in
   the shared review history plus a system message.
   `apps/opus-codex-workbench/src/components/file-viewer.js:73-98` and
   `apps/opus-codex-workbench/src/components/diff-surface.js:33-60` can launch review from
   file and diff origins, but returned state remains only in the review dock at
   `apps/opus-codex-workbench/src/components/review-routing.js:51-99`.
   This is same-window reachable, but not as origin-tight as the governing draft aims
   for.

4. `medium`: one same-context artifact jump is still broken in practice.
   Evidence:
   `apps/opus-codex-workbench/src/components/git-status.js:97-106` opens changed files by
   setting `selectedFile` directly, but it does not call the real file-loading path.
   The file viewer expects `fileContent` to be populated through `selectFile(...)`, as
   seen in `apps/opus-codex-workbench/src/components/file-viewer.js:39-71`.
   So the git surface advertises a file jump that can leave the file pane stuck at a
   loading state.

5. `low`: provider/build/config surfaces are truthfully absent, but still not rendered
   as explicit unavailable fields.
   Evidence:
   `apps/opus-codex-workbench/src/components/status-boundary.js:60-79` omits those fields
   entirely when they are null instead of showing visible unavailable placeholders.
   This is better than counterfeit values, but still less explicit than the draft's
   preferred unavailable-state rendering.

### Resolved Since Prior Review

- the app is now a real Electron desktop host rather than a Vite-only browser app
- the launch path is guarded against `ELECTRON_RUN_AS_NODE` through
  `apps/opus-codex-workbench/scripts/launch-electron.js`
- the mock ADEU runtime layer is gone and review/workflow now use explicit local-only
  request records with `not_executed` status
- file paths are no longer flattened to basenames
- the terminal is real and PTY-backed, with explicit interactive gating and listener
  cleanup through the preload bridge

### Checks Run

- `npm run build`
  Result: passed.
- `timeout 20s xvfb-run -a npm run electron:dev`
  Result: Vite and Electron both launched successfully in this repo shell; the command
  then exited on the timeout kill with expected shutdown noise.

### Current Verdict

- `preliminary_verdict`: `intermediate`
- note:
  this is no longer just a browser mock. It is now a materially improved desktop
  checkpoint with truthful local-only posture, but the wrong workspace root, split
  write posture, and incomplete origin-linked review/file flows keep it below
  near-spec status.

## Opus Review Update 2

Assessment summary:

- this follow-up materially improves the Opus variant again
- the previously reviewed workspace-root bug, global-write-posture overclaim, broken
  git-to-file jump, omitted provider/build/config placeholders, and missing same-context
  review markers on reply/file/diff origins are now all corrected in the inspected code
- `npm run build` and `npm run electron:dev` both still succeed in this repo shell
- the remaining gaps are now concentrated in the harness/profile surface and in
  sidebar/file-tree completeness rather than in desktop-host correctness
- review context note:
  the user reported that the model ran out of quota after this corrective pass, so the
  remaining gaps may reflect an interrupted checkpoint rather than the intended final
  closure state

### Findings

1. `high`: the harness/profile surface still stops short of the draft's required custom
   build/config control surface.
   Evidence:
   `apps/opus-codex-workbench/src/components/status-boundary.js:33-35` reads only provider,
   build, and config values, and
   `apps/opus-codex-workbench/src/components/status-boundary.js:62-109` renders those fields
   plus basic session controls.
   But the draft requires visible app-server reachability, profile identity, and custom
   build/profile selection with restart semantics.
   `apps/opus-codex-workbench/src/state.js:29-33` still carries `profileLabel` and
   `appServerAvailable` in state, yet
   `apps/opus-codex-workbench/src/components/status-boundary.js` never renders either one and
   exposes no build/profile picker or effective-config preview.

2. `medium`: the workspace/sidebar contract remains partial against the draft.
   Evidence:
   `apps/opus-codex-workbench/src/components/workspace-sidebar.js:23-40` shows only the
   current session and does not expose recent sessions.
   `apps/opus-codex-workbench/src/components/workspace-sidebar.js:43-63` renders the project
   tree but no workspace switch surface.
   `apps/opus-codex-workbench/src/components/workspace-sidebar.js:88-93` provides quick peek
   and open actions for files, but no direct tree-level `Send For Review` entry or
   current-session relevance markers.

3. `low`: review and workflow request history remains renderer-memory-only and does not
   survive relaunch.
   Evidence:
   `apps/opus-codex-workbench/src/state.js:56-66` stores review/workflow requests and pending
   review origin only in the in-memory state store, and no persistence layer is wired in
   `apps/opus-codex-workbench/src/host-bridge.js`.
   This is truthful and bounded, but it still leaves the audit/history posture lighter
   than the strongest reviewed variant.

### Resolved Since Prior Review

- `apps/opus-codex-workbench/electron/main.js:30-32` now binds the workspace root to the
  `odeu` repo root rather than the broader parent directory
- `apps/opus-codex-workbench/src/components/status-boundary.js:103-109` now scopes the write
  control truthfully to terminal interactivity rather than overstating global write
  authority
- `apps/opus-codex-workbench/src/components/git-status.js:97-107` now opens changed files via
  the real `selectFile(...)` path, so the file dock loads actual content
- `apps/opus-codex-workbench/src/components/status-boundary.js:62-81` now renders
  provider/build/config unavailable state explicitly instead of omitting those fields
- `apps/opus-codex-workbench/src/components/conversation.js:80-110`,
  `apps/opus-codex-workbench/src/components/file-viewer.js:72-120`, and
  `apps/opus-codex-workbench/src/components/diff-surface.js:33-86` now attach same-context
  review markers back to reply, file, and diff origins

### Checks Run

- `npm run build`
  Result: passed.
- `timeout 20s xvfb-run -a npm run electron:dev`
  Result: Vite and Electron both launched successfully in this repo shell; the command
  then exited on the timeout kill with expected shutdown noise only.

### Current Verdict

- `preliminary_verdict`: `near_spec`
- note:
  this variant is now materially stronger than its previous intermediate checkpoint and
  clears the desktop-host, filesystem, terminal, and truthful-unavailable-state gates
  cleanly. The remaining issues are narrower UX-contract omissions around
  harness/profile selection and sidebar completeness. Because the run appears to have
  ended on quota rather than on a declared final closure, those residuals look more like
  an interrupted checkpoint than a structural dead end.

## Opus Review Update 3

Assessment summary:

- this closure pass cleanly addresses the remaining checkpoint_3 residual set without
  widening the app beyond its bounded desktop-workbench posture
- the status boundary now exposes profile identity, app-server reachability, and a
  bounded profile/build/config intent surface with explicit restart semantics
- the sidebar now renders recent sessions, a truthful single-root workspace-switch
  disclosure, current-session review markers, and direct tree-level review entry points
- review/workflow request state now survives relaunch through persisted local state
- `npm run build` and `npm run electron:dev` still succeed after the closure pass

### Findings

1. `low`: workspace switching remains intentionally non-executable because this host is
   explicitly bound to one workspace root.
   Evidence:
   `apps/opus-codex-workbench/src/components/workspace-sidebar.js:68-81` renders a disabled
   switch control and states that the host is intentionally single-root.
   This is now a truthful bounded posture rather than a missing control, but it means
   the app still does not offer true multi-root switching.

2. `low`: request-history persistence is renderer-local rather than host-archived.
   Evidence:
   `apps/opus-codex-workbench/src/state.js:15-27` and
   `apps/opus-codex-workbench/src/state.js:176-203` persist review/workflow/session/profile
   slices through `localStorage`.
   `apps/opus-codex-workbench/src/host-bridge.js:64-81` archives recent-session metadata into
   that persisted renderer state.
   This closes relaunch survival, but it is still a lighter persistence posture than a
   host-owned audit archive.

### Resolved Since Prior Review

- `apps/opus-codex-workbench/src/components/status-boundary.js:95-197` now renders visible
  `Profile`, `App Server`, and bounded profile/build/config intent controls, including a
  custom draft surface and explicit `Apply + Restart` path
- `apps/opus-codex-workbench/src/components/workspace-sidebar.js:48-81` now renders recent
  sessions plus a truthful bounded workspace-switch disclosure
- `apps/opus-codex-workbench/src/components/workspace-sidebar.js:131-149` now adds direct
  tree-level review entry and current-session `R#` review markers for file origins
- `apps/opus-codex-workbench/src/state.js:15-27` and
  `apps/opus-codex-workbench/src/state.js:176-203` now persist review/workflow/session/profile
  slices across relaunch instead of keeping them renderer-memory-only

### Checks Run

- `npm run build`
  Result: passed.
- `timeout 25s xvfb-run -a npm run electron:dev`
  Result: Vite and Electron both launched successfully in this repo shell on the
  expected `5174` flow; the command then exited on timeout as expected.

### Current Verdict

- `preliminary_verdict`: `near_spec`
- note:
  the previous checkpoint_3 residual set is now closed. The remaining differences versus
  the GPT-5.4 Codex leading variant are bounded implementation choices rather than open
  correctness defects: workspace switching is intentionally disabled under the single-root
  host posture, and relaunch history persistence is renderer-local rather than
  host-archived.

## GPTPro Imported Snapshot Review

Assessment summary:

- this variant is materially more complete than the Opus browser mock and more grounded
  than the early Gemini checkpoints
- it adds a substantial `codex-workbench` surface plus real repo-access helpers and
  review/workflow wiring inside an imported `adeu-studio-main` snapshot
- it still fails the governing draft in two critical ways:
  - it is a web route inside the existing Studio app rather than a standalone
    desktop-native workbench
  - it exposes local repo and harness/config surfaces over plain Next routes, which
    collapses the intended host trust boundary

Source reviewed:

- baseline: `adeu-studio-main(6).zip`
- modified: `adeu-studio-codex-workbench-implemented.zip`

Both were unpacked into isolated temp directories and diffed with `git diff --no-index`
before code inspection.

### Findings

1. `critical`: this is not a standalone desktop application; it is a new route inside
   the existing Next web app.
   Evidence:
   `apps/web/package.json:6-15` exposes only `next dev`, `next build`, and
   `next start` for the app; there is no Electron or native desktop host runtime.
   `apps/web/src/app/codex-workbench/page.tsx:1-10` is a normal web route that renders
   `CodexWorkbenchClient`.
   This misses the draft's `desktop_host_shell` requirement and keeps the workbench
   web-primary rather than desktop-native.

2. `critical`: the added "desktop" server routes collapse the intended trust boundary
   by exposing repo contents, harness paths, and environment-derived config data over
   plain Next endpoints.
   Evidence:
   `apps/web/src/app/api/desktop/tree/route.ts:1-19`,
   `apps/web/src/app/api/desktop/file/route.ts:1-19`, and
   `apps/web/src/app/api/desktop/harness/route.ts:1-18` are direct GET routes with no
   authentication or local-host gating.
   `apps/web/src/app/lib/desktop/repo-access.ts:117-199` serves repo directory and file
   reads, while `apps/web/src/app/lib/desktop/repo-access.ts:299-330` returns absolute
   paths and environment summaries for Codex/config/evidence wiring.
   Direct helper execution during review returned a home-directory config path
   (`/home/rose/.codex/config.toml`), which confirms the harness surface can expose
   host-local paths rather than keeping them inside a native desktop boundary.

3. `high`: the review target selector is mostly representational, because review
   dispatch does not route to a target-specific backend surface.
   Evidence:
   `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:940-945` builds a
   review packet with `reviewTargetProfile`, and
   `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:955-961` records that
   target in UI state.
   But the actual remote call at
   `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:988-994` launches
   `adeu.run_workflow` only with the workflow dock's `templateId`; the chosen review
   target profile is not routed as an executable backend selector.
   That means the visible review target identity overstates what the dispatch path is
   actually honoring.

4. `medium`: same-context evidence reachability is still partial for file and diff
   origins.
   Evidence:
   file and transcript origins receive visible review counts in the workspace tree and
   transcript lane, but the selected file pane and diff pane do not attach returned
   review state back to those origin surfaces.
   `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:1410-1485` renders the
   diff surface with review launch controls but no attached review record or evidence
   return surface.
   `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:1585-1660` keeps the
   actual review records only in the review tab.

5. `low`: the newly added contract test is not wired into the package's default
   contract-test script.
   Evidence:
   `apps/web/tests/codex-workbench-contract.test.ts:1-67` adds the new test file, but
   `apps/web/package.json:13-15` still points `test:contracts` only at
   `tests/evidence-explorer-contract.test.ts`.
   The new test can pass when run directly, but it is not in the default script path.

### Checks Run

- `git diff --no-index --stat` between the unpacked baseline and modified snapshots
  Result: 17 changed files, 4393 insertions, 7 deletions.
- `cd apps/gptpro-codex-workbench && node scripts/gen-types.mjs`
  Result: passed via the new fallback, with a warning that
  `json-schema-to-typescript` was unavailable and committed generated files were reused.
- `cd apps/gptpro-codex-workbench && node --test tests/codex-workbench-contract.test.ts`
  Result: passed (5/5).
- direct helper smoke via `node --input-type=module`
  Result: `listRepoDirectory`, `readRepoFile`, `getHarnessSummary`,
  `runTerminalSnapshot`, and `buildDiffDocument` all executed successfully.
- full `next build`
  Result: not checked in this imported snapshot because dependencies were not installed
  in the unpacked temp repo.

### Current Verdict

- `preliminary_verdict`: `intermediate`
- note:
  this is a comparatively complete and more truthful web-grounded variant, but it is
  still not a spec-faithful desktop workbench because the host boundary is wrong and
  the new desktop routes would expose local repo/config state over HTTP.

## GPTPro Review Update 2

Assessment summary:

- this follow-up keeps the imported variant web-primary, so it still misses the
  governing draft's desktop-host requirement and still exposes the wrong trust boundary
- however, the `codex-workbench` chat/runtime lane now works end-to-end in its chosen
  web posture: the client handles the actual provider SSE schema, completed assistant
  turns render final text, and the initial hydration mismatch is removed
- the unpacked snapshot now also completes `next build`, so the prior `full build remains
  unverified` note is no longer current
- this materially strengthens the imported variant, but it does not change the overall
  `intermediate` verdict because the host boundary remains wrong

### Findings

1. `critical`: this is still not a standalone desktop application; it remains a route
   inside the existing Next web app.
   Evidence:
   `apps/web/package.json:6-15` still exposes only `next dev`, `next build`, and
   `next start`, and
   `apps/web/src/app/codex-workbench/page.tsx:1-10` still mounts the workbench as a
   normal web route.

2. `critical`: the imported variant still exposes repo and harness/config surfaces over
   plain Next routes, which collapses the intended host trust boundary.
   Evidence:
   `apps/web/src/app/api/desktop/tree/route.ts:1-19`,
   `apps/web/src/app/api/desktop/file/route.ts:1-19`, and
   `apps/web/src/app/api/desktop/harness/route.ts:1-18` remain direct web routes.
   `apps/web/src/app/lib/desktop/repo-access.ts:242-285` still resolves and returns
   host-local config candidates for that HTTP surface.

3. `high`: the visible review target selector is still only partially execution-bound.
   Evidence:
   `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:939-997` still records
   `reviewTargetProfile` in the packet and UI state, but dispatch executes
   `adeu.run_workflow` only with the current workflow template and prompt, not with a
   target-specific backend routing path.

4. `medium`: same-context evidence reachability is still partial for file and diff
   origins.
   Evidence:
   `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:1408-1480` renders file
   and diff review launch actions, while
   `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:1646-1665` keeps actual
   review records in the review tab rather than attaching them inline at the origin
   surface.

5. `low`: the package's default contract-test script still omits the dedicated
   `codex-workbench` contract test.
   Evidence:
   `apps/web/package.json:13-15` still points `test:contracts` only at
   `tests/evidence-explorer-contract.test.ts`, even though
   `apps/web/tests/codex-workbench-contract.test.ts:1-67` now exists and passes when run
   directly.

### Resolved Since Prior Review

- `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:449-479` and
  `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:1230-1284` now handle the
  actual provider SSE schema (`item/agentMessage/delta`, `item/started`,
  `item/completed`) and replace assistant turns with final completion text instead of
  leaving them blank in `STREAMING`
- `apps/web/src/app/codex-workbench/codex-workbench-client.tsx:281-288` now removes the
  initial `new Date()` hydration mismatch trigger from the welcome transcript seed
- `apps/web/src/app/lib/desktop/repo-access.ts:242-279` now preserves the typed harness
  candidate source literals cleanly enough for `next build` to pass

### Checks Run

- `cd apps/gptpro-codex-workbench && npm run lint`
  Result: passed.
- `cd apps/gptpro-codex-workbench && npm run build`
  Result: passed.
- `cd apps/gptpro-codex-workbench && npm run test:contracts`
  Result: passed (existing evidence-explorer contract suite).
- `cd apps/gptpro-codex-workbench && node --test tests/codex-workbench-contract.test.ts`
  Result: passed (5/5).
- runtime verification on `127.0.0.1:3101` with API `127.0.0.1:8101`
  Result: session start, write enable, and prompt send all worked; sending
  `Reply with exactly: OK` returned assistant text `OK` with terminal transcript status
  `DONE`.

### Current Verdict

- `preliminary_verdict`: `intermediate`
- note:
  this is now a materially stronger imported checkpoint than the initial review: it
  builds cleanly and the `codex-workbench` chat lane actually works in its chosen web
  posture. It still remains `intermediate` because the desktop host shell is absent and
  the public Next routes expose repo/harness surfaces over the wrong trust boundary.

## GPT-5.4 Codex Standalone Electron Review

Assessment summary:

- this is the strongest implementation reviewed so far and the current leading
  candidate
- it is a real standalone Electron workbench with a bounded host bridge, verified build
  and smoke launch, explicit launch-profile/session/write surfaces, and real ADEU
  runtime/tool/evidence wiring where available
- it follows the governing draft's transcript-first posture and keeps file, diff, git,
  workflow, review, and evidence surfaces same-context reachable without collapsing into
  terminal-first behavior
- despite that strength, I am not calling it fully spec-complete yet because the review
  target surface is only partially execution-bound, returned review/evidence state is
  not attached inline at origin surfaces, and failed dispatch/run attempts do not yet
  persist as negative request artifacts

### Findings

1. `medium`: returned review and workflow artifacts remain dock-reachable rather than
   origin-attached, which weakens the fastest same-context provenance trace from
   transcript, file, and diff sources.
   Evidence:
   `apps/gpt54-codex-workbench/src/renderer/app.ts:1048-1082` renders
   transcript items with `Send For Review`, but no inline request/evidence markers.
   `apps/gpt54-codex-workbench/src/renderer/app.ts:1192-1231` renders file
   and diff review launch controls, but again no attached return artifacts at the
   origin surface.
   `apps/gpt54-codex-workbench/src/renderer/app.ts:1103-1163` keeps review
   and workflow records in the docked artifact region instead.
   This still satisfies same-window reachability, but it is not as provenance-tight as
   inline origin attachments.

2. `medium`: the visible review target profile is only partially execution-bound.
   Evidence:
   `apps/gpt54-codex-workbench/src/renderer/app.ts:511-558` composes the
   selected target's guidance into the prompt and records `targetProfileId`, but the
   actual execution path still calls `adeu.run_workflow` with the currently selected
   workflow template id rather than routing review targets to distinct backend lanes.
   This is materially better than a decorative selector because it affects prompt
   content and recorded intent, but the target identity still overstates how much the
   backend execution path changes.

3. `low`: failed review/workflow attempts are surfaced as errors, but they do not
   persist as explicit failed request artifacts in the review/workflow records.
   Evidence:
   `apps/gpt54-codex-workbench/src/renderer/app.ts:236-249` captures task
   failures into the error banner.
   `apps/gpt54-codex-workbench/src/renderer/app.ts:466-497` and
   `apps/gpt54-codex-workbench/src/renderer/app.ts:511-558` only append
   workflow/review records after successful tool-call return.
   This preserves truthful failure visibility, but it leaves the negative path less
   explicit than the draft's ideal handoff/audit posture.

### Strengths Observed

- `apps/gpt54-codex-workbench/package.json:1-20` is a real Electron app
  with dedicated `build`, `dev`, `smoke`, and `check` scripts
- `apps/gpt54-codex-workbench/scripts/run-electron.mjs:1-22` removes
  `ELECTRON_RUN_AS_NODE` before spawning Electron, making launch robust in this repo
  shell
- `apps/gpt54-codex-workbench/src/main.ts:134-175` and
  `apps/gpt54-codex-workbench/src/main.ts:195-205` contain bounded
  workspace-path and file-read logic
- `apps/gpt54-codex-workbench/src/main.ts:343-358` keeps the terminal lane
  read-only through allowlisted presets rather than exposing a free-form shell
- `apps/gpt54-codex-workbench/src/renderer/app.ts:1460-1565` cleanly
  separates session/write state, host-declared launch metadata, observed runtime truth,
  and dispatch-state surfaces
- `apps/gpt54-codex-workbench/src/renderer/app.ts:1605-1669` keeps the
  transcript central while making file/diff/git/review/workflow surfaces same-context
  reachable

### Checks Run

- `npm run check`
  Result: passed.
- `npm run smoke`
  Result: passed under `xvfb-run`; Electron launched and exited on the smoke timer in
  this repo environment. The run emitted non-fatal DBus warnings only.

### Current Verdict

- `preliminary_verdict`: `leading_candidate`
- note:
  this is the strongest desktop-native variant reviewed so far. It is near-spec and
  materially stronger than the browser-root Opus variant and the imported GPTPro web
  route, but I would still want the review target binding and origin-attached evidence
  posture tightened before calling it fully spec-complete.

## GPT-5.4 Codex Standalone Electron Review Update

Assessment summary:

- this checkpoint cleanly closes the three targeted follow-up gaps from the prior
  GPT-5.4 Codex review
- review target selection is now execution-truthful rather than overclaimed as a
  backend-routed selector
- transcript, file, peek-file, diff, and workflow-origin surfaces now attach review
  request state inline instead of requiring dock-only discovery
- failed review/workflow handoffs now persist as explicit failed records
- `npm run check` and `npm run smoke` both still pass
- one narrow truthfulness defect remains in the failed-record phase labeling

### Findings

1. `medium`: failed review/workflow records now persist correctly, but the failure phase
   is still not fully execution-truthful when evidence loading fails after a successful
   dispatch.
   Evidence:
   `apps/gpt54-codex-workbench/src/renderer/app.ts:582-619` creates the
   workflow record before dispatch and preserves it on error, which is correct.
   However, `apps/gpt54-codex-workbench/src/renderer/app.ts:609-611`
   attempts `loadEvidence(...)` inside the same `try` block, and the catch at
   `apps/gpt54-codex-workbench/src/renderer/app.ts:614-619` rewrites the
   run as `failed` with a message saying the handoff failed before evidence creation.
   The same pattern appears for review dispatch at
   `apps/gpt54-codex-workbench/src/renderer/app.ts:676-679` and
   `apps/gpt54-codex-workbench/src/renderer/app.ts:681-686`.
   If dispatch succeeds and only the follow-on evidence read fails, the current wording
   still mislabels that as a dispatch failure rather than an evidence-load failure.

### Resolved Since Prior Review

- review target selection now explicitly states that the chosen target affects advisory
  prompt guidance while backend execution still uses `adeu.run_workflow` and the
  selected template; the surface no longer overclaims target-specific executor routing
- transcript items, docked file view, quick peek, diff view, and workflow-origin review
  launches now render inline request markers with request ids, status, and direct paths
  back to the review dock
- failed review/workflow attempts now persist as explicit ledger records with status and
  failure reason instead of existing only as transient error banners
- the bounded Electron posture and green verification state were preserved through the
  pass

### Checks Run

- `npm run check`
  Result: passed.
- `npm run smoke`
  Result: passed under `xvfb-run`; Electron launched and exited on the smoke timer in
  this repo environment. The run emitted the usual non-fatal DBus warnings only.

### Current Verdict

- `preliminary_verdict`: `leading_candidate`
- note:
  this is now the strongest reviewed implementation by a clear margin. The remaining
  issue is narrow and phase-truth-related rather than structural, so the variant moves
  from `near-spec` into a stronger `leading_candidate` posture, but I still would not
  call it perfect until evidence-load failures are distinguished from handoff failures.

## GPT-5.4 Codex Standalone Electron Review Update 2

Assessment summary:

- this closure pass resolves the last reviewed phase-truth defect from the prior
  GPT-5.4 Codex checkpoint
- successful workflow and review dispatches now retain their returned execution status
  even when the automatic evidence read fails afterward
- automatic evidence-read failures are now recorded distinctly from dispatch failures and
  are cleared if the same evidence is later loaded successfully
- `npm run check` and `npm run smoke` both still pass
- no further scored findings are observed in this review bundle at this checkpoint

### Findings

- none observed at this checkpoint

### Resolved Since Prior Review

- `apps/gpt54-codex-workbench/src/renderer/app.ts:562-580` now records
  automatic evidence-read failures as a separate post-dispatch issue rather than routing
  them through the handoff-failure path
- `apps/gpt54-codex-workbench/src/renderer/app.ts:616-655` and
  `apps/gpt54-codex-workbench/src/renderer/app.ts:668-724` now separate the
  `adeu.run_workflow` dispatch try/catch from the follow-on evidence load attempt
- `apps/gpt54-codex-workbench/src/shared/types.ts:178-210`,
  `apps/gpt54-codex-workbench/src/renderer/app.ts:1297-1340`, and
  `apps/gpt54-codex-workbench/src/renderer/app.ts:1354-1400` now render
  evidence-load issues as distinct record state instead of rewriting the whole run as a
  failed dispatch

### Checks Run

- `npm run check`
  Result: passed.
- `npm run smoke`
  Result: passed under `xvfb-run`; Electron launched and exited on the smoke timer in
  this repo environment. The run emitted the usual non-fatal DBus warnings only.

### Current Verdict

- `preliminary_verdict`: `leading_candidate`
- note:
  this variant now clears the current support-matrix findings and remains the strongest
  reviewed implementation by a clear margin. That does not mint shipping authorization by
  itself; it means the reviewed desktop-workbench criteria are now satisfied without a
  remaining scored defect in this review bundle.
