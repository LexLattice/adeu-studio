# Gemini Runtime Investigation

Date: `2026-04-10`

Scope:

- investigate the current `apps/gemini-codex-workbench` runtime behavior without
  patching the app
- explain why the user-observed surface shows:
  - `Local UI Boundary Spawned successfully`
  - `ADEU Backend server absent`
  - disabled start/stop/restart session controls
  - `Electron missing` / inactive terminal-git-diff behavior

## User-Observed Behavior

Observed on the live Gemini surface:

- the transcript shows:
  `Local UI Boundary Spawned successfully.`
  `Note: ADEU Backend server absent. Local operations (PTY standard shells/Git/FS Viewer) function standalone.`
- `Start Session` does not start a real Codex/ADEU session
- terminal / git / diff surfaces report Electron absence or inactivity

## Runtime Findings

### 1. The session controls are intentionally nonfunctional in the shipped Gemini UI.

The status boundary renders `Start Session`, `Stop`, and `Restart` as permanently
disabled buttons with static backend-absent tooltips:

- [App.tsx](/home/rose/work/LexLattice/odeu/apps/gemini-codex-workbench/src/App.tsx#L416)

The same region hard-codes:

- `Session ID: None`
- `Session Status: Offline`
- `Profile: Unconfigured`
- `Build/Config: Unknown`
- `App Server: Unavailable`

This is not a launch regression. It is the current implementation.

Implication:

- even inside a valid Electron launch, this app does not expose a real session-start
  path for Codex/ADEU backend work

### 2. The chat composer is also explicitly local/offline, not backed by a real Codex session.

`submitMessage()` only appends the user message to local React state and then inserts a
synthetic blocked system reply:

- `[Response Blocked]`
- `ADEU Codex Backend is Unconfigured/Missing.`
- `Local Request Stored.`

Source:

- [App.tsx](/home/rose/work/LexLattice/odeu/apps/gemini-codex-workbench/src/App.tsx#L366)

Implication:

- there is no hidden real session path behind the disabled `Start Session` button
- the current Gemini app is still an offline/local request surface for chat, not a real
  connected Codex session client

### 3. The exact UI you observed matches the plain Vite page, not an Electron-bound renderer.

Live inspection of `http://127.0.0.1:5173/` showed:

- `window.electronAPI === false`
- `Start Session` disabled
- transcript contains the same backend-absent note
- terminal pane renders `Terminal inactive (not running in Electron).`

That behavior is expected from the browser page because multiple surfaces explicitly gate
on `window.electronAPI`.

Code path:

- terminal mount returns early unless `window.electronAPI` exists:
  [App.tsx](/home/rose/work/LexLattice/odeu/apps/gemini-codex-workbench/src/App.tsx#L119)
- git/diff viewer shows Electron-missing content when `window.electronAPI` is absent:
  [App.tsx](/home/rose/work/LexLattice/odeu/apps/gemini-codex-workbench/src/App.tsx#L256)
- file tree bootstrap also only runs when `window.electronAPI` exists:
  [App.tsx](/home/rose/work/LexLattice/odeu/apps/gemini-codex-workbench/src/App.tsx#L352)

Implication:

- if the user is looking at the browser tab served by Vite on `:5173`, the terminal/git/
  diff/file integrations will degrade into Electron-absent behavior by design

### 4. A real Gemini Electron process was running during the investigation.

Process inspection confirmed an Electron process for Gemini was live:

- `apps/gemini-codex-workbench/node_modules/electron/dist/electron .`

The Electron main process creates a `BrowserWindow` with preload and loads
`http://localhost:5173` in dev:

- preload bridge export:
  [preload.js](/home/rose/work/LexLattice/odeu/apps/gemini-codex-workbench/electron/preload.js#L1)
- BrowserWindow creation and dev URL load:
  [main.js](/home/rose/work/LexLattice/odeu/apps/gemini-codex-workbench/electron/main.js#L15)

Inference:

- the Electron app itself was launched
- the `Electron missing` behavior the user reported is most consistent with viewing the
  plain browser page instead of the Electron window
- however, this does not change Finding 1: even the Electron window still has hard-coded
  offline session controls and no real ADEU/Codex session start path

## Structural Diagnosis

Two separate realities are overlapping:

1. `Browser vs Electron context`

- Browser page on `:5173`:
  `window.electronAPI` is absent
- Result:
  terminal/git/diff/file surfaces fall back to Electron-missing behavior

2. `Offline Gemini app design`

- Even with Electron present, the current Gemini implementation does not wire real
  session start/stop/restart or real chat/backend execution
- Result:
  `Start Session` remains disabled and message sending stays local/offline

## Bottom Line

The user-observed behavior is real and is explained by a combination of:

- viewing the browser-served Vite page instead of the Electron renderer for the
  Electron-dependent surfaces
- and a separately hard-coded offline session/chat posture in the current Gemini app

So:

- `Electron missing` is a context issue
- `Start Session does nothing` is an implementation issue in the current Gemini variant

## No-Change Outcome

No application code was patched as part of this investigation.
