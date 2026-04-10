# ADEU Codex Desktop Workbench (Opus Variant)

A standalone, minimalist, chat-first desktop workbench for the ADEU Codex ecosystem.

## Status

**Checkpoint 2** — desktop host shell with real filesystem, git, and terminal wiring.

This is an intermediate implementation. It is not yet spec-complete against
`docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md`.

## What Is Real

These capabilities are wired to real host/runtime surfaces:

- **Desktop host shell**: Electron with preload/IPC context isolation
- **Bounded filesystem**: read-only file tree and viewer, contained to
  workspace root via resolved-path checks
- **Git status/diff/log**: real `git` commands executed via child process
- **Bounded terminal**: PTY-backed via `node-pty`, with explicit read-only
  vs interactive gating and trust boundary notices
- **Session controls**: start / stop / restart / clear (local host session)
- **File provenance**: full relative paths preserved throughout

## What Is Unavailable

These require a real ADEU/Codex backend connection that is not yet wired:

- **ADEU session management** (adeu.get_app_state, etc.)
- **Provider/build/config identity** — shown as null until provided by backend
- **Assistant responses** — messages are recorded locally; no responses fabricated
- **Review dispatch** — creates local request tokens with `not_executed` status
- **Workflow execution** — creates local request tokens with `not_executed` status
- **Evidence bundle retrieval** — no fabricated evidence
- **SSE event stream** — not connected

Review and workflow surfaces make this unavailability explicit in the UI
rather than simulating success.

## Run

### Desktop mode (Electron)

```bash
cd apps/opus-codex-workbench
npm install
npm run electron:dev
```

This starts the Vite dev server and then launches Electron with the host
bridge. The launcher script scrubs `ELECTRON_RUN_AS_NODE` from the
environment to prevent the known repo-shell import failure.

### Browser fallback

```bash
cd apps/opus-codex-workbench
npm install
npm run dev
```

Opens at `http://localhost:5174`. In browser mode, filesystem, git, and
terminal surfaces are unavailable (shown explicitly in the UI).

### Build

```bash
npm run build
```

## Architecture

```
apps/opus-codex-workbench/
├── electron/
│   ├── main.js        Electron main process (IPC handlers)
│   └── preload.js     Context bridge (governed IPC surface)
├── scripts/
│   └── launch-electron.js   Launcher with env guard
├── src/
│   ├── main.js        Renderer entry point
│   ├── state.js       Pub/sub state store
│   ├── host-bridge.js Real host bridge (IPC + local-only fallbacks)
│   ├── layout-engine.js   Layout constraint math
│   ├── components/    UI components
│   └── styles/        Design system + layout CSS
├── index.html
├── package.json
└── vite.config.js
```

## Limitations

- `node-pty` requires native compilation; if it fails, terminal surface
  shows an explicit error rather than crashing.
- The app does not yet wire to a real ADEU/Codex backend. All
  review/workflow/session surfaces operate in local-request-only mode.
- This is the Opus variant (checkpoint 2). See the variant scorecard
  at `docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_VARIANT_SCORECARD_v0.md`.
