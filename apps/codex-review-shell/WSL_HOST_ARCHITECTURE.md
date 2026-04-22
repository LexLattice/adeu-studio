# Codex Review Shell v1.2 — Windows Host / WSL Workspace Backend

This version keeps the three-plane dual-partner workflow model and the Windows-host / WSL-workspace backend split for a long-term Remote-WSL style workflow.

## Version intent

The Electron process is the **native desktop host**. It owns:

- the single Windows app window
- the three-plane layout geometry
- the Codex and ChatGPT browser surfaces
- project binding persistence
- user-facing control-plane UI

The workspace is no longer assumed to be a Windows-path mirror. A project can now declare its workspace as WSL-native, and the workspace operations are delegated to a resident backend process running inside that workspace context.

## Plane model retained

- **Left plane:** Codex work companion / chat surface. It still uses the local Codex-style fallback unless the project binds a real Codex URL.
- **Middle plane:** workflow control plane. It owns project selection, thread deck, bindings, FlowProfile fields, handoff queue, watched artifacts, work tree, file preview, and backend status.
- **Right plane:** real embedded ChatGPT thread surface. This remains browser-embedded ChatGPT; no consumer ChatGPT API is invented.

The maximize/restore geometry fix from v1 is preserved: the shell renderer still remeasures live DOM surface slots, and the Electron main process still sends reflow pings on resize/maximize/restore/focus.

## Project config shape

Config is still stored in Electron user data as `workspace-config.json`. The config version is now `4`.

Each project keeps the existing binding fields and gains explicit workspace typing:

```json
{
  "id": "project_adeu_studio",
  "name": "ADEU Studio",
  "repoPath": "wsl:Ubuntu:/home/me/adeu-studio",
  "workspace": {
    "kind": "wsl",
    "distro": "Ubuntu",
    "linuxPath": "/home/me/adeu-studio",
    "label": "ADEU Studio in WSL"
  },
  "surfaceBinding": {
    "codex": {
      "mode": "local",
      "target": "codex://local-workspace",
      "label": "Local Codex lane"
    },
    "chatgpt": {
      "reviewThreadUrl": "https://chatgpt.com/c/...",
      "reduceChrome": true
    }
  },
  "chatThreads": [
    {
      "id": "thread_review_primary",
      "role": "review",
      "title": "Primary review",
      "url": "https://chatgpt.com/c/...",
      "isPrimary": true,
      "pinned": true,
      "archived": false
    }
  ],
  "activeChatThreadId": "thread_review_primary",
  "flowProfile": {
    "reviewPromptTemplate": "...",
    "watchedFilePatterns": ["**/*REVIEW*.md"],
    "returnHeader": "GPT feedback"
  }
}
```

Local/dev projects use:

```json
"workspace": {
  "kind": "local",
  "localPath": "C:\\path\\to\\repo",
  "label": "Local workspace"
}
```

Old configs are normalized in place. Existing `repoPath` values become local workspace roots unless they look like a WSL UNC path such as `\\wsl$\\Ubuntu\\home\\me\\repo`, in which case they migrate to `workspace.kind = "wsl"`.

## Backend transport

The host uses `src/main/workspace-backend.js` as the transport/session manager.

For a WSL project on Windows, the host starts a resident backend process like this conceptually:

```text
wsl.exe -d <distro> --cd <linuxPath> -- bash -lc "node <agent> --root $PWD --workspace-kind wsl --project-id <id>"
```

The actual implementation converts the Windows app path for `src/backend/wsl-agent.js` into a Linux-visible path with `wslpath -a` inside the distro. The WSL agent must be able to run `node` inside that distro.

The host and backend speak newline-delimited JSON over stdio. The protocol is intentionally small:

```json
{"id":"...","method":"hello","params":{}}
{"id":"...","method":"listTree","params":{"relPath":"src"}}
{"id":"...","method":"readFile","params":{"relPath":"README.md"}}
{"id":"...","method":"runCommand","params":{"command":"git","args":["status","--short"]}}
```

The backend replies with one JSON object per line:

```json
{"id":"...","result":{}}
{"id":"...","error":{"message":"..."}}
```

It can also emit session events:

```json
{"event":"ready","sessionId":"agent_...","root":"/home/me/adeu-studio"}
```

## What the backend owns now

The resident workspace backend owns:

- attach/session handshake
- workspace root truth
- directory listing / expansion
- file preview reads
- binary detection and preview truncation
- command execution scaffold for future Codex-side actions
- watched-pattern scans for review artifacts
- watcher capability scaffold/status

The middle control plane no longer reads the repo tree directly from a host path. Its current work tree and file preview IPC calls route through the backend session.

## Why UNC is not the core model

`\\wsl$` paths may still be recognized during migration or used manually as a fallback path, but the intended WSL project model is:

```text
Windows Electron host ⇄ resident WSL backend ⇄ canonical Linux workspace path
```

That avoids making a Windows mirror or UNC file browsing the source of truth.

## Native Windows dev launch

From PowerShell or Windows Terminal, run the Electron app from a Windows checkout of this app bundle:

```powershell
cd apps\codex-review-shell
npm install
npm run start
```

Then edit or create a project binding:

- Workspace kind: `WSL workspace`
- WSL distro: for example `Ubuntu`
- Canonical Linux path: for example `/home/<you>/adeu-studio`
- ChatGPT review URL: the real `https://chatgpt.com/c/...` thread

The app will start/attach the backend via `wsl.exe` and the work tree / preview will come from the WSL agent.

## Requirements

- Windows host with WSL installed.
- The selected distro must have Node.js available as `node`.
- The Linux path must exist inside the distro.
- During development, the app code can live on Windows; the launcher converts the agent script path for WSL with `wslpath`.

## Current limitations

- The backend is a per-session child process, not yet a named long-lived daemon reused across host restarts.
- Watched artifact scanning is implemented as an explicit backend scan; continuous live watcher subscriptions are still deferred.
- Command execution exists as a backend method but is not yet exposed as a full Codex relay UI.
- WSL attach currently depends on `wsl.exe --cd`, `bash`, `wslpath`, and `node` inside the distro.
- The right ChatGPT pane remains a browser surface with best-effort chrome/dark-mode behavior; there is no official consumer-thread control API assumed.
- Packaging as `.exe` is intentionally out of scope for this version.

## Next steps

1. Promote watched-artifact scanning into live subscriptions.
2. Add one-click review packet staging for selected markdown files.
3. Add safe command profiles for Codex-side actions.
4. Promote watcher events into the control-plane status/relay area.
5. Consider a named WSL daemon/socket once the protocol stabilizes.
