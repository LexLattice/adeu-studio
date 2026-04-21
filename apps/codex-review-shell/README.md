# ADEU Three-Plane Workspace v1.1

Electron desktop shell for a single-window coding/review loop with an explicit Windows-host / WSL-workspace backend split.

- **Left plane:** Codex work companion chat surface.
- **Middle plane:** ADEU control plane, not a chat.
- **Right plane:** ChatGPT review/world-model thread surface.

The shell remains the source of truth for project bindings. Each project stores:

- project name
- typed workspace binding
- Codex target/binding
- ChatGPT review thread URL/binding
- FlowProfile metadata: review prompt, watched file patterns, return header

## v1.1 additions

- Explicit `workspace.kind` in project config: `local` or `wsl`.
- WSL-native workspace config fields: distro + canonical Linux path.
- Resident backend session manager in the Electron host.
- WSL backend agent at `src/backend/wsl-agent.js`.
- Newline-delimited JSON protocol over stdio.
- Work tree and file preview now route through the workspace backend.
- Command execution and watcher scaffolding are present in the backend protocol.
- Existing three-plane geometry and maximize/restore reflow fix are preserved.
- Existing ChatGPT embedding/chrome reduction behavior is preserved.

## Architecture summary

For WSL projects on Windows:

```text
Native Windows Electron host
  ⇄ stdio JSON protocol
wsl.exe-launched resident backend agent
  ⇄ Linux filesystem
Canonical WSL workspace path
```

The app does **not** use `\\wsl$` browsing as the primary architecture. UNC paths may be recognized during migration or used as fallback display values, but WSL workspace truth lives on the Linux side.

## Config shape

Example WSL project:

```json
{
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
      "reviewThreadUrl": "https://chatgpt.com/",
      "reduceChrome": true
    }
  }
}
```

Example local/dev project:

```json
{
  "workspace": {
    "kind": "local",
    "localPath": "C:\\path\\to\\repo",
    "label": "Local workspace"
  }
}
```

## Native Windows dev run

From PowerShell or Windows Terminal:

```powershell
cd apps\codex-review-shell
npm install
npm run start
```

To attach to a WSL workspace, edit the project binding:

- Workspace kind: `WSL workspace`
- WSL distro: `Ubuntu` or your distro name; blank means WSL default
- Canonical Linux path: `/home/<you>/<repo>`

Node.js must be available as `node` inside that WSL distro.

## Validation

Syntax check:

```bash
npm run check:syntax
```

Agent smoke path for the local backend protocol:

```bash
npm run agent:smoke
```

Headless Electron smoke remains available on Linux environments that have `xvfb-run`:

```bash
npm run smoke
```

## Notes

ChatGPT is embedded as the real web thread surface. There is no assumed official consumer ChatGPT API for sending messages to an existing thread or uploading files. Chrome reduction, dark-mode forcing, and settings access are best-effort browser-surface behavior.

For the detailed architecture/support note, see [`WSL_HOST_ARCHITECTURE.md`](./WSL_HOST_ARCHITECTURE.md).
