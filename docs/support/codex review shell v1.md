## 1. v1 decision

I retained the **Electron v0 stack** and refactored it instead of restarting.

The v1 correction is now implemented as a **three-plane desktop shell**:

```text
Left:   Codex work companion chat surface
Middle: ADEU control plane
Right:  ChatGPT review/world-model thread surface
```

Electron remains the right v1 path because this app is still primarily a browser-surface workspace: it needs embedded remote web content, persistent browser sessions, robust single-window behavior, and future room for DOM/CSS/mechanical automation. Electron’s current embedding direction is `WebContentsView`; `BrowserView` is deprecated and replaced by `WebContentsView`, and `WebContentsView` exposes `webContents` for loading and controlling embedded pages. ([Electron][1])

I did **not** move to Tauri for v1 because the current issue is not binary size or native shell footprint; it is geometry, embedded browser control, and workflow responsiveness. Electron is still the more pragmatic fit.

I also kept ChatGPT as the **real embedded ChatGPT web surface**. I did not invent a consumer ChatGPT thread API. The OpenAI API docs describe the platform REST/streaming/realtime APIs; v1 therefore treats existing consumer ChatGPT threads as web UI surfaces rather than guaranteed backend-programmable review threads. ([OpenAI Developers][2])

Download the v1 app folder: [codex-review-shell-v1.zip](sandbox:/mnt/data/codex-review-shell-v1.zip)
Download the full modified repo: [adeu-studio-with-codex-review-shell-v1.zip](sandbox:/mnt/data/adeu-studio-with-codex-review-shell-v1.zip)

---

## 2. Architecture delta from v0

v0 was effectively:

```text
Project sidebar + Codex pane + ChatGPT pane
```

v1 is now:

```text
Codex plane | ADEU control plane | ChatGPT plane
```

The middle plane is now the shell’s real home. It owns:

```text
project selection
project binding editor
repo/workspace path
Codex binding
ChatGPT review URL
FlowProfile fields
relay controls
status
work tree
file preview
```

The left plane is no longer a shell-surrogate metadata panel. The local fallback surface now looks and behaves like a **Codex-style work chat**: transcript, input area, model selector, reasoning selector, and queue-note behavior. If a project’s Codex binding is set to `url`, the left plane loads that embedded URL instead.

The right plane remains a **real ChatGPT thread surface**, with best-effort chrome reduction and best-effort dark-mode forcing. OpenAI’s current ChatGPT Help guidance still describes settings/theme access through the profile icon, Settings, General, and Theme; v1 implements a control-plane “ChatGPT settings” button that tries to open that settings path via hash/modal/menu behavior inside the embedded surface. ([OpenAI Help Center][3])

---

## 3. Implementation

Implemented v1 changes:

* Three-plane geometry.
* Two draggable splitters.
* Persistent v1 layout ratios:

  * `ui.leftRatio`
  * `ui.middleRatio`
* Migration from old v0 `ui.splitRatio`.
* Resize/maximize/restore fix:

  * layout is recomputed from live DOM rects
  * no stale cached pane geometry
  * burst reflow on resize/maximize/restore/fullscreen/project-load
  * `ResizeObserver` on shell and both surface slots
  * main-process resize events request renderer remeasurement
* Left Codex plane:

  * local Codex-style chat fallback
  * transcript
  * input
  * model/reasoning controls
  * copy review prompt / return header
* Middle ADEU control plane:

  * project tree
  * project editor preserved
  * FlowProfile display
  * relay controls
  * work tree
  * file preview
* Right ChatGPT plane:

  * embedded ChatGPT URL/thread
  * persistent Electron browser session
  * best-effort dark mode
  * best-effort chrome reduction
  * control-plane ChatGPT settings button
* Work tree:

  * lazy directory expansion
  * skips heavy directories like `.git`, `node_modules`, `.next`, `dist`, `build`, `coverage`, `target`
  * caps entries for responsiveness
* File preview:

  * text/code preview
  * binary detection
  * 384 KB preview cap with truncation notice

Validation run:

```bash
npm run check:syntax
```

Passed.

The complete source is in the linked zip. The most important v1 layout fix is this pattern in `src/renderer/app.js`:

```js
function performLayout() {
  applyPlaneWidths();
  sendSurfaceLayout();
}

function scheduleLayout() {
  if (state.layoutFrame) cancelAnimationFrame(state.layoutFrame);
  state.layoutFrame = requestAnimationFrame(() => {
    state.layoutFrame = 0;
    performLayout();
  });
}

function scheduleResizeBurst() {
  state.lastLayoutSignature = "";
  for (const delay of [0, 16, 48, 110, 240, 480]) {
    setTimeout(scheduleLayout, delay);
  }
}
```

And the main process now actively asks the renderer to remeasure after window geometry events in `src/main.js`:

```js
for (const eventName of [
  "resize",
  "resized",
  "maximize",
  "unmaximize",
  "enter-full-screen",
  "leave-full-screen",
  "restore",
]) {
  mainWindow.on(eventName, () => {
    setShellBoundsToWindow();
    applySurfaceBounds();
    scheduleLayoutPing(eventName);
  });
}
```

Work-tree and preview are exposed through IPC in `src/preload.js`:

```js
listWorkTree: (projectId, relPath) =>
  ipcRenderer.invoke("worktree:list", { projectId, relPath }),

readProjectFile: (projectId, relPath) =>
  ipcRenderer.invoke("worktree:read-file", { projectId, relPath }),

openChatgptSettings: () =>
  ipcRenderer.invoke("chatgpt:open-settings"),

forceChatgptDark: () =>
  ipcRenderer.invoke("chatgpt:force-dark"),
```

---

## 4. File tree

```text
apps/codex-review-shell/
├── README.md
├── package.json
└── src/
    ├── main.js
    ├── preload.js
    └── renderer/
        ├── app.js
        ├── codex-surface.css
        ├── codex-surface.html
        ├── codex-surface.js
        ├── index.html
        └── styles.css
```

The v1 source is about 3,090 lines across the app files.

---

## 5. Run instructions

From the modified repo:

```bash
cd apps/codex-review-shell
npm install
npm run start
```

Syntax check:

```bash
npm run check:syntax
```

The app stores config in Electron’s per-user app data directory as:

```text
workspace-config.json
```

Existing v0 config is normalized in place. The old `ui.splitRatio` is migrated into v1-style plane ratios.

---

## 6. Limitations / next steps

What works now:

* Three visual planes.
* Shell-owned project bindings.
* Persistent project editor.
* Persistent layout ratios.
* Resize/maximize/restore reflow fix.
* Embedded Codex plane.
* Embedded ChatGPT plane.
* Middle ADEU control plane.
* Work tree.
* File preview.
* Manual relay controls.

What remains best-effort or brittle:

* ChatGPT dark mode depends partly on the underlying ChatGPT session/account theme. v1 forces Electron dark preference, injects dark CSS, and nudges local storage/theme state, but an explicit ChatGPT account setting may still win.
* ChatGPT chrome reduction is CSS-selector based. It can break if ChatGPT changes DOM structure.
* The ChatGPT settings button is pragmatic, not official. It tries hash/modal/menu access inside the embedded ChatGPT surface. If the ChatGPT UI changes, it may need selector updates.
* The local Codex plane is a Codex-style chat fallback, not a real Codex execution backend. Set the project’s Codex binding to a local app-server URL when you want the left plane to load an actual Codex surface.
* The work tree intentionally skips heavy directories and truncates file previews to keep the control plane snappy.
* No automatic markdown watcher, upload, prompt-send, response capture, or paste-back relay yet.

Natural next iteration:

```text
v1.1:
- watched markdown artifact queue
- one-click “stage review packet”
- prompt-template expansion with selected file
- copy/upload helper affordances

v2:
- Playwright-assisted mechanical relay
- response capture
- paste-back into Codex with configured return header
```

Complete working v1 source is here: [codex-review-shell-v1.zip](sandbox:/mnt/data/codex-review-shell-v1.zip)

[1]: https://electronjs.org/blog/migrate-to-webcontentsview?utm_source=chatgpt.com "Migrating from BrowserView to WebContentsView"
[2]: https://developers.openai.com/api/reference/overview/?utm_source=chatgpt.com "API Overview | OpenAI API Reference"
[3]: https://help.openai.com/en/articles/11958281-updating-your-visual-experience-on-chatgpt?utm_source=chatgpt.com "Updating your visual experience on ChatGPT"
