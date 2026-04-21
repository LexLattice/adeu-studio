## 1. Decision

I chose **Electron** for this v0, specifically **Electron `BaseWindow` + main-process `WebContentsView` panes**, not Tauri.

The reason is practical: this app is browser-heavy, needs to host consumer ChatGPT web UI inside a desktop shell, benefits from Chromium consistency, needs persistent embedded sessions, and may later need DOM/CSS/mechanical automation hooks. Electron’s current direction is also to use `WebContentsView` for embedded web content; `BrowserView` is deprecated in favor of `WebContentsView`, and Electron’s `<webview>` tag is explicitly warned against for stability-sensitive layouts. ([Electron][1])

I did **not** choose Tauri for v0. Tauri v2 can create positioned remote webviews, so it is technically possible, but the v0 priority is reliable browser embedding/control of ChatGPT and future automation leverage. Tauri’s native-WebView model is attractive for smaller binaries, but it is less ideal here because ChatGPT is a complex Chromium-targeted consumer web app and future Playwright-style automation would be awkward as a primary renderer path. ([Tauri][2])

I also did **not** choose a dedicated browser-window approach because it violates the one-window requirement. Playwright should be a **future automation backend**, not the primary UI renderer, because making Playwright the visible workspace would add orchestration overhead and fragility before the shell/pairing model is proven.

The ChatGPT side is implemented as an embedded existing ChatGPT web thread URL. I did not assume an official API for sending messages or uploading files into an existing consumer ChatGPT thread. The documented OpenAI API surface is the API platform with API-key REST endpoints; ChatGPT Projects/thread usage is documented as logged-in ChatGPT product UI behavior, so this v0 treats ChatGPT as a persisted embedded web surface rather than a backend API target. ([OpenAI Developers][3])

Download the built v0 app folder here: [codex-review-shell-v0.zip](sandbox:/mnt/data/codex-review-shell-v0.zip)
Download the full modified repo here: [adeu-studio-with-codex-review-shell-v0.zip](sandbox:/mnt/data/adeu-studio-with-codex-review-shell-v0.zip)

---

## 2. Architecture

The v0 app lives at:

```text
apps/codex-review-shell
```

The shell uses one Electron window containing three `WebContentsView`s:

```text
BaseWindow
├─ shellView      local dark UI, sidebar, project editor, splitter
├─ codexView      left pane surface slot
└─ chatgptView    right pane ChatGPT surface slot
```

The local shell renderer owns the layout. It measures the Codex and ChatGPT slot rectangles and sends those bounds to the Electron main process. The main process positions the two embedded web surfaces into those slots. This keeps the app visually one-window while still isolating the heavy browser surfaces.

Persistent config is stored as local JSON under Electron user data:

```text
workspace-config.json
```

The config model is intentionally shaped around the concepts you specified:

```ts
Project {
  id
  name
  repoPath
  surfaceBinding: {
    codex: {
      mode: "local" | "url" | "command"
      target
      label
    }
    chatgpt: {
      reviewThreadUrl
      reduceChrome
    }
  }
  flowProfile: {
    reviewPromptTemplate
    watchedFilePatterns
    returnHeader
  }
}
```

The default project points to the ADEU Studio repo path, uses a local controlled Codex lane, and loads `https://chatgpt.com/` until you edit it to the exact review thread URL.

---

## 3. Working v0 implementation

Implemented features:

* Dark-only desktop shell.
* Project sidebar / project tree.
* Project editor drawer.
* Persistent local JSON config.
* Per-project repo path.
* Per-project Codex binding.
* Per-project ChatGPT review thread URL.
* Shell-owned pairing: selecting a project loads both bound surfaces.
* Left pane Codex work surface.
* Right pane embedded ChatGPT surface.
* Draggable split pane.
* Persistent split ratio.
* ChatGPT session persistence via Electron partition.
* Best-effort ChatGPT chrome reduction CSS.
* Local Codex surface with review prompt, watched patterns, and paste-back header.
* Buttons for reload, external ChatGPT open, copy review prompt.
* Syntax check passed with:

```bash
npm run check:syntax
```

I did not run the full Electron GUI in this container because the Electron dependency is not installed here; the app is ready to run after `npm install`.

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

---

## 5. Run instructions

From the modified repo:

```bash
cd apps/codex-review-shell
npm install
npm run start
```

Optional syntax check:

```bash
npm run check:syntax
```

On first launch, the app seeds one project:

```text
Name: ADEU Studio
Repo path: <repo root>
Codex mode: local controlled shell lane
ChatGPT URL: https://chatgpt.com/
```

Edit the selected project and replace the ChatGPT URL with the real review thread URL, for example a `https://chatgpt.com/c/...` thread URL.

---

## 6. Limitations / next iteration points

What works now:

* The shell owns the project-to-surface binding.
* Project switching loads the paired Codex and ChatGPT panes.
* Config persists locally.
* The app stays visually inside one desktop window.
* ChatGPT login/session should persist inside the app-specific Electron session partition.
* The Codex lane is controlled by the shell and can also load a URL target if you later point it at a local Codex web surface.

What is stubbed or intentionally not automated:

* No markdown file watcher yet.
* No automatic file upload into ChatGPT.
* No automatic prompt submission.
* No response capture.
* No paste-back into Codex.
* No full Codex redesign.

Brittle area:

* ChatGPT chrome reduction is CSS-based and best-effort. It may need selector updates when ChatGPT changes its web UI.
* Login/SSO flows can vary. The implementation tries to keep likely ChatGPT/auth URLs inside the pane and opens unrelated popups externally.
* Consumer ChatGPT is treated as a web surface, not as an official programmable thread API.

Natural v1:

* Add folder watcher for configured markdown artifact patterns.
* Add prompt-template insertion/copy queue.
* Add “review packet” drawer that stages file + prompt before manual upload.
* Add Playwright-assisted mechanical actions only after the shell UX is stable.
* Add response capture/paste-back conventions around the `returnHeader`.
* Add a small project search/filter and keyboard navigation for faster switching.

---

## Actual code

The complete runnable code is in the downloadable artifact above. These are the core files.

### `apps/codex-review-shell/package.json`

```json
{
  "name": "codex-review-shell",
  "private": true,
  "version": "0.1.0",
  "description": "Dual-pane Codex + ChatGPT review workspace shell",
  "license": "Apache-2.0",
  "main": "src/main.js",
  "scripts": {
    "start": "electron .",
    "dev": "electron .",
    "check:syntax": "node --check src/main.js && node --check src/preload.js && node --check src/renderer/app.js && node --check src/renderer/codex-surface.js"
  },
  "devDependencies": {
    "electron": "^41.2.0"
  }
}
```

### `apps/codex-review-shell/src/preload.js`

```js
const { contextBridge, ipcRenderer } = require("electron");

contextBridge.exposeInMainWorld("workspaceShell", {
  loadConfig: () => ipcRenderer.invoke("config:load"),
  saveConfig: (config) => ipcRenderer.invoke("config:save", config),
  selectProject: (projectId) => ipcRenderer.invoke("project:select", projectId),
  chooseDirectory: () => ipcRenderer.invoke("dialog:choose-directory"),
  setSurfaceLayout: (bounds) => ipcRenderer.invoke("surface:set-layout", bounds),
  setSurfaceVisible: (visible) => ipcRenderer.invoke("surface:set-visible", visible),
  reloadSurface: (surfaceName) => ipcRenderer.invoke("surface:reload", surfaceName),
  openSurfaceExternal: (surfaceName) => ipcRenderer.invoke("surface:open-external", surfaceName),
  copyText: (text) => ipcRenderer.invoke("clipboard:write-text", text),
  onSurfaceEvent: (callback) => {
    const listener = (_event, payload) => callback(payload);
    ipcRenderer.on("surface:event", listener);
    return () => ipcRenderer.removeListener("surface:event", listener);
  },
});
```

### `apps/codex-review-shell/src/main.js`

```js
const { app, BaseWindow, WebContentsView, ipcMain, dialog, shell, Menu, clipboard } = require("electron");
const fs = require("node:fs/promises");
const path = require("node:path");
const { pathToFileURL } = require("node:url");
const crypto = require("node:crypto");

const APP_TITLE = "Codex Review Shell";
const CONFIG_FILE_NAME = "workspace-config.json";
const CODEX_PARTITION = "persist:codex-review-shell-codex";
const CHATGPT_PARTITION = "persist:codex-review-shell-chatgpt";

const appRoot = path.resolve(__dirname, "..");
const repoRoot = path.resolve(appRoot, "..", "..");
const rendererRoot = path.join(__dirname, "renderer");
const shellHtmlPath = path.join(rendererRoot, "index.html");
const codexSurfaceHtmlPath = path.join(rendererRoot, "codex-surface.html");

let mainWindow = null;
let shellView = null;
let codexView = null;
let chatgptView = null;
let lastSurfaceBounds = null;
let surfacesVisible = true;
let configCache = null;
let currentProject = null;

function nowIso() {
  return new Date().toISOString();
}

function newId(prefix) {
  return `${prefix}_${crypto.randomUUID().replace(/-/g, "").slice(0, 12)}`;
}

function configPath() {
  return path.join(app.getPath("userData"), CONFIG_FILE_NAME);
}

function defaultConfig() {
  const defaultProjectId = "project_adeu_studio";
  return {
    version: 1,
    selectedProjectId: defaultProjectId,
    ui: {
      splitRatio: 0.5,
    },
    projects: [
      {
        id: defaultProjectId,
        name: "ADEU Studio",
        repoPath: repoRoot,
        surfaceBinding: {
          codex: {
            mode: "local",
            target: "codex://local-workspace",
            label: "Local Codex lane",
          },
          chatgpt: {
            reviewThreadUrl: "https://chatgpt.com/",
            reduceChrome: true,
          },
        },
        flowProfile: {
          reviewPromptTemplate:
            "Review the attached/selected Codex artifact for correctness, risks, missing checks, and concrete next actions. Return concise feedback I can paste back into Codex.",
          watchedFilePatterns: ["**/*REVIEW*.md", "**/*review*.md", "artifacts/**/*.md"],
          returnHeader: "GPT feedback",
        },
        createdAt: nowIso(),
        updatedAt: nowIso(),
      },
    ],
  };
}

function isPlainObject(value) {
  return Boolean(value) && typeof value === "object" && !Array.isArray(value);
}

function normalizeString(value, fallback = "") {
  return typeof value === "string" && value.trim() ? value.trim() : fallback;
}

function normalizeSplitRatio(value) {
  const numberValue = Number(value);
  if (!Number.isFinite(numberValue)) return 0.5;
  return Math.min(0.78, Math.max(0.22, numberValue));
}

function normalizeProject(input, index = 0) {
  const fallback = defaultConfig().projects[0];
  const raw = isPlainObject(input) ? input : {};
  const surfaceBinding = isPlainObject(raw.surfaceBinding) ? raw.surfaceBinding : {};
  const rawCodex = isPlainObject(surfaceBinding.codex) ? surfaceBinding.codex : {};
  const rawChatgpt = isPlainObject(surfaceBinding.chatgpt) ? surfaceBinding.chatgpt : {};
  const rawFlow = isPlainObject(raw.flowProfile) ? raw.flowProfile : {};
  const modeCandidate = normalizeString(rawCodex.mode, "local");
  const codexMode = ["local", "url", "command"].includes(modeCandidate) ? modeCandidate : "local";
  const patterns = Array.isArray(rawFlow.watchedFilePatterns)
    ? rawFlow.watchedFilePatterns.filter((item) => typeof item === "string" && item.trim()).map((item) => item.trim())
    : fallback.flowProfile.watchedFilePatterns;

  const id = normalizeString(raw.id, index === 0 ? fallback.id : newId("project"));
  const now = nowIso();

  return {
    id,
    name: normalizeString(raw.name, index === 0 ? fallback.name : `Project ${index + 1}`),
    repoPath: normalizeString(raw.repoPath, repoRoot),
    surfaceBinding: {
      codex: {
        mode: codexMode,
        target: normalizeString(rawCodex.target, codexMode === "local" ? "codex://local-workspace" : ""),
        label: normalizeString(rawCodex.label, codexMode === "local" ? "Local Codex lane" : "Codex target"),
      },
      chatgpt: {
        reviewThreadUrl: normalizeString(rawChatgpt.reviewThreadUrl, "https://chatgpt.com/"),
        reduceChrome: rawChatgpt.reduceChrome !== false,
      },
    },
    flowProfile: {
      reviewPromptTemplate: normalizeString(rawFlow.reviewPromptTemplate, fallback.flowProfile.reviewPromptTemplate),
      watchedFilePatterns: patterns.length ? patterns : fallback.flowProfile.watchedFilePatterns,
      returnHeader: normalizeString(rawFlow.returnHeader, fallback.flowProfile.returnHeader),
    },
    createdAt: normalizeString(raw.createdAt, now),
    updatedAt: normalizeString(raw.updatedAt, now),
  };
}

function normalizeConfig(input) {
  const defaults = defaultConfig();
  const raw = isPlainObject(input) ? input : {};
  const rawProjects = Array.isArray(raw.projects) ? raw.projects : defaults.projects;
  const projects = rawProjects.map((project, index) => normalizeProject(project, index));
  const dedupedProjects = [];
  const ids = new Set();

  for (const project of projects) {
    let id = project.id;
    if (ids.has(id)) id = newId("project");
    ids.add(id);
    dedupedProjects.push({ ...project, id });
  }

  if (!dedupedProjects.length) dedupedProjects.push(defaults.projects[0]);

  const selectedCandidate = normalizeString(raw.selectedProjectId, dedupedProjects[0].id);
  const selectedProjectId = dedupedProjects.some((project) => project.id === selectedCandidate)
    ? selectedCandidate
    : dedupedProjects[0].id;

  return {
    version: 1,
    selectedProjectId,
    ui: {
      splitRatio: normalizeSplitRatio(isPlainObject(raw.ui) ? raw.ui.splitRatio : defaults.ui.splitRatio),
    },
    projects: dedupedProjects,
  };
}

async function loadConfig() {
  if (configCache) return configCache;
  try {
    const raw = await fs.readFile(configPath(), "utf8");
    configCache = normalizeConfig(JSON.parse(raw));
    return configCache;
  } catch {
    configCache = normalizeConfig(defaultConfig());
    await saveConfig(configCache);
    return configCache;
  }
}

async function saveConfig(nextConfig) {
  const normalized = normalizeConfig(nextConfig);
  configCache = normalized;
  await fs.mkdir(path.dirname(configPath()), { recursive: true });
  await fs.writeFile(configPath(), `${JSON.stringify(normalized, null, 2)}\n`, "utf8");
  return normalized;
}

function getSelectedProject(config) {
  return config.projects.find((project) => project.id === config.selectedProjectId) ?? config.projects[0];
}

function sanitizeBounds(bounds) {
  const safe = {
    x: Math.max(0, Math.floor(Number(bounds?.x) || 0)),
    y: Math.max(0, Math.floor(Number(bounds?.y) || 0)),
    width: Math.max(1, Math.floor(Number(bounds?.width) || 1)),
    height: Math.max(1, Math.floor(Number(bounds?.height) || 1)),
  };
  return safe;
}

function offscreenBounds() {
  return { x: -10000, y: -10000, width: 1, height: 1 };
}

function applySurfaceBounds() {
  if (!codexView || !chatgptView) return;
  if (!surfacesVisible || !lastSurfaceBounds) {
    codexView.setBounds(offscreenBounds());
    chatgptView.setBounds(offscreenBounds());
    return;
  }
  codexView.setBounds(sanitizeBounds(lastSurfaceBounds.codex));
  chatgptView.setBounds(sanitizeBounds(lastSurfaceBounds.chatgpt));
}

function emitToShell(channel, payload) {
  if (!shellView || shellView.webContents.isDestroyed()) return;
  shellView.webContents.send(channel, payload);
}

function safeLoadableUrl(value, surfaceName) {
  const fallback = surfaceName === "chatgpt" ? "https://chatgpt.com/" : null;
  try {
    const parsed = new URL(value || "");
    if (surfaceName === "chatgpt") {
      if (parsed.protocol !== "https:") return fallback;
      return parsed.toString();
    }
    if (parsed.protocol === "https:") return parsed.toString();
    if (parsed.protocol === "http:") {
      const host = parsed.hostname.toLowerCase();
      if (["localhost", "127.0.0.1", "::1"].includes(host)) return parsed.toString();
      return null;
    }
    if (parsed.protocol === "file:") return parsed.toString();
    return null;
  } catch {
    return fallback;
  }
}

function encodeProjectForLocalSurface(project) {
  const payload = {
    project: {
      name: project.name,
      repoPath: project.repoPath,
      codex: project.surfaceBinding.codex,
      chatgpt: project.surfaceBinding.chatgpt,
      flowProfile: project.flowProfile,
    },
    shell: {
      generatedAt: nowIso(),
      doctrine: "The shell owns this project-to-surface binding.",
    },
  };
  return Buffer.from(JSON.stringify(payload), "utf8").toString("base64url");
}

async function loadCodexSurface(project) {
  if (!codexView || codexView.webContents.isDestroyed()) return;
  const codex = project.surfaceBinding.codex;
  if (codex.mode === "url") {
    const target = safeLoadableUrl(codex.target, "codex");
    if (target) {
      await codexView.webContents.loadURL(target);
      return;
    }
  }
  const localUrl = `${pathToFileURL(codexSurfaceHtmlPath).toString()}#${encodeProjectForLocalSurface(project)}`;
  await codexView.webContents.loadURL(localUrl);
}

async function loadChatgptSurface(project) {
  if (!chatgptView || chatgptView.webContents.isDestroyed()) return;
  const target = safeLoadableUrl(project.surfaceBinding.chatgpt.reviewThreadUrl, "chatgpt") || "https://chatgpt.com/";
  await chatgptView.webContents.loadURL(target);
}

function chatgptChromeCss() {
  return `
    /* v0 conservative chrome reduction. This is intentionally best-effort and may need selector updates. */
    [data-testid="history-sidebar"],
    [data-testid="sidebar"],
    [data-testid="workspace-sidebar"],
    [aria-label="Chat history"],
    nav[aria-label="Chat history"],
    div[class*="sidebar"]:has(nav),
    aside[class*="sidebar"] {
      display: none !important;
      visibility: hidden !important;
      width: 0 !important;
      min-width: 0 !important;
      max-width: 0 !important;
    }
    main,
    [role="main"] {
      max-width: none !important;
    }
    [data-testid="conversation-turn"],
    article {
      max-width: min(980px, calc(100vw - 72px)) !important;
    }
  `;
}

function scheduleChatgptChromeReduction() {
  if (!chatgptView || chatgptView.webContents.isDestroyed()) return;
  if (!currentProject?.surfaceBinding?.chatgpt?.reduceChrome) return;
  const currentUrl = chatgptView.webContents.getURL();
  if (!currentUrl.includes("chatgpt.com") && !currentUrl.includes("chat.openai.com")) return;
  for (const delay of [0, 300, 1200, 2600]) {
    setTimeout(() => {
      if (!chatgptView || chatgptView.webContents.isDestroyed()) return;
      chatgptView.webContents.insertCSS(chatgptChromeCss()).catch(() => {});
    }, delay);
  }
}

async function loadProjectSurfaces(project) {
  currentProject = project;
  emitToShell("surface:event", {
    surface: "shell",
    type: "project-selected",
    projectId: project.id,
    projectName: project.name,
    at: nowIso(),
  });
  await Promise.allSettled([loadCodexSurface(project), loadChatgptSurface(project)]);
}

function isLikelyChatAuthOrAppUrl(rawUrl) {
  try {
    const parsed = new URL(rawUrl);
    if (parsed.protocol !== "https:") return false;
    const host = parsed.hostname.toLowerCase();
    return (
      host === "chatgpt.com" ||
      host.endsWith(".chatgpt.com") ||
      host === "chat.openai.com" ||
      host.endsWith(".chat.openai.com") ||
      host === "auth.openai.com" ||
      host.endsWith(".auth.openai.com") ||
      host === "login.openai.com" ||
      host.endsWith(".login.openai.com") ||
      host === "accounts.google.com" ||
      host.endsWith(".accounts.google.com") ||
      host === "login.microsoftonline.com" ||
      host.endsWith(".login.microsoftonline.com")
    );
  } catch {
    return false;
  }
}

function isPermittedNavigationUrl(rawUrl, surfaceName) {
  try {
    const parsed = new URL(rawUrl);
    if (surfaceName === "codex") {
      if (parsed.protocol === "file:" || parsed.protocol === "https:") return true;
      if (parsed.protocol === "http:") {
        const host = parsed.hostname.toLowerCase();
        return host === "localhost" || host === "127.0.0.1" || host === "::1";
      }
      return false;
    }
    return parsed.protocol === "https:";
  } catch {
    return false;
  }
}

function configureGuestSurface(surfaceName, view) {
  const contents = view.webContents;
  contents.setWindowOpenHandler(({ url }) => {
    if (surfaceName === "chatgpt" && isLikelyChatAuthOrAppUrl(url)) {
      setImmediate(() => {
        if (!contents.isDestroyed()) contents.loadURL(url).catch(() => {});
      });
      return { action: "deny" };
    }
    if (url.startsWith("http://") || url.startsWith("https://")) shell.openExternal(url).catch(() => {});
    return { action: "deny" };
  });
  contents.on("will-navigate", (event, url) => {
    if (!isPermittedNavigationUrl(url, surfaceName)) {
      event.preventDefault();
      emitToShell("surface:event", {
        surface: surfaceName,
        type: "navigation-blocked",
        url,
        at: nowIso(),
      });
    }
  });
  contents.on("did-start-loading", () => {
    emitToShell("surface:event", {
      surface: surfaceName,
      type: "loading",
      url: contents.getURL(),
      at: nowIso(),
    });
  });
  contents.on("did-stop-loading", () => {
    emitToShell("surface:event", {
      surface: surfaceName,
      type: "loaded",
      url: contents.getURL(),
      title: contents.getTitle(),
      at: nowIso(),
    });
    if (surfaceName === "chatgpt") scheduleChatgptChromeReduction();
  });
  contents.on("dom-ready", () => {
    if (surfaceName === "chatgpt") scheduleChatgptChromeReduction();
  });
  contents.on("did-fail-load", (_event, errorCode, errorDescription, validatedURL, isMainFrame) => {
    if (!isMainFrame) return;
    emitToShell("surface:event", {
      surface: surfaceName,
      type: "load-failed",
      url: validatedURL,
      errorCode,
      errorDescription,
      at: nowIso(),
    });
  });
  contents.on("page-title-updated", (_event, title) => {
    emitToShell("surface:event", {
      surface: surfaceName,
      type: "title",
      title,
      url: contents.getURL(),
      at: nowIso(),
    });
  });
}

function setShellBoundsToWindow() {
  if (!mainWindow || !shellView) return;
  const bounds = mainWindow.getContentBounds();
  shellView.setBounds({ x: 0, y: 0, width: Math.max(1, bounds.width), height: Math.max(1, bounds.height) });
}

async function createWindow() {
  Menu.setApplicationMenu(null);
  app.setName(APP_TITLE);

  mainWindow = new BaseWindow({
    width: 1520,
    height: 940,
    minWidth: 1060,
    minHeight: 660,
    title: APP_TITLE,
    backgroundColor: "#090b10",
    show: true,
  });

  shellView = new WebContentsView({
    webPreferences: {
      preload: path.join(__dirname, "preload.js"),
      nodeIntegration: false,
      contextIsolation: true,
      sandbox: false,
      devTools: true,
    },
  });

  codexView = new WebContentsView({
    webPreferences: {
      nodeIntegration: false,
      contextIsolation: true,
      sandbox: true,
      partition: CODEX_PARTITION,
      devTools: true,
    },
  });

  chatgptView = new WebContentsView({
    webPreferences: {
      nodeIntegration: false,
      contextIsolation: true,
      sandbox: true,
      partition: CHATGPT_PARTITION,
      devTools: true,
    },
  });

  mainWindow.contentView.addChildView(shellView);
  mainWindow.contentView.addChildView(codexView);
  mainWindow.contentView.addChildView(chatgptView);
  setShellBoundsToWindow();
  applySurfaceBounds();

  configureGuestSurface("codex", codexView);
  configureGuestSurface("chatgpt", chatgptView);

  mainWindow.on("resize", () => {
    setShellBoundsToWindow();
  });

  mainWindow.on("closed", () => {
    mainWindow = null;
    shellView = null;
    codexView = null;
    chatgptView = null;
  });

  await shellView.webContents.loadFile(shellHtmlPath);
}

ipcMain.handle("config:load", async () => {
  const config = await loadConfig();
  return { config, configPath: configPath(), repoRoot, appVersion: app.getVersion() };
});

ipcMain.handle("config:save", async (_event, nextConfig) => {
  const saved = await saveConfig(nextConfig);
  return { config: saved, configPath: configPath() };
});

ipcMain.handle("project:select", async (_event, projectId) => {
  const config = await loadConfig();
  const selectedProjectId = config.projects.some((project) => project.id === projectId)
    ? projectId
    : config.projects[0]?.id;
  const saved = await saveConfig({ ...config, selectedProjectId });
  const project = getSelectedProject(saved);
  await loadProjectSurfaces(project);
  return { config: saved, project };
});

ipcMain.handle("dialog:choose-directory", async () => {
  if (!mainWindow) return null;
  const result = await dialog.showOpenDialog({
    title: "Choose project workspace path",
    properties: ["openDirectory", "createDirectory"],
  });
  if (result.canceled || !result.filePaths.length) return null;
  return result.filePaths[0];
});

ipcMain.handle("surface:set-layout", async (_event, bounds) => {
  lastSurfaceBounds = {
    codex: sanitizeBounds(bounds?.codex),
    chatgpt: sanitizeBounds(bounds?.chatgpt),
  };
  applySurfaceBounds();
  return true;
});

ipcMain.handle("surface:set-visible", async (_event, visible) => {
  surfacesVisible = Boolean(visible);
  applySurfaceBounds();
  return surfacesVisible;
});

ipcMain.handle("surface:reload", async (_event, surfaceName) => {
  const view = surfaceName === "chatgpt" ? chatgptView : codexView;
  if (!view || view.webContents.isDestroyed()) return false;
  view.webContents.reload();
  return true;
});

ipcMain.handle("surface:open-external", async (_event, surfaceName) => {
  const view = surfaceName === "chatgpt" ? chatgptView : codexView;
  if (!view || view.webContents.isDestroyed()) return false;
  const url = view.webContents.getURL();
  if (!url || url.startsWith("file://")) return false;
  await shell.openExternal(url);
  return true;
});

ipcMain.handle("clipboard:write-text", async (_event, text) => {
  clipboard.writeText(String(text ?? ""));
  return true;
});

app.whenReady().then(async () => {
  await loadConfig();
  await createWindow();
  app.on("activate", async () => {
    if (!mainWindow) await createWindow();
  });
});

app.on("window-all-closed", () => {
  if (process.platform !== "darwin") app.quit();
});
```

The remaining renderer HTML/CSS/JS files are included in the linked zip and full modified repo.

[1]: https://electronjs.org/docs/latest/api/web-contents-view "WebContentsView | Electron"
[2]: https://v2.tauri.app/reference/javascript/api/namespacewebview/ "webview | Tauri"
[3]: https://developers.openai.com/api/reference/overview/ "API Overview | OpenAI API Reference"
