import { app, BrowserWindow, Menu, dialog, ipcMain, shell } from "electron";
import { spawn } from "node:child_process";
import { access, mkdir, readFile, readdir, stat, writeFile } from "node:fs/promises";
import path from "node:path";

import {
  DEFAULT_API_BASE_URL,
  DEFAULT_LAUNCH_PROFILES,
  type CopilotSessionResponse,
  type CopilotStreamEnvelope,
  type FileDiffResult,
  type GitSnapshot,
  type HostPersistedState,
  type PolicyProfileCurrentResponse,
  type PolicyProfileListResponse,
  type PolicyProfileSelectResponse,
  type TerminalPresetId,
  type TerminalPresetResult,
  type ToolCallRequestArgs,
  type ToolCallResponse,
  type WorkspaceTreeNode,
} from "./shared/types";

const distRoot = __dirname;
const appRoot = path.resolve(distRoot, "..");
const repoRoot = path.resolve(appRoot, "..", "..");
const rendererHtmlPath = path.join(distRoot, "renderer", "index.html");
const smokeExitMs = Number.parseInt(process.env.OPUS_WORKBENCH_SMOKE_EXIT_MS ?? "", 10);

const MAX_FILE_BYTES = 220_000;
const MAX_DIFF_BYTES = 220_000;
const SESSION_HISTORY_LIMIT = 10;
const HIDDEN_NAMES = new Set([
  ".git",
  ".next",
  ".venv",
  "__pycache__",
  "node_modules",
  "dist",
]);

const TERMINAL_PRESETS: Record<TerminalPresetId, { command: string }> = {
  pwd: { command: "pwd" },
  git_status: { command: "git status --short --branch" },
  git_diff_stat: { command: "git diff --stat" },
  git_log: { command: "git log --oneline -n 8" },
  ls: { command: "ls -la" },
};

let mainWindow: BrowserWindow | null = null;
let hostStateCache: HostPersistedState | null = null;
const streamControllers = new Map<string, AbortController>();

function defaultHostState(): HostPersistedState {
  return {
    workspaceRoot: repoRoot,
    apiBaseUrl: DEFAULT_API_BASE_URL,
    selectedLaunchProfileId: DEFAULT_LAUNCH_PROFILES[0].id,
    recentSessions: [],
  };
}

function hostStatePath(): string {
  return path.join(app.getPath("userData"), "host-state.json");
}

async function loadHostState(): Promise<HostPersistedState> {
  if (hostStateCache) return hostStateCache;
  const defaults = defaultHostState();
  try {
    const raw = await readFile(hostStatePath(), "utf8");
    const parsed = JSON.parse(raw) as Partial<HostPersistedState>;
    const workspaceRoot =
      typeof parsed.workspaceRoot === "string" && parsed.workspaceRoot.trim()
        ? parsed.workspaceRoot
        : defaults.workspaceRoot;
    const apiBaseUrl =
      typeof parsed.apiBaseUrl === "string" && parsed.apiBaseUrl.trim()
        ? parsed.apiBaseUrl
        : defaults.apiBaseUrl;
    const selectedLaunchProfileId =
      typeof parsed.selectedLaunchProfileId === "string" &&
      DEFAULT_LAUNCH_PROFILES.some((profile) => profile.id === parsed.selectedLaunchProfileId)
        ? parsed.selectedLaunchProfileId
        : defaults.selectedLaunchProfileId;
    const recentSessions = Array.isArray(parsed.recentSessions)
      ? parsed.recentSessions
          .filter(
            (entry): entry is HostPersistedState["recentSessions"][number] =>
              typeof entry === "object" &&
              entry !== null &&
              typeof entry.sessionId === "string" &&
              typeof entry.startedAt === "string" &&
              typeof entry.launchProfileId === "string",
          )
          .slice(0, SESSION_HISTORY_LIMIT)
      : defaults.recentSessions;
    hostStateCache = {
      workspaceRoot,
      apiBaseUrl,
      selectedLaunchProfileId,
      recentSessions,
    };
    return hostStateCache;
  } catch {
    hostStateCache = defaults;
    return hostStateCache;
  }
}

async function saveHostState(nextState: HostPersistedState): Promise<HostPersistedState> {
  hostStateCache = nextState;
  await mkdir(path.dirname(hostStatePath()), { recursive: true });
  await writeFile(hostStatePath(), JSON.stringify(nextState, null, 2) + "\n", "utf8");
  return nextState;
}

async function patchHostState(
  partial: Partial<HostPersistedState>,
): Promise<HostPersistedState> {
  const current = await loadHostState();
  return saveHostState({
    workspaceRoot:
      typeof partial.workspaceRoot === "string" && partial.workspaceRoot.trim()
        ? partial.workspaceRoot
        : current.workspaceRoot,
    apiBaseUrl:
      typeof partial.apiBaseUrl === "string" && partial.apiBaseUrl.trim()
        ? partial.apiBaseUrl
        : current.apiBaseUrl,
    selectedLaunchProfileId:
      typeof partial.selectedLaunchProfileId === "string" &&
      DEFAULT_LAUNCH_PROFILES.some((profile) => profile.id === partial.selectedLaunchProfileId)
        ? partial.selectedLaunchProfileId
        : current.selectedLaunchProfileId,
    recentSessions: Array.isArray(partial.recentSessions)
      ? partial.recentSessions.slice(0, SESSION_HISTORY_LIMIT)
      : current.recentSessions,
  });
}

function normalizeApiBaseUrl(baseUrl: string): string {
  return baseUrl.endsWith("/") ? baseUrl : `${baseUrl}/`;
}

function resolveWorkspacePath(workspaceRoot: string, relativePath = ""): string {
  const absolute = path.resolve(workspaceRoot, relativePath);
  const normalizedRoot = path.resolve(workspaceRoot);
  if (
    absolute !== normalizedRoot &&
    !absolute.startsWith(`${normalizedRoot}${path.sep}`)
  ) {
    throw new Error("Path escapes the selected workspace.");
  }
  return absolute;
}

async function ensureWorkspaceRoot(workspaceRoot: string): Promise<void> {
  const absolute = path.resolve(workspaceRoot);
  const stats = await stat(absolute);
  if (!stats.isDirectory()) {
    throw new Error("Selected workspace root is not a directory.");
  }
}

async function listDirectory(relativePath = ""): Promise<WorkspaceTreeNode[]> {
  const { workspaceRoot } = await loadHostState();
  await ensureWorkspaceRoot(workspaceRoot);
  const absolute = resolveWorkspacePath(workspaceRoot, relativePath);
  const entries = await readdir(absolute, { withFileTypes: true });
  const next: WorkspaceTreeNode[] = [];

  for (const entry of entries) {
    if (HIDDEN_NAMES.has(entry.name)) continue;
    const entryRelativePath = path.posix.join(
      relativePath.replaceAll("\\", "/"),
      entry.name,
    );
    if (entry.isDirectory()) {
      let hasChildren = false;
      try {
        const childEntries = await readdir(path.join(absolute, entry.name));
        hasChildren = childEntries.some((child) => !HIDDEN_NAMES.has(child));
      } catch {
        hasChildren = false;
      }
      next.push({
        name: entry.name,
        relativePath: entryRelativePath,
        kind: "dir",
        hasChildren,
      });
      continue;
    }
    if (entry.isFile()) {
      next.push({
        name: entry.name,
        relativePath: entryRelativePath,
        kind: "file",
        hasChildren: false,
      });
    }
  }

  return next.sort((left, right) => {
    if (left.kind !== right.kind) return left.kind === "dir" ? -1 : 1;
    return left.name.localeCompare(right.name);
  });
}

async function readWorkspaceFile(relativePath: string) {
  const { workspaceRoot } = await loadHostState();
  await ensureWorkspaceRoot(workspaceRoot);
  const absolute = resolveWorkspacePath(workspaceRoot, relativePath);
  const buffer = await readFile(absolute);
  const truncated = buffer.byteLength > MAX_FILE_BYTES;
  const text = buffer
    .subarray(0, truncated ? MAX_FILE_BYTES : buffer.byteLength)
    .toString("utf8");
  return {
    relativePath,
    absolutePath: absolute,
    content: text,
    truncated,
    approxLineCount: text.split(/\r?\n/).length,
  };
}

type CommandResult = {
  stdout: string;
  stderr: string;
  exitCode: number;
};

async function runShellCommand(command: string, cwd: string): Promise<CommandResult> {
  return new Promise((resolve) => {
    const child = spawn("bash", ["-lc", command], {
      cwd,
      stdio: ["ignore", "pipe", "pipe"],
      env: process.env,
    });
    let stdout = "";
    let stderr = "";
    child.stdout.on("data", (chunk: Buffer | string) => {
      stdout += chunk.toString();
    });
    child.stderr.on("data", (chunk: Buffer | string) => {
      stderr += chunk.toString();
    });
    child.on("close", (code) => {
      resolve({ stdout, stderr, exitCode: code ?? 1 });
    });
    child.on("error", (error) => {
      resolve({ stdout, stderr: `${stderr}${String(error)}`, exitCode: 1 });
    });
  });
}

async function runGitCommand(args: string[], cwd: string): Promise<CommandResult> {
  return new Promise((resolve) => {
    const child = spawn("git", args, {
      cwd,
      stdio: ["ignore", "pipe", "pipe"],
      env: process.env,
    });
    let stdout = "";
    let stderr = "";
    child.stdout.on("data", (chunk: Buffer | string) => {
      stdout += chunk.toString();
    });
    child.stderr.on("data", (chunk: Buffer | string) => {
      stderr += chunk.toString();
    });
    child.on("close", (code) => {
      resolve({ stdout, stderr, exitCode: code ?? 1 });
    });
    child.on("error", (error) => {
      resolve({ stdout, stderr: `${stderr}${String(error)}`, exitCode: 1 });
    });
  });
}

async function getGitSnapshot(): Promise<GitSnapshot> {
  const { workspaceRoot } = await loadHostState();
  await ensureWorkspaceRoot(workspaceRoot);
  const branch = await runGitCommand(["rev-parse", "--abbrev-ref", "HEAD"], workspaceRoot);
  if (branch.exitCode !== 0) {
    return {
      isRepo: false,
      branch: "unavailable",
      shortStatus: [],
      recentCommits: [],
      diffStat: "",
      error: branch.stderr.trim() || "Workspace is not a git repository.",
    };
  }
  const [status, recentCommits, diffStat] = await Promise.all([
    runGitCommand(["status", "--short", "--branch"], workspaceRoot),
    runGitCommand(["log", "--oneline", "-n", "8"], workspaceRoot),
    runGitCommand(["diff", "--stat"], workspaceRoot),
  ]);
  return {
    isRepo: true,
    branch: branch.stdout.trim() || "HEAD",
    shortStatus: status.stdout
      .split(/\r?\n/)
      .map((line) => line.trimEnd())
      .filter(Boolean),
    recentCommits: recentCommits.stdout
      .split(/\r?\n/)
      .map((line) => line.trim())
      .filter(Boolean),
    diffStat: diffStat.stdout.trim(),
  };
}

async function getFileDiff(relativePath?: string | null): Promise<FileDiffResult> {
  const { workspaceRoot } = await loadHostState();
  await ensureWorkspaceRoot(workspaceRoot);
  const args = ["diff", "--no-ext-diff"];
  let target: string | null = null;
  if (relativePath && relativePath.trim()) {
    resolveWorkspacePath(workspaceRoot, relativePath);
    target = relativePath;
    args.push("--", relativePath);
  }
  const result = await runGitCommand(args, workspaceRoot);
  if (result.exitCode !== 0) {
    return {
      target,
      diffText: "",
      truncated: false,
      error: result.stderr.trim() || "Unable to read git diff.",
    };
  }
  const truncated = Buffer.byteLength(result.stdout, "utf8") > MAX_DIFF_BYTES;
  return {
    target,
    diffText: result.stdout.slice(0, MAX_DIFF_BYTES),
    truncated,
  };
}

async function runTerminalPreset(commandId: TerminalPresetId): Promise<TerminalPresetResult> {
  const preset = TERMINAL_PRESETS[commandId];
  if (!preset) {
    throw new Error(`Unsupported terminal preset: ${commandId}`);
  }
  const { workspaceRoot } = await loadHostState();
  await ensureWorkspaceRoot(workspaceRoot);
  const result = await runShellCommand(preset.command, workspaceRoot);
  return {
    commandId,
    command: preset.command,
    stdout: result.stdout,
    stderr: result.stderr,
    exitCode: result.exitCode,
    ranAt: new Date().toISOString(),
    readOnly: true,
  };
}

async function parseErrorMessage(response: Response): Promise<string> {
  const text = await response.text();
  if (!text) return `HTTP ${response.status}`;
  try {
    const parsed = JSON.parse(text) as {
      detail?: { code?: string; message?: string };
      message?: string;
      error?: string;
    };
    if (parsed.detail?.code && parsed.detail.message) {
      return `${parsed.detail.code}: ${parsed.detail.message}`;
    }
    if (typeof parsed.message === "string") return parsed.message;
    if (typeof parsed.error === "string") return parsed.error;
  } catch {
    // ignore
  }
  return text;
}

async function requestJson<T>(pathname: string, init?: RequestInit): Promise<T> {
  const { apiBaseUrl } = await loadHostState();
  const url = new URL(pathname, normalizeApiBaseUrl(apiBaseUrl));
  const response = await fetch(url, init);
  if (!response.ok) {
    throw new Error(await parseErrorMessage(response));
  }
  return (await response.json()) as T;
}

function requestId(): string {
  return typeof crypto !== "undefined" && "randomUUID" in crypto
    ? crypto.randomUUID()
    : `${Date.now()}-${Math.random().toString(16).slice(2)}`;
}

async function startSession(): Promise<CopilotSessionResponse> {
  const response = await requestJson<CopilotSessionResponse>("/urm/copilot/start", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      provider: "codex",
      client_request_id: requestId(),
    }),
  });
  const current = await loadHostState();
  const recentSessions = [
    {
      sessionId: response.session_id,
      startedAt: new Date().toISOString(),
      launchProfileId: current.selectedLaunchProfileId,
    },
    ...current.recentSessions.filter((item) => item.sessionId !== response.session_id),
  ].slice(0, SESSION_HISTORY_LIMIT);
  await patchHostState({ recentSessions });
  return response;
}

async function stopSession(sessionId: string): Promise<CopilotSessionResponse> {
  await stopCopilotStream(sessionId);
  return requestJson<CopilotSessionResponse>("/urm/copilot/stop", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      provider: "codex",
      session_id: sessionId,
    }),
  });
}

async function sendMessage(sessionId: string, text: string): Promise<CopilotSessionResponse> {
  return requestJson<CopilotSessionResponse>("/urm/copilot/send", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      provider: "codex",
      session_id: sessionId,
      client_request_id: requestId(),
      message: {
        jsonrpc: "2.0",
        id: requestId(),
        method: "copilot.user_message",
        params: { text },
      },
    }),
  });
}

async function setWrites(
  sessionId: string,
  writesAllowed: boolean,
): Promise<CopilotSessionResponse> {
  let approvalId: string | null = null;
  if (writesAllowed) {
    const approval = await requestJson<{ approval_id: string }>("/urm/approval/issue", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        provider: "codex",
        session_id: sessionId,
        action_kind: "urm.set_mode.enable_writes",
        action_payload: { writes_allowed: true },
      }),
    });
    approvalId = approval.approval_id;
  }
  return requestJson<CopilotSessionResponse>("/urm/copilot/mode", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      provider: "codex",
      session_id: sessionId,
      writes_allowed: writesAllowed,
      approval_id: approvalId,
    }),
  });
}

async function callTool(args: ToolCallRequestArgs): Promise<ToolCallResponse> {
  return requestJson<ToolCallResponse>("/urm/tools/call", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      provider: "codex",
      role: "copilot",
      session_id: args.sessionId ?? null,
      tool_name: args.toolName,
      arguments: args.argumentsValue,
    }),
  });
}

async function listPolicyProfiles(): Promise<PolicyProfileListResponse> {
  return requestJson<PolicyProfileListResponse>("/urm/policy/profile/list?provider=codex");
}

async function getCurrentPolicyProfile(
  sessionId: string,
): Promise<PolicyProfileCurrentResponse> {
  return requestJson<PolicyProfileCurrentResponse>(
    `/urm/policy/profile/current?provider=codex&session_id=${encodeURIComponent(sessionId)}`,
  );
}

async function selectPolicyProfile(
  sessionId: string,
  profileId: string,
): Promise<PolicyProfileSelectResponse> {
  return requestJson<PolicyProfileSelectResponse>("/urm/policy/profile/select", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      provider: "codex",
      session_id: sessionId,
      profile_id: profileId,
      client_request_id: requestId(),
    }),
  });
}

function parseSseFrame(rawFrame: string): { eventType: string; payload: unknown } | null {
  const trimmed = rawFrame.trim();
  if (!trimmed) return null;
  let eventType = "message";
  const data: string[] = [];
  for (const line of trimmed.split(/\r?\n/)) {
    if (line.startsWith("event:")) {
      eventType = line.slice("event:".length).trim();
      continue;
    }
    if (line.startsWith("data:")) {
      data.push(line.slice("data:".length).trim());
    }
  }
  const rawData = data.join("\n");
  if (!rawData) return null;
  try {
    return { eventType, payload: JSON.parse(rawData) };
  } catch {
    return { eventType, payload: { raw: rawData } };
  }
}

function emitCopilotEvent(envelope: CopilotStreamEnvelope): void {
  if (!mainWindow || mainWindow.isDestroyed()) return;
  mainWindow.webContents.send("adeu:copilot-event", envelope);
}

async function startCopilotStream(sessionId: string): Promise<void> {
  await stopCopilotStream(sessionId);
  const { apiBaseUrl } = await loadHostState();
  const controller = new AbortController();
  streamControllers.set(sessionId, controller);
  emitCopilotEvent({ sessionId, eventType: "stream_status", payload: { status: "connecting" } });

  const url = new URL("/urm/copilot/events", normalizeApiBaseUrl(apiBaseUrl));
  url.searchParams.set("provider", "codex");
  url.searchParams.set("session_id", sessionId);
  url.searchParams.set("after_seq", "0");

  try {
    const response = await fetch(url, {
      headers: { accept: "text/event-stream" },
      signal: controller.signal,
    });
    if (!response.ok || !response.body) {
      throw new Error(await parseErrorMessage(response));
    }
    emitCopilotEvent({ sessionId, eventType: "stream_status", payload: { status: "connected" } });
    const reader = response.body.getReader();
    const decoder = new TextDecoder();
    let buffer = "";
    while (true) {
      const { value, done } = await reader.read();
      if (done) break;
      buffer += decoder.decode(value, { stream: true });
      let boundaryIndex = buffer.indexOf("\n\n");
      while (boundaryIndex >= 0) {
        const frame = buffer.slice(0, boundaryIndex);
        buffer = buffer.slice(boundaryIndex + 2);
        const parsed = parseSseFrame(frame);
        if (parsed) {
          emitCopilotEvent({
            sessionId,
            eventType: parsed.eventType,
            payload: parsed.payload,
          });
        }
        boundaryIndex = buffer.indexOf("\n\n");
      }
    }
  } catch (error) {
    if (!controller.signal.aborted) {
      emitCopilotEvent({
        sessionId,
        eventType: "stream_error",
        payload: { message: String(error) },
      });
    }
  } finally {
    if (streamControllers.get(sessionId) === controller) {
      streamControllers.delete(sessionId);
    }
    emitCopilotEvent({ sessionId, eventType: "stream_status", payload: { status: "disconnected" } });
  }
}

async function stopCopilotStream(sessionId: string): Promise<void> {
  const controller = streamControllers.get(sessionId);
  if (!controller) return;
  controller.abort();
  streamControllers.delete(sessionId);
}

async function createMainWindow(): Promise<void> {
  const iconPath = undefined;
  mainWindow = new BrowserWindow({
    width: 1680,
    height: 1120,
    minWidth: 1180,
    minHeight: 820,
    title: "GPT-5.4 Codex ADEU Desktop Workbench",
    icon: iconPath,
    backgroundColor: "#e7dfd3",
    webPreferences: {
      preload: path.join(distRoot, "preload.js"),
      contextIsolation: true,
      nodeIntegration: false,
      sandbox: false,
    },
  });

  if (Number.isFinite(smokeExitMs) && smokeExitMs > 0) {
    mainWindow.webContents.once("did-finish-load", () => {
      setTimeout(() => {
        app.exit(0);
      }, smokeExitMs);
    });
  }

  await mainWindow.loadFile(rendererHtmlPath);
  buildMenu();
}

function buildMenu(): void {
  const template: Electron.MenuItemConstructorOptions[] = [
    {
      label: "File",
      submenu: [
        {
          label: "Open Workspace…",
          click: async () => {
            const chosen = await chooseWorkspaceRoot();
            if (chosen) {
              mainWindow?.webContents.send("adeu:copilot-event", {
                sessionId: "host",
                eventType: "workspace_changed",
                payload: { workspaceRoot: chosen },
              } satisfies CopilotStreamEnvelope);
            }
          },
        },
        {
          label: "Reveal Workspace",
          click: async () => {
            const state = await loadHostState();
            await shell.openPath(state.workspaceRoot);
          },
        },
        { type: "separator" },
        { role: "quit" },
      ],
    },
    {
      label: "View",
      submenu: [{ role: "reload" }, { role: "forceReload" }, { role: "toggleDevTools" }],
    },
  ];
  Menu.setApplicationMenu(Menu.buildFromTemplate(template));
}

async function chooseWorkspaceRoot(): Promise<string | null> {
  const current = await loadHostState();
  const result = await dialog.showOpenDialog(mainWindow!, {
    defaultPath: current.workspaceRoot,
    properties: ["openDirectory"],
    title: "Select ADEU workspace root",
  });
  if (result.canceled || result.filePaths.length === 0) return null;
  const nextRoot = result.filePaths[0];
  await patchHostState({ workspaceRoot: nextRoot });
  return nextRoot;
}

ipcMain.handle("host:get-state", async () => loadHostState());
ipcMain.handle("host:update-state", async (_event, partial: Partial<HostPersistedState>) =>
  patchHostState(partial),
);
ipcMain.handle("workspace:choose-root", async () => chooseWorkspaceRoot());
ipcMain.handle("workspace:list-directory", async (_event, relativePath?: string) =>
  listDirectory(relativePath ?? ""),
);
ipcMain.handle("workspace:read-file", async (_event, relativePath: string) =>
  readWorkspaceFile(relativePath),
);
ipcMain.handle("git:get-snapshot", async () => getGitSnapshot());
ipcMain.handle("git:get-diff", async (_event, relativePath?: string | null) =>
  getFileDiff(relativePath),
);
ipcMain.handle("terminal:run-preset", async (_event, commandId: TerminalPresetId) =>
  runTerminalPreset(commandId),
);
ipcMain.handle("adeu:start-session", async () => startSession());
ipcMain.handle("adeu:stop-session", async (_event, sessionId: string) => stopSession(sessionId));
ipcMain.handle(
  "adeu:send-message",
  async (_event, payload: { sessionId: string; text: string }) =>
    sendMessage(payload.sessionId, payload.text),
);
ipcMain.handle(
  "adeu:set-writes",
  async (_event, payload: { sessionId: string; writesAllowed: boolean }) =>
    setWrites(payload.sessionId, payload.writesAllowed),
);
ipcMain.handle("adeu:call-tool", async (_event, args: ToolCallRequestArgs) => callTool(args));
ipcMain.handle("adeu:list-policy-profiles", async () => listPolicyProfiles());
ipcMain.handle(
  "adeu:get-current-policy-profile",
  async (_event, sessionId: string) => getCurrentPolicyProfile(sessionId),
);
ipcMain.handle(
  "adeu:select-policy-profile",
  async (_event, payload: { sessionId: string; profileId: string }) =>
    selectPolicyProfile(payload.sessionId, payload.profileId),
);
ipcMain.handle("adeu:start-stream", async (_event, sessionId: string) =>
  startCopilotStream(sessionId),
);
ipcMain.handle("adeu:stop-stream", async (_event, sessionId: string) =>
  stopCopilotStream(sessionId),
);

app
  .whenReady()
  .then(async () => {
    await mkdir(path.dirname(hostStatePath()), { recursive: true });
    try {
      await access(rendererHtmlPath);
    } catch {
      throw new Error(
        "Renderer bundle is missing. Run `npm run build` inside apps/gpt54-codex-workbench first.",
      );
    }
    await createMainWindow();
  })
  .catch((error) => {
    console.error(error);
    app.exit(1);
  });

app.on("window-all-closed", () => {
  if (process.platform !== "darwin") {
    app.quit();
  }
});

app.on("before-quit", () => {
  for (const controller of streamControllers.values()) {
    controller.abort();
  }
  streamControllers.clear();
});

app.on("activate", async () => {
  if (BrowserWindow.getAllWindows().length === 0) {
    await createMainWindow();
  }
});
