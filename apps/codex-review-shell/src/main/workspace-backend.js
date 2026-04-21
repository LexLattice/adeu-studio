"use strict";

/**
 * Host-side workspace backend transport.
 *
 * The Electron host owns UI and browser surfaces. Workspace truth is delegated to
 * a resident backend process. For WSL workspaces on Windows this starts one
 * long-lived `wsl.exe` process running `src/backend/wsl-agent.js` inside the
 * selected distro/root. For local/dev workspaces it starts the same agent as a
 * local child process.
 */

const { EventEmitter } = require("node:events");
const { spawn } = require("node:child_process");
const path = require("node:path");
const crypto = require("node:crypto");

const DEFAULT_REQUEST_TIMEOUT_MS = 10_000;
const ATTACH_TIMEOUT_MS = 8_000;

function isPlainObject(value) {
  return Boolean(value) && typeof value === "object" && !Array.isArray(value);
}

function normalizeString(value, fallback = "") {
  return typeof value === "string" && value.trim() ? value.trim() : fallback;
}

function normalizeWorkspace(input, repoPath, fallbackRoot) {
  const raw = isPlainObject(input) ? input : null;
  if (raw?.kind === "wsl") {
    return {
      kind: "wsl",
      distro: normalizeString(raw.distro, ""),
      linuxPath: normalizeLinuxPath(raw.linuxPath, "/home"),
      label: normalizeString(raw.label, ""),
    };
  }
  return {
    kind: "local",
    localPath: normalizeString(raw?.localPath, normalizeString(repoPath, fallbackRoot)),
    label: normalizeString(raw?.label, ""),
  };
}

function normalizeLinuxPath(value, fallback = "/home") {
  const text = normalizeString(value, fallback).replace(/\\/g, "/");
  return text.startsWith("/") ? text : `/${text}`;
}

function workspaceRoot(project, fallbackRoot) {
  const workspace = normalizeWorkspace(project?.workspace, project?.repoPath, fallbackRoot);
  return workspace.kind === "wsl" ? workspace.linuxPath : workspace.localPath;
}

function workspaceLabel(project, fallbackRoot) {
  const workspace = normalizeWorkspace(project?.workspace, project?.repoPath, fallbackRoot);
  if (workspace.kind === "wsl") {
    const distro = workspace.distro ? `${workspace.distro}:` : "default:";
    return `WSL ${distro}${workspace.linuxPath}`;
  }
  return `Local ${workspace.localPath}`;
}

function workspaceSessionKey(project, fallbackRoot) {
  const workspace = normalizeWorkspace(project?.workspace, project?.repoPath, fallbackRoot);
  if (workspace.kind === "wsl") return `wsl:${workspace.distro || "default"}:${workspace.linuxPath}`;
  return `local:${path.resolve(workspace.localPath || fallbackRoot || ".")}`;
}

function cleanEnvForLocalAgent() {
  return {
    ...process.env,
    ELECTRON_RUN_AS_NODE: "1",
  };
}

function launchDescriptor(project, options) {
  const workspace = normalizeWorkspace(project.workspace, project.repoPath, options.fallbackRoot);
  const agentPath = options.agentPath;
  const projectId = project.id || "unknown-project";

  if (workspace.kind === "wsl" && process.platform === "win32") {
    const args = [];
    if (workspace.distro) args.push("-d", workspace.distro);
    args.push(
      "--cd",
      workspace.linuxPath,
      "--",
      "bash",
      "-lc",
      [
        "set -e",
        "if ! command -v node >/dev/null 2>&1; then echo 'Node.js is required inside the selected WSL distro.' >&2; exit 127; fi",
        "AGENT_PATH=$(wslpath -a \"$1\")",
        "exec node \"$AGENT_PATH\" --root \"$PWD\" --workspace-kind wsl --project-id \"$2\"",
      ].join("; "),
      "adeu-wsl-agent-launch",
      agentPath,
      projectId,
    );
    return {
      command: "wsl.exe",
      args,
      cwd: undefined,
      env: process.env,
      transport: "wsl.exe",
      workspace,
    };
  }

  // Local/dev path. This is also used when running from Linux/WSL directly so
  // the same config can be smoke-tested without a native Windows host.
  const root = workspace.kind === "wsl" ? workspace.linuxPath : workspace.localPath;
  return {
    command: process.execPath,
    args: [agentPath, "--root", root, "--workspace-kind", workspace.kind, "--project-id", projectId],
    cwd: root,
    env: cleanEnvForLocalAgent(),
    transport: workspace.kind === "wsl" ? "direct-linux-dev" : "local-child",
    workspace,
  };
}

class NdjsonTransport extends EventEmitter {
  constructor(child) {
    super();
    this.child = child;
    this.buffer = "";
    this.pending = new Map();
    this.closed = false;

    child.stdout.setEncoding("utf8");
    child.stdout.on("data", (chunk) => this.handleData(chunk));
    child.stderr.setEncoding("utf8");
    child.stderr.on("data", (chunk) => this.emit("stderr", chunk));
    child.on("error", (error) => this.close(error));
    child.on("exit", (code, signal) => {
      const error = new Error(`Workspace backend exited: code=${code ?? "null"} signal=${signal ?? "null"}`);
      error.exitCode = code;
      error.signal = signal;
      this.close(error);
      this.emit("exit", { code, signal });
    });
  }

  handleData(chunk) {
    this.buffer += chunk;
    let newlineIndex = this.buffer.indexOf("\n");
    while (newlineIndex >= 0) {
      const line = this.buffer.slice(0, newlineIndex).trim();
      this.buffer = this.buffer.slice(newlineIndex + 1);
      if (line) this.handleLine(line);
      newlineIndex = this.buffer.indexOf("\n");
    }
  }

  handleLine(line) {
    let message;
    try {
      message = JSON.parse(line);
    } catch (error) {
      this.emit("event", { type: "protocol-error", error: `Invalid backend JSON: ${error.message}`, raw: line });
      return;
    }

    if (message.event) {
      this.emit("event", message);
      return;
    }

    if (message.id !== undefined && this.pending.has(message.id)) {
      const pending = this.pending.get(message.id);
      this.pending.delete(message.id);
      clearTimeout(pending.timer);
      if (message.error) {
        const error = new Error(message.error.message || "Workspace backend request failed.");
        error.backendStack = message.error.stack;
        pending.reject(error);
      } else {
        pending.resolve(message.result);
      }
      return;
    }

    this.emit("event", { type: "unmatched-message", message });
  }

  request(method, params = {}, timeoutMs = DEFAULT_REQUEST_TIMEOUT_MS) {
    if (this.closed) return Promise.reject(new Error("Workspace backend transport is closed."));
    const id = crypto.randomUUID();
    const payload = { id, method, params };
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`Workspace backend request timed out: ${method}`));
      }, timeoutMs);
      this.pending.set(id, { resolve, reject, timer, method });
      this.child.stdin.write(`${JSON.stringify(payload)}\n`, (error) => {
        if (!error) return;
        clearTimeout(timer);
        this.pending.delete(id);
        reject(error);
      });
    });
  }

  close(error) {
    if (this.closed) return;
    this.closed = true;
    for (const [id, pending] of this.pending.entries()) {
      clearTimeout(pending.timer);
      pending.reject(error || new Error("Workspace backend transport closed."));
      this.pending.delete(id);
    }
    this.emit("closed", error);
  }

  dispose() {
    this.close(new Error("Workspace backend disposed."));
    try {
      this.child.stdin.end();
    } catch {}
    if (!this.child.killed) {
      this.child.kill();
    }
  }
}

class WorkspaceSession extends EventEmitter {
  constructor(project, options) {
    super();
    this.project = project;
    this.options = options;
    this.key = workspaceSessionKey(project, options.fallbackRoot);
    this.child = null;
    this.transport = null;
    this.status = "idle";
    this.attachPromise = null;
    this.descriptor = null;
    this.hello = null;
    this.lastError = null;
  }

  snapshot() {
    return {
      key: this.key,
      projectId: this.project.id,
      projectName: this.project.name,
      status: this.status,
      transport: this.descriptor?.transport || "not-started",
      workspace: this.descriptor?.workspace || normalizeWorkspace(this.project.workspace, this.project.repoPath, this.options.fallbackRoot),
      hello: this.hello,
      lastError: this.lastError,
    };
  }

  emitStatus(type, extra = {}) {
    const payload = { type, session: this.snapshot(), at: new Date().toISOString(), ...extra };
    this.emit("status", payload);
  }

  async attach() {
    if (this.status === "attached" && this.transport && !this.transport.closed) return this;
    if (this.attachPromise) return this.attachPromise;

    this.attachPromise = this.attachInner()
      .then(() => {
        this.attachPromise = null;
        return this;
      })
      .catch((error) => {
        this.attachPromise = null;
        throw error;
      });
    return this.attachPromise;
  }

  async attachInner() {
    this.status = "starting";
    this.lastError = null;
    this.descriptor = launchDescriptor(this.project, this.options);
    this.emitStatus("backend-starting");

    this.child = spawn(this.descriptor.command, this.descriptor.args, {
      cwd: this.descriptor.cwd,
      env: this.descriptor.env,
      stdio: ["pipe", "pipe", "pipe"],
      windowsHide: true,
    });
    this.transport = new NdjsonTransport(this.child);
    this.transport.on("event", (event) => {
      this.emit("agent-event", { session: this.snapshot(), event });
      if (event.event === "ready") this.emitStatus("backend-agent-ready", { agent: event });
      if (event.event === "startup-error") {
        this.lastError = event.error;
        this.status = "failed";
        this.emitStatus("backend-failed", { error: event.error });
      }
    });
    this.transport.on("stderr", (chunk) => {
      const text = String(chunk || "").trim();
      if (text) this.emitStatus("backend-stderr", { stderr: text.slice(0, 2000) });
    });
    this.transport.on("closed", (error) => {
      if (this.status !== "failed" && this.status !== "disposed") {
        this.status = "closed";
        this.lastError = error?.message || "Backend closed.";
        this.emitStatus("backend-closed", { error: this.lastError });
      }
    });

    this.status = "attaching";
    try {
      this.hello = await this.transport.request("hello", {}, ATTACH_TIMEOUT_MS);
      this.status = "attached";
      this.emitStatus("backend-attached");
    } catch (error) {
      this.status = "failed";
      this.lastError = error.message;
      this.emitStatus("backend-failed", { error: error.message });
      this.dispose();
      throw error;
    }
  }

  async request(method, params = {}, timeoutMs = DEFAULT_REQUEST_TIMEOUT_MS) {
    await this.attach();
    if (!this.transport) throw new Error("Workspace backend transport is unavailable.");
    return this.transport.request(method, params, timeoutMs);
  }

  dispose() {
    this.status = "disposed";
    if (this.transport) this.transport.dispose();
    this.emitStatus("backend-disposed");
  }
}

class WorkspaceBackendManager extends EventEmitter {
  constructor(options) {
    super();
    this.options = options;
    this.sessions = new Map();
  }

  sessionForProject(project) {
    const key = workspaceSessionKey(project, this.options.fallbackRoot);
    let session = this.sessions.get(key);
    if (!session) {
      session = new WorkspaceSession(project, this.options);
      session.on("status", (payload) => this.emit("status", payload));
      session.on("agent-event", (payload) => this.emit("agent-event", payload));
      this.sessions.set(key, session);
    } else {
      session.project = project;
    }
    return session;
  }

  async ensureForProject(project) {
    const session = this.sessionForProject(project);
    await session.attach();
    return session;
  }

  async requestForProject(project, method, params = {}, timeoutMs) {
    const session = await this.ensureForProject(project);
    return session.request(method, params, timeoutMs);
  }

  statusForProject(project) {
    return this.sessionForProject(project).snapshot();
  }

  disposeAll() {
    for (const session of this.sessions.values()) session.dispose();
    this.sessions.clear();
  }
}

module.exports = {
  WorkspaceBackendManager,
  normalizeWorkspace,
  workspaceLabel,
  workspaceRoot,
  workspaceSessionKey,
};
