#!/usr/bin/env node
"use strict";

/**
 * ADEU workspace backend agent.
 *
 * This file is intentionally plain Node/CommonJS and has no Electron dependency.
 * For WSL projects it runs inside the selected distro, rooted at the canonical
 * Linux workspace path. For local/dev projects it can also run as a local
 * resident backend process. The host talks to it over newline-delimited JSON.
 */

const fs = require("node:fs/promises");
const fsSync = require("node:fs");
const path = require("node:path");
const readline = require("node:readline");
const { spawn } = require("node:child_process");
const crypto = require("node:crypto");

const PROTOCOL_VERSION = 1;
const PREVIEW_LIMIT_BYTES = 384 * 1024;
const DIRECTORY_ENTRY_LIMIT = 500;
const COMMAND_OUTPUT_LIMIT_BYTES = 256 * 1024;
const DEFAULT_COMMAND_TIMEOUT_MS = 30_000;
const MATCH_SCAN_LIMIT = 240;
const MATCH_WALK_LIMIT = 8000;

const SKIPPED_DIR_NAMES = new Set([
  ".git",
  ".hg",
  ".svn",
  "node_modules",
  ".next",
  "dist",
  "build",
  "out",
  "coverage",
  "target",
  "__pycache__",
  ".pytest_cache",
  ".mypy_cache",
  ".ruff_cache",
  ".venv",
  "venv",
]);

function parseArgv(argv) {
  const result = {};
  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    if (!arg.startsWith("--")) continue;
    const key = arg.slice(2);
    const next = argv[index + 1];
    if (!next || next.startsWith("--")) {
      result[key] = "true";
    } else {
      result[key] = next;
      index += 1;
    }
  }
  return result;
}

const argv = parseArgv(process.argv);
const root = path.resolve(argv.root || process.cwd());
const workspaceKind = argv["workspace-kind"] || "local";
const projectId = argv["project-id"] || "unknown-project";
const sessionId = `agent_${crypto.randomUUID().replace(/-/g, "").slice(0, 12)}`;

function send(message) {
  process.stdout.write(`${JSON.stringify(message)}\n`);
}

function sendEvent(type, payload = {}) {
  send({ event: type, sessionId, at: new Date().toISOString(), ...payload });
}

function normalizeRelPath(relPath) {
  const text = String(relPath ?? "").replace(/\\/g, "/").trim();
  if (!text || text === ".") return "";
  const parts = text.split("/").filter(Boolean);
  if (parts.some((part) => part === "..")) throw new Error("Parent-path traversal is not allowed.");
  return parts.join(path.sep);
}

function displayRelPath(value) {
  return String(value || "").split(path.sep).join("/");
}

function resolveWithinRoot(relPath = "") {
  const rel = normalizeRelPath(relPath);
  const fullPath = path.resolve(root, rel || ".");
  const relative = path.relative(root, fullPath);
  if (relative.startsWith("..") || path.isAbsolute(relative)) {
    throw new Error("Requested path is outside the workspace root.");
  }
  return {
    root,
    rel,
    fullPath,
    displayRel: displayRelPath(relative === "." ? "" : relative),
  };
}

function direntType(dirent) {
  if (dirent.isSymbolicLink()) return "symlink";
  if (dirent.isDirectory()) return "dir";
  if (dirent.isFile()) return "file";
  return "other";
}

async function listTree(params = {}) {
  const { fullPath, displayRel } = resolveWithinRoot(params.relPath || "");
  const stat = await fs.lstat(fullPath);
  if (!stat.isDirectory()) throw new Error("Requested path is not a directory.");

  const rawEntries = await fs.readdir(fullPath, { withFileTypes: true });
  const entries = [];
  let skipped = 0;

  for (const dirent of rawEntries) {
    const type = direntType(dirent);
    if (type === "dir" && SKIPPED_DIR_NAMES.has(dirent.name)) {
      skipped += 1;
      continue;
    }
    if (entries.length >= DIRECTORY_ENTRY_LIMIT) {
      skipped += 1;
      continue;
    }
    const childRel = displayRel ? `${displayRel}/${dirent.name}` : dirent.name;
    entries.push({
      name: dirent.name,
      relPath: childRel,
      type,
      expandable: type === "dir",
    });
  }

  entries.sort((a, b) => {
    if (a.type === "dir" && b.type !== "dir") return -1;
    if (a.type !== "dir" && b.type === "dir") return 1;
    return a.name.localeCompare(b.name, undefined, { sensitivity: "base", numeric: true });
  });

  return {
    root,
    relPath: displayRel,
    entries,
    skipped,
    limit: DIRECTORY_ENTRY_LIMIT,
    source: workspaceKind,
  };
}

function looksBinary(buffer) {
  if (!buffer.length) return false;
  const sample = buffer.subarray(0, Math.min(buffer.length, 8192));
  let suspicious = 0;
  for (const byte of sample) {
    if (byte === 0) return true;
    if (byte < 7 || (byte > 13 && byte < 32)) suspicious += 1;
  }
  return suspicious / sample.length > 0.12;
}

async function readFilePreview(params = {}) {
  const { fullPath, displayRel } = resolveWithinRoot(params.relPath || "");
  const stat = await fs.lstat(fullPath);
  if (stat.isSymbolicLink()) throw new Error("Symlink preview is disabled for this workspace agent.");
  if (!stat.isFile()) throw new Error("Selected path is not a file.");

  const bytesToRead = Math.min(stat.size, PREVIEW_LIMIT_BYTES);
  const file = await fs.open(fullPath, "r");
  let buffer;
  try {
    buffer = Buffer.alloc(bytesToRead);
    if (bytesToRead > 0) await file.read(buffer, 0, bytesToRead, 0);
  } finally {
    await file.close();
  }

  const binary = looksBinary(buffer);
  return {
    relPath: displayRel,
    absolutePath: fullPath,
    size: stat.size,
    truncated: stat.size > PREVIEW_LIMIT_BYTES,
    binary,
    limit: PREVIEW_LIMIT_BYTES,
    text: binary ? "" : buffer.toString("utf8"),
    source: workspaceKind,
  };
}


function escapeRegex(value) {
  return String(value).replace(/[|\\{}()[\]^$+?.]/g, "\\$&");
}

function globToRegex(pattern) {
  const normalized = String(pattern || "").replace(/\\/g, "/").trim();
  if (!normalized) return null;
  let output = "^";
  for (let index = 0; index < normalized.length; index += 1) {
    const char = normalized[index];
    const next = normalized[index + 1];
    if (char === "*" && next === "*") {
      const after = normalized[index + 2];
      if (after === "/") {
        output += "(?:.*/)?";
        index += 2;
      } else {
        output += ".*";
        index += 1;
      }
    } else if (char === "*") {
      output += "[^/]*";
    } else if (char === "?") {
      output += "[^/]";
    } else {
      output += escapeRegex(char);
    }
  }
  output += "$";
  return new RegExp(output, "i");
}

function matchesAnyPattern(relPath, regexes) {
  const normalized = String(relPath || "").replace(/\\/g, "/");
  return regexes.some((regex) => regex.test(normalized));
}

async function listMatchingFiles(params = {}) {
  const patterns = Array.isArray(params.patterns) ? params.patterns.filter((item) => typeof item === "string" && item.trim()) : [];
  const ignored = new Set(
    (Array.isArray(params.ignoredRelPaths) ? params.ignoredRelPaths : [])
      .filter((item) => typeof item === "string" && item.trim())
      .map((item) => item.replace(/\\/g, "/")),
  );
  const regexes = patterns.map(globToRegex).filter(Boolean);
  if (!regexes.length) {
    return { root, patterns, entries: [], skipped: 0, scanned: 0, limit: MATCH_SCAN_LIMIT, source: workspaceKind };
  }

  const entries = [];
  let skipped = 0;
  let scanned = 0;

  async function walk(relDir) {
    if (scanned >= MATCH_WALK_LIMIT || entries.length >= MATCH_SCAN_LIMIT) return;
    const { fullPath, displayRel } = resolveWithinRoot(relDir);
    let dirents;
    try {
      dirents = await fs.readdir(fullPath, { withFileTypes: true });
    } catch {
      skipped += 1;
      return;
    }

    for (const dirent of dirents) {
      if (scanned >= MATCH_WALK_LIMIT || entries.length >= MATCH_SCAN_LIMIT) return;
      const type = direntType(dirent);
      if (type === "dir" && SKIPPED_DIR_NAMES.has(dirent.name)) {
        skipped += 1;
        continue;
      }
      const childRel = displayRel ? `${displayRel}/${dirent.name}` : dirent.name;
      scanned += 1;
      if (type === "dir") {
        await walk(childRel);
      } else if (type === "file" && !ignored.has(childRel) && matchesAnyPattern(childRel, regexes)) {
        try {
          const stat = await fs.lstat(path.join(root, childRel.split("/").join(path.sep)));
          entries.push({
            name: dirent.name,
            relPath: childRel,
            type: "file",
            size: stat.size,
            mtimeMs: stat.mtimeMs,
            mtime: stat.mtime.toISOString(),
          });
        } catch {
          skipped += 1;
        }
      }
    }
  }

  await walk("");
  entries.sort((a, b) => b.mtimeMs - a.mtimeMs || a.relPath.localeCompare(b.relPath));
  return {
    root,
    patterns,
    entries,
    skipped,
    scanned,
    limit: MATCH_SCAN_LIMIT,
    walkLimit: MATCH_WALK_LIMIT,
    source: workspaceKind,
  };
}

async function resolvePathPreview(params = {}) {
  const { fullPath, displayRel } = resolveWithinRoot(params.relPath || "");
  const stat = await fs.lstat(fullPath);
  return {
    relPath: displayRel,
    absolutePath: fullPath,
    isFile: stat.isFile(),
    isDirectory: stat.isDirectory(),
    size: stat.size,
    source: workspaceKind,
  };
}

function appendLimited(chunks, chunk, limitBytes) {
  const buffer = Buffer.isBuffer(chunk) ? chunk : Buffer.from(String(chunk));
  let current = chunks.reduce((sum, item) => sum + item.length, 0);
  if (current >= limitBytes) return true;
  if (current + buffer.length <= limitBytes) {
    chunks.push(buffer);
    return false;
  }
  chunks.push(buffer.subarray(0, limitBytes - current));
  return true;
}

async function runCommand(params = {}) {
  const command = String(params.command || "").trim();
  if (!command) throw new Error("Command is required.");
  const args = Array.isArray(params.args) ? params.args.map((arg) => String(arg)) : [];
  const { fullPath, displayRel } = resolveWithinRoot(params.cwdRelPath || "");
  const timeoutMs = Number.isFinite(Number(params.timeoutMs))
    ? Math.max(1000, Math.min(Number(params.timeoutMs), 10 * 60_000))
    : DEFAULT_COMMAND_TIMEOUT_MS;

  return new Promise((resolve, reject) => {
    const startedAt = Date.now();
    const child = spawn(command, args, {
      cwd: fullPath,
      env: { ...process.env, ...(params.env && typeof params.env === "object" ? params.env : {}) },
      shell: false,
      windowsHide: true,
    });

    const stdoutChunks = [];
    const stderrChunks = [];
    let stdoutTruncated = false;
    let stderrTruncated = false;
    let settled = false;
    const timer = setTimeout(() => {
      if (settled) return;
      child.kill("SIGTERM");
      setTimeout(() => {
        if (!settled) child.kill("SIGKILL");
      }, 1200);
    }, timeoutMs);

    child.stdout.on("data", (chunk) => {
      stdoutTruncated = appendLimited(stdoutChunks, chunk, COMMAND_OUTPUT_LIMIT_BYTES) || stdoutTruncated;
    });
    child.stderr.on("data", (chunk) => {
      stderrTruncated = appendLimited(stderrChunks, chunk, COMMAND_OUTPUT_LIMIT_BYTES) || stderrTruncated;
    });
    child.on("error", (error) => {
      clearTimeout(timer);
      settled = true;
      reject(error);
    });
    child.on("close", (exitCode, signal) => {
      clearTimeout(timer);
      settled = true;
      resolve({
        command,
        args,
        cwdRelPath: displayRel,
        exitCode,
        signal,
        durationMs: Date.now() - startedAt,
        stdout: Buffer.concat(stdoutChunks).toString("utf8"),
        stderr: Buffer.concat(stderrChunks).toString("utf8"),
        stdoutTruncated,
        stderrTruncated,
        outputLimit: COMMAND_OUTPUT_LIMIT_BYTES,
      });
    });
  });
}

async function watchStatus() {
  return {
    available: typeof fsSync.watch === "function",
    active: false,
    note: "Watcher protocol scaffold is present; persistent watch subscriptions are reserved for the next iteration.",
  };
}

async function handleRequest(method, params = {}) {
  if (method === "hello") {
    const stat = await fs.stat(root);
    if (!stat.isDirectory()) throw new Error("Workspace root is not a directory.");
    return {
      protocolVersion: PROTOCOL_VERSION,
      sessionId,
      projectId,
      workspaceKind,
      root,
      platform: process.platform,
      pid: process.pid,
      node: process.version,
      cwd: process.cwd(),
      capabilities: {
        listTree: true,
        readFilePreview: true,
        runCommand: true,
        listMatchingFiles: true,
        resolvePath: true,
        watchScaffold: true,
      },
    };
  }
  if (method === "listTree") return listTree(params);
  if (method === "readFile") return readFilePreview(params);
  if (method === "listMatchingFiles") return listMatchingFiles(params);
  if (method === "resolvePath") return resolvePathPreview(params);
  if (method === "runCommand") return runCommand(params);
  if (method === "watchStatus") return watchStatus(params);
  throw new Error(`Unknown workspace-agent method: ${method}`);
}

async function handleLine(line) {
  if (!line.trim()) return;
  let request;
  try {
    request = JSON.parse(line);
  } catch (error) {
    send({ error: { message: `Invalid JSON: ${error.message}` } });
    return;
  }
  const id = request.id;
  try {
    const result = await handleRequest(request.method, request.params || {});
    send({ id, result });
  } catch (error) {
    send({ id, error: { message: error.message, stack: error.stack } });
  }
}

async function main() {
  try {
    const stat = await fs.stat(root);
    if (!stat.isDirectory()) throw new Error(`${root} is not a directory.`);
  } catch (error) {
    sendEvent("startup-error", { root, workspaceKind, projectId, error: error.message });
    process.exitCode = 2;
    return;
  }

  sendEvent("ready", {
    protocolVersion: PROTOCOL_VERSION,
    root,
    workspaceKind,
    projectId,
    pid: process.pid,
    platform: process.platform,
  });

  const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });
  rl.on("line", (line) => {
    handleLine(line).catch((error) => {
      sendEvent("internal-error", { error: error.message });
    });
  });
  rl.on("close", () => {
    // Do not force-exit immediately; allow in-flight async handlers to flush replies.
  });
}

process.on("uncaughtException", (error) => {
  sendEvent("uncaught-exception", { error: error.message, stack: error.stack });
});

process.on("unhandledRejection", (error) => {
  sendEvent("unhandled-rejection", { error: error?.message || String(error), stack: error?.stack });
});

main().catch((error) => {
  sendEvent("fatal", { error: error.message, stack: error.stack });
  process.exit(1);
});
