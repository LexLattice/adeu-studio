import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { constants as fsConstants, existsSync } from "node:fs";
import { access, readFile, readdir, realpath, stat } from "node:fs/promises";
import os from "node:os";
import path from "node:path";

import type {
  DiffDocument,
  DiffLine,
  FileDocument,
  GitSnapshot,
  HarnessConfigCandidate,
  HarnessSummary,
  RepoTreeEntry,
  RepoTreeResponse,
  TerminalSnapshot,
} from "../../codex-workbench/models";
import type { TerminalCommandId } from "../../codex-workbench/contract";

const REPO_ROOT = path.resolve(process.cwd(), "..", "..");
const DEFAULT_MAX_FILE_BYTES = 200_000;
const IGNORED_NAMES = new Set([
  ".git",
  ".next",
  ".venv",
  "node_modules",
  "__pycache__",
  ".mypy_cache",
]);
const TEXT_EXTENSIONS = new Set([
  ".md",
  ".txt",
  ".py",
  ".tsx",
  ".ts",
  ".jsx",
  ".js",
  ".json",
  ".jsonl",
  ".toml",
  ".yml",
  ".yaml",
  ".css",
  ".html",
  ".mjs",
  ".cjs",
  ".sh",
  ".svg",
  ".csv",
  ".ini",
  ".lock",
  ".cfg",
  ".mk",
]);

function ensureRepoRelativePath(input: string | null | undefined): string {
  const raw = decodeURIComponent((input ?? "").trim());
  if (!raw || raw === ".") return "";
  const normalized = raw.replace(/\\/g, "/").replace(/^\/+/, "");
  const segments = normalized.split("/");
  const safe: string[] = [];

  for (const segment of segments) {
    if (!segment || segment === ".") continue;
    if (segment === "..") throw new Error("path traversal is not allowed");
    safe.push(segment);
  }

  return safe.join("/");
}

function resolveRepoPath(relativePath: string): string {
  const safeRelative = ensureRepoRelativePath(relativePath);
  const resolved = path.resolve(REPO_ROOT, safeRelative);
  assertWithinRepoRoot(resolved);
  return resolved;
}

function assertWithinRepoRoot(targetPath: string): void {
  const relative = path.relative(REPO_ROOT, targetPath);
  if (relative.startsWith("..") || path.isAbsolute(relative)) {
    throw new Error("path escapes the repo root");
  }
}

async function resolveExistingRepoPath(relativePath: string): Promise<string> {
  const lexicalPath = resolveRepoPath(relativePath);
  const boundedRealPath = await realpath(lexicalPath);
  assertWithinRepoRoot(boundedRealPath);
  return boundedRealPath;
}

function extensionOf(name: string): string | null {
  const ext = path.extname(name).trim();
  return ext || null;
}

async function fileExists(targetPath: string): Promise<boolean> {
  try {
    await access(targetPath, fsConstants.F_OK);
    return true;
  } catch {
    return false;
  }
}

function isLikelyTextFile(name: string, buffer: Buffer): boolean {
  const extension = extensionOf(name);
  if (extension && TEXT_EXTENSIONS.has(extension.toLowerCase())) return true;
  const sample = buffer.subarray(0, Math.min(buffer.length, 512));
  return !sample.includes(0);
}

function sha256For(buffer: Buffer): string {
  return createHash("sha256").update(buffer).digest("hex");
}

function clipBuffer(buffer: Buffer, maxBytes: number): { buffer: Buffer; truncated: boolean } {
  if (buffer.length <= maxBytes) return { buffer, truncated: false };
  return { buffer: buffer.subarray(0, maxBytes), truncated: true };
}

export function normalizeRepoRelativePath(input: string | null | undefined): string {
  return ensureRepoRelativePath(input);
}

export async function listRepoDirectory(relativePath = ""): Promise<RepoTreeResponse> {
  const safeRelative = ensureRepoRelativePath(relativePath);
  const absolutePath = await resolveExistingRepoPath(safeRelative);
  const metadata = await stat(absolutePath);
  if (!metadata.isDirectory()) {
    throw new Error(`${safeRelative || "."} is not a directory`);
  }

  const entries = await readdir(absolutePath, { withFileTypes: true });
  const results: RepoTreeEntry[] = [];

  for (const entry of entries) {
    if (IGNORED_NAMES.has(entry.name)) continue;
    const entryRelativePath = safeRelative ? `${safeRelative}/${entry.name}` : entry.name;
    const kind: RepoTreeEntry["kind"] = entry.isDirectory()
      ? "directory"
      : entry.isSymbolicLink()
        ? "symlink"
        : "file";

    let size: number | null = null;
    if (kind !== "directory") {
      try {
        size = (await stat(await resolveExistingRepoPath(entryRelativePath))).size;
      } catch {
        size = null;
      }
    }

    results.push({
      name: entry.name,
      path: entryRelativePath,
      kind,
      extension: extensionOf(entry.name),
      size,
      hidden: entry.name.startsWith("."),
    });
  }

  results.sort((left, right) => {
    if (left.kind === "directory" && right.kind !== "directory") return -1;
    if (left.kind !== "directory" && right.kind === "directory") return 1;
    return left.name.localeCompare(right.name);
  });

  return {
    repoRoot: REPO_ROOT,
    directoryPath: safeRelative,
    entries: results,
  };
}

export async function readRepoFile(
  relativePath: string,
  maxBytes = DEFAULT_MAX_FILE_BYTES,
): Promise<FileDocument> {
  const safeRelative = ensureRepoRelativePath(relativePath);
  if (!safeRelative) throw new Error("a file path is required");
  const absolutePath = await resolveExistingRepoPath(safeRelative);
  const metadata = await stat(absolutePath);
  if (!metadata.isFile()) {
    throw new Error(`${safeRelative} is not a file`);
  }

  const raw = await readFile(absolutePath);
  const clipped = clipBuffer(raw, maxBytes);
  const isBinary = !isLikelyTextFile(path.basename(safeRelative), clipped.buffer);
  const text = isBinary ? "" : clipped.buffer.toString("utf-8");
  const preview = isBinary ? "Binary or unsupported file preview." : text.slice(0, 6_000);

  return {
    path: safeRelative,
    name: path.basename(safeRelative),
    extension: extensionOf(safeRelative),
    size: raw.length,
    sha256: sha256For(raw),
    isBinary,
    truncated: clipped.truncated,
    lineCount: isBinary ? 0 : text.split(/\r?\n/).length,
    text,
    preview,
  };
}

function searchExecutable(command: string): string | null {
  const trimmed = command.trim();
  if (!trimmed) return null;
  const candidates: string[] = [];

  if (trimmed.includes(path.sep)) {
    candidates.push(path.resolve(trimmed));
  } else {
    const pathValue = process.env.PATH ?? "";
    for (const root of pathValue.split(path.delimiter).filter(Boolean)) {
      candidates.push(path.join(root, trimmed));
    }
  }

  for (const candidate of candidates) {
    try {
      const result = spawnSync(candidate, ["--version"], {
        encoding: "utf-8",
        timeout: 2_000,
      });
      if (result.error == null) return candidate;
    } catch {
      // keep scanning
    }
  }

  return null;
}

function defaultDbPath(): string {
  const envValue = process.env.ADEU_API_DB_PATH?.trim();
  if (envValue) return path.resolve(envValue);
  return path.join(REPO_ROOT, "apps", "api", "var", "adeu.sqlite3");
}

function defaultEvidenceRoot(dbPath: string): string {
  const envValue = process.env.URM_EVIDENCE_ROOT?.trim();
  if (envValue) return path.resolve(envValue);
  return path.join(path.dirname(dbPath), "evidence", "codex");
}

async function configCandidates(): Promise<HarnessConfigCandidate[]> {
  const home = os.homedir();
  const rawCandidates = [
    {
      label: "ADEU_CODEX_CONFIG",
      path: process.env.ADEU_CODEX_CONFIG?.trim() || "",
      exists: false,
      source: "env",
    },
    {
      label: "CODEX_CONFIG",
      path: process.env.CODEX_CONFIG?.trim() || "",
      exists: false,
      source: "env",
    },
    {
      label: "repo .codex/config.toml",
      path: path.join(REPO_ROOT, ".codex", "config.toml"),
      exists: false,
      source: "repo",
    },
    {
      label: "repo config.toml",
      path: path.join(REPO_ROOT, "config.toml"),
      exists: false,
      source: "repo",
    },
    {
      label: "home ~/.codex/config.toml",
      path: path.join(home, ".codex", "config.toml"),
      exists: false,
      source: "home",
    },
  ] satisfies HarnessConfigCandidate[];

  const deduped = new Map<string, HarnessConfigCandidate>();
  for (const candidate of rawCandidates.filter((entry) => entry.path)) {
    const resolvedPath = path.resolve(candidate.path);
    deduped.set(resolvedPath, {
      ...candidate,
      path: resolvedPath,
      exists: await fileExists(resolvedPath),
    });
  }

  return [...deduped.values()];
}

function selectActiveConfigCandidate(
  candidates: HarnessConfigCandidate[],
): HarnessConfigCandidate | null {
  const byLabel = new Map(candidates.map((candidate) => [candidate.label, candidate]));
  const explicit = byLabel.get("ADEU_CODEX_CONFIG") ?? byLabel.get("CODEX_CONFIG");
  if (explicit?.exists) return explicit;
  return candidates.find((candidate) => candidate.exists) ?? null;
}

export async function getHarnessSummary(): Promise<HarnessSummary> {
  const codexBinConfigured = process.env.ADEU_CODEX_BIN?.trim() || "codex";
  const codexBinResolved = searchExecutable(codexBinConfigured);
  const dbPath = defaultDbPath();
  const evidenceRoot = defaultEvidenceRoot(dbPath);
  const policyRegistryPath = process.env.URM_POLICY_PROFILES_PATH?.trim()
    ? path.resolve(process.env.URM_POLICY_PROFILES_PATH)
    : path.join(REPO_ROOT, "policy", "profiles.v1.json");
  const candidates = await configCandidates();
  const activeConfig = selectActiveConfigCandidate(candidates);

  return {
    repoRoot: REPO_ROOT,
    codexBinConfigured,
    codexBinResolved,
    codexBinAvailable: codexBinResolved !== null,
    apiDbPath: dbPath,
    evidenceRoot,
    policyRegistryPath,
    codexModel: process.env.ADEU_CODEX_MODEL?.trim() || null,
    activeConfigPath: activeConfig?.path ?? null,
    activeConfigSource: activeConfig?.label ?? null,
    configTomlCandidates: candidates,
    envSummary: {
      ADEU_CODEX_BIN: process.env.ADEU_CODEX_BIN?.trim() || null,
      ADEU_CODEX_MODEL: process.env.ADEU_CODEX_MODEL?.trim() || null,
      ADEU_API_DB_PATH: process.env.ADEU_API_DB_PATH?.trim() || null,
      URM_EVIDENCE_ROOT: process.env.URM_EVIDENCE_ROOT?.trim() || null,
      URM_POLICY_PROFILES_PATH: process.env.URM_POLICY_PROFILES_PATH?.trim() || null,
      CODEX_CONFIG: process.env.CODEX_CONFIG?.trim() || null,
      ADEU_CODEX_CONFIG: process.env.ADEU_CODEX_CONFIG?.trim() || null,
    },
  };
}

function gitAvailable(): boolean {
  const result = spawnSync("git", ["--version"], {
    encoding: "utf-8",
    timeout: 2_000,
  });
  return result.error == null && result.status === 0;
}

function gitMetadataPresent(): boolean {
  return existsSync(path.join(REPO_ROOT, ".git"));
}

function runGit(args: string[]): { ok: boolean; stdout: string; stderr: string } {
  const result = spawnSync("git", args, {
    cwd: REPO_ROOT,
    encoding: "utf-8",
    timeout: 5_000,
  });
  return {
    ok: result.error == null && result.status === 0,
    stdout: result.stdout || "",
    stderr: result.stderr || (result.error ? String(result.error) : ""),
  };
}

export async function getGitSnapshot(): Promise<GitSnapshot> {
  if (!gitAvailable()) {
    return {
      status: "unavailable",
      branch: null,
      head: null,
      summary: "git is not available on the host PATH.",
      statusLines: [],
      recentCommits: [],
    };
  }

  if (!gitMetadataPresent()) {
    return {
      status: "unavailable",
      branch: null,
      head: null,
      summary:
        "This project source does not expose .git metadata, so the Git lane stays explicit but unavailable.",
      statusLines: [],
      recentCommits: [],
    };
  }

  const branch = runGit(["rev-parse", "--abbrev-ref", "HEAD"]);
  const head = runGit(["rev-parse", "--short", "HEAD"]);
  const status = runGit(["status", "--short", "--branch"]);
  const log = runGit(["log", "--oneline", "-5"]);

  if (!branch.ok || !head.ok || !status.ok || !log.ok) {
    return {
      status: "error",
      branch: null,
      head: null,
      summary:
        status.stderr ||
        branch.stderr ||
        head.stderr ||
        log.stderr ||
        "git command failed",
      statusLines: [],
      recentCommits: [],
    };
  }

  return {
    status: "ready",
    branch: branch.stdout.trim() || null,
    head: head.stdout.trim() || null,
    summary: "Git status is read-only and same-context reachable.",
    statusLines: status.stdout
      .split(/\r?\n/)
      .map((line) => line.trimEnd())
      .filter(Boolean),
    recentCommits: log.stdout
      .split(/\r?\n/)
      .map((line) => line.trimEnd())
      .filter(Boolean),
  };
}

function parseUnifiedDiff(raw: string): {
  lines: DiffLine[];
  additions: number;
  removals: number;
  hunks: number;
} {
  const lines: DiffLine[] = [];
  let additions = 0;
  let removals = 0;
  let hunks = 0;

  for (const line of raw.split(/\r?\n/)) {
    if (!line) continue;
    if (line.startsWith("@@")) {
      hunks += 1;
      lines.push({ kind: "hunk", text: line });
      continue;
    }
    if (
      (line.startsWith("+++") ||
        line.startsWith("---") ||
        line.startsWith("diff --git") ||
        line.startsWith("index ")) &&
      !line.startsWith("++++") &&
      !line.startsWith("----")
    ) {
      lines.push({ kind: "meta", text: line });
      continue;
    }
    if (line.startsWith("+") && !line.startsWith("+++")) {
      additions += 1;
      lines.push({ kind: "add", text: line });
      continue;
    }
    if (line.startsWith("-") && !line.startsWith("---")) {
      removals += 1;
      lines.push({ kind: "remove", text: line });
      continue;
    }
    lines.push({ kind: "context", text: line });
  }

  return { lines, additions, removals, hunks };
}

function fallbackDiff(left: FileDocument, right: FileDocument): DiffDocument {
  if (left.isBinary || right.isBinary) {
    const raw =
      left.sha256 === right.sha256
        ? "Binary files are identical."
        : "Binary files differ. Preview is not rendered. Use file provenance and hashes for review dispatch.";
    return {
      leftPath: left.path,
      rightPath: right.path,
      leftSha256: left.sha256,
      rightSha256: right.sha256,
      identical: left.sha256 === right.sha256,
      truncated: left.truncated || right.truncated,
      raw,
      lines: [{ kind: "meta", text: raw }],
      summary: {
        additions: 0,
        removals: 0,
        hunks: left.sha256 === right.sha256 ? 0 : 1,
      },
    };
  }

  const leftLines = left.text.split(/\r?\n/);
  const rightLines = right.text.split(/\r?\n/);
  const max = Math.max(leftLines.length, rightLines.length);
  const output: DiffLine[] = [];
  let additions = 0;
  let removals = 0;

  for (let index = 0; index < max; index += 1) {
    const leftLine = leftLines[index];
    const rightLine = rightLines[index];
    if (leftLine === rightLine) {
      if (leftLine !== undefined) {
        output.push({ kind: "context", text: ` ${leftLine}` });
      }
      continue;
    }
    if (leftLine !== undefined) {
      removals += 1;
      output.push({ kind: "remove", text: `-${leftLine}` });
    }
    if (rightLine !== undefined) {
      additions += 1;
      output.push({ kind: "add", text: `+${rightLine}` });
    }
  }

  const raw = output.map((line) => line.text).join("\n");
  return {
    leftPath: left.path,
    rightPath: right.path,
    leftSha256: left.sha256,
    rightSha256: right.sha256,
    identical: additions === 0 && removals === 0,
    truncated: left.truncated || right.truncated,
    raw,
    lines: output.length > 0 ? output : [{ kind: "context", text: "Files are identical." }],
    summary: { additions, removals, hunks: output.length > 0 ? 1 : 0 },
  };
}

export async function buildDiffDocument(
  leftPath: string,
  rightPath: string,
): Promise<DiffDocument> {
  const left = await readRepoFile(leftPath);
  const right = await readRepoFile(rightPath);

  if (gitAvailable()) {
    const result = spawnSync(
      "git",
      [
        "diff",
        "--no-index",
        "--no-color",
        "--unified=3",
        await resolveExistingRepoPath(left.path),
        await resolveExistingRepoPath(right.path),
      ],
      {
        cwd: REPO_ROOT,
        encoding: "utf-8",
        timeout: 5_000,
      },
    );
    const exitCode = result.status ?? 0;
    const stdout = result.stdout || "";

    if (result.error == null && (exitCode === 0 || exitCode === 1)) {
      if (!stdout.trim()) {
        return {
          leftPath: left.path,
          rightPath: right.path,
          leftSha256: left.sha256,
          rightSha256: right.sha256,
          identical: true,
          truncated: left.truncated || right.truncated,
          raw: "Files are identical.",
          lines: [{ kind: "context", text: "Files are identical." }],
          summary: { additions: 0, removals: 0, hunks: 0 },
        };
      }
      const parsed = parseUnifiedDiff(stdout);
      return {
        leftPath: left.path,
        rightPath: right.path,
        leftSha256: left.sha256,
        rightSha256: right.sha256,
        identical: false,
        truncated: left.truncated || right.truncated,
        raw: stdout,
        lines: parsed.lines,
        summary: {
          additions: parsed.additions,
          removals: parsed.removals,
          hunks: parsed.hunks,
        },
      };
    }
  }

  return fallbackDiff(left, right);
}

function pythonExecutable(): string | null {
  const venvPython = path.join(REPO_ROOT, ".venv", "bin", "python");
  if (
    spawnSync(venvPython, ["--version"], {
      encoding: "utf-8",
      timeout: 2_000,
    }).error == null
  ) {
    return venvPython;
  }

  for (const candidate of ["python3", "python"]) {
    if (searchExecutable(candidate)) return candidate;
  }
  return null;
}

export async function runTerminalSnapshot(
  commandId: TerminalCommandId,
  relativeCwd = "",
): Promise<TerminalSnapshot> {
  const safeCwd = ensureRepoRelativePath(relativeCwd);
  const cwd = await resolveExistingRepoPath(safeCwd);

  if (commandId === "pwd") {
    return {
      commandId,
      cwd: safeCwd || ".",
      title: "Present working directory",
      status: "ready",
      lines: ["$ pwd", cwd],
    };
  }

  if (commandId === "ls") {
    const listing = await listRepoDirectory(safeCwd);
    return {
      commandId,
      cwd: safeCwd || ".",
      title: "Directory listing",
      status: "ready",
      lines: [
        `$ ls ${safeCwd || "."}`,
        ...listing.entries.map((entry) => `${entry.kind === "directory" ? "d" : "-"} ${entry.path}`),
      ],
    };
  }

  if (commandId === "git-status") {
    const snapshot = await getGitSnapshot();
    return {
      commandId,
      cwd: safeCwd || ".",
      title: "Git status",
      status: snapshot.status === "error" ? "error" : "ready",
      lines: [
        "$ git status --short --branch",
        snapshot.summary,
        ...(snapshot.statusLines.length > 0 ? snapshot.statusLines : ["(no status lines)"]),
      ],
    };
  }

  if (commandId === "node-version") {
    return {
      commandId,
      cwd: safeCwd || ".",
      title: "Node version",
      status: "ready",
      lines: ["$ node --version", process.version],
    };
  }

  const python = pythonExecutable();
  if (!python) {
    return {
      commandId,
      cwd: safeCwd || ".",
      title: "Python version",
      status: "error",
      lines: ["$ python --version", "python executable unavailable"],
    };
  }

  const result = spawnSync(python, ["--version"], {
    cwd,
    encoding: "utf-8",
    timeout: 2_000,
  });
  return {
    commandId,
    cwd: safeCwd || ".",
    title: "Python version",
    status: result.error == null ? "ready" : "error",
    lines: [
      "$ python --version",
      (result.stdout || result.stderr || "python version unavailable").trim(),
    ],
  };
}
