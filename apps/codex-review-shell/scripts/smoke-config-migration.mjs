import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import crypto from "node:crypto";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const appRoot = path.resolve(__dirname, "..");
const mainPath = path.join(appRoot, "src", "main.js");
const source = fs.readFileSync(mainPath, "utf8");
const start = source.indexOf("function nowIso()");
const end = source.indexOf("async function loadConfig()", start);
if (start < 0 || end < 0) throw new Error("Unable to locate config-normalization block in main.js");

const sandbox = {
  console,
  crypto,
  path,
  URL,
  repoRoot: appRoot,
};
vm.createContext(sandbox);
vm.runInContext(`${source.slice(start, end)}\nthis.normalizeConfig = normalizeConfig;`, sandbox, { filename: "main-config-slice.js" });

const legacyConfig = {
  version: 3,
  selectedProjectId: "project_legacy",
  ui: { splitRatio: 0.5 },
  projects: [
    {
      id: "project_legacy",
      name: "Legacy project",
      repoPath: appRoot,
      surfaceBinding: {
        codex: { mode: "local", target: "codex://local-workspace", label: "Local Codex lane" },
        chatgpt: { reviewThreadUrl: "https://chatgpt.com/c/legacy-review", reduceChrome: true },
      },
      flowProfile: {
        reviewPromptTemplate: "Review this.",
        watchedFilePatterns: ["**/*REVIEW*.md"],
        returnHeader: "GPT feedback",
      },
    },
  ],
};

const migrated = sandbox.normalizeConfig(legacyConfig);
const project = migrated.projects[0];
if (migrated.version !== 4) throw new Error(`Expected config version 4, got ${migrated.version}`);
if (!Array.isArray(project.chatThreads) || project.chatThreads.length !== 1) throw new Error("Expected one migrated ChatGPT thread.");
const thread = project.chatThreads[0];
if (thread.role !== "review" || !thread.isPrimary) throw new Error("Migrated thread is not the primary review thread.");
if (thread.url !== "https://chatgpt.com/c/legacy-review") throw new Error(`Unexpected migrated URL: ${thread.url}`);
if (project.activeChatThreadId !== thread.id) throw new Error("Active thread was not set to the migrated review thread.");

const malformed = structuredClone(legacyConfig);
malformed.projects[0].surfaceBinding.chatgpt.reviewThreadUrl = "file:///not-safe";
const safe = sandbox.normalizeConfig(malformed).projects[0].chatThreads[0];
if (safe.url !== "https://chatgpt.com/") throw new Error("Malformed ChatGPT URL did not fail closed to https://chatgpt.com/.");

console.log("Config migration smoke passed.");
