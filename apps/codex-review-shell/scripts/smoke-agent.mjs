import { spawn } from "node:child_process";
import { once } from "node:events";
import { fileURLToPath } from "node:url";
import path from "node:path";
import process from "node:process";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const appRoot = path.resolve(__dirname, "..");
const agentPath = path.join(appRoot, "src", "backend", "wsl-agent.js");
const child = spawn(process.execPath, [agentPath, "--root", appRoot, "--workspace-kind", "local", "--project-id", "smoke"], {
  cwd: appRoot,
  stdio: ["pipe", "pipe", "pipe"],
});

let buffer = "";
const responses = new Map();
const events = [];
let failed = false;

function handleLine(line) {
  if (!line.trim()) return;
  const message = JSON.parse(line);
  if (message.event) {
    events.push(message);
    return;
  }
  responses.set(message.id, message);
}

child.stdout.setEncoding("utf8");
child.stdout.on("data", (chunk) => {
  buffer += chunk;
  let index = buffer.indexOf("\n");
  while (index >= 0) {
    handleLine(buffer.slice(0, index));
    buffer = buffer.slice(index + 1);
    index = buffer.indexOf("\n");
  }
});

child.stderr.setEncoding("utf8");
child.stderr.on("data", (chunk) => {
  process.stderr.write(chunk);
});

function send(id, method, params = {}) {
  child.stdin.write(`${JSON.stringify({ id, method, params })}\n`);
}

send("hello", "hello");
send("tree", "listTree", { relPath: "src" });
send("readme", "readFile", { relPath: "README.md" });
send("matches", "listMatchingFiles", { patterns: ["README.md", "src/**/*.js"], ignoredRelPaths: [] });
send("resolve", "resolvePath", { relPath: "README.md" });
child.stdin.end();

const timeout = setTimeout(() => {
  failed = true;
  child.kill();
}, 6000);

await once(child, "exit");
clearTimeout(timeout);

for (const required of ["hello", "tree", "readme", "matches", "resolve"]) {
  const response = responses.get(required);
  if (!response || response.error) {
    failed = true;
    console.error(`Missing or failed response: ${required}`, response?.error || "no response");
  }
}

if (!events.some((event) => event.event === "ready")) {
  failed = true;
  console.error("Agent did not emit ready event.");
}

const matches = responses.get("matches")?.result?.entries || [];
if (!matches.some((entry) => entry.relPath === "README.md")) {
  failed = true;
  console.error("Matching-file smoke did not find README.md through the backend.");
}

if (failed) process.exit(1);
console.log("Workspace backend agent smoke passed.");
