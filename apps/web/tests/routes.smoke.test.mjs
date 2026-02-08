import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { readFile } from "node:fs/promises";
import path from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const WEB_ROOT = path.resolve(__dirname, "..");
const HOST = "127.0.0.1";
const PORT = 3217;
const BASE_URL = `http://${HOST}:${PORT}`;

function startWebServer() {
  const proc = spawn("npm", ["run", "dev", "--", "--hostname", HOST, "--port", String(PORT)], {
    cwd: WEB_ROOT,
    env: {
      ...process.env,
      NEXT_TELEMETRY_DISABLED: "1",
    },
    detached: true,
    stdio: "ignore",
  });
  proc.unref();
  return proc;
}

async function waitForServerReady(proc, timeoutMs = 90_000) {
  const deadline = Date.now() + timeoutMs;

  while (Date.now() < deadline) {
    if (proc.exitCode !== null) {
      throw new Error(`web dev server exited early (${proc.exitCode}).`);
    }
    try {
      const res = await fetch(`${BASE_URL}/`);
      if (res.ok) return;
    } catch {
      // retry
    }
    await new Promise((resolve) => setTimeout(resolve, 400));
  }
  throw new Error(`web dev server did not become ready within ${timeoutMs}ms`);
}

async function stopProcess(proc) {
  if (proc.exitCode !== null) return;
  try {
    process.kill(-proc.pid, "SIGTERM");
  } catch {
    return;
  }
  await new Promise((resolve) => setTimeout(resolve, 300));
  if (proc.exitCode === null) {
    try {
      process.kill(-proc.pid, "SIGKILL");
    } catch {
      // already stopped
    }
  }
}

test("route smoke: home, concepts, puzzles render core controls", { timeout: 120_000 }, async () => {
  const proc = startWebServer();
  try {
    await waitForServerReady(proc);

    const routeExpectations = [
      { path: "/", mustInclude: "Analyze as Concepts" },
      { path: "/concepts", mustInclude: "Concept Text" },
      { path: "/puzzles", mustInclude: "Puzzle Text" },
    ];

    for (const route of routeExpectations) {
      const res = await fetch(`${BASE_URL}${route.path}`);
      assert.equal(res.status, 200, `expected 200 for ${route.path}`);
      const html = await res.text();
      assert.match(html, /<html/i, `expected HTML document for ${route.path}`);
      assert.match(html, new RegExp(route.mustInclude), `expected marker text for ${route.path}`);
    }
  } finally {
    await stopProcess(proc);
  }
});

test("mobile baseline: globals.css has single-column breakpoint", async () => {
  const cssPath = path.join(WEB_ROOT, "src", "app", "globals.css");
  const css = await readFile(cssPath, "utf-8");
  assert.match(css, /@media \(max-width: 860px\)/);
  assert.match(css, /grid-template-columns:\s*minmax\(0, 1fr\)/);
});
