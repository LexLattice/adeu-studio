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

test("route smoke: home, explain, concepts, puzzles, papers, paper semantic workbench, copilot, evidence-explorer render core controls", { timeout: 120_000 }, async () => {
  const proc = startWebServer();
  try {
    await waitForServerReady(proc);

    const routeExpectations = [
      { path: "/", mustInclude: "Analyze as Concepts" },
      { path: "/explain", mustInclude: "Explain Evidence Studio" },
      { path: "/concepts", mustInclude: "Generate alignment" },
      { path: "/puzzles", mustInclude: "Puzzle Text" },
      { path: "/papers", mustInclude: "Paper Abstract Studio" },
      { path: "/papers/semantic-workbench", mustInclude: "Paper Semantic Workbench" },
      { path: "/copilot", mustInclude: "Copilot Runtime" },
      { path: "/evidence-explorer", mustInclude: "Evidence Explorer" },
      { path: "/artifact-inspector", mustInclude: "Artifact Inspector Reference Surface" },
      { path: "/odeu-sim", mustInclude: "ODEU Simulation Summary" },
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

test(
  "artifact inspector reference surface exposes rendered law hooks and boundaries",
  { timeout: 120_000 },
  async () => {
    const proc = startWebServer();
    try {
      await waitForServerReady(proc);

      const res = await fetch(`${BASE_URL}/artifact-inspector`);
      assert.equal(res.status, 200);
      const html = await res.text();

      assert.match(html, /data-route-id="artifact_inspector_reference_surface"/);
      assert.match(html, /data-route-path="\/artifact-inspector"/);
      assert.match(html, /data-reference-surface-family="artifact_inspector_advisory_workbench"/);
      assert.match(html, /data-reference-instance-id="artifact_inspector_reference_main"/);
      assert.match(html, /data-approved-profile-id="artifact_inspector_reference"/);
      assert.match(
        html,
        /data-route-payload-parity="presentational_transform_only_no_authority_or_reachability_meaning_drift"/,
      );
      assert.match(
        html,
        /data-diagnostics-lane-mode="placeholder_or_existing_artifact_backed_read_only_only"/,
      );
      assert.match(html, /Explicit Commit Gate/);
      assert.match(html, /Diagnostics lane remains read-only placeholder in v63\./);
      assert.match(html, /required evidence reachable before commit/i);
      assert.match(html, /UI may express but may not mint authority/i);
      assert.match(html, /data-epistemic-state="loading"/);
      assert.match(html, /data-epistemic-state="authoritative"/);
      assert.match(html, /data-epistemic-state="ambiguous"/);
      assert.match(html, /adeu\.binding\.commit-gate/);
      assert.match(html, /adeu\.binding\.warning-surface/);
      assert.match(html, /v36b\.prov:artifact_inspector_reference_main:authority_bearing_control/);
      assert.match(html, /data-truth-source="accepted_v36_artifacts_only"/);
      assert.match(html, /data-lane-id="action-lane"[\s\S]*data-rendered-cluster-ids="advisory-actions commit-actions"/);
      assert.match(html, /data-lane-id="work-context-lane"[\s\S]*data-rendered-cluster-ids="comparison-actions"/);
    } finally {
      await stopProcess(proc);
    }
  },
);
