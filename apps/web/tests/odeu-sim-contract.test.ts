import assert from "node:assert/strict";
import { existsSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

import {
  buildDefaultViewConfig,
  createViewModelFromApiResponse,
  DEFAULT_SCENARIO_NAME,
  DEFAULT_SEED,
  DEFAULT_STEPS,
  mapApiRequestStatusToRouteStatus,
  ODEU_RUN_OUTPUT_MODE,
  parseApiResponse,
} from "../src/app/odeu-sim/view-model.ts";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const REPO_ROOT = path.resolve(__dirname, "..", "..", "..");
if (!existsSync(path.join(REPO_ROOT, "Makefile"))) {
  throw new Error(`Could not resolve repository root at ${REPO_ROOT}`);
}
const ODEU_SIM_ROUTE_DIR = path.join(REPO_ROOT, "apps", "web", "src", "app", "odeu-sim");

async function readFixture(name: string): Promise<unknown> {
  const fixturePath = path.join(
    REPO_ROOT,
    "apps",
    "api",
    "tests",
    "fixtures",
    "v51b",
    name,
  );
  return JSON.parse(await readFile(fixturePath, "utf-8"));
}

async function collectRouteSources(dir: string): Promise<string[]> {
  const entries = await readdir(dir, { withFileTypes: true });
  const files: string[] = [];
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...(await collectRouteSources(fullPath)));
      continue;
    }
    if (entry.name.endsWith(".ts") || entry.name.endsWith(".tsx")) {
      files.push(fullPath);
    }
  }
  return files.sort();
}

test("odeu sim defaults: idle-first config is frozen", () => {
  const config = buildDefaultViewConfig();
  assert.equal(config.scenario_name, DEFAULT_SCENARIO_NAME);
  assert.equal(config.seed, DEFAULT_SEED);
  assert.equal(config.steps, DEFAULT_STEPS);
  assert.equal(config.output_mode, ODEU_RUN_OUTPUT_MODE);
});

test("odeu sim view-model: API status maps directly after completion", () => {
  assert.equal(mapApiRequestStatusToRouteStatus("completed_clean"), "completed_clean");
  assert.equal(
    mapApiRequestStatusToRouteStatus("fail_closed_invalid_request"),
    "fail_closed_invalid_request",
  );
  assert.equal(
    mapApiRequestStatusToRouteStatus("fail_closed_kernel_mismatch"),
    "fail_closed_kernel_mismatch",
  );
});

test("odeu sim view-model: completed response preserves full released objects and response_hash", async () => {
  const fixture = await readFixture("reference_odeu_run_response_healthy_baseline.json");
  const parsed = parseApiResponse(fixture);
  assert.ok(parsed);

  const viewModel = createViewModelFromApiResponse(parsed);
  assert.equal(viewModel.route_status, "completed_clean");
  assert.equal(viewModel.response_hash, parsed.response_hash);
  assert.deepEqual(viewModel.config_snapshot, parsed.run_summary?.config_snapshot ?? null);
  assert.deepEqual(viewModel.current_metric, parsed.run_summary?.current_metric ?? null);
});

test("odeu sim view-model: failure response preserves response_hash and null summary fields", async () => {
  const fixture = await readFixture("reference_odeu_run_response_kernel_mismatch.json");
  const parsed = parseApiResponse(fixture);
  assert.ok(parsed);

  const viewModel = createViewModelFromApiResponse(parsed);
  assert.equal(viewModel.route_status, "fail_closed_kernel_mismatch");
  assert.equal(viewModel.response_hash, parsed.response_hash);
  assert.equal(viewModel.config_snapshot, null);
  assert.equal(viewModel.current_metric, null);
});

test("odeu sim route: no direct kernel import under apps/web/src/app/odeu-sim", async () => {
  const routeFiles = await collectRouteSources(ODEU_SIM_ROUTE_DIR);
  assert.ok(routeFiles.length > 0);

  for (const routeFile of routeFiles) {
    const source = await readFile(routeFile, "utf-8");
    assert.doesNotMatch(
      source,
      /\bfrom\s+["']adeu_odeu_sim(?:\/.*)?["']|\bimport\s*(?:\(\s*)?["']adeu_odeu_sim(?:\/.*)?["']\s*\)?/,
      `unexpected direct kernel import in ${routeFile}`,
    );
  }
});
