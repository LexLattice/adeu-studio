import assert from "node:assert/strict";
import { existsSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

import {
  buildDefaultViewConfig,
  createInvalidFixtureStackViewModel,
  createViewModel,
  PAPER_SEMANTIC_WORKBENCH_ROUTE_ID,
  parsePaperSemanticArtifact,
  SOURCE_AUTHORITY_POSTURE,
} from "../src/app/papers/semantic-workbench/view-model.ts";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const REPO_ROOT = path.resolve(__dirname, "..", "..", "..");
if (!existsSync(path.join(REPO_ROOT, "Makefile"))) {
  throw new Error(`Could not resolve repository root at ${REPO_ROOT}`);
}
const WORKBENCH_ROUTE_DIR = path.join(
  REPO_ROOT,
  "apps",
  "web",
  "src",
  "app",
  "papers",
  "semantic-workbench",
);
const FIXTURE_ROOT = path.join(
  REPO_ROOT,
  "packages",
  "adeu_paper_semantics",
  "tests",
  "fixtures",
  "v52a",
);

const ABSTRACT_FIXTURE_REF =
  "packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json";
const PARAGRAPH_FIXTURE_REF =
  "packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_paragraph.json";

async function readFixture(name: string): Promise<unknown> {
  return JSON.parse(await readFile(path.join(FIXTURE_ROOT, name), "utf-8"));
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

test("paper semantic workbench defaults: committed abstract sample is frozen", () => {
  const config = buildDefaultViewConfig(ABSTRACT_FIXTURE_REF);
  assert.equal(config.route_id, PAPER_SEMANTIC_WORKBENCH_ROUTE_ID);
  assert.equal(config.selected_sample_artifact_ref, ABSTRACT_FIXTURE_REF);
  assert.equal(config.selected_surface, "artifact");
  assert.equal(config.focus_claim_id, null);
  assert.deepEqual(config.visible_lane_ids, ["O", "E", "D", "U"]);
  assert.deepEqual(
    Object.keys(config).sort(),
    [
      "focus_claim_id",
      "route_id",
      "schema",
      "selected_sample_artifact_ref",
      "selected_surface",
      "visible_lane_ids",
    ],
  );
});

test("paper semantic workbench parser: committed abstract fixture validates against released shape", async () => {
  const fixture = await readFixture("reference_paper_semantic_artifact_abstract.json");
  const artifact = parsePaperSemanticArtifact(fixture);
  assert.ok(artifact);
  assert.equal(artifact.source_authority_posture, SOURCE_AUTHORITY_POSTURE);
  assert.equal(artifact.artifact_id, "paper_semantic:5ce49f7c50dff3f2");
  assert.equal(artifact.semantic_hash.length, 64);
});

test("paper semantic workbench parser: malformed released fixture fails closed", async () => {
  const fixture = await readFixture("reject_malformed_span_anchor.json");
  assert.equal(parsePaperSemanticArtifact(fixture), null);
});

test("paper semantic workbench view-model: preserves semantic law fields and ref split", async () => {
  const abstract = parsePaperSemanticArtifact(
    await readFixture("reference_paper_semantic_artifact_abstract.json"),
  );
  const paragraph = parsePaperSemanticArtifact(
    await readFixture("reference_paper_semantic_artifact_paragraph.json"),
  );
  assert.ok(abstract);
  assert.ok(paragraph);

  const viewModel = createViewModel(
    [
      { ref: ABSTRACT_FIXTURE_REF, artifact: abstract },
      { ref: PARAGRAPH_FIXTURE_REF, artifact: paragraph },
    ],
    buildDefaultViewConfig(ABSTRACT_FIXTURE_REF),
  );

  assert.equal(viewModel.route_status, "ready_clean");
  assert.equal(viewModel.selected_sample_artifact_ref, ABSTRACT_FIXTURE_REF);
  assert.equal(viewModel.artifact_ref, abstract.artifact_id);
  assert.equal(viewModel.semantic_hash, abstract.semantic_hash);
  assert.deepEqual(viewModel.identity_field_names, abstract.identity_field_names);
  assert.deepEqual(viewModel.projection_field_names, abstract.projection_field_names);
  assert.deepEqual(viewModel.ordered_claim_ids, abstract.projections[0]?.claim_order ?? []);
});

test("paper semantic workbench view-model: missing selected surface projection fails closed", async () => {
  const abstract = parsePaperSemanticArtifact(
    await readFixture("reference_paper_semantic_artifact_abstract.json"),
  );
  assert.ok(abstract);

  const viewModel = createViewModel(
    [{ ref: ABSTRACT_FIXTURE_REF, artifact: abstract }],
    {
      ...buildDefaultViewConfig(ABSTRACT_FIXTURE_REF),
      selected_surface: "local",
    },
  );

  assert.equal(viewModel.route_status, "fail_closed_invalid_fixture_stack");
  assert.equal(viewModel.failure_code, "INVALID_SELECTED_SURFACE_PROJECTION");
  assert.equal(viewModel.artifact, null);
});

test("paper semantic workbench view-model: spatial surface stays derived from released ordering anchors", async () => {
  const abstract = parsePaperSemanticArtifact(
    await readFixture("reference_paper_semantic_artifact_abstract.json"),
  );
  assert.ok(abstract);

  const firstViewModel = createViewModel(
    [{ ref: ABSTRACT_FIXTURE_REF, artifact: abstract }],
    {
      ...buildDefaultViewConfig(ABSTRACT_FIXTURE_REF),
      selected_surface: "spatial",
    },
  );
  const secondViewModel = createViewModel(
    [{ ref: ABSTRACT_FIXTURE_REF, artifact: abstract }],
    {
      ...buildDefaultViewConfig(ABSTRACT_FIXTURE_REF),
      selected_surface: "spatial",
    },
  );

  assert.equal(firstViewModel.route_status, "ready_clean");
  assert.ok(firstViewModel.spatial_scene);
  assert.equal(firstViewModel.selected_surface, "spatial");
  assert.equal(firstViewModel.spatial_scene.artifact_ref, abstract.artifact_id);
  assert.equal(firstViewModel.spatial_scene.semantic_hash, abstract.semantic_hash);
  assert.equal(firstViewModel.spatial_scene.scene_hash, secondViewModel.spatial_scene?.scene_hash);
  assert.deepEqual(firstViewModel.spatial_scene.node_order, secondViewModel.spatial_scene?.node_order);
  assert.ok(firstViewModel.spatial_scene.nodes.length > 0);
  assert.ok(firstViewModel.spatial_scene.edges.length > 0);
  assert.deepEqual(
    [...new Set(firstViewModel.spatial_scene.nodes.map((node) => node.node_kind))].sort(),
    ["claim", "lane_fragment"],
  );
  assert.deepEqual(
    [...new Set(firstViewModel.spatial_scene.edges.map((edge) => edge.edge_kind))].sort(),
    ["claim_to_fragment", "inference_bridge"],
  );
  assert.ok(firstViewModel.ordered_claim_ids.length > 0);
});

test("paper semantic workbench parser: invalid diagnostic enum fixture fails closed", async () => {
  const fixture = await readFixture("reject_invalid_diagnostic_kind.json");
  assert.equal(parsePaperSemanticArtifact(fixture), null);
});

test("paper semantic workbench view-model: invalid fixture stack stays typed and fail-closed", () => {
  const viewModel = createInvalidFixtureStackViewModel({
    selectedSampleArtifactRef: ABSTRACT_FIXTURE_REF,
    availableSampleArtifactRefs: [ABSTRACT_FIXTURE_REF, PARAGRAPH_FIXTURE_REF],
    failureCode: "INVALID_RELEASED_V52A_ARTIFACT:abstract",
  });

  assert.equal(viewModel.route_status, "fail_closed_invalid_fixture_stack");
  assert.equal(viewModel.artifact, null);
  assert.equal(viewModel.failure_code, "INVALID_RELEASED_V52A_ARTIFACT:abstract");
  assert.equal(viewModel.selected_sample_artifact_ref, ABSTRACT_FIXTURE_REF);
});

test("paper semantic workbench route: no direct API, fetch, live-worker, or spatial imports", async () => {
  const routeFiles = await collectRouteSources(WORKBENCH_ROUTE_DIR);
  assert.ok(routeFiles.length > 0);

  for (const routeFile of routeFiles) {
    const source = await readFile(routeFile, "utf-8");
    assert.doesNotMatch(source, /\bfetch\s*\(/, `unexpected fetch in ${routeFile}`);
    assert.doesNotMatch(
      source,
      /\bfrom\s+["']\.\.\/\.\.\/lib\/api-base["']|\bfrom\s+["']\.\.?\/.*live-worker["']/,
      `unexpected live bridge import in ${routeFile}`,
    );
    assert.doesNotMatch(
      source,
      /examples\/external_prototypes\/adeu-paper-semantic-workbench-poc/,
      `unexpected direct prototype overlay import in ${routeFile}`,
    );
    assert.doesNotMatch(
      source,
      /from\s+["'].*adeu_paper_semantics.*spatial/i,
      `unexpected artifact-authority spatial import in ${routeFile}`,
    );
  }
});
