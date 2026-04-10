import { access } from "node:fs/promises";
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const repoRoot = path.resolve(__dirname, "../../..");
const schemaDir = path.join(repoRoot, "packages", "adeu_ir", "schema");
const outDir = path.join(repoRoot, "apps", "web", "src", "gen");

const bannerComment = [
  "/*",
  " * GENERATED FILE — do not edit by hand.",
  " *",
  " * Regenerate:",
  " *   cd apps/gptpro-codex-workbench",
  " *   npm run gen:types",
  " */",
].join("\n");

async function generatedOutputsExist() {
  try {
    await access(path.join(outDir, "adeu_ir.ts"));
    await access(path.join(outDir, "check_report.ts"));
    return true;
  } catch {
    return false;
  }
}

async function loadCompiler() {
  try {
    const mod = await import("json-schema-to-typescript");
    return mod.compileFromFile;
  } catch (error) {
    if (await generatedOutputsExist()) {
      console.warn(
        `[gen:types] json-schema-to-typescript unavailable; keeping committed generated files. ${String(error)}`,
      );
      return null;
    }
    throw error;
  }
}

async function genOne(compileFromFile, schemaFile, outFile) {
  const schemaPath = path.join(schemaDir, schemaFile);
  const ts = await compileFromFile(schemaPath, {
    bannerComment,
    style: { singleQuote: false },
  });

  await mkdir(outDir, { recursive: true });
  await writeFile(path.join(outDir, outFile), ts, { encoding: "utf-8" });
}

const compileFromFile = await loadCompiler();
if (compileFromFile) {
  await genOne(compileFromFile, "adeu.ir.v0.json", "adeu_ir.ts");
  await genOne(compileFromFile, "adeu.check_report.v0.json", "check_report.ts");
}
