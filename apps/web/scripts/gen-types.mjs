import { compileFromFile } from "json-schema-to-typescript";
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
  " *   cd apps/web",
  " *   npm run gen:types",
  " */"
].join("\n");

async function genOne(schemaFile, outFile) {
  const schemaPath = path.join(schemaDir, schemaFile);
  const ts = await compileFromFile(schemaPath, {
    bannerComment,
    style: { singleQuote: false }
  });

  await mkdir(outDir, { recursive: true });
  await writeFile(path.join(outDir, outFile), ts, { encoding: "utf-8" });
}

await genOne("adeu.ir.v0.json", "adeu_ir.ts");
await genOne("adeu.check_report.v0.json", "check_report.ts");

