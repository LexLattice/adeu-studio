import { build } from "esbuild";
import { cp, mkdir, rm } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const appRoot = path.resolve(__dirname, "..");
const distRoot = path.join(appRoot, "dist");
const rendererDist = path.join(distRoot, "renderer");

await rm(distRoot, { recursive: true, force: true });
await mkdir(rendererDist, { recursive: true });

await Promise.all([
  build({
    entryPoints: [path.join(appRoot, "src", "main.ts")],
    outfile: path.join(distRoot, "main.js"),
    bundle: true,
    format: "cjs",
    platform: "node",
    target: "node20",
    external: ["electron"],
    sourcemap: false,
  }),
  build({
    entryPoints: [path.join(appRoot, "src", "preload.ts")],
    outfile: path.join(distRoot, "preload.js"),
    bundle: true,
    format: "cjs",
    platform: "node",
    target: "node20",
    external: ["electron"],
    sourcemap: false,
  }),
  build({
    entryPoints: [path.join(appRoot, "src", "renderer", "app.ts")],
    outfile: path.join(rendererDist, "app.js"),
    bundle: true,
    format: "esm",
    platform: "browser",
    target: "chrome124",
    sourcemap: false,
  }),
]);

await Promise.all([
  cp(path.join(appRoot, "src", "renderer", "index.html"), path.join(rendererDist, "index.html")),
  cp(path.join(appRoot, "src", "renderer", "styles.css"), path.join(rendererDist, "styles.css")),
]);
