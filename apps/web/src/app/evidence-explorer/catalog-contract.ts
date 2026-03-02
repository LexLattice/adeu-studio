export const EVIDENCE_EXPLORER_FAMILIES = [
  "read_surface",
  "normative_advice",
  "proof_trust",
  "semantics_v4_candidate",
  "extraction_fidelity",
] as const;

export type EvidenceExplorerFamily = (typeof EVIDENCE_EXPLORER_FAMILIES)[number];

export const EVIDENCE_EXPLORER_LIST_REF_PATH_TEMPLATE = "/urm/evidence-explorer/catalog/{family}";
export const EVIDENCE_EXPLORER_LIST_REF_PATH_PREFIX = "/urm/evidence-explorer/catalog/";

const FAMILY_PLACEHOLDER = "{family}";
const EVIDENCE_EXPLORER_FAMILY_SET: ReadonlySet<string> = new Set(EVIDENCE_EXPLORER_FAMILIES);

function extractBraceTokens(path: string): string[] | null {
  const tokens: string[] = [];
  let offset = 0;
  while (offset < path.length) {
    const open = path.indexOf("{", offset);
    if (open < 0) break;
    const close = path.indexOf("}", open + 1);
    if (close < 0) {
      return null;
    }
    tokens.push(path.slice(open, close + 1));
    offset = close + 1;
  }
  return tokens;
}

export function isEvidenceExplorerFamily(value: unknown): value is EvidenceExplorerFamily {
  return typeof value === "string" && EVIDENCE_EXPLORER_FAMILY_SET.has(value);
}

export function isCatalogListRefTemplate(path: unknown): path is string {
  if (typeof path !== "string") return false;
  if (!path.startsWith(EVIDENCE_EXPLORER_LIST_REF_PATH_PREFIX)) return false;
  const tokens = extractBraceTokens(path);
  if (!tokens || tokens.length !== 1) return false;
  if (tokens[0] !== FAMILY_PLACEHOLDER) return false;
  const first = path.indexOf(FAMILY_PLACEHOLDER);
  if (first < 0) return false;
  if (first !== path.lastIndexOf(FAMILY_PLACEHOLDER)) return false;
  return path === EVIDENCE_EXPLORER_LIST_REF_PATH_TEMPLATE;
}

export function expandCatalogListRefTemplate(
  templatePath: string,
  family: EvidenceExplorerFamily,
): string | null {
  if (!isCatalogListRefTemplate(templatePath)) return null;
  const expanded = templatePath.replace(FAMILY_PLACEHOLDER, encodeURIComponent(family));
  if (!expanded.startsWith(EVIDENCE_EXPLORER_LIST_REF_PATH_PREFIX)) return null;
  return expanded;
}

export function sortFamiliesLexicographic<T extends { family: EvidenceExplorerFamily }>(
  values: readonly T[],
): T[] {
  return [...values].sort((a, b) => a.family.localeCompare(b.family));
}

export function hasLexicographicFamilyOrder<T extends { family: EvidenceExplorerFamily }>(
  values: readonly T[],
): boolean {
  for (let index = 1; index < values.length; index += 1) {
    if (values[index - 1].family.localeCompare(values[index].family) > 0) {
      return false;
    }
  }
  return true;
}
