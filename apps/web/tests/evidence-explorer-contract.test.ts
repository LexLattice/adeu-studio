import assert from "node:assert/strict";
import test from "node:test";

import {
  EVIDENCE_EXPLORER_FAMILIES,
  EVIDENCE_EXPLORER_LIST_REF_PATH_TEMPLATE,
  expandCatalogListRefTemplate,
  hasLexicographicFamilyOrder,
  isCatalogListRefTemplate,
  isEvidenceExplorerFamily,
  sortFamiliesLexicographic,
} from "../src/app/evidence-explorer/catalog-contract.ts";

test("family contract: accepted set equals frozen set and unknown fails closed", () => {
  const candidates = [
    ...EVIDENCE_EXPLORER_FAMILIES,
    "unknown_family",
    "read-surface",
  ];
  const accepted = candidates.filter(isEvidenceExplorerFamily);

  assert.equal(new Set(accepted).size, EVIDENCE_EXPLORER_FAMILIES.length);
  assert.deepEqual(new Set(accepted), new Set(EVIDENCE_EXPLORER_FAMILIES));
  assert.equal(isEvidenceExplorerFamily("unknown_family"), false);
});

test("list_ref template validation: exact template accepted and expanded path rejected", () => {
  assert.equal(isCatalogListRefTemplate(EVIDENCE_EXPLORER_LIST_REF_PATH_TEMPLATE), true);
  assert.equal(isCatalogListRefTemplate("/urm/evidence-explorer/catalog/read_surface"), false);
});

test("list_ref template validation: malformed placeholder forms fail closed", () => {
  assert.equal(isCatalogListRefTemplate("/urm/evidence-explorer/catalog/family"), false);
  assert.equal(
    isCatalogListRefTemplate("/urm/evidence-explorer/catalog/{family}/{family}"),
    false,
  );
  assert.equal(isCatalogListRefTemplate("/urm/evidence-explorer/catalog/{fam}"), false);
  assert.equal(
    isCatalogListRefTemplate("/urm/evidence-explorer/catalog/{family?}"),
    false,
  );
  assert.equal(
    isCatalogListRefTemplate("/urm/evidence-explorer/catalog/{family"),
    false,
  );
});

test("template expansion: deterministic family path expansion", () => {
  const expanded = expandCatalogListRefTemplate(
    EVIDENCE_EXPLORER_LIST_REF_PATH_TEMPLATE,
    "read_surface",
  );
  assert.equal(expanded, "/urm/evidence-explorer/catalog/read_surface");
});

test("family ordering helper: deterministic lexicographic order", () => {
  const unsorted = [
    { family: "semantics_v4_candidate" as const, entry_count: 1 },
    { family: "read_surface" as const, entry_count: 1 },
    { family: "proof_trust" as const, entry_count: 1 },
  ];
  const sorted = sortFamiliesLexicographic(unsorted);
  assert.deepEqual(
    sorted.map((row) => row.family),
    ["proof_trust", "read_surface", "semantics_v4_candidate"],
  );
  assert.equal(hasLexicographicFamilyOrder(sorted), true);
  assert.equal(hasLexicographicFamilyOrder(unsorted), false);
});
