import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";

import { cache } from "react";

import {
  buildDefaultViewConfig,
  type CommittedSampleArtifact,
  createViewModel,
  createInvalidFixtureStackViewModel,
  type PaperSemanticWorkbenchViewModel,
  parsePaperSemanticArtifact,
} from "./view-model";

export const COMMITTED_SAMPLE_ARTIFACT_REFS = [
  "packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json",
  "packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_paragraph.json",
] as const;

export type PaperSemanticWorkbenchBootstrap = {
  sampleArtifacts: CommittedSampleArtifact[];
  initialViewModel: PaperSemanticWorkbenchViewModel;
};

const loadCommittedSampleArtifactsCached = cache(async (): Promise<PaperSemanticWorkbenchBootstrap> => {
  const repoRoot = path.resolve(process.cwd(), "..", "..");
  const availableRefs = [...COMMITTED_SAMPLE_ARTIFACT_REFS];

  try {
    if (!existsSync(path.join(repoRoot, "Makefile"))) {
      throw new Error(`INVALID_REPO_ROOT:${process.cwd()}`);
    }

    const sampleArtifacts = await Promise.all(
      COMMITTED_SAMPLE_ARTIFACT_REFS.map(async (ref): Promise<CommittedSampleArtifact> => {
        const raw = JSON.parse(await readFile(path.join(repoRoot, ref), "utf-8")) as unknown;
        const artifact = parsePaperSemanticArtifact(raw);
        if (!artifact) {
          throw new Error(`INVALID_RELEASED_V52A_ARTIFACT:${ref}`);
        }
        return { ref, artifact };
      }),
    );

    const initialViewModel = createViewModel(
      sampleArtifacts,
      buildDefaultViewConfig(COMMITTED_SAMPLE_ARTIFACT_REFS[0]),
    );
    return {
      sampleArtifacts,
      initialViewModel,
    };
  } catch (error) {
    const failureCode =
      error instanceof Error && error.message.length > 0
        ? error.message
        : "INVALID_RELEASED_V52A_ARTIFACT_STACK";
    return {
      sampleArtifacts: [],
      initialViewModel: createInvalidFixtureStackViewModel({
        selectedSampleArtifactRef: COMMITTED_SAMPLE_ARTIFACT_REFS[0],
        availableSampleArtifactRefs: availableRefs,
        failureCode,
      }),
    };
  }
});

export async function loadCommittedSampleArtifacts(): Promise<PaperSemanticWorkbenchBootstrap> {
  return loadCommittedSampleArtifactsCached();
}
