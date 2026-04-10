import type { Metadata } from "next";

import { PaperSemanticWorkbenchClient } from "./paper-semantic-workbench-client";
import { loadCommittedSampleArtifacts } from "./sample-artifacts";

export const metadata: Metadata = {
  title: "Paper Semantic Workbench | ADEU Studio",
};

export default async function PaperSemanticWorkbenchPage() {
  const { sampleArtifacts, initialViewModel } = await loadCommittedSampleArtifacts();
  return (
    <PaperSemanticWorkbenchClient
      sampleArtifacts={sampleArtifacts}
      initialViewModel={initialViewModel}
    />
  );
}
