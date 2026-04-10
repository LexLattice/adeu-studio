import type { Metadata } from "next";

import { CodexWorkbenchClient } from "./codex-workbench-client";

export const metadata: Metadata = {
  title: "ADEU Codex Desktop Workbench | ADEU Studio",
};

export default function CodexWorkbenchPage() {
  return <CodexWorkbenchClient />;
}
