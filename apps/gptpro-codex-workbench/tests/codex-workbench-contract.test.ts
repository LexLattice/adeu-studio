import assert from "node:assert/strict";
import test from "node:test";

import {
  buildReviewDispatchPacket,
  buildReviewPrompt,
  CONTEXT_ARTIFACT_TABS,
  extractReadableEvidenceSummary,
  isTerminalCommandId,
  isWorkspaceRootOption,
  summarizePath,
} from "../src/app/codex-workbench/contract.ts";
import { normalizeRepoRelativePath } from "../src/app/lib/desktop/repo-access.ts";

test("codex workbench contract: bounded tab set remains frozen", () => {
  assert.deepEqual(CONTEXT_ARTIFACT_TABS, [
    "files",
    "diff",
    "terminal",
    "git",
    "review",
    "workflow",
  ]);
});

test("codex workbench contract: terminal and workspace guards fail closed", () => {
  assert.equal(isTerminalCommandId("pwd"), true);
  assert.equal(isTerminalCommandId("bash"), false);
  assert.equal(isWorkspaceRootOption("apps/web"), true);
  assert.equal(isWorkspaceRootOption("../../etc"), false);
});

test("codex workbench contract: review packet preserves advisory posture", () => {
  const packet = buildReviewDispatchPacket({
    origin: {
      originKind: "reply",
      originRef: "assistant:123",
      title: "Assistant reply",
      provenance: { role: "assistant" },
      content: "Return a concise review.",
    },
    targetProfile: "adeu_read_only_review",
    requestId: "req-1",
    createdAt: "2026-04-09T00:00:00.000Z",
  });

  assert.equal(packet.advisory_only, true);
  assert.equal(packet.origin_kind, "reply");
  assert.match(buildReviewPrompt(packet), /advisory reviewer/i);
  assert.match(buildReviewPrompt(packet), /Origin ref: assistant:123/);
});

test("codex workbench contract: evidence summary prefers latest readable payload", () => {
  const raw = [
    JSON.stringify({ msg: "ignored earlier" }),
    JSON.stringify({ text: "latest summary text" }),
  ].join("\n");

  assert.equal(extractReadableEvidenceSummary(raw), "latest summary text");
});

test("codex workbench contract: summarizePath and repo path normalization stay bounded", () => {
  assert.equal(summarizePath("apps/web/src/app/codex-workbench/page.tsx", 3), "…/app/codex-workbench/page.tsx");
  assert.equal(normalizeRepoRelativePath("apps/web"), "apps/web");
  assert.equal(normalizeRepoRelativePath("/apps/web"), "apps/web");
  assert.throws(() => normalizeRepoRelativePath("../secrets"), /path traversal/i);
});
