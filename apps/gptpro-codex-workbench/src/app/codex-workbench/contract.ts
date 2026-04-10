export const CODEX_WORKBENCH_ID = "adeu_codex_desktop_workbench";
export const CODEX_WORKBENCH_ROUTE_ID = "adeu_codex_desktop_reference_route";
export const CODEX_WORKBENCH_PROFILE_ID = "adeu_codex_desktop_reference";

export const CONTEXT_ARTIFACT_TABS = [
  "files",
  "diff",
  "terminal",
  "git",
  "review",
  "workflow",
] as const;

export const REVIEW_TARGET_PROFILES = [
  "adeu_read_only_review",
  "adeu_second_pass_review",
  "export_packet",
] as const;

export const WORKSPACE_ROOT_OPTIONS = [
  "",
  "apps",
  "apps/web",
  "apps/api",
  "packages",
  "policy",
  "docs",
] as const;

export const TERMINAL_COMMAND_IDS = [
  "pwd",
  "ls",
  "git-status",
  "node-version",
  "python-version",
] as const;

export type ContextArtifactTab = (typeof CONTEXT_ARTIFACT_TABS)[number];
export type ReviewTargetProfile = (typeof REVIEW_TARGET_PROFILES)[number];
export type WorkspaceRootOption = (typeof WORKSPACE_ROOT_OPTIONS)[number];
export type TerminalCommandId = (typeof TERMINAL_COMMAND_IDS)[number];
export type ReviewOriginKind = "reply" | "file" | "diff";

export type ReviewOrigin = {
  originKind: ReviewOriginKind;
  originRef: string;
  title: string;
  provenance: Record<string, unknown>;
  content: string;
};

export type ReviewDispatchPacket = {
  schema: "adeu.review_dispatch_packet@1";
  request_id: string;
  advisory_only: true;
  target_profile: ReviewTargetProfile;
  created_at: string;
  origin_kind: ReviewOriginKind;
  origin_ref: string;
  title: string;
  payload_scope: {
    chars: number;
    preview: string;
  };
  provenance: Record<string, unknown>;
  dispatch_note: string;
  instructions: {
    verdict: string;
    risk_scan: string;
    revisions: string;
    confidence: string;
  };
  content: string;
};

export function isContextArtifactTab(value: string): value is ContextArtifactTab {
  return (CONTEXT_ARTIFACT_TABS as readonly string[]).includes(value);
}

export function isReviewTargetProfile(value: string): value is ReviewTargetProfile {
  return (REVIEW_TARGET_PROFILES as readonly string[]).includes(value);
}

export function isWorkspaceRootOption(value: string): value is WorkspaceRootOption {
  return (WORKSPACE_ROOT_OPTIONS as readonly string[]).includes(value);
}

export function isTerminalCommandId(value: string): value is TerminalCommandId {
  return (TERMINAL_COMMAND_IDS as readonly string[]).includes(value);
}

export function summarizePath(pathValue: string, maxSegments = 3): string {
  const normalized = pathValue
    .replace(/\\/g, "/")
    .split("/")
    .filter(Boolean);
  if (normalized.length <= maxSegments) return normalized.join("/") || ".";
  return `…/${normalized.slice(-maxSegments).join("/")}`;
}

export function clipText(text: string, maxChars = 320): string {
  const normalized = text.replace(/\s+/g, " ").trim();
  if (normalized.length <= maxChars) return normalized;
  return `${normalized.slice(0, maxChars - 1).trimEnd()}…`;
}

export function buildReviewDispatchPacket(args: {
  origin: ReviewOrigin;
  targetProfile: ReviewTargetProfile;
  requestId: string;
  createdAt: string;
  dispatchNote?: string;
}): ReviewDispatchPacket {
  const dispatchNote =
    args.dispatchNote?.trim() ||
    "Advisory review requested from the bounded desktop workbench.";

  return {
    schema: "adeu.review_dispatch_packet@1",
    request_id: args.requestId,
    advisory_only: true,
    target_profile: args.targetProfile,
    created_at: args.createdAt,
    origin_kind: args.origin.originKind,
    origin_ref: args.origin.originRef,
    title: args.origin.title,
    payload_scope: {
      chars: args.origin.content.length,
      preview: clipText(args.origin.content, 280),
    },
    provenance: args.origin.provenance,
    dispatch_note: dispatchNote,
    instructions: {
      verdict:
        "Return a concise verdict and state whether the origin is safe to accept as-is.",
      risk_scan: "List correctness, missing-evidence, and trust-boundary risks.",
      revisions:
        "Suggest the smallest concrete revisions that improve the artifact.",
      confidence:
        "State confidence as high, medium, or low with one sentence of rationale.",
    },
    content: args.origin.content,
  };
}

export function buildReviewPrompt(packet: ReviewDispatchPacket): string {
  return [
    "You are an ADEU advisory reviewer operating inside a bounded read-only workflow.",
    "Treat the supplied material as advisory-only. Do not imply merge, commit, or write authority.",
    "Respond in four short sections: Verdict, Risks, Revisions, Confidence.",
    `Target profile: ${packet.target_profile}`,
    `Origin kind: ${packet.origin_kind}`,
    `Origin ref: ${packet.origin_ref}`,
    `Title: ${packet.title}`,
    `Dispatch note: ${packet.dispatch_note}`,
    "",
    "Payload preview:",
    packet.payload_scope.preview,
    "",
    "Full content:",
    packet.content,
  ].join("\n");
}

export function extractReadableEvidenceSummary(
  rawJsonl: string | null | undefined,
): string {
  if (!rawJsonl) return "No evidence payload was returned.";

  const lines = rawJsonl
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean);

  if (lines.length === 0) return "No evidence payload was returned.";

  for (let index = lines.length - 1; index >= 0; index -= 1) {
    const line = lines[index];
    try {
      const parsed = JSON.parse(line) as {
        text?: string;
        msg?: string;
        final_output?: unknown;
      };
      if (typeof parsed.text === "string" && parsed.text.trim()) {
        return clipText(parsed.text, 500);
      }
      if (typeof parsed.msg === "string" && parsed.msg.trim()) {
        return clipText(parsed.msg, 500);
      }
      if (parsed.final_output !== undefined) {
        return clipText(JSON.stringify(parsed.final_output, null, 2), 500);
      }
      return clipText(JSON.stringify(parsed, null, 2), 500);
    } catch {
      return clipText(line, 500);
    }
  }

  return "No evidence payload was returned.";
}
