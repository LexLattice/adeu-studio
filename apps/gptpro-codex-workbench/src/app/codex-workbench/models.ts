import type {
  ReviewOriginKind,
  ReviewTargetProfile,
  TerminalCommandId,
} from "./contract";

export type RepoTreeEntry = {
  name: string;
  path: string;
  kind: "directory" | "file" | "symlink";
  extension: string | null;
  size: number | null;
  hidden: boolean;
};

export type RepoTreeResponse = {
  repoRoot: string;
  directoryPath: string;
  entries: RepoTreeEntry[];
};

export type FileDocument = {
  path: string;
  name: string;
  extension: string | null;
  size: number;
  sha256: string;
  isBinary: boolean;
  truncated: boolean;
  lineCount: number;
  text: string;
  preview: string;
};

export type DiffLine = {
  kind: "meta" | "hunk" | "context" | "add" | "remove";
  text: string;
};

export type DiffDocument = {
  leftPath: string;
  rightPath: string;
  leftSha256: string;
  rightSha256: string;
  identical: boolean;
  truncated: boolean;
  raw: string;
  lines: DiffLine[];
  summary: {
    additions: number;
    removals: number;
    hunks: number;
  };
};

export type HarnessConfigCandidate = {
  label: string;
  path: string;
  exists: boolean;
  source: "env" | "repo" | "home" | "derived";
};

export type HarnessSummary = {
  repoRoot: string;
  codexBinConfigured: string;
  codexBinResolved: string | null;
  codexBinAvailable: boolean;
  apiDbPath: string | null;
  evidenceRoot: string | null;
  policyRegistryPath: string | null;
  codexModel: string | null;
  activeConfigPath: string | null;
  activeConfigSource: string | null;
  configTomlCandidates: HarnessConfigCandidate[];
  envSummary: Record<string, string | null>;
};

export type GitSnapshot = {
  status: "ready" | "unavailable" | "error";
  branch: string | null;
  head: string | null;
  summary: string;
  statusLines: string[];
  recentCommits: string[];
};

export type TerminalSnapshot = {
  commandId: TerminalCommandId;
  cwd: string;
  title: string;
  lines: string[];
  status: "ready" | "error";
};

export type CopilotSessionResponse = {
  session_id: string;
  status: "starting" | "running" | "stopped" | "failed";
  profile_id: string;
  profile_version: string;
  app_server_unavailable: boolean;
  idempotent_replay: boolean;
};

export type ToolCallResponse = {
  tool_name: string;
  warrant: "observed" | "derived" | "checked" | "hypothesis" | "unknown";
  result: unknown;
  policy_trace?: Record<string, unknown> | null;
};

export type ApprovalIssueResponse = {
  approval_id: string;
  session_id: string;
  action_kind: string;
  action_hash: string;
  expires_at: string;
};

export type PolicyProfileDescriptor = {
  profile_id: string;
  profile_version: string;
  default_policy_hash: string;
  allowed_policy_hashes: string[];
  policy_ref: string;
};

export type PolicyProfileListResponse = {
  profiles: PolicyProfileDescriptor[];
};

export type PolicyProfileCurrentResponse = {
  session_id: string;
  profile_id: string;
  profile_version: string;
  policy_hash: string;
};

export type PolicyProfileSelectResponse = {
  session_id: string;
  profile_id: string;
  profile_version: string;
  policy_hash: string;
  idempotent_replay: boolean;
};

export type AppStateSnapshot = {
  counts: Record<string, number>;
  active_copilot_session_id?: string | null;
  active_copilot_writes_allowed: boolean;
  codex_version?: string | null;
  codex_exec_available?: boolean | null;
  codex_app_server_available?: boolean | null;
};

export type TemplateMeta = {
  template_id: string;
  template_version: string;
  schema_version: string;
  domain_pack_id: string;
  domain_pack_version: string;
  role: string;
  description: string;
};

export type EvidenceBundle = {
  evidence_id: string;
  source: string;
  role: string;
  status: string;
  started_at: string;
  ended_at?: string | null;
  raw_jsonl_path?: string | null;
  raw_jsonl?: string | null;
  purged: boolean;
  metadata: Record<string, unknown>;
  error?: Record<string, unknown> | null;
};

export type ReviewRecord = {
  id: string;
  requestId: string;
  createdAt: string;
  originKind: ReviewOriginKind;
  originRef: string;
  title: string;
  targetProfile: ReviewTargetProfile;
  dispatchNote: string;
  status: "prepared" | "exported" | "running" | "completed" | "failed";
  summary: string;
  packetJson: string;
  evidenceId: string | null;
  evidence: EvidenceBundle | null;
};

export type WorkflowRunRecord = {
  id: string;
  createdAt: string;
  templateId: string;
  prompt: string;
  status: "prepared" | "running" | "completed" | "failed";
  evidenceId: string | null;
  evidence: EvidenceBundle | null;
  summary: string;
};
