export const DEFAULT_API_BASE_URL = "http://127.0.0.1:8000";
export const DEFAULT_WORKFLOW_TEMPLATE_ID = "adeu.workflow.pipeline_worker.v0";

export type WorkspaceNodeKind = "file" | "dir";
export type CopilotStatus = "idle" | "starting" | "running" | "stopped" | "failed";
export type ConnectionStatus = "disconnected" | "connecting" | "connected";
export type ToolWarrant = "observed" | "derived" | "checked" | "hypothesis" | "unknown";
export type TerminalPresetId = "pwd" | "git_status" | "git_diff_stat" | "git_log" | "ls";
export type ArtifactTabId =
  | "files"
  | "diff"
  | "terminal"
  | "git"
  | "review"
  | "workflow";
export type ReviewOriginKind = "reply" | "file" | "diff" | "workflow";
export type ReviewTargetBindingMode = "backend_routed" | "prompt_guidance_only";

export type LaunchProfile = {
  id: string;
  label: string;
  codexBinary: string;
  provider: "codex";
  configPath: string;
  desiredPolicyProfileId: string;
  notes: string;
};

export type RecentSessionRecord = {
  sessionId: string;
  startedAt: string;
  launchProfileId: string;
};

export type HostPersistedState = {
  workspaceRoot: string;
  apiBaseUrl: string;
  selectedLaunchProfileId: string;
  recentSessions: RecentSessionRecord[];
};

export type WorkspaceTreeNode = {
  name: string;
  relativePath: string;
  kind: WorkspaceNodeKind;
  hasChildren: boolean;
};

export type FileReadResult = {
  relativePath: string;
  absolutePath: string;
  content: string;
  truncated: boolean;
  approxLineCount: number;
};

export type GitSnapshot = {
  isRepo: boolean;
  branch: string;
  shortStatus: string[];
  recentCommits: string[];
  diffStat: string;
  error?: string;
};

export type FileDiffResult = {
  target: string | null;
  diffText: string;
  truncated: boolean;
  error?: string;
};

export type TerminalPresetResult = {
  commandId: TerminalPresetId;
  command: string;
  stdout: string;
  stderr: string;
  exitCode: number;
  ranAt: string;
  readOnly: boolean;
};

export type CopilotSessionResponse = {
  session_id: string;
  status: Exclude<CopilotStatus, "idle">;
  app_server_unavailable: boolean;
  idempotent_replay: boolean;
};

export type ToolCallResponse = {
  tool_name: string;
  warrant: ToolWarrant;
  result: unknown;
  policy_trace?: unknown;
};

export type ToolCallRequestArgs = {
  sessionId?: string | null;
  toolName: string;
  argumentsValue: Record<string, unknown>;
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

export type WorkflowRunRef = {
  worker_id?: string;
  evidence_id?: string;
  status?: string;
  template_id?: string;
  template_version?: string;
};

export type ReviewTargetProfile = {
  id: string;
  label: string;
  guidance: string;
  promptPreamble: string;
};

export type ReviewDispatchRecord = {
  id: string;
  createdAt: string;
  originKind: ReviewOriginKind;
  originRef: string;
  targetProfileId: string;
  executionToolName: string;
  executionTemplateId: string | null;
  targetBindingMode: ReviewTargetBindingMode;
  targetBindingSummary: string;
  requestId: string;
  status: string;
  statusDetail?: string;
  failureReason?: string;
  evidenceLoadError?: string;
  evidenceId?: string;
  workerId?: string;
  summary: string;
};

export type WorkflowRecord = {
  id: string;
  createdAt: string;
  prompt: string;
  templateId: string;
  requestId: string;
  status: string;
  statusDetail?: string;
  failureReason?: string;
  evidenceLoadError?: string;
  evidenceId?: string;
  workerId?: string;
};

export type CopilotStreamEnvelope = {
  sessionId: string;
  eventType: string;
  payload: unknown;
};

export type HostBridge = {
  getHostState: () => Promise<HostPersistedState>;
  updateHostState: (
    partial: Partial<HostPersistedState>,
  ) => Promise<HostPersistedState>;
  chooseWorkspaceRoot: () => Promise<string | null>;
  listDirectory: (relativePath?: string) => Promise<WorkspaceTreeNode[]>;
  readWorkspaceFile: (relativePath: string) => Promise<FileReadResult>;
  getGitSnapshot: () => Promise<GitSnapshot>;
  getFileDiff: (relativePath?: string | null) => Promise<FileDiffResult>;
  runTerminalPreset: (commandId: TerminalPresetId) => Promise<TerminalPresetResult>;
  startSession: () => Promise<CopilotSessionResponse>;
  stopSession: (sessionId: string) => Promise<CopilotSessionResponse>;
  sendMessage: (sessionId: string, text: string) => Promise<CopilotSessionResponse>;
  setWrites: (
    sessionId: string,
    writesAllowed: boolean,
  ) => Promise<CopilotSessionResponse>;
  callTool: (args: ToolCallRequestArgs) => Promise<ToolCallResponse>;
  listPolicyProfiles: () => Promise<PolicyProfileListResponse>;
  getCurrentPolicyProfile: (
    sessionId: string,
  ) => Promise<PolicyProfileCurrentResponse>;
  selectPolicyProfile: (
    sessionId: string,
    profileId: string,
  ) => Promise<PolicyProfileSelectResponse>;
  startCopilotStream: (sessionId: string) => Promise<void>;
  stopCopilotStream: (sessionId: string) => Promise<void>;
  onCopilotEvent: (listener: (event: CopilotStreamEnvelope) => void) => () => void;
};

export const DEFAULT_LAUNCH_PROFILES: LaunchProfile[] = [
  {
    id: "repo-default",
    label: "Repo Default",
    codexBinary: "codex",
    provider: "codex",
    configPath: "~/.config/codex/config.toml",
    desiredPolicyProfileId: "default",
    notes: "Balanced default posture for the connected ADEU runtime.",
  },
  {
    id: "safe-review",
    label: "Safe Review",
    codexBinary: "codex",
    provider: "codex",
    configPath: "~/.config/codex/review.toml",
    desiredPolicyProfileId: "safe_mode",
    notes: "Biases the session toward review and advisory work with explicit guard posture.",
  },
  {
    id: "experimental",
    label: "Experimental",
    codexBinary: "codex",
    provider: "codex",
    configPath: "~/.config/codex/experimental.toml",
    desiredPolicyProfileId: "experimental",
    notes: "Fast-path profile for broader experimentation. Keep authority boundaries explicit.",
  },
];

export const REVIEW_TARGETS: ReviewTargetProfile[] = [
  {
    id: "risk-review",
    label: "Risk Review",
    guidance: "Behavioral regression, correctness risk, and missing test review.",
    promptPreamble:
      "Review the provided artifact in code-review mode. Prioritize concrete bugs, risks, regressions, missing tests, and false authority claims. Treat the result as advisory evidence only.",
  },
  {
    id: "alignment-review",
    label: "Alignment Review",
    guidance: "ADEU/Morphic UX alignment and authority-boundary review.",
    promptPreamble:
      "Review the provided artifact for ADEU alignment, truth posture, authority boundaries, evidence visibility, and workflow handoff clarity. Treat the result as advisory evidence only.",
  },
  {
    id: "summary-review",
    label: "Dispatch Summary",
    guidance: "Short review packet suitable for quick external consumption.",
    promptPreamble:
      "Produce a short external review summary of the provided artifact, explicitly separating observed facts, inferred risks, and follow-up questions. Treat the result as advisory evidence only.",
  },
];

export const DEFAULT_REFLEXIVE_PAYLOAD = {
  schema: "adeu_brokered_reflexive_payload@1",
  payload_id: "udeo_master_payload_v1",
  title: "ADEU / UDEO Master Executable Payload",
  source_doc_ref: "docs/DRAFT_MASTER_EXECUTABLE_PAYLOAD_v0.md",
  source_doc_sha256:
    "fc9b583716159916ac982335a993365828e05fddfb84e1e21bc41e49ca3c60e2",
  domain_class: "soft_reflexive",
  max_delegation_depth: 3,
  advisory_only: true,
  requested_roles: [
    "orchestrator",
    "explorer",
    "adversarial_reviewer",
    "implementer",
    "code_reviewer",
    "gatekeeper",
  ],
  compiler_pipeline: {
    ontology_question: "What is the object, claim, or system boundary?",
    epistemics_question: "What is the provenance, access route, and justification?",
    deontics_question: "What is permitted, required, or binding?",
    utility_question: "What stake or optimization pressure is guiding the artifact?",
  },
};
