import {
  DEFAULT_LAUNCH_PROFILES,
  DEFAULT_REFLEXIVE_PAYLOAD,
  DEFAULT_WORKFLOW_TEMPLATE_ID,
  REVIEW_TARGETS,
  type AppStateSnapshot,
  type ArtifactTabId,
  type ConnectionStatus,
  type CopilotSessionResponse,
  type CopilotStatus,
  type EvidenceBundle,
  type FileDiffResult,
  type FileReadResult,
  type GitSnapshot,
  type HostPersistedState,
  type LaunchProfile,
  type PolicyProfileCurrentResponse,
  type PolicyProfileDescriptor,
  type ReviewDispatchRecord,
  type ReviewOriginKind,
  type ReviewTargetBindingMode,
  type ReviewTargetProfile,
  type TerminalPresetId,
  type TerminalPresetResult,
  type TemplateMeta,
  type WorkflowRecord,
  type WorkspaceTreeNode,
} from "../shared/types";

type TranscriptRole = "user" | "assistant";
type TranscriptStatus = "pending" | "streaming" | "complete";

type TranscriptItem = {
  id: string;
  role: TranscriptRole;
  text: string;
  createdAt: string;
  status: TranscriptStatus;
  turnId?: string;
};

type TimelineEntry = {
  id: string;
  at: string;
  summary: string;
};

type ReviewOrigin = {
  kind: ReviewOriginKind;
  ref: string;
  title: string;
  content: string;
  provenance: string;
};

type OverlayState =
  | { kind: "none" }
  | { kind: "file-peek"; file: FileReadResult }
  | { kind: "review-picker"; origin: ReviewOrigin; selectedTargetId: string };

type NormalizedEventLike = {
  seq?: number;
  ts?: string;
  event_kind?: string;
  payload?: unknown;
  detail?: unknown;
};

type State = {
  ready: boolean;
  error: string | null;
  busy: Set<string>;
  hostState: HostPersistedState | null;
  apiBaseDraft: string;
  appState: AppStateSnapshot | null;
  sessionId: string | null;
  status: CopilotStatus;
  connection: ConnectionStatus;
  writesAllowed: boolean;
  workerOnlyMode: boolean;
  lastHeartbeatAt: string | null;
  policyProfiles: PolicyProfileDescriptor[];
  currentPolicy: PolicyProfileCurrentResponse | null;
  messageDraft: string;
  workflowPrompt: string;
  selectedTemplateId: string;
  templates: TemplateMeta[];
  evidenceIdInput: string;
  loadedEvidence: EvidenceBundle | null;
  compiledPlan: unknown | null;
  activeArtifact: ArtifactTabId;
  directoryCache: Map<string, WorkspaceTreeNode[]>;
  expandedDirs: Set<string>;
  dockedFile: FileReadResult | null;
  selectedFilePath: string | null;
  diffResult: FileDiffResult | null;
  gitSnapshot: GitSnapshot | null;
  terminalRuns: TerminalPresetResult[];
  transcript: TranscriptItem[];
  timeline: TimelineEntry[];
  reviewDispatches: ReviewDispatchRecord[];
  workflowRuns: WorkflowRecord[];
  focusedReviewDispatchId: string | null;
  focusedWorkflowRunId: string | null;
  overlay: OverlayState;
};

const rootElement = document.getElementById("app");

if (!rootElement) {
  throw new Error("App root is missing.");
}

const root = rootElement;

const state: State = {
  ready: false,
  error: null,
  busy: new Set<string>(),
  hostState: null,
  apiBaseDraft: "",
  appState: null,
  sessionId: null,
  status: "idle",
  connection: "disconnected",
  writesAllowed: false,
  workerOnlyMode: false,
  lastHeartbeatAt: null,
  policyProfiles: [],
  currentPolicy: null,
  messageDraft: "",
  workflowPrompt:
    "Summarize the current ADEU Codex runtime posture, including session state, policy profile, and any active review or workflow evidence.",
  selectedTemplateId: DEFAULT_WORKFLOW_TEMPLATE_ID,
  templates: [],
  evidenceIdInput: "",
  loadedEvidence: null,
  compiledPlan: null,
  activeArtifact: "review",
  directoryCache: new Map<string, WorkspaceTreeNode[]>(),
  expandedDirs: new Set<string>([""]),
  dockedFile: null,
  selectedFilePath: null,
  diffResult: null,
  gitSnapshot: null,
  terminalRuns: [],
  transcript: [],
  timeline: [],
  reviewDispatches: [],
  workflowRuns: [],
  focusedReviewDispatchId: null,
  focusedWorkflowRunId: null,
  overlay: { kind: "none" },
};

function requestId(): string {
  return typeof crypto !== "undefined" && "randomUUID" in crypto
    ? crypto.randomUUID()
    : `${Date.now()}-${Math.random().toString(16).slice(2)}`;
}

function escapeHtml(value: string): string {
  return value
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

function prettyTime(value: string | null): string {
  if (!value) return "n/a";
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return value;
  return date.toLocaleString();
}

function prettyJson(value: unknown): string {
  try {
    return JSON.stringify(value, null, 2);
  } catch {
    return String(value);
  }
}

function truncateText(value: string, max = 180): string {
  return value.length > max ? `${value.slice(0, max - 1)}…` : value;
}

function describeError(error: unknown): string {
  if (error instanceof Error) return error.message;
  if (typeof error === "string") return error;
  try {
    return JSON.stringify(error);
  } catch {
    return String(error);
  }
}

function selectedLaunchProfile(): LaunchProfile {
  const selectedId = state.hostState?.selectedLaunchProfileId;
  return (
    DEFAULT_LAUNCH_PROFILES.find((profile) => profile.id === selectedId) ??
    DEFAULT_LAUNCH_PROFILES[0]
  );
}

function targetLabel(targetId: string): string {
  return REVIEW_TARGETS.find((target) => target.id === targetId)?.label ?? targetId;
}

function bindingModeLabel(mode: ReviewTargetBindingMode): string {
  return mode === "backend_routed" ? "backend routed" : "prompt guidance only";
}

function statusTagClass(status: string): string {
  const normalized = status.toLowerCase();
  if (
    normalized.includes("fail") ||
    normalized.includes("error") ||
    normalized.includes("unavailable")
  ) {
    return "tagWarning";
  }
  if (
    normalized.includes("done") ||
    normalized.includes("complete") ||
    normalized.includes("success")
  ) {
    return "tagSuccess";
  }
  if (normalized.includes("running") || normalized.includes("pending") || normalized.includes("queued")) {
    return "tagAdvisory";
  }
  return "tagObserved";
}

function reviewDispatchesForOrigin(
  originKind: ReviewOriginKind,
  originRef: string,
): ReviewDispatchRecord[] {
  return state.reviewDispatches.filter(
    (record) => record.originKind === originKind && record.originRef === originRef,
  );
}

function renderOriginRequestMarkers(
  originKind: ReviewOriginKind,
  originRef: string,
  emptyLabel?: string,
): string {
  const records = reviewDispatchesForOrigin(originKind, originRef);
  if (records.length === 0) {
    return emptyLabel
      ? `<div class="inlineRequestBlock"><div class="recordSummary">${escapeHtml(emptyLabel)}</div></div>`
      : "";
  }
  return `
    <div class="inlineRequestBlock">
      <div class="recordSummary">Linked review requests remain same-context reachable from this origin.</div>
      <div class="requestMarkerList">
        ${records
          .map(
            (record) => `
              <div class="requestMarker">
                <div class="miniRow">
                  <strong class="mono">${escapeHtml(record.requestId)}</strong>
                  <span class="tag ${statusTagClass(record.status)}">${escapeHtml(record.status)}</span>
                </div>
                <div class="chipRow">
                  <span class="tag tagDeclared">${escapeHtml(targetLabel(record.targetProfileId))}</span>
                  <button class="ghostButton" data-action="focus-review-record" data-record-id="${escapeHtml(record.id)}">Open Review Dock</button>
                </div>
              </div>
            `,
          )
          .join("")}
      </div>
    </div>
  `;
}

function reviewBindingSummary(target: ReviewTargetProfile, templateId: string): string {
  return `${target.label} changes advisory prompt guidance only. Backend execution still uses adeu.run_workflow with template ${templateId}.`;
}

function addTimeline(summary: string): void {
  state.timeline = [
    {
      id: requestId(),
      at: new Date().toISOString(),
      summary,
    },
    ...state.timeline,
  ].slice(0, 48);
}

function setError(error: unknown): void {
  state.error = describeError(error);
}

function clearError(): void {
  state.error = null;
}

async function runTask<T>(key: string, task: () => Promise<T>): Promise<T | null> {
  state.busy.add(key);
  render();
  try {
    clearError();
    return await task();
  } catch (error) {
    setError(error);
    return null;
  } finally {
    state.busy.delete(key);
    render();
  }
}

function hasBusy(key?: string): boolean {
  if (!key) return state.busy.size > 0;
  return state.busy.has(key);
}

function sessionSummary(): string {
  if (!state.sessionId) return "No active session";
  return `${state.sessionId} · ${state.status}`;
}

function ensureAssistantTurn(turnId: string): TranscriptItem {
  let existing = state.transcript.find((item) => item.turnId === turnId);
  if (existing) return existing;
  existing = {
    id: requestId(),
    role: "assistant",
    text: "",
    createdAt: new Date().toISOString(),
    status: "pending",
    turnId,
  };
  state.transcript.push(existing);
  return existing;
}

function handleAgentDelta(turnId: string, delta: string): void {
  const item = ensureAssistantTurn(turnId);
  item.text += delta;
  item.status = "streaming";
}

function handleTurnCompleted(turnId: string): void {
  const item = ensureAssistantTurn(turnId);
  item.status = "complete";
}

function eventSummary(event: NormalizedEventLike): string {
  const seq = typeof event.seq === "number" ? `#${event.seq}` : "event";
  const eventKind = event.event_kind ?? "unknown";
  return `${seq} · ${eventKind}`;
}

function payloadAsObject(value: unknown): Record<string, unknown> | null {
  return typeof value === "object" && value !== null && !Array.isArray(value)
    ? (value as Record<string, unknown>)
    : null;
}

function extractTurnId(payload: unknown): string | null {
  const candidate = payloadAsObject(payload);
  if (!candidate) return null;
  const params = payloadAsObject(candidate.params);
  if (params) {
    if (typeof params.id === "string" && params.id) return params.id;
    const turn = payloadAsObject(params.turn);
    if (turn && typeof turn.id === "string" && turn.id) return turn.id;
  }
  const result = payloadAsObject(candidate.result);
  if (result) {
    const turn = payloadAsObject(result.turn);
    if (turn && typeof turn.id === "string" && turn.id) return turn.id;
  }
  return null;
}

function handleStreamEvent(eventType: string, payload: unknown): void {
  if (eventType === "stream_status") {
    const status = payloadAsObject(payload)?.status;
    state.connection =
      status === "connecting" || status === "connected" ? status : "disconnected";
    render();
    return;
  }

  if (eventType === "heartbeat") {
    const object = payloadAsObject(payload);
    state.lastHeartbeatAt =
      typeof object?.ts === "string" ? object.ts : new Date().toISOString();
    state.connection = "connected";
    render();
    return;
  }

  if (eventType === "session_status") {
    const object = payloadAsObject(payload);
    if (typeof object?.status === "string") {
      state.status = object.status as CopilotStatus;
    }
    render();
    return;
  }

  if (eventType === "stream_error") {
    state.connection = "disconnected";
    setError(payloadAsObject(payload)?.message ?? "Copilot event stream failed.");
    render();
    return;
  }

  if (eventType !== "codex_event") {
    render();
    return;
  }

  const event = payload as NormalizedEventLike;
  addTimeline(eventSummary(event));
  const providerPayload = event.payload;
  const turnId = extractTurnId(providerPayload);

  if (event.event_kind === "codex/event/agent_message_delta" && turnId) {
    const params = payloadAsObject(providerPayload)?.params as Record<string, unknown> | undefined;
    const msg = params ? payloadAsObject(params.msg) : null;
    const delta = typeof msg?.delta === "string" ? msg.delta : "";
    handleAgentDelta(turnId, delta);
  }

  if (event.event_kind === "turn/completed" && turnId) {
    handleTurnCompleted(turnId);
  }

  if (event.event_kind === "MODE_CHANGED") {
    const detail = payloadAsObject(event.detail);
    if (typeof detail?.writes_allowed === "boolean") {
      state.writesAllowed = detail.writes_allowed;
    }
  }

  if (event.event_kind === "PROFILE_SELECTED" && state.sessionId) {
    void refreshCurrentPolicy();
  }

  render();
}

async function refreshWorkspaceTree(relativePath = ""): Promise<void> {
  const nodes = await window.opusWorkbench.listDirectory(relativePath);
  state.directoryCache.set(relativePath, nodes);
}

async function loadDockedFile(relativePath: string): Promise<void> {
  const file = await window.opusWorkbench.readWorkspaceFile(relativePath);
  state.selectedFilePath = relativePath;
  state.dockedFile = file;
  state.activeArtifact = "files";
}

async function openPeekFile(relativePath: string): Promise<void> {
  const file = await window.opusWorkbench.readWorkspaceFile(relativePath);
  state.overlay = { kind: "file-peek", file };
}

async function refreshGitSnapshot(): Promise<void> {
  state.gitSnapshot = await window.opusWorkbench.getGitSnapshot();
}

async function refreshDiff(relativePath?: string | null): Promise<void> {
  state.diffResult = await window.opusWorkbench.getFileDiff(relativePath ?? null);
}

async function refreshAppState(): Promise<void> {
  const response = await window.opusWorkbench.callTool({
    toolName: "adeu.get_app_state",
    argumentsValue: {},
  });
  state.appState = response.result as AppStateSnapshot;
  if (!state.sessionId && state.appState.active_copilot_session_id) {
    state.sessionId = state.appState.active_copilot_session_id;
    state.status = "running";
    state.writesAllowed = state.appState.active_copilot_writes_allowed;
    await window.opusWorkbench.startCopilotStream(state.sessionId);
  }
}

async function refreshTemplates(): Promise<void> {
  const response = await window.opusWorkbench.callTool({
    toolName: "adeu.list_templates",
    argumentsValue: {},
  });
  const body = response.result as { templates?: TemplateMeta[] };
  state.templates = body.templates ?? [];
  if (!state.templates.some((item) => item.template_id === state.selectedTemplateId)) {
    state.selectedTemplateId =
      state.templates[0]?.template_id ?? DEFAULT_WORKFLOW_TEMPLATE_ID;
  }
}

async function refreshPolicyProfiles(): Promise<void> {
  const response = await window.opusWorkbench.listPolicyProfiles();
  state.policyProfiles = response.profiles;
}

async function refreshCurrentPolicy(): Promise<void> {
  if (!state.sessionId) {
    state.currentPolicy = null;
    return;
  }
  state.currentPolicy = await window.opusWorkbench.getCurrentPolicyProfile(state.sessionId);
}

async function loadEvidence(evidenceId?: string): Promise<void> {
  const target = (evidenceId ?? state.evidenceIdInput).trim();
  if (!target) return;
  const response = await window.opusWorkbench.callTool({
    sessionId: state.sessionId,
    toolName: "adeu.read_evidence",
    argumentsValue: {
      evidence_id: target,
      max_bytes: 200_000,
    },
  });
  state.loadedEvidence = response.result as EvidenceBundle;
  state.evidenceIdInput = target;
  state.reviewDispatches.forEach((record) => {
    if (record.evidenceId === target) {
      record.evidenceLoadError = undefined;
    }
  });
  state.workflowRuns.forEach((record) => {
    if (record.evidenceId === target) {
      record.evidenceLoadError = undefined;
    }
  });
}

type WorkflowRunResult = {
  evidence_id?: string;
  worker_id?: string;
  status?: string;
  status_reason?: string;
  template_id?: string;
};

function extractStatusDetail(result: WorkflowRunResult): string | undefined {
  return typeof result.status_reason === "string" && result.status_reason.trim()
    ? result.status_reason
    : undefined;
}

function appendStatusDetail(current: string | undefined, addition: string): string {
  return current ? `${current} ${addition}` : addition;
}

async function loadEvidenceAfterDispatch(
  record: WorkflowRecord | ReviewDispatchRecord,
  issueSummary: string,
): Promise<void> {
  if (!record.evidenceId) return;
  state.evidenceIdInput = record.evidenceId;
  try {
    await loadEvidence(record.evidenceId);
    record.evidenceLoadError = undefined;
  } catch (error) {
    record.evidenceLoadError = `Automatic evidence load failed for ${record.evidenceId}: ${describeError(error)}`;
    record.statusDetail = appendStatusDetail(
      record.statusDetail,
      `Dispatch completed, but evidence ${record.evidenceId} could not be loaded automatically.`,
    );
    addTimeline(issueSummary);
    throw error;
  }
}

function createWorkflowRecord(prompt: string, templateId: string, summary: string): WorkflowRecord {
  return {
    id: requestId(),
    createdAt: new Date().toISOString(),
    prompt,
    templateId,
    requestId: requestId(),
    status: "pending",
    statusDetail: summary,
  };
}

function createReviewDispatchRecord(
  origin: ReviewOrigin,
  target: ReviewTargetProfile,
  templateId: string,
): ReviewDispatchRecord {
  return {
    id: requestId(),
    createdAt: new Date().toISOString(),
    originKind: origin.kind,
    originRef: origin.ref,
    targetProfileId: target.id,
    executionToolName: "adeu.run_workflow",
    executionTemplateId: templateId,
    targetBindingMode: "prompt_guidance_only",
    targetBindingSummary: reviewBindingSummary(target, templateId),
    requestId: requestId(),
    status: "pending",
    statusDetail: `Review handoff requested from ${origin.provenance}.`,
    summary: origin.title,
  };
}

async function runWorkflow(prompt: string, summary: string): Promise<void> {
  const record = createWorkflowRecord(prompt, state.selectedTemplateId, summary);
  state.workflowRuns.unshift(record);
  state.workflowRuns = state.workflowRuns.slice(0, 10);
  state.activeArtifact = "workflow";
  state.focusedWorkflowRunId = record.id;
  render();
  try {
    const response = await window.opusWorkbench.callTool({
      sessionId: state.sessionId,
      toolName: "adeu.run_workflow",
      argumentsValue: {
        template_id: state.selectedTemplateId,
        inputs: { prompt },
        mode: "read_only",
        client_request_id: record.requestId,
        cwd: state.hostState?.workspaceRoot,
      },
    });
    const result = response.result as WorkflowRunResult;
    record.templateId = result.template_id ?? state.selectedTemplateId;
    record.status = result.status ?? "unknown";
    record.statusDetail =
      extractStatusDetail(result) ??
      `Workflow executed through adeu.run_workflow using template ${record.templateId}.`;
    record.evidenceId = result.evidence_id;
    record.workerId = result.worker_id;
    addTimeline(summary);
  } catch (error) {
    record.status = "failed";
    record.failureReason = describeError(error);
    record.statusDetail = `Workflow handoff failed before evidence creation.`;
    addTimeline(`Workflow dispatch failed for template ${record.templateId}.`);
    throw error;
  }
  await loadEvidenceAfterDispatch(
    record,
    `Workflow dispatch succeeded, but automatic evidence load failed for ${record.evidenceId}.`,
  );
}

async function compileReflexivePlan(): Promise<void> {
  const response = await window.opusWorkbench.callTool({
    sessionId: state.sessionId,
    toolName: "adeu.compile_brokered_reflexive_execution",
    argumentsValue: DEFAULT_REFLEXIVE_PAYLOAD,
  });
  state.compiledPlan = response.result;
  state.activeArtifact = "workflow";
  addTimeline("Compiled brokered reflexive execution plan.");
}

async function sendReviewDispatch(origin: ReviewOrigin, target: ReviewTargetProfile): Promise<void> {
  const prompt = [
    target.promptPreamble,
    "",
    `Origin kind: ${origin.kind}`,
    `Origin ref: ${origin.ref}`,
    `Provenance: ${origin.provenance}`,
    "",
    "Artifact payload follows.",
    origin.content,
  ].join("\n");
  const record = createReviewDispatchRecord(origin, target, state.selectedTemplateId);
  state.reviewDispatches.unshift(record);
  state.reviewDispatches = state.reviewDispatches.slice(0, 12);
  state.overlay = { kind: "none" };
  state.activeArtifact = "review";
  state.focusedReviewDispatchId = record.id;
  render();
  try {
    const response = await window.opusWorkbench.callTool({
      sessionId: state.sessionId,
      toolName: "adeu.run_workflow",
      argumentsValue: {
        template_id: state.selectedTemplateId,
        inputs: { prompt },
        mode: "read_only",
        client_request_id: record.requestId,
        cwd: state.hostState?.workspaceRoot,
      },
    });
    const result = response.result as WorkflowRunResult;
    record.executionTemplateId = result.template_id ?? state.selectedTemplateId;
    record.targetBindingSummary = reviewBindingSummary(
      target,
      record.executionTemplateId ?? state.selectedTemplateId,
    );
    record.status = result.status ?? "unknown";
    record.statusDetail =
      extractStatusDetail(result) ??
      `Executed through ${record.executionToolName} using template ${record.executionTemplateId ?? "unknown"}.`;
    record.evidenceId = result.evidence_id;
    record.workerId = result.worker_id;
    addTimeline(`Dispatched ${origin.kind} for advisory review via ${target.label}.`);
  } catch (error) {
    record.status = "failed";
    record.failureReason = describeError(error);
    record.statusDetail = `Review handoff failed before evidence creation.`;
    addTimeline(`Review dispatch failed for ${origin.kind} via ${target.label}.`);
    throw error;
  }
  await loadEvidenceAfterDispatch(
    record,
    `Review dispatch succeeded, but automatic evidence load failed for ${record.evidenceId}.`,
  );
}

function transcriptById(itemId: string): TranscriptItem | null {
  return state.transcript.find((item) => item.id === itemId) ?? null;
}

function buildReviewOrigin(kind: ReviewOriginKind, ref: string): ReviewOrigin | null {
  if (kind === "reply") {
    const item = transcriptById(ref);
    if (!item) return null;
    return {
      kind,
      ref,
      title: `${item.role} message`,
      content: item.text,
      provenance: `transcript item ${item.id} @ ${prettyTime(item.createdAt)}`,
    };
  }
  if (kind === "file") {
    const file = state.dockedFile && state.dockedFile.relativePath === ref ? state.dockedFile : null;
    const content = file?.content ?? "";
    return {
      kind,
      ref,
      title: ref,
      content,
      provenance: `workspace file ${ref}`,
    };
  }
  if (kind === "diff") {
    return {
      kind,
      ref,
      title: ref || "workspace diff",
      content: state.diffResult?.diffText ?? "",
      provenance: ref ? `git diff for ${ref}` : "workspace git diff",
    };
  }
  if (kind === "workflow") {
    const record = state.workflowRuns.find((item) => item.id === ref);
    if (!record) return null;
    const executionSummary = [
      `Workflow request id: ${record.requestId}`,
      `Template: ${record.templateId}`,
      `Status: ${record.status}`,
      record.statusDetail ? `Status detail: ${record.statusDetail}` : "",
      "",
      record.prompt,
    ]
      .filter(Boolean)
      .join("\n");
    return {
      kind,
      ref,
      title: `workflow ${record.templateId}`,
      content: executionSummary,
      provenance: `workflow record ${record.id}`,
    };
  }
  return null;
}

function openReviewPicker(origin: ReviewOrigin | null): void {
  if (!origin) return;
  state.overlay = {
    kind: "review-picker",
    origin,
    selectedTargetId: REVIEW_TARGETS[0].id,
  };
}

async function bootstrap(): Promise<void> {
  const unsubscribe = window.opusWorkbench.onCopilotEvent((event) => {
    if (state.sessionId && event.sessionId !== state.sessionId && event.sessionId !== "host") {
      return;
    }
    if (event.eventType === "workspace_changed") {
      void refreshWorkspaceAfterChange();
      return;
    }
    handleStreamEvent(event.eventType, event.payload);
  });
  void unsubscribe;

  await runTask("bootstrap", async () => {
    state.hostState = await window.opusWorkbench.getHostState();
    state.apiBaseDraft = state.hostState.apiBaseUrl;
    await Promise.all([
      refreshWorkspaceTree(""),
      refreshGitSnapshot(),
      refreshPolicyProfiles(),
      refreshAppState(),
      refreshTemplates(),
    ]);
    if (state.sessionId) {
      await refreshCurrentPolicy();
    }
    state.ready = true;
  });
}

async function refreshWorkspaceAfterChange(): Promise<void> {
  await runTask("workspace-refresh", async () => {
    state.hostState = await window.opusWorkbench.getHostState();
    state.directoryCache = new Map<string, WorkspaceTreeNode[]>();
    state.expandedDirs = new Set<string>([""]);
    state.dockedFile = null;
    state.selectedFilePath = null;
    await Promise.all([refreshWorkspaceTree(""), refreshGitSnapshot(), refreshDiff(null)]);
  });
}

async function startSessionFromProfile(restart = false): Promise<void> {
  await runTask(restart ? "restart-session" : "start-session", async () => {
    if (restart && state.sessionId) {
      await window.opusWorkbench.stopSession(state.sessionId);
      state.sessionId = null;
      state.status = "idle";
      state.connection = "disconnected";
    }
    const response = await window.opusWorkbench.startSession();
    await applyStartedSession(response);
  });
}

async function applyStartedSession(response: CopilotSessionResponse): Promise<void> {
  state.sessionId = response.session_id;
  state.status = response.status;
  state.workerOnlyMode = response.app_server_unavailable;
  state.writesAllowed = false;
  await window.opusWorkbench.startCopilotStream(response.session_id);
  const desiredPolicy = selectedLaunchProfile().desiredPolicyProfileId;
  if (desiredPolicy && desiredPolicy !== "default") {
    await window.opusWorkbench.selectPolicyProfile(response.session_id, desiredPolicy);
  }
  await Promise.all([refreshAppState(), refreshCurrentPolicy()]);
  addTimeline(`Started session ${response.session_id}.`);
}

async function stopSession(): Promise<void> {
  if (!state.sessionId) return;
  await runTask("stop-session", async () => {
    const response = await window.opusWorkbench.stopSession(state.sessionId!);
    state.status = response.status;
    state.connection = "disconnected";
    addTimeline(`Stopped session ${response.session_id}.`);
  });
}

async function toggleWrites(): Promise<void> {
  if (!state.sessionId) return;
  await runTask("toggle-writes", async () => {
    const response = await window.opusWorkbench.setWrites(state.sessionId!, !state.writesAllowed);
    state.status = response.status;
    state.writesAllowed = !state.writesAllowed;
    await refreshAppState();
    addTimeline(`writes_allowed set to ${String(state.writesAllowed)}.`);
  });
}

async function sendMessage(): Promise<void> {
  const text = state.messageDraft.trim();
  if (!state.sessionId || !text) return;
  await runTask("send-message", async () => {
    state.transcript.push({
      id: requestId(),
      role: "user",
      text,
      createdAt: new Date().toISOString(),
      status: "complete",
    });
    await window.opusWorkbench.sendMessage(state.sessionId!, text);
    state.messageDraft = "";
    addTimeline(`Sent user message (${text.length} chars).`);
  });
}

async function resendMessage(itemId: string): Promise<void> {
  const item = transcriptById(itemId);
  if (!item) return;
  state.messageDraft = item.text;
  render();
}

async function copyText(text: string): Promise<void> {
  try {
    await navigator.clipboard.writeText(text);
    addTimeline("Copied content to clipboard.");
    render();
  } catch (error) {
    setError(error);
    render();
  }
}

async function handleAction(action: string, dataset: DOMStringMap): Promise<void> {
  if (action === "choose-workspace") {
    await runTask("choose-workspace", async () => {
      const nextRoot = await window.opusWorkbench.chooseWorkspaceRoot();
      if (!nextRoot) return;
      await refreshWorkspaceAfterChange();
    });
    return;
  }

  if (action === "save-api-base") {
    await runTask("save-api-base", async () => {
      if (!state.hostState) return;
      state.hostState = await window.opusWorkbench.updateHostState({
        apiBaseUrl: state.apiBaseDraft.trim(),
      });
      if (state.sessionId) {
        await window.opusWorkbench.stopCopilotStream(state.sessionId);
        await window.opusWorkbench.startCopilotStream(state.sessionId);
      }
      await Promise.allSettled([refreshAppState(), refreshTemplates(), refreshPolicyProfiles()]);
    });
    return;
  }

  if (action === "apply-launch-profile") {
    await runTask("apply-launch-profile", async () => {
      if (!state.hostState) return;
      state.hostState = await window.opusWorkbench.updateHostState({
        selectedLaunchProfileId: state.hostState.selectedLaunchProfileId,
      });
      await refreshCurrentPolicy();
    });
    return;
  }

  if (action === "start-session") {
    await startSessionFromProfile(false);
    return;
  }

  if (action === "restart-session") {
    await startSessionFromProfile(true);
    return;
  }

  if (action === "stop-session") {
    await stopSession();
    return;
  }

  if (action === "toggle-writes") {
    await toggleWrites();
    return;
  }

  if (action === "refresh-runtime") {
    await runTask("refresh-runtime", async () => {
      await Promise.allSettled([
        refreshAppState(),
        refreshTemplates(),
        refreshGitSnapshot(),
        state.sessionId ? refreshCurrentPolicy() : Promise.resolve(),
      ]);
    });
    return;
  }

  if (action === "send-message") {
    await sendMessage();
    return;
  }

  if (action === "toggle-dir") {
    const relativePath = dataset.path ?? "";
    if (state.expandedDirs.has(relativePath)) {
      state.expandedDirs.delete(relativePath);
      render();
      return;
    }
    await runTask(`dir:${relativePath}`, async () => {
      state.expandedDirs.add(relativePath);
      if (!state.directoryCache.has(relativePath)) {
        await refreshWorkspaceTree(relativePath);
      }
    });
    return;
  }

  if (action === "open-file") {
    const relativePath = dataset.path;
    if (!relativePath) return;
    await runTask(`file:${relativePath}`, async () => {
      await loadDockedFile(relativePath);
      await refreshDiff(relativePath);
    });
    return;
  }

  if (action === "peek-file") {
    const relativePath = dataset.path;
    if (!relativePath) return;
    await runTask(`peek:${relativePath}`, async () => {
      await openPeekFile(relativePath);
    });
    return;
  }

  if (action === "open-diff") {
    const relativePath = dataset.path ?? state.selectedFilePath;
    await runTask("diff", async () => {
      state.activeArtifact = "diff";
      await refreshDiff(relativePath);
    });
    return;
  }

  if (action === "open-artifact") {
    const tab = dataset.tab as ArtifactTabId | undefined;
    if (!tab) return;
    state.activeArtifact = tab;
    if (tab === "git") {
      await runTask("git", refreshGitSnapshot);
      return;
    }
    if (tab === "diff") {
      await runTask("diff", async () => refreshDiff(state.selectedFilePath));
      return;
    }
    render();
    return;
  }

  if (action === "focus-review-record") {
    if (!dataset.recordId) return;
    state.activeArtifact = "review";
    state.focusedReviewDispatchId = dataset.recordId;
    render();
    return;
  }

  if (action === "focus-workflow-record") {
    if (!dataset.recordId) return;
    state.activeArtifact = "workflow";
    state.focusedWorkflowRunId = dataset.recordId;
    render();
    return;
  }

  if (action === "run-terminal-preset") {
    const preset = dataset.preset as TerminalPresetId | undefined;
    if (!preset) return;
    await runTask(`terminal:${preset}`, async () => {
      const result = await window.opusWorkbench.runTerminalPreset(preset);
      state.terminalRuns.unshift(result);
      state.terminalRuns = state.terminalRuns.slice(0, 10);
      state.activeArtifact = "terminal";
    });
    return;
  }

  if (action === "run-workflow") {
    const prompt = state.workflowPrompt.trim();
    if (!prompt) return;
    await runTask("workflow", async () => {
      await runWorkflow(prompt, "Ran ADEU workflow.");
    });
    return;
  }

  if (action === "compile-plan") {
    await runTask("compile-plan", async () => {
      await compileReflexivePlan();
    });
    return;
  }

  if (action === "load-evidence") {
    await runTask("load-evidence", async () => {
      await loadEvidence();
    });
    return;
  }

  if (action === "copy-item") {
    const item = transcriptById(dataset.itemId ?? "");
    if (!item) return;
    await copyText(item.text);
    return;
  }

  if (action === "resend-item") {
    await resendMessage(dataset.itemId ?? "");
    return;
  }

  if (action === "review-item") {
    openReviewPicker(buildReviewOrigin("reply", dataset.itemId ?? ""));
    render();
    return;
  }

  if (action === "review-file") {
    openReviewPicker(buildReviewOrigin("file", dataset.path ?? ""));
    render();
    return;
  }

  if (action === "review-diff") {
    openReviewPicker(buildReviewOrigin("diff", dataset.path ?? state.selectedFilePath ?? ""));
    render();
    return;
  }

  if (action === "review-workflow-record") {
    openReviewPicker(buildReviewOrigin("workflow", dataset.recordId ?? ""));
    render();
    return;
  }

  if (action === "open-evidence") {
    if (!dataset.evidenceId) return;
    await runTask("open-evidence", async () => {
      await loadEvidence(dataset.evidenceId);
    });
    return;
  }

  if (action === "select-policy-profile") {
    if (!state.sessionId || !dataset.profileId) return;
    await runTask("select-policy", async () => {
      state.currentPolicy = await window.opusWorkbench.selectPolicyProfile(
        state.sessionId!,
        dataset.profileId!,
      );
      addTimeline(`Selected policy profile ${dataset.profileId}.`);
    });
    return;
  }

  if (action === "close-overlay") {
    state.overlay = { kind: "none" };
    render();
    return;
  }

  if (action === "confirm-review-dispatch") {
    if (state.overlay.kind !== "review-picker") return;
    const overlay = state.overlay;
    const target = REVIEW_TARGETS.find(
      (item) => item.id === overlay.selectedTargetId,
    );
    if (!target) return;
    await runTask("review-dispatch", async () => {
      await sendReviewDispatch(overlay.origin, target);
    });
    return;
  }
}

function renderTree(relativePath = "", depth = 0): string {
  const nodes = state.directoryCache.get(relativePath) ?? [];
  return nodes
    .map((node) => {
      const expanded = state.expandedDirs.has(node.relativePath);
      const children =
        node.kind === "dir" && expanded
          ? `<div class="treeIndent">${renderTree(node.relativePath, depth + 1)}</div>`
          : "";
      const icon = node.kind === "dir" ? (expanded ? "▾" : "▸") : "·";
      const actions =
        node.kind === "file"
          ? `
            <div class="treeActions">
              <button class="ghostButton" data-action="peek-file" data-path="${escapeHtml(node.relativePath)}">Peek</button>
              <button class="softButton" data-action="open-file" data-path="${escapeHtml(node.relativePath)}">Dock</button>
              <button class="ghostButton" data-action="review-file" data-path="${escapeHtml(node.relativePath)}">Review</button>
            </div>
          `
          : "";
      return `
        <div class="treeNode" data-kind="${node.kind}" data-path="${escapeHtml(node.relativePath)}" style="margin-left:${depth * 10}px">
          <div class="treeNodeRow">
            <div class="treeNodeMain">
              ${
                node.kind === "dir"
                  ? `<button class="ghostButton" data-action="toggle-dir" data-path="${escapeHtml(node.relativePath)}">${icon}</button>`
                  : `<span class="mono">${icon}</span>`
              }
              <div class="treeNodeName">${escapeHtml(node.name)}</div>
            </div>
            ${actions}
          </div>
          ${children}
        </div>
      `;
    })
    .join("");
}

function renderRecentSessions(): string {
  const recent = state.hostState?.recentSessions ?? [];
  if (recent.length === 0) {
    return `<div class="emptyState">No local session history yet.</div>`;
  }
  return recent
    .map((session) => {
      const profile = DEFAULT_LAUNCH_PROFILES.find(
        (item) => item.id === session.launchProfileId,
      );
      return `
        <div class="recordCard">
          <div class="miniRow">
            <strong class="mono">${escapeHtml(session.sessionId)}</strong>
            <span class="tag tagDeclared">${escapeHtml(profile?.label ?? session.launchProfileId)}</span>
          </div>
          <div class="recordSummary">${escapeHtml(prettyTime(session.startedAt))}</div>
        </div>
      `;
    })
    .join("");
}

function renderTranscript(): string {
  if (state.transcript.length === 0) {
    return `
      <div class="emptyState">
        Transcript is empty. Start a session or reconnect to an active session to make the chat lane authoritative for this workbench.
      </div>
    `;
  }
  return state.transcript
    .map((item) => {
      const bubbleClass =
        item.role === "user" ? "bubble bubbleUser" : "bubble bubbleAssistant";
      const reviewMarkers = renderOriginRequestMarkers("reply", item.id);
      return `
        <article class="${bubbleClass}" data-item-id="${escapeHtml(item.id)}">
          <div class="bubbleHeader">
            <div class="bubbleTitle">
              <strong>${item.role === "user" ? "Operator" : "Codex"}</strong>
              <span class="bubbleMeta">${escapeHtml(prettyTime(item.createdAt))}</span>
            </div>
            <div class="recordActions">
              <button class="ghostButton" data-action="copy-item" data-item-id="${escapeHtml(item.id)}">Copy</button>
              <button class="ghostButton" data-action="resend-item" data-item-id="${escapeHtml(item.id)}">Resend</button>
              <button class="softButton" data-action="review-item" data-item-id="${escapeHtml(item.id)}">Send For Review</button>
            </div>
          </div>
          <div class="bubbleBody">${escapeHtml(item.text || (item.status === "pending" ? "Waiting for assistant response…" : ""))}</div>
          <div class="chipRow">
            <span class="tag ${item.role === "assistant" ? "tagObserved" : "tagDeclared"}">${escapeHtml(item.role)}</span>
            <span class="tag ${item.status === "complete" ? "tagSuccess" : "tagAdvisory"}">${escapeHtml(item.status)}</span>
            ${item.turnId ? `<span class="tag tagObserved">${escapeHtml(item.turnId)}</span>` : ""}
          </div>
          ${reviewMarkers}
        </article>
      `;
    })
    .join("");
}

function renderEvidence(): string {
  if (!state.loadedEvidence) {
    return `<div class="emptyState">No evidence loaded.</div>`;
  }
  return `
    <div class="recordCard">
      <div class="miniRow">
        <strong class="mono">${escapeHtml(state.loadedEvidence.evidence_id)}</strong>
        <span class="tag tagObserved">${escapeHtml(state.loadedEvidence.status)}</span>
      </div>
      <div class="recordSummary">
        source=${escapeHtml(state.loadedEvidence.source)} · role=${escapeHtml(state.loadedEvidence.role)}
      </div>
      <pre class="preBlock">${escapeHtml(state.loadedEvidence.raw_jsonl ?? "Evidence payload is unavailable.")}</pre>
    </div>
  `;
}

function renderReviewRecords(): string {
  if (state.reviewDispatches.length === 0) {
    return `<div class="emptyState">No review dispatches yet. Use a transcript reply, file, diff, or workflow record to open the review picker.</div>`;
  }
  return state.reviewDispatches
    .map((record) => {
      const focusedClass =
        record.id === state.focusedReviewDispatchId ? " recordCardFocused" : "";
      return `
        <div class="recordCard${focusedClass}">
          <div class="miniRow">
            <strong>${escapeHtml(targetLabel(record.targetProfileId))}</strong>
            <span class="tag ${statusTagClass(record.status)}">${escapeHtml(record.status)}</span>
          </div>
          <div class="recordSummary">
            ${escapeHtml(record.summary)} · ${escapeHtml(record.originKind)} · ${escapeHtml(prettyTime(record.createdAt))}
          </div>
          <div class="chipRow">
            <span class="tag tagDeclared">${escapeHtml(record.originRef)}</span>
            <span class="tag tagObserved">${escapeHtml(record.requestId)}</span>
            <span class="tag tagDeclared">${escapeHtml(bindingModeLabel(record.targetBindingMode))}</span>
            ${
              record.executionTemplateId
                ? `<span class="tag tagObserved">${escapeHtml(record.executionTemplateId)}</span>`
                : ""
            }
          </div>
          <div class="recordSummary">${escapeHtml(record.targetBindingSummary)}</div>
          ${
            record.statusDetail
              ? `<div class="recordSummary">${escapeHtml(record.statusDetail)}</div>`
              : ""
          }
          ${
            record.failureReason
              ? `<div class="errorBanner">${escapeHtml(record.failureReason)}</div>`
              : ""
          }
          ${
            record.evidenceLoadError
              ? `<div class="errorBanner">${escapeHtml(record.evidenceLoadError)}</div>`
              : ""
          }
          <div class="recordActions">
            <button class="ghostButton" data-action="focus-review-record" data-record-id="${escapeHtml(record.id)}">Focus</button>
            ${
              record.evidenceId
                ? `<button class="softButton" data-action="open-evidence" data-evidence-id="${escapeHtml(record.evidenceId)}">Load Evidence</button>`
                : ""
            }
          </div>
        </div>
      `;
    })
    .join("");
}

function renderWorkflowRecords(): string {
  if (state.workflowRuns.length === 0) {
    return `<div class="emptyState">No workflow runs yet.</div>`;
  }
  return state.workflowRuns
    .map((record) => {
      const focusedClass =
        record.id === state.focusedWorkflowRunId ? " recordCardFocused" : "";
      const relatedReviewMarkers = renderOriginRequestMarkers("workflow", record.id);
      return `
        <div class="recordCard${focusedClass}">
          <div class="miniRow">
            <strong>${escapeHtml(record.templateId)}</strong>
            <span class="tag ${statusTagClass(record.status)}">${escapeHtml(record.status)}</span>
          </div>
          <div class="recordSummary">${escapeHtml(truncateText(record.prompt, 160))}</div>
          <div class="chipRow">
            <span class="tag tagDeclared">${escapeHtml(prettyTime(record.createdAt))}</span>
            <span class="tag tagObserved">${escapeHtml(record.requestId)}</span>
            ${record.workerId ? `<span class="tag tagObserved">${escapeHtml(record.workerId)}</span>` : ""}
          </div>
          ${
            record.statusDetail
              ? `<div class="recordSummary">${escapeHtml(record.statusDetail)}</div>`
              : ""
          }
          ${
            record.failureReason
              ? `<div class="errorBanner">${escapeHtml(record.failureReason)}</div>`
              : ""
          }
          ${
            record.evidenceLoadError
              ? `<div class="errorBanner">${escapeHtml(record.evidenceLoadError)}</div>`
              : ""
          }
          ${relatedReviewMarkers}
          <div class="recordActions">
            <button class="ghostButton" data-action="focus-workflow-record" data-record-id="${escapeHtml(record.id)}">Focus</button>
            ${
              record.evidenceId
                ? `<button class="softButton" data-action="open-evidence" data-evidence-id="${escapeHtml(record.evidenceId)}">Load Evidence</button>`
                : ""
            }
            <button class="ghostButton" data-action="review-workflow-record" data-record-id="${escapeHtml(record.id)}">Review</button>
          </div>
        </div>
      `;
    })
    .join("");
}

function renderTerminalRuns(): string {
  if (state.terminalRuns.length === 0) {
    return `<div class="emptyState">Read-only terminal presets have not been run yet.</div>`;
  }
  return state.terminalRuns
    .map((run) => {
      const output = [run.stdout.trim(), run.stderr.trim()].filter(Boolean).join("\n");
      return `
        <div class="terminalRun">
          <div class="miniRow">
            <strong class="mono">${escapeHtml(run.command)}</strong>
            <span class="tag ${run.exitCode === 0 ? "tagSuccess" : "tagWarning"}">exit ${run.exitCode}</span>
          </div>
          <div class="recordSummary">${escapeHtml(prettyTime(run.ranAt))}</div>
          <pre class="preBlock">${escapeHtml(output || "No terminal output.")}</pre>
        </div>
      `;
    })
    .join("");
}

function renderArtifactContent(): string {
  if (state.activeArtifact === "files") {
    if (!state.dockedFile) {
      return `<div class="emptyState">Select a workspace file to dock it here. File peeks stay overlay-bounded and leave the transcript visible.</div>`;
    }
    const reviewMarkers = renderOriginRequestMarkers(
      "file",
      state.dockedFile.relativePath,
      "No review handoffs recorded for this docked file yet.",
    );
    return `
      <div class="artifactPanel">
        <div class="artifactHeader">
          <div>
            <p class="sectionEyebrow">Docked Reader</p>
            <h3 class="artifactTitle">${escapeHtml(state.dockedFile.relativePath)}</h3>
          </div>
          <div class="recordActions">
            <button class="ghostButton" data-action="peek-file" data-path="${escapeHtml(state.dockedFile.relativePath)}">Peek</button>
            <button class="softButton" data-action="review-file" data-path="${escapeHtml(state.dockedFile.relativePath)}">Send For Review</button>
          </div>
        </div>
        <div class="chipRow">
          <span class="tag tagDeclared">${state.dockedFile.truncated ? "truncated" : "full"}</span>
          <span class="tag tagObserved">${state.dockedFile.approxLineCount} lines</span>
        </div>
        ${reviewMarkers}
        <pre class="preBlock">${escapeHtml(state.dockedFile.content)}</pre>
      </div>
    `;
  }

  if (state.activeArtifact === "diff") {
    if (!state.diffResult) {
      return `<div class="emptyState">Open the diff artifact to inspect workspace or file-level changes without leaving the current transcript.</div>`;
    }
    const diffRef = state.diffResult.target ?? "";
    const reviewMarkers = renderOriginRequestMarkers(
      "diff",
      diffRef,
      "No review handoffs recorded for this diff yet.",
    );
    return `
      <div class="artifactPanel">
        <div class="artifactHeader">
          <div>
            <p class="sectionEyebrow">Diff Surface</p>
            <h3 class="artifactTitle">${escapeHtml(state.diffResult.target ?? "Workspace Diff")}</h3>
          </div>
          <button class="softButton" data-action="review-diff" data-path="${escapeHtml(state.diffResult.target ?? "")}">Send For Review</button>
        </div>
        ${reviewMarkers}
        ${
          state.diffResult.error
            ? `<div class="errorBanner">${escapeHtml(state.diffResult.error)}</div>`
            : `<pre class="preBlock">${escapeHtml(state.diffResult.diffText || "No diff output.")}</pre>`
        }
      </div>
    `;
  }

  if (state.activeArtifact === "terminal") {
    return `
      <div class="artifactPanel">
        <div class="artifactHeader">
          <div>
            <p class="sectionEyebrow">Terminal Surface</p>
            <h3 class="artifactTitle">Read-only command lane</h3>
          </div>
          <span class="tag tagDeclared">No free-form shell</span>
        </div>
        <div class="toolbarRow">
          <button class="ghostButton" data-action="run-terminal-preset" data-preset="pwd">pwd</button>
          <button class="ghostButton" data-action="run-terminal-preset" data-preset="ls">ls -la</button>
          <button class="softButton" data-action="run-terminal-preset" data-preset="git_status">git status</button>
          <button class="ghostButton" data-action="run-terminal-preset" data-preset="git_diff_stat">git diff --stat</button>
          <button class="ghostButton" data-action="run-terminal-preset" data-preset="git_log">git log</button>
        </div>
      </div>
      ${renderTerminalRuns()}
    `;
  }

  if (state.activeArtifact === "git") {
    if (!state.gitSnapshot) {
      return `<div class="emptyState">Git status is not loaded yet.</div>`;
    }
    return `
      <div class="artifactPanel">
        <div class="artifactHeader">
          <div>
            <p class="sectionEyebrow">Git Status Surface</p>
            <h3 class="artifactTitle">${escapeHtml(state.gitSnapshot.branch)}</h3>
          </div>
          <button class="ghostButton" data-action="refresh-runtime">Refresh</button>
        </div>
        ${
          state.gitSnapshot.error
            ? `<div class="errorBanner">${escapeHtml(state.gitSnapshot.error)}</div>`
            : `
              <div class="recordCard">
                <strong>Status</strong>
                <pre class="preBlock">${escapeHtml(state.gitSnapshot.shortStatus.join("\n") || "Clean working tree.")}</pre>
              </div>
              <div class="recordCard">
                <strong>Recent commits</strong>
                <pre class="preBlock">${escapeHtml(state.gitSnapshot.recentCommits.join("\n") || "No commits.")}</pre>
              </div>
              <div class="recordCard">
                <strong>Diff stat</strong>
                <pre class="preBlock">${escapeHtml(state.gitSnapshot.diffStat || "No diff stat.")}</pre>
              </div>
            `
        }
      </div>
    `;
  }

  if (state.activeArtifact === "review") {
    return `
      <div class="artifactPanel">
        <div class="artifactHeader">
          <div>
            <p class="sectionEyebrow">Review Routing Surface</p>
            <h3 class="artifactTitle">Explicit advisory dispatch</h3>
          </div>
          <span class="tag tagAdvisory">Advisory only</span>
        </div>
        <p class="subtle">
          Reviews are explicit handoffs. They do not silently inherit local authority, and returned artifacts stay same-context reachable.
        </p>
      </div>
      ${renderReviewRecords()}
      ${renderEvidence()}
    `;
  }

  return `
    <div class="artifactPanel">
      <div class="artifactHeader">
        <div>
          <p class="sectionEyebrow">Workflow Dock</p>
          <h3 class="artifactTitle">ADEU workflows and evidence</h3>
        </div>
        <span class="tag tagObserved">Repo-wired</span>
      </div>
      <div class="field">
        <label for="templateSelect">Template</label>
        <select id="templateSelect" data-bind="selectedTemplateId">
          ${state.templates
            .map(
              (template) => `
                <option value="${escapeHtml(template.template_id)}" ${
                  template.template_id === state.selectedTemplateId ? "selected" : ""
                }>
                  ${escapeHtml(template.template_id)}
                </option>
              `,
            )
            .join("")}
        </select>
      </div>
      <div class="fieldWide">
        <label for="workflowPrompt">Workflow prompt</label>
        <textarea id="workflowPrompt" data-bind="workflowPrompt">${escapeHtml(state.workflowPrompt)}</textarea>
      </div>
      <div class="toolbarRow">
        <button class="solidButton" data-action="run-workflow">Run ADEU Workflow</button>
        <button class="ghostButton" data-action="compile-plan">Compile Reflexive Plan</button>
        <button class="ghostButton" data-action="refresh-runtime">Refresh Templates</button>
      </div>
      <div class="fieldGridCompact">
        <div class="field">
          <label for="evidenceIdInput">Evidence id</label>
          <input id="evidenceIdInput" data-bind="evidenceIdInput" value="${escapeHtml(state.evidenceIdInput)}" />
        </div>
        <div class="field">
          <label>&nbsp;</label>
          <button class="softButton" data-action="load-evidence">Load Evidence</button>
        </div>
      </div>
    </div>
    ${state.compiledPlan ? `<div class="recordCard"><strong>Compiled plan</strong><pre class="preBlock">${escapeHtml(prettyJson(state.compiledPlan))}</pre></div>` : ""}
    ${renderWorkflowRecords()}
    ${renderEvidence()}
    ${
      state.timeline.length > 0
        ? `<div class="recordCard"><strong>Operational events</strong><div class="eventList">${state.timeline
            .map((entry) => `<div class="recordSummary">${escapeHtml(entry.summary)} · ${escapeHtml(prettyTime(entry.at))}</div>`)
            .join("")}</div></div>`
        : ""
    }
  `;
}

function renderOverlay(): string {
  if (state.overlay.kind === "none") return "";
  if (state.overlay.kind === "file-peek") {
    const reviewMarkers = renderOriginRequestMarkers(
      "file",
      state.overlay.file.relativePath,
      "No review handoffs recorded for this peeked file yet.",
    );
    return `
      <div class="overlay" data-action="close-overlay">
        <div class="overlayCard" onclick="event.stopPropagation()">
          <div class="overlayHead">
            <div>
              <p class="sectionEyebrow">Quick Peek</p>
              <h2>${escapeHtml(state.overlay.file.relativePath)}</h2>
            </div>
            <button class="ghostButton" data-action="close-overlay">Close</button>
          </div>
          <div class="chipRow">
            <span class="tag tagDeclared">${state.overlay.file.truncated ? "truncated" : "full"}</span>
            <span class="tag tagObserved">${state.overlay.file.approxLineCount} lines</span>
          </div>
          ${reviewMarkers}
          <pre class="preBlock">${escapeHtml(state.overlay.file.content)}</pre>
        </div>
      </div>
    `;
  }
  const overlay = state.overlay;
  const targetOptions = REVIEW_TARGETS.map(
    (target) => `
      <option value="${escapeHtml(target.id)}" ${
        target.id === overlay.selectedTargetId ? "selected" : ""
      }>
        ${escapeHtml(target.label)}
      </option>
    `,
  ).join("");
  const target = REVIEW_TARGETS.find((item) => item.id === overlay.selectedTargetId) ?? REVIEW_TARGETS[0];
  return `
    <div class="overlay" data-action="close-overlay">
      <div class="overlayCard" onclick="event.stopPropagation()">
        <div class="overlayHead">
          <div>
            <p class="sectionEyebrow">Review Dispatch</p>
            <h2>${escapeHtml(overlay.origin.title)}</h2>
          </div>
          <button class="ghostButton" data-action="close-overlay">Close</button>
        </div>
        <div class="field">
          <label for="reviewTargetSelect">Target profile</label>
          <select id="reviewTargetSelect" data-bind="overlayTargetId">${targetOptions}</select>
        </div>
        <div class="recordCard">
          <strong>${escapeHtml(target.label)}</strong>
          <div class="recordSummary">${escapeHtml(target.guidance)}</div>
        </div>
        <div class="recordCard">
          <strong>Execution truth</strong>
          <div class="recordSummary">
            ${escapeHtml(reviewBindingSummary(target, state.selectedTemplateId))}
          </div>
          <div class="chipRow">
            <span class="tag tagDeclared">${escapeHtml(bindingModeLabel("prompt_guidance_only"))}</span>
            <span class="tag tagObserved">adeu.run_workflow</span>
            <span class="tag tagObserved">${escapeHtml(state.selectedTemplateId)}</span>
          </div>
        </div>
        <div class="recordCard">
          <strong>Dispatch scope</strong>
          <div class="recordSummary">${escapeHtml(overlay.origin.provenance)}</div>
          <pre class="preBlock">${escapeHtml(overlay.origin.content)}</pre>
        </div>
        <div class="toolbarRow">
          <button class="solidButton" data-action="confirm-review-dispatch">Send For Review</button>
          <button class="ghostButton" data-action="close-overlay">Cancel</button>
        </div>
      </div>
    </div>
  `;
}

function render(): void {
  const launchProfile = selectedLaunchProfile();
  const reviewPending = state.reviewDispatches.filter((item) =>
    ["pending", "queued", "running"].includes(item.status.toLowerCase()),
  ).length;
  const workflowLatest = state.workflowRuns[0];
  const policyMismatch =
    state.currentPolicy &&
    state.currentPolicy.profile_id !== launchProfile.desiredPolicyProfileId;
  root.innerHTML = `
    <div class="shell">
      <section class="region statusBoundary">
        <div class="boundaryTitleRow">
          <div>
            <p class="boundaryEyebrow">Opus / ADEU Codex Desktop Reference</p>
            <h1 class="boundaryTitle">Transcript-first governed workbench</h1>
            <p class="boundarySubtitle">
              Chat remains primary, while status, evidence, file context, diff inspection, review dispatch, and workflow runs stay same-context reachable without route breaks.
            </p>
          </div>
          <div class="truthNotice">
            <strong>Authority posture</strong>
            <span>Observed runtime state, host-declared launch metadata, and advisory review outputs remain visually separate. This surface may express authority, but it does not mint it.</span>
          </div>
        </div>
        ${state.error ? `<div class="errorBanner">${escapeHtml(state.error)}</div>` : ""}
        <div class="statusGrid">
          <article class="statusCard">
            <div class="statusHead">
              <div>
                <p class="cardEyebrow">Session Control Surface</p>
                <h3>Session / Writes / Reachability</h3>
              </div>
              <span class="pill ${state.writesAllowed ? "pillWarning" : "pillObserved"}">${state.writesAllowed ? "writes enabled" : "read only"}</span>
            </div>
            <div class="statusGridRows">
              <div class="metaRow"><span>Session</span><span class="mono">${escapeHtml(state.sessionId ?? "none")}</span></div>
              <div class="metaRow"><span>Status</span><span class="mono">${escapeHtml(state.status)}</span></div>
              <div class="metaRow"><span>Connection</span><span class="mono">${escapeHtml(state.connection)}</span></div>
              <div class="metaRow"><span>Heartbeat</span><span class="mono">${escapeHtml(prettyTime(state.lastHeartbeatAt))}</span></div>
            </div>
            <div class="buttonRow">
              <button class="solidButton" data-action="start-session" ${hasBusy("start-session") ? "disabled" : ""}>Start</button>
              <button class="ghostButton" data-action="restart-session" ${!state.sessionId || hasBusy("restart-session") ? "disabled" : ""}>Restart</button>
              <button class="ghostButton" data-action="stop-session" ${!state.sessionId || hasBusy("stop-session") ? "disabled" : ""}>Stop</button>
              <button class="${state.writesAllowed ? "dangerButton" : "softButton"}" data-action="toggle-writes" ${!state.sessionId || hasBusy("toggle-writes") ? "disabled" : ""}>${state.writesAllowed ? "Disable Writes" : "Enable Writes"}</button>
            </div>
          </article>

          <article class="statusCard">
            <div class="statusHead">
              <div>
                <p class="cardEyebrow">Harness / Config Surface</p>
                <h3>Launch profile and host declaration</h3>
              </div>
              <span class="pill pillDeclared">host declared</span>
            </div>
            <div class="statusGridRows">
              <div class="metaRow"><span>Profile</span><span class="mono">${escapeHtml(launchProfile.label)}</span></div>
              <div class="metaRow"><span>Codex binary</span><span class="mono">${escapeHtml(launchProfile.codexBinary)}</span></div>
              <div class="metaRow"><span>Config path</span><span class="mono">${escapeHtml(launchProfile.configPath)}</span></div>
              <div class="metaRow"><span>Desired policy</span><span class="mono">${escapeHtml(launchProfile.desiredPolicyProfileId)}</span></div>
            </div>
            ${policyMismatch ? `<div class="errorBanner">Desired launch policy and active session policy diverge. The session remains authoritative for current policy truth.</div>` : ""}
          </article>

          <article class="statusCard">
            <div class="statusHead">
              <div>
                <p class="cardEyebrow">Observed Runtime Surface</p>
                <h3>Provider / Build / App Server</h3>
              </div>
              <span class="pill pillObserved">observed</span>
            </div>
            <div class="statusGridRows">
              <div class="metaRow"><span>Provider</span><span class="mono">codex</span></div>
              <div class="metaRow"><span>Codex version</span><span class="mono">${escapeHtml(state.appState?.codex_version ?? "unknown")}</span></div>
              <div class="metaRow"><span>Exec available</span><span class="mono">${escapeHtml(String(state.appState?.codex_exec_available ?? "unknown"))}</span></div>
              <div class="metaRow"><span>App server</span><span class="mono">${escapeHtml(String(state.appState?.codex_app_server_available ?? "unknown"))}</span></div>
            </div>
            ${state.workerOnlyMode ? `<div class="errorBanner">Worker-only mode: the connected Codex install reported app-server unavailability.</div>` : ""}
          </article>

          <article class="statusCard">
            <div class="statusHead">
              <div>
                <p class="cardEyebrow">Dispatch State Surfaces</p>
                <h3>Review / Workflow / Evidence</h3>
              </div>
              <span class="pill ${reviewPending > 0 ? "pillWarning" : "pillAdvisory"}">${reviewPending > 0 ? "handoff active" : "advisory calm"}</span>
            </div>
            <div class="statusGridRows">
              <div class="metaRow"><span>Review requests</span><span class="mono">${state.reviewDispatches.length}</span></div>
              <div class="metaRow"><span>Workflow runs</span><span class="mono">${state.workflowRuns.length}</span></div>
              <div class="metaRow"><span>Loaded evidence</span><span class="mono">${escapeHtml(state.loadedEvidence?.evidence_id ?? "none")}</span></div>
              <div class="metaRow"><span>Latest workflow</span><span class="mono">${escapeHtml(workflowLatest?.status ?? "none")}</span></div>
            </div>
          </article>
        </div>
      </section>

      <section class="mainGrid">
        <aside class="region workspaceRegion">
          <div class="laneStack">
            <section class="laneCard">
              <div class="laneHeader">
                <div>
                  <p class="laneEyebrow">Workspace Lane</p>
                  <h3 class="laneTitle">Project root and launch profile</h3>
                  <p>Bounded host settings stay explicit and are separate from observed runtime state.</p>
                </div>
                ${hasBusy() ? `<div class="spinner">working</div>` : ""}
              </div>
              <div class="workspaceSummary">
                <div class="fieldWide">
                  <label for="apiBaseInput">ADEU API base</label>
                  <input id="apiBaseInput" data-bind="apiBaseDraft" value="${escapeHtml(state.apiBaseDraft)}" />
                </div>
                <div class="buttonRow">
                  <button class="ghostButton" data-action="save-api-base">Save API Base</button>
                  <button class="ghostButton" data-action="refresh-runtime">Refresh Runtime</button>
                </div>
                <div class="field">
                  <label for="launchProfileSelect">Launch profile</label>
                  <select id="launchProfileSelect" data-bind="selectedLaunchProfileId">
                    ${DEFAULT_LAUNCH_PROFILES.map((profile) => `<option value="${escapeHtml(profile.id)}" ${profile.id === launchProfile.id ? "selected" : ""}>${escapeHtml(profile.label)}</option>`).join("")}
                  </select>
                </div>
                <div class="buttonRow">
                  <button class="ghostButton" data-action="apply-launch-profile">Save Profile</button>
                  <button class="softButton" data-action="restart-session" ${hasBusy("restart-session") ? "disabled" : ""}>Restart With Profile</button>
                </div>
                <p class="subtle">${escapeHtml(launchProfile.notes)}</p>
              </div>
            </section>

            <section class="laneCard">
              <div class="laneHeader">
                <div>
                  <p class="laneEyebrow">Recent Sessions</p>
                  <h3 class="laneTitle">Recent chats</h3>
                  <p>${escapeHtml(sessionSummary())}</p>
                </div>
              </div>
              <div class="scrollRegion">${renderRecentSessions()}</div>
            </section>

            <section class="laneCard">
              <div class="laneHeader">
                <div>
                  <p class="laneEyebrow">Workspace Selector</p>
                  <h3 class="laneTitle">${escapeHtml(state.hostState?.workspaceRoot ?? "Loading workspace…")}</h3>
                  <p>File selection does not imply edit entitlement.</p>
                </div>
                <button class="softButton" data-action="choose-workspace">Open Workspace…</button>
              </div>
            </section>

            <section class="treePanel">
              <div class="laneHeader">
                <div>
                  <p class="laneEyebrow">File Tree Surface</p>
                  <h3 class="laneTitle">Read-only project tree</h3>
                  <p>Dock files, peek them, or dispatch them for review without leaving the transcript.</p>
                </div>
              </div>
              <div class="scrollRegion">
                <div class="treeList">${renderTree("")}</div>
              </div>
            </section>
          </div>
        </aside>

        <main class="region conversationRegion">
          <div class="conversationStack">
            <section class="runtimeCard">
              <div class="sectionHeader">
                <div>
                  <p class="sectionEyebrow">Conversation Workbench</p>
                  <h2 class="sectionTitle">Transcript remains the center of gravity</h2>
                  <p>Reply review is explicit, same-context reachable, and advisory by default.</p>
                </div>
                <div class="chipRow">
                  <span class="tag tagObserved">${escapeHtml(state.connection)}</span>
                  ${state.currentPolicy ? `<span class="tag tagDeclared">${escapeHtml(state.currentPolicy.profile_id)}</span>` : ""}
                </div>
              </div>
            </section>
            <section class="transcriptPanel">
              <div class="transcriptScroller">${renderTranscript()}</div>
            </section>
            <section class="composer">
              <div class="fieldWide">
                <label for="messageDraft">Prompt entry</label>
                <textarea id="messageDraft" data-bind="messageDraft" placeholder="Send a bounded prompt into the active Codex session...">${escapeHtml(state.messageDraft)}</textarea>
              </div>
              <div class="composerFooter">
                <div class="composerActions">
                  <button class="ghostButton" data-action="open-artifact" data-tab="files">Files</button>
                  <button class="ghostButton" data-action="open-artifact" data-tab="diff">Diff</button>
                  <button class="ghostButton" data-action="open-artifact" data-tab="terminal">Terminal</button>
                  <button class="ghostButton" data-action="open-artifact" data-tab="git">Git</button>
                  <button class="softButton" data-action="open-artifact" data-tab="workflow">Workflow</button>
                  <button class="softButton" data-action="open-artifact" data-tab="review">Review Inbox</button>
                </div>
                <div class="buttonRow">
                  <span class="composerHint">Conversation actions stay local. Write enablement, review dispatch, and workflow launch remain visually separate handoff boundaries.</span>
                  <button class="solidButton" data-action="send-message" ${!state.sessionId || !state.messageDraft.trim() || hasBusy("send-message") ? "disabled" : ""}>Send</button>
                </div>
              </div>
            </section>
          </div>
        </main>

        <aside class="region artifactRegion">
          <div class="artifactStack">
            <section class="artifactPanel">
              <div class="artifactHeader">
                <div>
                  <p class="sectionEyebrow">Context Artifact Region</p>
                  <h2 class="artifactTitle">Bounded secondary surfaces</h2>
                  <p>No route change is required to inspect file, diff, terminal, git, review, or workflow evidence relevant to the current conversation.</p>
                </div>
                <span class="tag tagDeclared">same-context</span>
              </div>
            </section>
            <nav class="tabs" aria-label="artifact tabs">
              ${(["files", "diff", "terminal", "git", "review", "workflow"] as ArtifactTabId[])
                .map(
                  (tab) => `
                    <button
                      class="tabButton ${state.activeArtifact === tab ? "tabButtonActive" : ""}"
                      data-action="open-artifact"
                      data-tab="${tab}"
                    >
                      ${escapeHtml(tab)}
                    </button>
                  `,
                )
                .join("")}
            </nav>
            <div class="artifactBody">${renderArtifactContent()}</div>
          </div>
        </aside>
      </section>

      <section class="region trustBoundary">
        <div class="sectionHeader">
          <div>
            <p class="sectionEyebrow">Trust Boundary Lane</p>
            <h2 class="sectionTitle">Explicit handoff notices</h2>
            <p>Capability changes and cross-process handoffs remain visible so they cannot masquerade as ordinary transcript-local actions.</p>
          </div>
        </div>
        <div class="trustGrid">
          <article class="noticeCard">
            <strong>${state.writesAllowed ? "Writes are enabled" : "Writes remain disabled"}</strong>
            <div class="recordSummary">Current write posture is explicit and should be treated as a capability boundary, not decoration.</div>
            <div class="chipRow"><span class="tag ${state.writesAllowed ? "tagWarning" : "tagObserved"}">${state.writesAllowed ? "authoritative side effects possible" : "safe read posture"}</span></div>
          </article>
          <article class="noticeCard">
            <strong>Review dispatch remains advisory</strong>
            <div class="recordSummary">${reviewPending > 0 ? `${reviewPending} advisory dispatches are in flight.` : "Returned reviews may inform judgment, but they do not silently override local authority."}</div>
            <div class="chipRow"><span class="tag tagAdvisory">review handoff boundary</span></div>
          </article>
          <article class="noticeCard">
            <strong>Workflow launches are explicit</strong>
            <div class="recordSummary">${workflowLatest ? `Latest workflow status: ${workflowLatest.status}. Evidence remains reachable from the workflow dock.` : "No workflow has been launched in this session yet."}</div>
            <div class="chipRow"><span class="tag tagDeclared">workflow boundary</span></div>
          </article>
        </div>
      </section>
      ${renderOverlay()}
    </div>
  `;
}

root.addEventListener("click", (event) => {
  const target = (event.target as HTMLElement).closest<HTMLElement>("[data-action]");
  if (!target) return;
  void handleAction(target.dataset.action ?? "", target.dataset);
});

root.addEventListener("input", (event) => {
  const target = event.target as HTMLInputElement | HTMLTextAreaElement | HTMLSelectElement;
  const binding = target.dataset.bind;
  if (!binding) return;

  if (binding === "messageDraft") {
    state.messageDraft = target.value;
  } else if (binding === "workflowPrompt") {
    state.workflowPrompt = target.value;
  } else if (binding === "evidenceIdInput") {
    state.evidenceIdInput = target.value;
  } else if (binding === "apiBaseDraft") {
    state.apiBaseDraft = target.value;
  } else if (binding === "overlayTargetId" && state.overlay.kind === "review-picker") {
    state.overlay.selectedTargetId = target.value;
  }
});

root.addEventListener("change", (event) => {
  const target = event.target as HTMLInputElement | HTMLTextAreaElement | HTMLSelectElement;
  const binding = target.dataset.bind;
  if (!binding) return;

  if (binding === "selectedTemplateId") {
    state.selectedTemplateId = target.value;
  } else if (binding === "selectedLaunchProfileId" && state.hostState) {
    state.hostState.selectedLaunchProfileId = target.value;
  }
  render();
});

root.addEventListener("contextmenu", (event) => {
  const transcriptTarget = (event.target as HTMLElement).closest<HTMLElement>("[data-item-id]");
  if (transcriptTarget) {
    const itemId = transcriptTarget.dataset.itemId;
    if (itemId) {
      event.preventDefault();
      openReviewPicker(buildReviewOrigin("reply", itemId));
      render();
      return;
    }
  }

  const fileTarget = (event.target as HTMLElement).closest<HTMLElement>('[data-kind="file"]');
  if (fileTarget?.dataset.path) {
    event.preventDefault();
    openReviewPicker(buildReviewOrigin("file", fileTarget.dataset.path));
    render();
    return;
  }
});

void bootstrap();
