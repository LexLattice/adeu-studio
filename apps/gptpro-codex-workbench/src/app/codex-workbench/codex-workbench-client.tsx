"use client";

import Link from "next/link";
import {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
  type ReactNode,
} from "react";

import { apiBase } from "../lib/api-base";
import {
  buildReviewDispatchPacket,
  buildReviewPrompt,
  clipText,
  CODEX_WORKBENCH_ID,
  CODEX_WORKBENCH_PROFILE_ID,
  CODEX_WORKBENCH_ROUTE_ID,
  CONTEXT_ARTIFACT_TABS,
  extractReadableEvidenceSummary,
  REVIEW_TARGET_PROFILES,
  summarizePath,
  TERMINAL_COMMAND_IDS,
  WORKSPACE_ROOT_OPTIONS,
  type ContextArtifactTab,
  type ReviewOrigin,
  type ReviewTargetProfile,
  type TerminalCommandId,
  type WorkspaceRootOption,
} from "./contract";
import type {
  AppStateSnapshot,
  ApprovalIssueResponse,
  CopilotSessionResponse,
  DiffDocument,
  EvidenceBundle,
  FileDocument,
  GitSnapshot,
  HarnessSummary,
  PolicyProfileCurrentResponse,
  PolicyProfileDescriptor,
  PolicyProfileListResponse,
  PolicyProfileSelectResponse,
  RepoTreeEntry,
  RepoTreeResponse,
  ReviewRecord,
  TemplateMeta,
  TerminalSnapshot,
  ToolCallResponse,
  WorkflowRunRecord,
} from "./models";
import styles from "./page.module.css";

type CopilotStatus = "idle" | "starting" | "running" | "stopped" | "failed";
type ConnectionStatus = "disconnected" | "connecting" | "connected";
type TranscriptRole = "system" | "user" | "assistant";

type TranscriptItem = {
  id: string;
  role: TranscriptRole;
  text: string;
  createdAt: string;
  status: "sent" | "streaming" | "done" | "failed";
  turnId?: string;
};

type SessionHistoryEntry = {
  sessionId: string;
  startedAt: string;
  status: CopilotStatus;
  profileId: string;
};

type SSECodexEvent = {
  event?: string;
  seq?: number;
  ts?: string;
  event_kind?: string | null;
  payload?: Record<string, unknown>;
  raw_line?: string | null;
};

type SessionStatusEvent = {
  session_id?: string;
  status?: string;
  last_seq?: number;
  error?: unknown;
};

type Notice = {
  id: string;
  tone: "neutral" | "good" | "warn" | "critical";
  title: string;
  detail: string;
};

const DEFAULT_TEMPLATE_ID = "adeu.workflow.pipeline_worker.v0";
const SESSION_STORAGE_KEY = "adeu-codex-workbench-sessions-v1";
const MAX_CONTEXT_INSERT_CHARS = 1_800;

function requestId(): string {
  if (typeof crypto !== "undefined" && "randomUUID" in crypto) {
    return crypto.randomUUID();
  }
  return `${Date.now()}-${Math.random().toString(16).slice(2)}`;
}

function stringify(value: unknown): string {
  try {
    return JSON.stringify(value, null, 2);
  } catch {
    return String(value);
  }
}

function asRecord(value: unknown): Record<string, unknown> | null {
  if (typeof value !== "object" || value === null || Array.isArray(value)) return null;
  return value as Record<string, unknown>;
}

function asString(value: unknown): string | null {
  return typeof value === "string" ? value : null;
}

function formatTimestamp(value: string | null | undefined): string {
  if (!value) return "n/a";
  try {
    return new Date(value).toLocaleString();
  } catch {
    return value;
  }
}

function formatBytes(value: number | null | undefined): string {
  if (typeof value !== "number" || Number.isNaN(value)) return "n/a";
  if (value < 1_024) return `${value} B`;
  if (value < 1_024 * 1_024) return `${(value / 1_024).toFixed(1)} KB`;
  return `${(value / (1_024 * 1_024)).toFixed(1)} MB`;
}

function buildTranscriptOrigin(item: TranscriptItem): ReviewOrigin {
  return {
    originKind: "reply",
    originRef: item.id,
    title:
      item.role === "assistant"
        ? "Assistant reply"
        : item.role === "user"
          ? "User message"
          : "System note",
    content: item.text,
    provenance: {
      transcript_item_id: item.id,
      turn_id: item.turnId ?? null,
      created_at: item.createdAt,
      role: item.role,
      status: item.status,
    },
  };
}

function loadSessionHistory(): SessionHistoryEntry[] {
  if (typeof window === "undefined") return [];
  try {
    const raw = window.localStorage.getItem(SESSION_STORAGE_KEY);
    if (!raw) return [];
    const parsed = JSON.parse(raw) as SessionHistoryEntry[];
    return Array.isArray(parsed) ? parsed.slice(0, 12) : [];
  } catch {
    return [];
  }
}

function storeSessionHistory(entries: SessionHistoryEntry[]) {
  if (typeof window === "undefined") return;
  window.localStorage.setItem(
    SESSION_STORAGE_KEY,
    JSON.stringify(entries.slice(0, 12)),
  );
}

function toRepoRelativePath(
  absolutePath: string,
  harness: HarnessSummary | null,
): string | null {
  if (!harness) return null;
  const normalizedRoot = `${harness.repoRoot.replace(/\\/g, "/")}/`;
  const normalizedPath = absolutePath.replace(/\\/g, "/");
  if (!normalizedPath.startsWith(normalizedRoot)) return null;
  return normalizedPath.slice(normalizedRoot.length);
}

async function parseErrorMessage(response: Response): Promise<string> {
  const text = await response.text();
  if (!text) return `HTTP ${response.status}`;
  try {
    const parsed = JSON.parse(text) as {
      error?: string;
      message?: string;
      detail?: { code?: string; message?: string };
    };
    if (parsed.detail?.code && parsed.detail.message) {
      return `${parsed.detail.code}: ${parsed.detail.message}`;
    }
    return parsed.error || parsed.message || text;
  } catch {
    return text;
  }
}

async function fetchJson<T>(url: string, init?: RequestInit): Promise<T> {
  const response = await fetch(url, init);
  if (!response.ok) {
    throw new Error(await parseErrorMessage(response));
  }
  return (await response.json()) as T;
}

function StatusChip({
  label,
  tone = "neutral",
}: {
  label: string;
  tone?: "neutral" | "good" | "warn" | "critical";
}) {
  return (
    <span className={styles.statusChip} data-tone={tone}>
      {label}
    </span>
  );
}

function MetaRow({ label, value }: { label: string; value: ReactNode }) {
  return (
    <div className={styles.metaRow}>
      <span className={styles.metaLabel}>{label}</span>
      <span className={styles.metaValue}>{value}</span>
    </div>
  );
}

function EvidenceBlock({ evidence }: { evidence: EvidenceBundle | null }) {
  if (!evidence) return null;
  return (
    <div className={styles.evidenceBlock}>
      <div className={styles.stackRow}>
        <StatusChip
          label={`${evidence.role} · ${evidence.status}`}
          tone={evidence.error ? "critical" : evidence.purged ? "warn" : "good"}
        />
        <span className={styles.mutedText}>{evidence.evidence_id}</span>
      </div>
      <p className={styles.summaryText}>
        {extractReadableEvidenceSummary(evidence.raw_jsonl)}
      </p>
      <details className={styles.detailsBlock}>
        <summary>Evidence payload</summary>
        <pre className={styles.codeBlock}>
          {evidence.raw_jsonl || stringify(evidence.metadata)}
        </pre>
      </details>
    </div>
  );
}

export function CodexWorkbenchClient() {
  const [sessionId, setSessionId] = useState<string | null>(null);
  const [sessionStatus, setSessionStatus] = useState<CopilotStatus>("idle");
  const [connectionStatus, setConnectionStatus] =
    useState<ConnectionStatus>("disconnected");
  const [writesAllowed, setWritesAllowed] = useState(false);
  const [workerOnlyMode, setWorkerOnlyMode] = useState(false);
  const [apiReachable, setApiReachable] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [busyCount, setBusyCount] = useState(0);
  const [lastHeartbeatAt, setLastHeartbeatAt] = useState<string | null>(null);

  const [messageText, setMessageText] = useState("");
  const [transcript, setTranscript] = useState<TranscriptItem[]>([
    {
      id: "system:welcome",
      role: "system",
      text: "Transcript-first operator loop. Review dispatch and workflow launch remain explicit handoff boundaries.",
      createdAt: "",
      status: "done",
    },
  ]);

  const [sessionHistory, setSessionHistory] = useState<SessionHistoryEntry[]>([]);

  const [selectedProfileId, setSelectedProfileId] = useState("default");
  const [profiles, setProfiles] = useState<PolicyProfileDescriptor[]>([]);
  const [currentProfile, setCurrentProfile] =
    useState<PolicyProfileCurrentResponse | null>(null);
  const [appState, setAppState] = useState<AppStateSnapshot | null>(null);
  const [templates, setTemplates] = useState<TemplateMeta[]>([]);
  const [templateId, setTemplateId] = useState(DEFAULT_TEMPLATE_ID);
  const [harness, setHarness] = useState<HarnessSummary | null>(null);
  const [showHarnessInspector, setShowHarnessInspector] = useState(false);

  const [workspaceRoot, setWorkspaceRoot] = useState<WorkspaceRootOption>("");
  const [treeByPath, setTreeByPath] = useState<Record<string, RepoTreeEntry[]>>({});
  const [expandedPaths, setExpandedPaths] = useState<string[]>([]);
  const [selectedFile, setSelectedFile] = useState<FileDocument | null>(null);
  const [peekFile, setPeekFile] = useState<FileDocument | null>(null);
  const [contextTab, setContextTab] = useState<ContextArtifactTab>("files");

  const [diffLeftPath, setDiffLeftPath] = useState("");
  const [diffRightPath, setDiffRightPath] = useState("");
  const [diffDocument, setDiffDocument] = useState<DiffDocument | null>(null);

  const [terminalCommand, setTerminalCommand] =
    useState<TerminalCommandId>("pwd");
  const [terminalSnapshot, setTerminalSnapshot] =
    useState<TerminalSnapshot | null>(null);
  const [gitSnapshot, setGitSnapshot] = useState<GitSnapshot | null>(null);

  const [reviewOrigin, setReviewOrigin] = useState<ReviewOrigin | null>(null);
  const [reviewTargetProfile, setReviewTargetProfile] =
    useState<ReviewTargetProfile>("adeu_read_only_review");
  const [reviewNote, setReviewNote] = useState("");
  const [reviewRecords, setReviewRecords] = useState<ReviewRecord[]>([]);

  const [workflowPrompt, setWorkflowPrompt] = useState(
    "Run a short read-only sanity check against the selected workspace context.",
  );
  const [workflowRuns, setWorkflowRuns] = useState<WorkflowRunRecord[]>([]);

  const lastSeqRef = useRef(0);

  const withBusy = useCallback(async <T,>(operation: () => Promise<T>): Promise<T> => {
    setBusyCount((current) => current + 1);
    try {
      return await operation();
    } finally {
      setBusyCount((current) => Math.max(0, current - 1));
    }
  }, []);

  const isBusy = busyCount > 0;

  const selectedWorkingPath = selectedFile?.path
    ? selectedFile.path.split("/").slice(0, -1).join("/")
    : workspaceRoot;

  const activeConfigRepoPath = useMemo(() => {
    if (!harness?.activeConfigPath) return null;
    return toRepoRelativePath(harness.activeConfigPath, harness);
  }, [harness]);

  const currentDirectoryEntries = useMemo(
    () => treeByPath[workspaceRoot] ?? [],
    [treeByPath, workspaceRoot],
  );

  const reviewCountByOrigin = useMemo(() => {
    const counts = new Map<string, number>();
    for (const record of reviewRecords) {
      const key = `${record.originKind}:${record.originRef}`;
      counts.set(key, (counts.get(key) ?? 0) + 1);
    }
    return counts;
  }, [reviewRecords]);

  const profileMismatch = useMemo(() => {
    if (!currentProfile) return false;
    return currentProfile.profile_id !== selectedProfileId;
  }, [currentProfile, selectedProfileId]);

  const notices = useMemo<Notice[]>(() => {
    const base: Array<Notice | null> = [
      writesAllowed
        ? {
            id: "writes-enabled",
            tone: "critical",
            title: "Writes enabled",
            detail:
              "Capability-changing state is explicit. Review local evidence before any authoritative action.",
          }
        : {
            id: "writes-disabled",
            tone: "neutral",
            title: "Writes disabled",
            detail:
              "Read-only remains the default posture for conversation, review, and workflow dispatch.",
          },
      {
        id: "review-boundary",
        tone: "warn",
        title: "Review dispatch is advisory",
        detail:
          "Returned review artifacts can inform judgment, but they do not silently override local authority.",
      },
      {
        id: "workflow-boundary",
        tone: "warn",
        title: "Workflow launch is explicit",
        detail:
          "Workflow runs stay same-context reachable in the docked artifact region with evidence attached.",
      },
      workerOnlyMode
        ? {
            id: "worker-only",
            tone: "warn",
            title: "Worker-only mode",
            detail:
              "The Codex app-server is unavailable for this build, so chat replies may be limited while read-only workflows still work.",
          }
        : {
            id: "app-server",
            tone: "good",
            title: "App-server reachable",
            detail:
              "Session, workflow, and evidence surfaces stay visible in one bounded workbench when the backend is reachable.",
          },
      profileMismatch
        ? {
            id: "profile-mismatch",
            tone: "warn",
            title: "Configured vs effective profile mismatch",
            detail: `Configured ${selectedProfileId} but runtime is ${currentProfile?.profile_id ?? "unknown"}.`,
          }
        : null,
    ];
    return base.filter(Boolean) as Notice[];
  }, [
    currentProfile?.profile_id,
    profileMismatch,
    selectedProfileId,
    workerOnlyMode,
    writesAllowed,
  ]);

  const pushSystemNote = useCallback((text: string) => {
    setTranscript((current) => [
      ...current,
      {
        id: `system:${requestId()}`,
        role: "system",
        text,
        createdAt: new Date().toISOString(),
        status: "done",
      },
    ]);
  }, []);

  const updateAssistantTurn = useCallback(
    (turnId: string, deltaText?: string, done?: boolean, fullText?: string) => {
      setTranscript((current) => {
        const index = current.findIndex((item) => item.turnId === turnId);
        if (index === -1) {
          return [
            ...current,
            {
              id: `assistant:${turnId}`,
              role: "assistant",
              text: fullText ?? deltaText ?? "",
              createdAt: new Date().toISOString(),
              status: done ? "done" : "streaming",
              turnId,
            },
          ];
        }
        const next = [...current];
        const target = next[index];
        next[index] = {
          ...target,
          text:
            fullText ??
            (deltaText ? `${target.text}${deltaText}` : target.text),
          status: done ? "done" : target.status,
        };
        return next;
      });
    },
    [],
  );

  const callTool = useCallback(
    async <T,>(
      toolName: string,
      argumentsValue: Record<string, unknown>,
      overrideSessionId?: string | null,
    ): Promise<T> => {
      const body: Record<string, unknown> = {
        provider: "codex",
        role: "copilot",
        tool_name: toolName,
        arguments: argumentsValue,
      };
      const resolvedSessionId =
        overrideSessionId === undefined ? sessionId : overrideSessionId;
      if (resolvedSessionId) body.session_id = resolvedSessionId;
      const response = await fetch(`${apiBase()}/urm/tools/call`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify(body),
      });
      if (!response.ok) {
        setApiReachable(false);
        throw new Error(await parseErrorMessage(response));
      }
      const payload = (await response.json()) as ToolCallResponse;
      setApiReachable(true);
      return payload.result as T;
    },
    [sessionId],
  );

  const loadHarness = useCallback(async () => {
    setHarness(await fetchJson<HarnessSummary>("/api/desktop/harness"));
  }, []);

  const loadGit = useCallback(async () => {
    setGitSnapshot(await fetchJson<GitSnapshot>("/api/desktop/git"));
  }, []);

  const loadTerminal = useCallback(async (commandId: TerminalCommandId, cwd?: string) => {
    const query = new URLSearchParams({ command: commandId });
    if (cwd) query.set("cwd", cwd);
    setTerminalSnapshot(
      await fetchJson<TerminalSnapshot>(`/api/desktop/terminal?${query.toString()}`),
    );
  }, []);

  const loadDirectory = useCallback(async (pathValue: string) => {
    const query = new URLSearchParams();
    if (pathValue) query.set("path", pathValue);
    const payload = await fetchJson<RepoTreeResponse>(`/api/desktop/tree?${query.toString()}`);
    setTreeByPath((current) => ({ ...current, [pathValue]: payload.entries }));
  }, []);

  const fetchFileDocument = useCallback(async (pathValue: string) => {
    const query = new URLSearchParams({ path: pathValue });
    return await fetchJson<FileDocument>(`/api/desktop/file?${query.toString()}`);
  }, []);

  const loadFile = useCallback(
    async (pathValue: string, mode: "select" | "peek") => {
      const payload = await fetchFileDocument(pathValue);
      if (mode === "peek") {
        setPeekFile(payload);
        return payload;
      }
      setSelectedFile(payload);
      setContextTab("files");
      return payload;
    },
    [fetchFileDocument],
  );

  const loadDiff = useCallback(async (leftPath: string, rightPath: string) => {
    const query = new URLSearchParams({ left: leftPath, right: rightPath });
    const payload = await fetchJson<DiffDocument>(`/api/desktop/diff?${query.toString()}`);
    setDiffDocument(payload);
    setContextTab("diff");
    return payload;
  }, []);

  const loadProfiles = useCallback(async () => {
    const payload = await fetchJson<PolicyProfileListResponse>(
      `${apiBase()}/urm/policy/profile/list?provider=codex`,
    );
    setProfiles(payload.profiles);
    setSelectedProfileId((current) => {
      if (payload.profiles.some((profile) => profile.profile_id === current)) {
        return current;
      }
      return payload.profiles[0]?.profile_id ?? current;
    });
    setApiReachable(true);
  }, []);

  const loadCurrentProfile = useCallback(async (targetSessionId: string) => {
    const payload = await fetchJson<PolicyProfileCurrentResponse>(
      `${apiBase()}/urm/policy/profile/current?provider=codex&session_id=${encodeURIComponent(targetSessionId)}`,
    );
    setCurrentProfile(payload);
    setApiReachable(true);
  }, []);

  const refreshAppState = useCallback(async () => {
    const payload = await callTool<AppStateSnapshot>("adeu.get_app_state", {}, null);
    setAppState(payload);
    if (payload.codex_app_server_available === false) setWorkerOnlyMode(true);
    if (payload.codex_app_server_available === true) setWorkerOnlyMode(false);
  }, [callTool]);

  const refreshTemplates = useCallback(async () => {
    const payload = await callTool<{ templates?: TemplateMeta[] }>(
      "adeu.list_templates",
      {},
      null,
    );
    const nextTemplates = payload.templates ?? [];
    setTemplates(nextTemplates);
    setTemplateId((current) => {
      if (nextTemplates.length === 0) return current;
      if (nextTemplates.some((template) => template.template_id === current)) {
        return current;
      }
      return nextTemplates[0].template_id;
    });
  }, [callTool]);

  const loadEvidence = useCallback(
    async (evidenceId: string): Promise<EvidenceBundle> => {
      return await callTool<EvidenceBundle>(
        "adeu.read_evidence",
        { evidence_id: evidenceId, max_bytes: 200_000 },
        sessionId,
      );
    },
    [callTool, sessionId],
  );

  const refreshRemoteState = useCallback(async () => {
    try {
      await Promise.all([loadProfiles(), refreshAppState(), refreshTemplates()]);
      setApiReachable(true);
    } catch (nextError) {
      setApiReachable(false);
      setError((current) => current ?? `Remote API unavailable: ${String(nextError)}`);
    }
  }, [loadProfiles, refreshAppState, refreshTemplates]);

  const refreshRuntime = useCallback(async () => {
    setError(null);
    try {
      await withBusy(async () => {
        await Promise.all([
          loadHarness(),
          loadGit(),
          loadDirectory(workspaceRoot),
          loadTerminal(terminalCommand, selectedWorkingPath),
        ]);
      });
      setExpandedPaths((current) =>
        current.includes(workspaceRoot) ? current : [...current, workspaceRoot],
      );
      await refreshRemoteState();
    } catch (nextError) {
      setError(String(nextError));
    }
  }, [
    loadDirectory,
    loadGit,
    loadHarness,
    loadTerminal,
    refreshRemoteState,
    selectedWorkingPath,
    terminalCommand,
    withBusy,
    workspaceRoot,
  ]);

  const startSession = useCallback(async () => {
    setError(null);
    try {
      const payload = await withBusy(async () =>
        await fetchJson<CopilotSessionResponse>(`${apiBase()}/urm/copilot/start`, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({
            provider: "codex",
            client_request_id: requestId(),
            profile_id: selectedProfileId,
          }),
        }),
      );
      setSessionId(payload.session_id);
      setSessionStatus(payload.status);
      setWorkerOnlyMode(payload.app_server_unavailable);
      setWritesAllowed(false);
      setCurrentProfile({
        session_id: payload.session_id,
        profile_id: payload.profile_id,
        profile_version: payload.profile_version,
        policy_hash: "pending",
      });
      lastSeqRef.current = 0;
      pushSystemNote(
        `Session ${payload.session_id} started with profile ${payload.profile_id}.`,
      );
      setSessionHistory((current) => {
        const next = [
          {
            sessionId: payload.session_id,
            startedAt: new Date().toISOString(),
            status: payload.status,
            profileId: payload.profile_id,
          },
          ...current.filter((entry) => entry.sessionId !== payload.session_id),
        ].slice(0, 12);
        storeSessionHistory(next);
        return next;
      });
      await Promise.allSettled([loadCurrentProfile(payload.session_id), refreshAppState()]);
      setApiReachable(true);
    } catch (nextError) {
      setApiReachable(false);
      setError(String(nextError));
    }
  }, [
    loadCurrentProfile,
    pushSystemNote,
    refreshAppState,
    selectedProfileId,
    withBusy,
  ]);

  const stopSession = useCallback(async () => {
    if (!sessionId) return;
    setError(null);
    try {
      const payload = await withBusy(async () =>
        await fetchJson<CopilotSessionResponse>(`${apiBase()}/urm/copilot/stop`, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ provider: "codex", session_id: sessionId }),
        }),
      );
      setSessionStatus(payload.status);
      setWritesAllowed(false);
      pushSystemNote(`Session ${payload.session_id} stopped.`);
      setSessionHistory((current) => {
        const next = current.map((entry) =>
          entry.sessionId === payload.session_id ? { ...entry, status: payload.status } : entry,
        );
        storeSessionHistory(next);
        return next;
      });
      await refreshAppState();
    } catch (nextError) {
      setError(String(nextError));
    }
  }, [pushSystemNote, refreshAppState, sessionId, withBusy]);

  const restartSessionWithProfile = useCallback(async () => {
    if (sessionId) {
      await stopSession();
    }
    await startSession();
  }, [sessionId, startSession, stopSession]);

  const applyProfileToSession = useCallback(async () => {
    if (!sessionId) return;
    setError(null);
    try {
      const payload = await withBusy(async () =>
        await fetchJson<PolicyProfileSelectResponse>(
          `${apiBase()}/urm/policy/profile/select`,
          {
            method: "POST",
            headers: { "content-type": "application/json" },
            body: JSON.stringify({
              provider: "codex",
              session_id: sessionId,
              client_request_id: requestId(),
              profile_id: selectedProfileId,
            }),
          },
        ),
      );
      setCurrentProfile({
        session_id: payload.session_id,
        profile_id: payload.profile_id,
        profile_version: payload.profile_version,
        policy_hash: payload.policy_hash,
      });
      pushSystemNote(`Policy profile switched to ${payload.profile_id}.`);
    } catch (nextError) {
      setError(String(nextError));
    }
  }, [pushSystemNote, selectedProfileId, sessionId, withBusy]);

  const toggleWrites = useCallback(async () => {
    if (!sessionId) return;
    setError(null);
    try {
      await withBusy(async () => {
        let approvalId: string | null = null;
        if (!writesAllowed) {
          const approval = await fetchJson<ApprovalIssueResponse>(
            `${apiBase()}/urm/approval/issue`,
            {
              method: "POST",
              headers: { "content-type": "application/json" },
              body: JSON.stringify({
                provider: "codex",
                session_id: sessionId,
                action_kind: "urm.set_mode.enable_writes",
                action_payload: { writes_allowed: true },
              }),
            },
          );
          approvalId = approval.approval_id;
        }

        await fetchJson<CopilotSessionResponse>(`${apiBase()}/urm/copilot/mode`, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({
            provider: "codex",
            session_id: sessionId,
            writes_allowed: !writesAllowed,
            approval_id: approvalId,
          }),
        });
      });
      setWritesAllowed((current) => !current);
      pushSystemNote(
        !writesAllowed
          ? "Writes enabled after explicit approval."
          : "Writes reset to read-only mode.",
      );
      await refreshAppState();
    } catch (nextError) {
      setError(String(nextError));
    }
  }, [pushSystemNote, refreshAppState, sessionId, withBusy, writesAllowed]);

  const sendMessage = useCallback(async () => {
    const trimmed = messageText.trim();
    if (!sessionId || !trimmed) return;
    setError(null);
    const userItem: TranscriptItem = {
      id: `user:${requestId()}`,
      role: "user",
      text: trimmed,
      createdAt: new Date().toISOString(),
      status: "sent",
    };
    setTranscript((current) => [...current, userItem]);
    setMessageText("");
    try {
      await withBusy(async () =>
        await fetchJson<CopilotSessionResponse>(`${apiBase()}/urm/copilot/send`, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({
            provider: "codex",
            session_id: sessionId,
            client_request_id: requestId(),
            message: {
              jsonrpc: "2.0",
              id: requestId(),
              method: "copilot.user_message",
              params: { text: trimmed },
            },
          }),
        }),
      );
    } catch (nextError) {
      setTranscript((current) =>
        current.map((item) =>
          item.id === userItem.id ? { ...item, status: "failed" } : item,
        ),
      );
      setError(String(nextError));
    }
  }, [messageText, sessionId, withBusy]);

  const quoteTranscriptItem = useCallback((item: TranscriptItem) => {
    const quoted = `> ${item.text.replace(/\n/g, "\n> ")}`;
    setMessageText((current) => `${current.trim()}\n\n${quoted}`.trim());
  }, []);

  const insertSelectedFileContext = useCallback(() => {
    if (!selectedFile) return;
    const header = `[file:${selectedFile.path} sha256=${selectedFile.sha256}]`;
    const body = selectedFile.isBinary
      ? selectedFile.preview
      : clipText(selectedFile.text, MAX_CONTEXT_INSERT_CHARS);
    setMessageText((current) => `${current.trim()}\n\n${header}\n${body}`.trim());
  }, [selectedFile]);

  const insertDiffContext = useCallback(() => {
    if (!diffDocument) return;
    const header = `[diff:${diffDocument.leftPath} -> ${diffDocument.rightPath}]`;
    const body = clipText(diffDocument.raw, MAX_CONTEXT_INSERT_CHARS);
    setMessageText((current) => `${current.trim()}\n\n${header}\n${body}`.trim());
  }, [diffDocument]);

  const copyText = useCallback(async (text: string) => {
    try {
      await navigator.clipboard.writeText(text);
    } catch (nextError) {
      setError(`Clipboard write failed: ${String(nextError)}`);
    }
  }, []);

  const openReviewForFile = useCallback((document: FileDocument) => {
    setReviewOrigin({
      originKind: "file",
      originRef: document.path,
      title: `File review · ${document.path}`,
      content: document.isBinary ? document.preview : document.text,
      provenance: {
        path: document.path,
        sha256: document.sha256,
        size: document.size,
        truncated: document.truncated,
      },
    });
  }, []);

  const reviewFilePath = useCallback(
    async (pathValue: string) => {
      setError(null);
      try {
        const payload = await withBusy(async () => await fetchFileDocument(pathValue));
        openReviewForFile(payload);
      } catch (nextError) {
        setError(String(nextError));
      }
    },
    [fetchFileDocument, openReviewForFile, withBusy],
  );

  const openReviewForDiff = useCallback((document: DiffDocument) => {
    setReviewOrigin({
      originKind: "diff",
      originRef: `${document.leftPath}::${document.rightPath}`,
      title: `Diff review · ${document.leftPath} → ${document.rightPath}`,
      content: document.raw,
      provenance: {
        left_path: document.leftPath,
        right_path: document.rightPath,
        left_sha256: document.leftSha256,
        right_sha256: document.rightSha256,
        summary: document.summary,
      },
    });
  }, []);

  const dispatchReview = useCallback(async () => {
    if (!reviewOrigin) return;
    const createdAt = new Date().toISOString();
    const packet = buildReviewDispatchPacket({
      origin: reviewOrigin,
      targetProfile: reviewTargetProfile,
      requestId: requestId(),
      createdAt,
      dispatchNote: reviewNote,
    });
    const packetJson = JSON.stringify(packet, null, 2);
    const baseRecord: ReviewRecord = {
      id: `review:${packet.request_id}`,
      requestId: packet.request_id,
      createdAt,
      originKind: reviewOrigin.originKind,
      originRef: reviewOrigin.originRef,
      title: reviewOrigin.title,
      targetProfile: reviewTargetProfile,
      dispatchNote: packet.dispatch_note,
      status: reviewTargetProfile === "export_packet" ? "exported" : "running",
      summary:
        reviewTargetProfile === "export_packet"
          ? "Dispatch packet exported for external review."
          : "Read-only review workflow launched.",
      packetJson,
      evidenceId: null,
      evidence: null,
    };
    setReviewRecords((current) => [baseRecord, ...current]);
    setContextTab("review");

    if (reviewTargetProfile === "export_packet") {
      try {
        const blob = new Blob([packetJson], { type: "application/json" });
        const url = URL.createObjectURL(blob);
        const anchor = document.createElement("a");
        anchor.href = url;
        anchor.download = `${packet.request_id}.json`;
        anchor.click();
        URL.revokeObjectURL(url);
      } catch (nextError) {
        setError(`Packet export failed: ${String(nextError)}`);
      } finally {
        setReviewOrigin(null);
        setReviewNote("");
      }
      return;
    }

    try {
      const workflow = await withBusy(async () =>
        await callTool<{ evidence_id?: string }>("adeu.run_workflow", {
          template_id: templateId,
          mode: "read_only",
          client_request_id: requestId(),
          inputs: { prompt: buildReviewPrompt(packet) },
        }),
      );
      const evidenceId = asString(workflow.evidence_id) ?? null;
      let evidence: EvidenceBundle | null = null;
      if (evidenceId) {
        evidence = await withBusy(async () => await loadEvidence(evidenceId));
      }
      const summary = evidence
        ? extractReadableEvidenceSummary(evidence.raw_jsonl)
        : "Review workflow completed without a readable evidence payload.";
      setReviewRecords((current) =>
        current.map((record) =>
          record.id === baseRecord.id
            ? {
                ...record,
                status: evidence ? "completed" : "failed",
                summary,
                evidenceId,
                evidence,
              }
            : record,
        ),
      );
    } catch (nextError) {
      setReviewRecords((current) =>
        current.map((record) =>
          record.id === baseRecord.id
            ? { ...record, status: "failed", summary: String(nextError) }
            : record,
        ),
      );
      setError(String(nextError));
    } finally {
      setReviewOrigin(null);
      setReviewNote("");
    }
  }, [
    callTool,
    loadEvidence,
    reviewNote,
    reviewOrigin,
    reviewTargetProfile,
    templateId,
    withBusy,
  ]);

  const runWorkflow = useCallback(async () => {
    const trimmed = workflowPrompt.trim();
    if (!trimmed) return;
    const record: WorkflowRunRecord = {
      id: `workflow:${requestId()}`,
      createdAt: new Date().toISOString(),
      templateId,
      prompt: trimmed,
      status: "running",
      evidenceId: null,
      evidence: null,
      summary: "Workflow launched in read-only mode.",
    };
    setWorkflowRuns((current) => [record, ...current]);
    setContextTab("workflow");
    try {
      const result = await withBusy(async () =>
        await callTool<{ evidence_id?: string }>("adeu.run_workflow", {
          template_id: templateId,
          mode: "read_only",
          client_request_id: requestId(),
          inputs: { prompt: trimmed },
        }),
      );
      const evidenceId = asString(result.evidence_id) ?? null;
      let evidence: EvidenceBundle | null = null;
      if (evidenceId) {
        evidence = await withBusy(async () => await loadEvidence(evidenceId));
      }
      const summary = evidence
        ? extractReadableEvidenceSummary(evidence.raw_jsonl)
        : "Workflow completed without a readable evidence payload.";
      setWorkflowRuns((current) =>
        current.map((item) =>
          item.id === record.id
            ? {
                ...item,
                status: evidence ? "completed" : "failed",
                evidenceId,
                evidence,
                summary,
              }
            : item,
        ),
      );
    } catch (nextError) {
      setWorkflowRuns((current) =>
        current.map((item) =>
          item.id === record.id
            ? { ...item, status: "failed", summary: String(nextError) }
            : item,
        ),
      );
      setError(String(nextError));
    }
  }, [callTool, loadEvidence, templateId, withBusy, workflowPrompt]);

  const toggleDirectory = useCallback(
    async (pathValue: string) => {
      if (expandedPaths.includes(pathValue)) {
        setExpandedPaths((current) => current.filter((item) => item !== pathValue));
        return;
      }
      try {
        await withBusy(async () => {
          if (!treeByPath[pathValue]) await loadDirectory(pathValue);
        });
        setExpandedPaths((current) => [...current, pathValue]);
      } catch (nextError) {
        setError(String(nextError));
      }
    },
    [expandedPaths, loadDirectory, treeByPath, withBusy],
  );

  const selectFile = useCallback(
    async (pathValue: string) => {
      setError(null);
      try {
        const payload = await withBusy(async () => await loadFile(pathValue, "select"));
        setDiffLeftPath((current) => current || payload.path);
      } catch (nextError) {
        setError(String(nextError));
      }
    },
    [loadFile, withBusy],
  );

  const peekAtFile = useCallback(
    async (pathValue: string) => {
      setError(null);
      try {
        await withBusy(async () => await loadFile(pathValue, "peek"));
      } catch (nextError) {
        setError(String(nextError));
      }
    },
    [loadFile, withBusy],
  );

  const computeDiff = useCallback(async () => {
    if (!diffLeftPath || !diffRightPath) return;
    setError(null);
    try {
      await withBusy(async () => await loadDiff(diffLeftPath, diffRightPath));
    } catch (nextError) {
      setError(String(nextError));
    }
  }, [diffLeftPath, diffRightPath, loadDiff, withBusy]);

  useEffect(() => {
    setSessionHistory(loadSessionHistory());
    void refreshRuntime();
  }, [refreshRuntime]);

  useEffect(() => {
    setExpandedPaths((current) =>
      current.includes(workspaceRoot) ? current : [...current, workspaceRoot],
    );
    void withBusy(async () => {
      try {
        await loadDirectory(workspaceRoot);
      } catch (nextError) {
        setError(String(nextError));
      }
    });
  }, [loadDirectory, withBusy, workspaceRoot]);

  useEffect(() => {
    void withBusy(async () => {
      try {
        await loadTerminal(terminalCommand, selectedWorkingPath);
      } catch (nextError) {
        setError(String(nextError));
      }
    });
  }, [loadTerminal, selectedWorkingPath, terminalCommand, withBusy]);

  useEffect(() => {
    if (!sessionId) {
      setConnectionStatus("disconnected");
      setCurrentProfile(null);
      return;
    }

    setSessionHistory((current) => {
      const next = current.some((entry) => entry.sessionId === sessionId)
        ? current.map((entry) =>
            entry.sessionId === sessionId
              ? {
                  ...entry,
                  status: sessionStatus,
                  profileId: currentProfile?.profile_id ?? entry.profileId,
                }
              : entry,
          )
        : [
            {
              sessionId,
              startedAt: new Date().toISOString(),
              status: sessionStatus,
              profileId: currentProfile?.profile_id ?? selectedProfileId,
            },
            ...current,
          ];
      storeSessionHistory(next);
      return next.slice(0, 12);
    });
  }, [currentProfile?.profile_id, selectedProfileId, sessionId, sessionStatus]);

  useEffect(() => {
    if (!sessionId) {
      setConnectionStatus("disconnected");
      setCurrentProfile(null);
      return;
    }

    setConnectionStatus("connecting");
    const url = `${apiBase()}/urm/copilot/events?provider=codex&session_id=${encodeURIComponent(sessionId)}&after_seq=0`;
    const stream = new EventSource(url);

    stream.onopen = () => setConnectionStatus("connected");

    stream.addEventListener("heartbeat", (event) => {
      const payload = JSON.parse((event as MessageEvent).data) as { ts?: string };
      setLastHeartbeatAt(payload.ts ?? new Date().toISOString());
    });

    stream.addEventListener("codex_event", (event) => {
      const frame = JSON.parse((event as MessageEvent).data) as SSECodexEvent;
      const seq = typeof frame.seq === "number" ? frame.seq : null;
      if (seq !== null) {
        if (seq <= lastSeqRef.current) return;
        lastSeqRef.current = seq;
      }

      const providerPayload = asRecord(frame.payload) ?? {};
      const params = asRecord(providerPayload.params);
      const providerMethod = asString(providerPayload.method);
      const eventKind = frame.event_kind || providerMethod || frame.event || "event";
      const turnIdFromParams =
        asString(params?.turnId) ??
        asString(params?.turn_id) ??
        asString(params?.id);

      if (eventKind === "turn/started") {
        const turn = asRecord(params?.turn);
        const turnId = asString(turn?.id);
        if (turnId) updateAssistantTurn(turnId);
      }

      if (eventKind === "item/started") {
        const item = asRecord(params?.item);
        const itemType = asString(item?.type);
        const turnId =
          turnIdFromParams ??
          asString(item?.turnId) ??
          asString(item?.turn_id);
        if (itemType === "agentMessage" && turnId) {
          updateAssistantTurn(turnId, asString(item?.text) ?? "");
        }
      }

      if (
        eventKind === "codex/event/agent_message_delta" ||
        eventKind === "item/agentMessage/delta"
      ) {
        const turnId = turnIdFromParams;
        const msg = asRecord(params?.msg);
        const delta = asString(params?.delta) ?? asString(msg?.delta);
        if (turnId) updateAssistantTurn(turnId, delta ?? "");
      }

      if (eventKind === "item/completed") {
        const item = asRecord(params?.item);
        const itemType = asString(item?.type);
        const turnId =
          turnIdFromParams ??
          asString(item?.turnId) ??
          asString(item?.turn_id);
        if (itemType === "agentMessage" && turnId) {
          updateAssistantTurn(turnId, undefined, true, asString(item?.text) ?? undefined);
        }
      }

      const result = asRecord(providerPayload.result);
      const completedTurn = asRecord(result?.turn);
      const completedTurnId = asString(completedTurn?.id);
      if ((eventKind === "turn/completed" || completedTurn?.status === "completed") && completedTurnId) {
        updateAssistantTurn(completedTurnId, undefined, true);
      }
    });

    stream.addEventListener("session_status", (event) => {
      const payload = JSON.parse((event as MessageEvent).data) as SessionStatusEvent;
      if (typeof payload.status === "string") {
        setSessionStatus(payload.status as CopilotStatus);
      }
      if (typeof payload.last_seq === "number" && payload.last_seq > lastSeqRef.current) {
        lastSeqRef.current = payload.last_seq;
      }
    });

    stream.onerror = () => {
      setConnectionStatus("disconnected");
    };

    return () => {
      stream.close();
      setConnectionStatus("disconnected");
    };
  }, [sessionId, updateAssistantTurn]);

  const renderTreeEntries = useCallback(
    (entries: RepoTreeEntry[], depth = 0): ReactNode => {
      return entries.map((entry) => {
        const isDirectory = entry.kind === "directory";
        const isExpanded = expandedPaths.includes(entry.path);
        const isSelected = selectedFile?.path === entry.path;
        const childEntries = treeByPath[entry.path] ?? [];
        const reviewCount = reviewCountByOrigin.get(`file:${entry.path}`) ?? 0;
        return (
          <div key={entry.path} className={styles.treeNode}>
            <div className={styles.treeRow} style={{ paddingLeft: `${depth * 14}px` }}>
              <button
                type="button"
                className={styles.treePrimary}
                data-selected={isSelected ? "true" : undefined}
                onClick={() => {
                  if (isDirectory) {
                    void toggleDirectory(entry.path);
                  } else {
                    void selectFile(entry.path);
                  }
                }}
              >
                <span className={styles.treeGlyph}>
                  {isDirectory ? (isExpanded ? "▾" : "▸") : "•"}
                </span>
                <span className={styles.treeName}>{entry.name}</span>
                {entry.hidden ? <StatusChip label="hidden" tone="warn" /> : null}
              </button>
              {!isDirectory ? (
                <div className={styles.treeActions}>
                  <button type="button" onClick={() => void peekAtFile(entry.path)}>
                    Peek
                  </button>
                  <button type="button" onClick={() => void reviewFilePath(entry.path)}>
                    Review
                  </button>
                  <button type="button" onClick={() => setDiffLeftPath(entry.path)}>
                    L
                  </button>
                  <button type="button" onClick={() => setDiffRightPath(entry.path)}>
                    R
                  </button>
                  {reviewCount > 0 ? (
                    <StatusChip label={`${reviewCount} review`} tone="warn" />
                  ) : null}
                </div>
              ) : null}
            </div>
            {isDirectory && isExpanded ? (
              <div className={styles.treeChildren}>
                {childEntries.length > 0 ? (
                  renderTreeEntries(childEntries, depth + 1)
                ) : (
                  <div className={styles.treeEmpty}>No visible entries.</div>
                )}
              </div>
            ) : null}
          </div>
        );
      });
    },
    [
      expandedPaths,
      peekAtFile,
      reviewCountByOrigin,
      reviewFilePath,
      selectFile,
      selectedFile?.path,
      toggleDirectory,
      treeByPath,
    ],
  );

  const renderArtifactContent = () => {
    if (contextTab === "files") {
      if (!selectedFile) {
        return (
          <p className={styles.placeholderText}>
            Select a file from the workspace lane to open it in the docked reader.
          </p>
        );
      }
      return (
        <div className={styles.tabPanelBody}>
          <div className={styles.stackRow}>
            <StatusChip
              label={selectedFile.isBinary ? "binary" : "read-only text"}
              tone={selectedFile.isBinary ? "warn" : "good"}
            />
            {selectedFile.truncated ? <StatusChip label="truncated" tone="warn" /> : null}
            <span className={styles.mutedText}>{selectedFile.path}</span>
          </div>
          <div className={styles.inlineActions}>
            <button type="button" onClick={insertSelectedFileContext}>
              Attach to composer
            </button>
            <button type="button" onClick={() => openReviewForFile(selectedFile)}>
              Send for review
            </button>
            <button type="button" onClick={() => setDiffLeftPath(selectedFile.path)}>
              Use as left diff
            </button>
            <button type="button" onClick={() => setDiffRightPath(selectedFile.path)}>
              Use as right diff
            </button>
            <button
              type="button"
              onClick={() =>
                void copyText(selectedFile.isBinary ? selectedFile.preview : selectedFile.text)
              }
            >
              Copy
            </button>
          </div>
          <div className={styles.metaGrid}>
            <MetaRow label="Size" value={formatBytes(selectedFile.size)} />
            <MetaRow label="Lines" value={selectedFile.lineCount} />
            <MetaRow
              label="SHA256"
              value={<span className={styles.monoText}>{selectedFile.sha256.slice(0, 16)}…</span>}
            />
          </div>
          <pre className={styles.codeBlock}>{selectedFile.preview}</pre>
        </div>
      );
    }

    if (contextTab === "diff") {
      return (
        <div className={styles.tabPanelBody}>
          <div className={styles.fieldGrid}>
            <label className={styles.fieldLabel}>
              Left path
              <input
                value={diffLeftPath}
                onChange={(event) => setDiffLeftPath(event.target.value)}
                placeholder="repo-relative path"
              />
            </label>
            <label className={styles.fieldLabel}>
              Right path
              <input
                value={diffRightPath}
                onChange={(event) => setDiffRightPath(event.target.value)}
                placeholder="repo-relative path"
              />
            </label>
          </div>
          <div className={styles.inlineActions}>
            <button
              type="button"
              onClick={() => void computeDiff()}
              disabled={!diffLeftPath || !diffRightPath}
            >
              Compute diff
            </button>
            <button type="button" onClick={insertDiffContext} disabled={!diffDocument}>
              Attach to composer
            </button>
            <button
              type="button"
              onClick={() => diffDocument && openReviewForDiff(diffDocument)}
              disabled={!diffDocument}
            >
              Send diff for review
            </button>
          </div>
          {diffDocument ? (
            <>
              <div className={styles.stackRow}>
                <StatusChip
                  label={diffDocument.identical ? "identical" : "changed"}
                  tone={diffDocument.identical ? "good" : "warn"}
                />
                <span className={styles.mutedText}>
                  {diffDocument.leftPath} → {diffDocument.rightPath}
                </span>
              </div>
              <div className={styles.metaGrid}>
                <MetaRow label="Additions" value={diffDocument.summary.additions} />
                <MetaRow label="Removals" value={diffDocument.summary.removals} />
                <MetaRow label="Hunks" value={diffDocument.summary.hunks} />
              </div>
              <div className={styles.diffBlock}>
                {diffDocument.lines.slice(0, 500).map((line, index) => (
                  <div
                    key={`${index}:${line.text}`}
                    className={styles.diffLine}
                    data-kind={line.kind}
                  >
                    {line.text}
                  </div>
                ))}
              </div>
              {diffDocument.lines.length > 500 ? (
                <p className={styles.mutedText}>Showing first 500 diff lines.</p>
              ) : null}
            </>
          ) : (
            <p className={styles.placeholderText}>
              Select two repo-relative files to compare them in a bounded read-only diff surface.
            </p>
          )}
        </div>
      );
    }

    if (contextTab === "terminal") {
      return (
        <div className={styles.tabPanelBody}>
          <div className={styles.inlineActions}>
            <label className={styles.inlineSelect}>
              Command
              <select
                value={terminalCommand}
                onChange={(event) => setTerminalCommand(event.target.value as TerminalCommandId)}
              >
                {TERMINAL_COMMAND_IDS.map((commandId) => (
                  <option key={commandId} value={commandId}>
                    {commandId}
                  </option>
                ))}
              </select>
            </label>
            <button type="button" onClick={() => void loadTerminal(terminalCommand, selectedWorkingPath)}>
              Refresh terminal lane
            </button>
          </div>
          {terminalSnapshot ? (
            <>
              <div className={styles.stackRow}>
                <StatusChip
                  label={terminalSnapshot.status}
                  tone={terminalSnapshot.status === "ready" ? "good" : "critical"}
                />
                <span className={styles.mutedText}>
                  {terminalSnapshot.title} · cwd {terminalSnapshot.cwd}
                </span>
              </div>
              <pre className={styles.codeBlock}>{terminalSnapshot.lines.join("\n")}</pre>
            </>
          ) : (
            <p className={styles.placeholderText}>
              The terminal lane is explicit and read-only until a command is selected.
            </p>
          )}
        </div>
      );
    }

    if (contextTab === "git") {
      return (
        <div className={styles.tabPanelBody}>
          <div className={styles.inlineActions}>
            <button type="button" onClick={() => void loadGit()}>
              Refresh git
            </button>
          </div>
          {gitSnapshot ? (
            <>
              <div className={styles.stackRow}>
                <StatusChip
                  label={gitSnapshot.status}
                  tone={
                    gitSnapshot.status === "ready"
                      ? "good"
                      : gitSnapshot.status === "unavailable"
                        ? "warn"
                        : "critical"
                  }
                />
                <span className={styles.mutedText}>
                  {gitSnapshot.branch
                    ? `${gitSnapshot.branch} @ ${gitSnapshot.head ?? "n/a"}`
                    : gitSnapshot.summary}
                </span>
              </div>
              <p className={styles.summaryText}>{gitSnapshot.summary}</p>
              <div className={styles.splitList}>
                <div className={styles.cardSection}>
                  <h4>Status</h4>
                  <pre className={styles.codeBlock}>
                    {gitSnapshot.statusLines.join("\n") || "No status lines."}
                  </pre>
                </div>
                <div className={styles.cardSection}>
                  <h4>Recent commits</h4>
                  <pre className={styles.codeBlock}>
                    {gitSnapshot.recentCommits.join("\n") || "No commit metadata available."}
                  </pre>
                </div>
              </div>
            </>
          ) : (
            <p className={styles.placeholderText}>
              Git status stays a bounded summary, not a full git client.
            </p>
          )}
        </div>
      );
    }

    if (contextTab === "review") {
      return (
        <div className={styles.tabPanelBody}>
          <div className={styles.inlineActions}>
            <button
              type="button"
              onClick={() => reviewOrigin && void dispatchReview()}
              disabled={!reviewOrigin}
            >
              Dispatch current review
            </button>
            <button
              type="button"
              onClick={() => setReviewOrigin(null)}
              disabled={!reviewOrigin}
            >
              Clear pending target
            </button>
          </div>
          {reviewOrigin ? (
            <div className={styles.pendingBox}>
              <div className={styles.stackRow}>
                <StatusChip label={`pending ${reviewOrigin.originKind}`} tone="warn" />
                <span className={styles.mutedText}>{reviewOrigin.title}</span>
              </div>
              <p className={styles.summaryText}>{clipText(reviewOrigin.content, 360)}</p>
            </div>
          ) : null}
          {reviewRecords.length > 0 ? (
            reviewRecords.map((record) => (
              <div key={record.id} className={styles.recordCard}>
                <div className={styles.stackRow}>
                  <StatusChip
                    label={`${record.targetProfile} · ${record.status}`}
                    tone={
                      record.status === "completed" || record.status === "exported"
                        ? "good"
                        : record.status === "running"
                          ? "warn"
                          : "critical"
                    }
                  />
                  <span className={styles.mutedText}>{record.title}</span>
                </div>
                <p className={styles.summaryText}>{record.summary}</p>
                <div className={styles.metaGrid}>
                  <MetaRow label="Request" value={record.requestId} />
                  <MetaRow label="Created" value={formatTimestamp(record.createdAt)} />
                  <MetaRow
                    label="Origin"
                    value={`${record.originKind}:${record.originRef}`}
                  />
                </div>
                <div className={styles.inlineActions}>
                  <button type="button" onClick={() => void copyText(record.packetJson)}>
                    Copy packet
                  </button>
                  <button
                    type="button"
                    onClick={() => record.evidenceId && void copyText(record.evidenceId)}
                    disabled={!record.evidenceId}
                  >
                    Copy evidence id
                  </button>
                </div>
                <details className={styles.detailsBlock}>
                  <summary>Dispatch packet</summary>
                  <pre className={styles.codeBlock}>{record.packetJson}</pre>
                </details>
                <EvidenceBlock evidence={record.evidence} />
              </div>
            ))
          ) : (
            <p className={styles.placeholderText}>
              No review dispatches yet. Send a reply, file, or diff for advisory review.
            </p>
          )}
        </div>
      );
    }

    return (
      <div className={styles.tabPanelBody}>
        <div className={styles.fieldGrid}>
          <label className={styles.fieldLabel}>
            Workflow template
            <select value={templateId} onChange={(event) => setTemplateId(event.target.value)}>
              {templates.length > 0 ? (
                templates.map((template) => (
                  <option key={template.template_id} value={template.template_id}>
                    {template.template_id}
                  </option>
                ))
              ) : (
                <option value={templateId}>{templateId}</option>
              )}
            </select>
          </label>
          <label className={styles.fieldLabel}>
            Launch intent
            <textarea
              value={workflowPrompt}
              onChange={(event) => setWorkflowPrompt(event.target.value)}
              className={styles.shortTextarea}
            />
          </label>
        </div>
        <div className={styles.inlineActions}>
          <button type="button" onClick={() => void runWorkflow()}>
            Run ADEU workflow
          </button>
          <button type="button" onClick={() => void refreshTemplates()}>
            Refresh templates
          </button>
        </div>
        {workflowRuns.length > 0 ? (
          workflowRuns.map((run) => (
            <div key={run.id} className={styles.recordCard}>
              <div className={styles.stackRow}>
                <StatusChip
                  label={`${run.templateId} · ${run.status}`}
                  tone={
                    run.status === "completed"
                      ? "good"
                      : run.status === "running"
                        ? "warn"
                        : "critical"
                  }
                />
                <span className={styles.mutedText}>{formatTimestamp(run.createdAt)}</span>
              </div>
              <p className={styles.summaryText}>{run.summary}</p>
              <details className={styles.detailsBlock}>
                <summary>Launch prompt</summary>
                <pre className={styles.codeBlock}>{run.prompt}</pre>
              </details>
              <EvidenceBlock evidence={run.evidence} />
            </div>
          ))
        ) : (
          <p className={styles.placeholderText}>
            No workflow runs yet. Launch one from the dock to keep evidence same-context reachable.
          </p>
        )}
      </div>
    );
  };

  return (
    <div
      className={styles.pageRoot}
      data-route-id={CODEX_WORKBENCH_ROUTE_ID}
      data-workbench-id={CODEX_WORKBENCH_ID}
      data-approved-profile-id={CODEX_WORKBENCH_PROFILE_ID}
    >
      <header className={styles.boundaryStrip}>
        <div className={styles.boundaryHeader}>
          <div>
            <p className={styles.eyebrow}>ADEU desktop reference</p>
            <h1 className={styles.title}>ADEU Codex Desktop Workbench</h1>
            <p className={styles.subtitle}>
              Transcript-first, same-context evidence, and explicit handoff boundaries for review and workflow execution.
            </p>
          </div>
          <div className={styles.headerLinks}>
            <Link href="/" className={styles.headerLink}>
              Studio
            </Link>
            <Link href="/copilot" className={styles.headerLink}>
              Copilot
            </Link>
            <button type="button" onClick={() => void refreshRuntime()} disabled={isBusy}>
              Refresh
            </button>
            <button type="button" onClick={() => setShowHarnessInspector(true)}>
              Harness / Config
            </button>
          </div>
        </div>

        <div className={styles.boundaryMetrics}>
          <div className={styles.metricCard}>
            <div className={styles.stackRow}>
              <StatusChip
                label={sessionStatus}
                tone={
                  sessionStatus === "running"
                    ? "good"
                    : sessionStatus === "failed"
                      ? "critical"
                      : "warn"
                }
              />
              <StatusChip
                label={connectionStatus}
                tone={
                  connectionStatus === "connected"
                    ? "good"
                    : connectionStatus === "connecting"
                      ? "warn"
                      : "neutral"
                }
              />
            </div>
            <div className={styles.metricValue}>
              {sessionId ? summarizePath(sessionId, 1) : "no session"}
            </div>
            <div className={styles.metricLabel}>Session / SSE</div>
          </div>

          <div className={styles.metricCard}>
            <div className={styles.stackRow}>
              <StatusChip
                label={writesAllowed ? "writes enabled" : "read-only"}
                tone={writesAllowed ? "critical" : "good"}
              />
              <StatusChip
                label={apiReachable ? "API reachable" : "API down"}
                tone={apiReachable ? "good" : "critical"}
              />
            </div>
            <div className={styles.metricValue}>{selectedProfileId}</div>
            <div className={styles.metricLabel}>Selected policy profile</div>
          </div>

          <div className={styles.metricCard}>
            <div className={styles.stackRow}>
              <StatusChip
                label={workerOnlyMode ? "worker-only" : "app-server"}
                tone={workerOnlyMode ? "warn" : "good"}
              />
              <StatusChip
                label={appState?.codex_exec_available ? "exec available" : "exec unknown"}
                tone={appState?.codex_exec_available ? "good" : "neutral"}
              />
            </div>
            <div className={styles.metricValue}>
              {harness?.codexBinResolved
                ? summarizePath(harness.codexBinResolved, 3)
                : harness?.codexBinConfigured ?? "codex"}
            </div>
            <div className={styles.metricLabel}>Codex binary / build identity</div>
          </div>

          <div className={styles.metricCard}>
            <div className={styles.stackRow}>
              <StatusChip
                label={reviewRecords.length ? `${reviewRecords.length} reviews` : "no reviews"}
                tone={reviewRecords.length ? "warn" : "neutral"}
              />
              <StatusChip
                label={workflowRuns.length ? `${workflowRuns.length} workflows` : "no workflows"}
                tone={workflowRuns.length ? "warn" : "neutral"}
              />
            </div>
            <div className={styles.metricValue}>
              {harness?.activeConfigSource ?? "config pending"}
            </div>
            <div className={styles.metricLabel}>Config provenance</div>
          </div>
        </div>

        {error ? <div className={styles.errorBanner}>Error: {error}</div> : null}
      </header>

      <div className={styles.appFrame}>
        <aside className={styles.workspaceLane}>
          <section className={styles.panelCard}>
            <div className={styles.panelHeader}>
              <div>
                <p className={styles.panelEyebrow}>Sessions</p>
                <h2 className={styles.panelTitle}>Recent chats</h2>
              </div>
              <div className={styles.inlineActions}>
                <button
                  type="button"
                  onClick={() => void startSession()}
                  disabled={isBusy || sessionStatus === "running" || sessionStatus === "starting"}
                >
                  Start
                </button>
                <button
                  type="button"
                  onClick={() => void stopSession()}
                  disabled={isBusy || !sessionId}
                >
                  Stop
                </button>
              </div>
            </div>
            <div className={styles.inlineActions}>
              <label className={styles.inlineSelect}>
                Profile
                <select
                  value={selectedProfileId}
                  onChange={(event) => setSelectedProfileId(event.target.value)}
                >
                  {profiles.length > 0 ? (
                    profiles.map((profile) => (
                      <option key={profile.profile_id} value={profile.profile_id}>
                        {profile.profile_id}
                      </option>
                    ))
                  ) : (
                    <option value={selectedProfileId}>{selectedProfileId}</option>
                  )}
                </select>
              </label>
              <button type="button" onClick={() => void restartSessionWithProfile()} disabled={isBusy}>
                Restart
              </button>
              <button
                type="button"
                onClick={() => void applyProfileToSession()}
                disabled={isBusy || !sessionId}
              >
                Apply
              </button>
              <button type="button" onClick={() => void toggleWrites()} disabled={isBusy || !sessionId}>
                {writesAllowed ? "Read-only" : "Enable Writes"}
              </button>
            </div>
            <div className={styles.sessionList}>
              {sessionHistory.length > 0 ? (
                sessionHistory.map((entry) => (
                  <button key={entry.sessionId} type="button" className={styles.sessionCard}>
                    <div className={styles.stackRow}>
                      <StatusChip
                        label={entry.status}
                        tone={
                          entry.status === "running"
                            ? "good"
                            : entry.status === "failed"
                              ? "critical"
                              : "neutral"
                        }
                      />
                      <span className={styles.mutedText}>{entry.profileId}</span>
                    </div>
                    <div className={styles.sessionPrimary}>{summarizePath(entry.sessionId, 1)}</div>
                    <div className={styles.sessionMeta}>{formatTimestamp(entry.startedAt)}</div>
                  </button>
                ))
              ) : (
                <p className={styles.placeholderText}>
                  Session history appears here after you start a Codex session.
                </p>
              )}
            </div>
          </section>

          <section className={styles.panelCard}>
            <div className={styles.panelHeader}>
              <div>
                <p className={styles.panelEyebrow}>Workspace</p>
                <h2 className={styles.panelTitle}>Project tree</h2>
              </div>
              <div className={styles.inlineActions}>
                <label className={styles.inlineSelect}>
                  Root
                  <select
                    value={workspaceRoot}
                    onChange={(event) => setWorkspaceRoot(event.target.value as WorkspaceRootOption)}
                  >
                    {WORKSPACE_ROOT_OPTIONS.map((option) => (
                      <option key={option || "repo-root"} value={option}>
                        {option || "repo root"}
                      </option>
                    ))}
                  </select>
                </label>
                <button type="button" onClick={() => void loadDirectory(workspaceRoot)}>
                  Refresh tree
                </button>
              </div>
            </div>
            <div className={styles.workspaceSummary}>
              <div className={styles.metaGrid}>
                <MetaRow label="Visible entries" value={currentDirectoryEntries.length} />
                <MetaRow
                  label="Selected file"
                  value={selectedFile ? summarizePath(selectedFile.path) : "none"}
                />
                <MetaRow label="Left diff" value={diffLeftPath ? summarizePath(diffLeftPath) : "none"} />
                <MetaRow label="Right diff" value={diffRightPath ? summarizePath(diffRightPath) : "none"} />
              </div>
            </div>
            <div className={styles.fileTree}>{renderTreeEntries(currentDirectoryEntries)}</div>
          </section>
        </aside>

        <main className={styles.conversationLane}>
          <section className={styles.panelCard}>
            <div className={styles.panelHeader}>
              <div>
                <p className={styles.panelEyebrow}>Conversation</p>
                <h2 className={styles.panelTitle}>Transcript</h2>
              </div>
              <div className={styles.inlineActions}>
                <button type="button" onClick={() => setContextTab("review")}>
                  Review inbox
                </button>
                <button type="button" onClick={() => setContextTab("workflow")}>
                  Workflow dock
                </button>
              </div>
            </div>
            <div className={styles.transcriptSurface}>
              {transcript.map((item) => {
                const reviewCount = reviewCountByOrigin.get(`reply:${item.id}`) ?? 0;
                return (
                  <article key={item.id} className={styles.transcriptItem} data-role={item.role}>
                    <div className={styles.transcriptMeta}>
                      <div className={styles.stackRow}>
                        <StatusChip
                          label={item.role}
                          tone={
                            item.role === "assistant"
                              ? "good"
                              : item.role === "user"
                                ? "warn"
                                : "neutral"
                          }
                        />
                        <StatusChip
                          label={item.status}
                          tone={
                            item.status === "done"
                              ? "good"
                              : item.status === "failed"
                                ? "critical"
                                : item.status === "streaming"
                                  ? "warn"
                                  : "neutral"
                          }
                        />
                        {reviewCount > 0 ? (
                          <StatusChip label={`${reviewCount} review`} tone="warn" />
                        ) : null}
                      </div>
                      <span className={styles.mutedText}>{formatTimestamp(item.createdAt)}</span>
                    </div>
                    <pre className={styles.transcriptBody}>{item.text}</pre>
                    <div className={styles.transcriptActions}>
                      <button type="button" onClick={() => quoteTranscriptItem(item)}>
                        Quote
                      </button>
                      <button type="button" onClick={() => void copyText(item.text)}>
                        Copy
                      </button>
                      <button type="button" onClick={() => setReviewOrigin(buildTranscriptOrigin(item))}>
                        Send For Review
                      </button>
                    </div>
                  </article>
                );
              })}
            </div>
          </section>

          <section className={styles.panelCard}>
            <div className={styles.panelHeader}>
              <div>
                <p className={styles.panelEyebrow}>Composer</p>
                <h2 className={styles.panelTitle}>Prompt entry</h2>
              </div>
              <div className={styles.inlineActions}>
                <button type="button" onClick={() => setContextTab("files")}>
                  Files
                </button>
                <button type="button" onClick={() => setContextTab("diff")}>
                  Diff
                </button>
                <button type="button" onClick={() => setContextTab("terminal")}>
                  Terminal
                </button>
                <button type="button" onClick={() => setContextTab("git")}>
                  Git
                </button>
                <button type="button" onClick={() => setContextTab("workflow")}>
                  Workflow
                </button>
              </div>
            </div>
            <textarea
              value={messageText}
              onChange={(event) => setMessageText(event.target.value)}
              placeholder="Send a message into the active Codex session. You can attach file or diff context explicitly first."
              className={styles.composerArea}
            />
            <div className={styles.inlineActions}>
              <button type="button" onClick={insertSelectedFileContext} disabled={!selectedFile}>
                Attach file
              </button>
              <button type="button" onClick={insertDiffContext} disabled={!diffDocument}>
                Attach diff
              </button>
              <button
                type="button"
                onClick={() => selectedFile && openReviewForFile(selectedFile)}
                disabled={!selectedFile}
              >
                Review file
              </button>
              <button
                type="button"
                onClick={() => diffDocument && openReviewForDiff(diffDocument)}
                disabled={!diffDocument}
              >
                Review diff
              </button>
              <button type="button" onClick={() => setContextTab("workflow")}>
                Open workflow dock
              </button>
              <button
                type="button"
                onClick={() => void sendMessage()}
                disabled={isBusy || !sessionId || !messageText.trim()}
              >
                Send
              </button>
            </div>
            <div className={styles.composerMeta}>
              <span className={styles.mutedText}>
                last heartbeat: {lastHeartbeatAt ? formatTimestamp(lastHeartbeatAt) : "n/a"}
              </span>
              <span className={styles.mutedText}>provider: codex</span>
              <span className={styles.mutedText}>route: {CODEX_WORKBENCH_ROUTE_ID}</span>
            </div>
          </section>
        </main>

        <aside className={styles.contextLane}>
          <section className={styles.panelCard}>
            <div className={styles.panelHeader}>
              <div>
                <p className={styles.panelEyebrow}>Context artifacts</p>
                <h2 className={styles.panelTitle}>Docked bounded artifacts</h2>
              </div>
            </div>
            <div className={styles.tabBar}>
              {CONTEXT_ARTIFACT_TABS.map((tab) => (
                <button
                  key={tab}
                  type="button"
                  className={styles.tabButton}
                  data-active={contextTab === tab ? "true" : undefined}
                  onClick={() => setContextTab(tab)}
                >
                  {tab}
                </button>
              ))}
            </div>
            <div className={styles.tabPanel}>{renderArtifactContent()}</div>
          </section>
        </aside>
      </div>

      <section className={styles.noticesRow}>
        {notices.map((notice) => (
          <article key={notice.id} className={styles.noticeCard} data-tone={notice.tone}>
            <div className={styles.stackRow}>
              <StatusChip label={notice.title} tone={notice.tone} />
            </div>
            <p>{notice.detail}</p>
          </article>
        ))}
      </section>

      {peekFile ? (
        <div className={styles.overlayBackdrop} role="presentation">
          <div className={styles.overlayCard} role="dialog" aria-modal="true">
            <div className={styles.overlayHeader}>
              <div>
                <p className={styles.panelEyebrow}>Quick peek</p>
                <h3 className={styles.overlayTitle}>{peekFile.path}</h3>
              </div>
              <button type="button" onClick={() => setPeekFile(null)}>
                Close
              </button>
            </div>
            <div className={styles.inlineActions}>
              <button
                type="button"
                onClick={() => {
                  setSelectedFile(peekFile);
                  setContextTab("files");
                  setPeekFile(null);
                }}
              >
                Open in context pane
              </button>
              <button
                type="button"
                onClick={() => {
                  openReviewForFile(peekFile);
                  setPeekFile(null);
                }}
              >
                Send for review
              </button>
            </div>
            <pre className={styles.codeBlock}>{peekFile.preview}</pre>
          </div>
        </div>
      ) : null}

      {showHarnessInspector ? (
        <div className={styles.overlayBackdrop} role="presentation">
          <div className={styles.overlayCard} role="dialog" aria-modal="true">
            <div className={styles.overlayHeader}>
              <div>
                <p className={styles.panelEyebrow}>Harness and config surface</p>
                <h3 className={styles.overlayTitle}>Build / config / evidence wiring</h3>
              </div>
              <button type="button" onClick={() => setShowHarnessInspector(false)}>
                Close
              </button>
            </div>
            {harness ? (
              <div className={styles.overlayBody}>
                <div className={styles.metaGrid}>
                  <MetaRow label="Repo root" value={harness.repoRoot} />
                  <MetaRow label="Codex bin configured" value={harness.codexBinConfigured} />
                  <MetaRow label="Codex bin resolved" value={harness.codexBinResolved ?? "not found"} />
                  <MetaRow label="Model" value={harness.codexModel ?? "n/a"} />
                  <MetaRow label="Active config" value={harness.activeConfigPath ?? "n/a"} />
                  <MetaRow label="Evidence root" value={harness.evidenceRoot ?? "n/a"} />
                </div>
                <div className={styles.inlineActions}>
                  {activeConfigRepoPath ? (
                    <button
                      type="button"
                      onClick={() => {
                        void selectFile(activeConfigRepoPath);
                        setShowHarnessInspector(false);
                      }}
                    >
                      Open active config in reader
                    </button>
                  ) : null}
                  <button type="button" onClick={() => void loadHarness()}>
                    Refresh harness
                  </button>
                </div>
                <div className={styles.splitList}>
                  <div className={styles.cardSection}>
                    <h4>Config candidates</h4>
                    <div className={styles.recordList}>
                      {harness.configTomlCandidates.map((candidate) => (
                        <div key={candidate.path} className={styles.recordCard}>
                          <div className={styles.stackRow}>
                            <StatusChip
                              label={candidate.exists ? "exists" : "missing"}
                              tone={candidate.exists ? "good" : "warn"}
                            />
                            <span className={styles.mutedText}>{candidate.label}</span>
                          </div>
                          <p className={styles.summaryText}>{candidate.path}</p>
                          {candidate.exists ? (
                            <button
                              type="button"
                              onClick={() => {
                                const repoPath = toRepoRelativePath(candidate.path, harness);
                                if (!repoPath) return;
                                void selectFile(repoPath);
                                setShowHarnessInspector(false);
                              }}
                            >
                              Open in reader
                            </button>
                          ) : null}
                        </div>
                      ))}
                    </div>
                  </div>
                  <div className={styles.cardSection}>
                    <h4>Environment summary</h4>
                    <pre className={styles.codeBlock}>{stringify(harness.envSummary)}</pre>
                  </div>
                </div>
              </div>
            ) : (
              <p className={styles.placeholderText}>Harness summary unavailable.</p>
            )}
          </div>
        </div>
      ) : null}

      {reviewOrigin ? (
        <div className={styles.overlayBackdrop} role="presentation">
          <div className={styles.overlayCard} role="dialog" aria-modal="true">
            <div className={styles.overlayHeader}>
              <div>
                <p className={styles.panelEyebrow}>Review routing surface</p>
                <h3 className={styles.overlayTitle}>{reviewOrigin.title}</h3>
              </div>
              <button type="button" onClick={() => setReviewOrigin(null)}>
                Close
              </button>
            </div>
            <div className={styles.overlayBody}>
              <div className={styles.metaGrid}>
                <MetaRow label="Origin kind" value={reviewOrigin.originKind} />
                <MetaRow label="Origin ref" value={reviewOrigin.originRef} />
                <MetaRow label="Chars" value={reviewOrigin.content.length} />
                <MetaRow label="Target" value={reviewTargetProfile} />
              </div>
              <div className={styles.fieldGrid}>
                <label className={styles.fieldLabel}>
                  Target profile
                  <select
                    value={reviewTargetProfile}
                    onChange={(event) => setReviewTargetProfile(event.target.value as ReviewTargetProfile)}
                  >
                    {REVIEW_TARGET_PROFILES.map((profile) => (
                      <option key={profile} value={profile}>
                        {profile}
                      </option>
                    ))}
                  </select>
                </label>
                <label className={styles.fieldLabel}>
                  Dispatch note
                  <textarea
                    value={reviewNote}
                    onChange={(event) => setReviewNote(event.target.value)}
                    className={styles.shortTextarea}
                    placeholder="Optional operator note for the advisory review."
                  />
                </label>
              </div>
              <p className={styles.summaryText}>{clipText(reviewOrigin.content, 420)}</p>
              <details className={styles.detailsBlock}>
                <summary>Origin provenance</summary>
                <pre className={styles.codeBlock}>{stringify(reviewOrigin.provenance)}</pre>
              </details>
              <div className={styles.inlineActions}>
                <button type="button" onClick={() => void dispatchReview()}>
                  {reviewTargetProfile === "export_packet" ? "Export packet" : "Launch review"}
                </button>
                <button type="button" onClick={() => setReviewOrigin(null)}>
                  Cancel
                </button>
              </div>
            </div>
          </div>
        </div>
      ) : null}
    </div>
  );
}
