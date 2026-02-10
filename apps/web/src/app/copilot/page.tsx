"use client";

import Link from "next/link";
import { useEffect, useMemo, useRef, useState } from "react";

import { apiBase } from "../lib/api-base";

type CopilotStatus = "idle" | "starting" | "running" | "stopped" | "failed";
type ConnectionStatus = "disconnected" | "connecting" | "connected";

type CopilotSessionResponse = {
  session_id: string;
  status: "starting" | "running" | "stopped" | "failed";
  app_server_unavailable: boolean;
  idempotent_replay: boolean;
};

type ToolCallResponse = {
  tool_name: string;
  warrant: "observed" | "derived" | "checked" | "hypothesis" | "unknown";
  result: unknown;
};

type TimelineEntry = {
  id: string;
  at: string;
  channel: "sse" | "local";
  event: string;
  summary: string;
  payload?: unknown;
};

type EvidenceBundle = {
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

type AppStateSnapshot = {
  counts: Record<string, number>;
  active_copilot_session_id?: string | null;
  active_copilot_writes_allowed: boolean;
  codex_version?: string | null;
  codex_exec_available?: boolean | null;
  codex_app_server_available?: boolean | null;
};

type TemplateMeta = {
  template_id: string;
  template_version: string;
  schema_version: string;
  domain_pack_id: string;
  domain_pack_version: string;
  role: string;
  description: string;
};

type SSECodexEvent = {
  seq?: number;
  ts?: string;
  event_kind?: string;
  payload?: Record<string, unknown>;
  raw_line?: string;
};

type SESSessionStatus = {
  session_id?: string;
  status?: string;
  last_seq?: number;
  error?: unknown;
};

const TOOL_ALLOWLIST = [
  "adeu.get_app_state",
  "adeu.list_templates",
  "adeu.run_workflow",
  "adeu.read_evidence",
  "urm.spawn_worker",
  "urm.set_mode",
] as const;

const DEFAULT_TEMPLATE_ID = "adeu.workflow.pipeline_worker.v0";
const TIMELINE_LIMIT = 500;

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

async function parseErrorMessage(response: Response): Promise<string> {
  const text = await response.text();
  if (!text) return `HTTP ${response.status}`;
  try {
    const parsed = JSON.parse(text) as {
      detail?: { code?: string; message?: string };
      message?: string;
      error?: string;
    };
    const detail = parsed.detail;
    if (detail?.code && detail.message) {
      return `${detail.code}: ${detail.message}`;
    }
    if (typeof parsed.message === "string") return parsed.message;
    if (typeof parsed.error === "string") return parsed.error;
  } catch {
    // fall through
  }
  return text;
}

export default function CopilotPage() {
  const [sessionId, setSessionId] = useState<string | null>(null);
  const [status, setStatus] = useState<CopilotStatus>("idle");
  const [connection, setConnection] = useState<ConnectionStatus>("disconnected");
  const [writesAllowed, setWritesAllowed] = useState<boolean>(false);
  const [workerOnlyMode, setWorkerOnlyMode] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);
  const [messageText, setMessageText] = useState<string>("");
  const [workerPrompt, setWorkerPrompt] = useState<string>("Run a quick read-only sanity check.");
  const [templateId, setTemplateId] = useState<string>(DEFAULT_TEMPLATE_ID);
  const [templates, setTemplates] = useState<TemplateMeta[]>([]);
  const [appState, setAppState] = useState<AppStateSnapshot | null>(null);
  const [evidenceId, setEvidenceId] = useState<string>("");
  const [evidence, setEvidence] = useState<EvidenceBundle | null>(null);
  const [timeline, setTimeline] = useState<TimelineEntry[]>([]);
  const [isBusy, setIsBusy] = useState<boolean>(false);
  const [lastHeartbeatAt, setLastHeartbeatAt] = useState<string | null>(null);
  const lastSeqRef = useRef<number>(0);

  function pushTimeline(entry: Omit<TimelineEntry, "id" | "at">): void {
    const full: TimelineEntry = {
      id: requestId(),
      at: new Date().toISOString(),
      ...entry,
    };
    setTimeline((current) => {
      const next = [...current, full];
      if (next.length <= TIMELINE_LIMIT) return next;
      return next.slice(next.length - TIMELINE_LIMIT);
    });
  }

  async function startSession(): Promise<void> {
    setError(null);
    setIsBusy(true);
    try {
      const response = await fetch(`${apiBase()}/urm/copilot/start`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          provider: "codex",
          client_request_id: requestId(),
        }),
      });
      if (!response.ok) {
        const message = await parseErrorMessage(response);
        setError(message);
        if (message.includes("URM_CODEX_APP_SERVER_UNAVAILABLE")) {
          setWorkerOnlyMode(true);
        }
        return;
      }
      const body = (await response.json()) as CopilotSessionResponse;
      setSessionId(body.session_id);
      setStatus(body.status);
      setWorkerOnlyMode(body.app_server_unavailable);
      setWritesAllowed(false);
      lastSeqRef.current = 0;
      pushTimeline({
        channel: "local",
        event: "session_started",
        summary: `Session ${body.session_id} started (${body.status}).`,
      });
    } catch (exc) {
      setError(String(exc));
    } finally {
      setIsBusy(false);
    }
  }

  async function stopSession(): Promise<void> {
    if (!sessionId) return;
    setError(null);
    setIsBusy(true);
    try {
      const response = await fetch(`${apiBase()}/urm/copilot/stop`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ provider: "codex", session_id: sessionId }),
      });
      if (!response.ok) {
        setError(await parseErrorMessage(response));
        return;
      }
      const body = (await response.json()) as CopilotSessionResponse;
      setStatus(body.status);
      pushTimeline({
        channel: "local",
        event: "session_stopped",
        summary: `Session ${body.session_id} is ${body.status}.`,
      });
    } catch (exc) {
      setError(String(exc));
    } finally {
      setIsBusy(false);
    }
  }

  async function setMode(nextWritesAllowed: boolean): Promise<void> {
    if (!sessionId) return;
    setError(null);
    setIsBusy(true);
    try {
      const response = await fetch(`${apiBase()}/urm/copilot/mode`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          provider: "codex",
          session_id: sessionId,
          writes_allowed: nextWritesAllowed,
        }),
      });
      if (!response.ok) {
        setError(await parseErrorMessage(response));
        return;
      }
      setWritesAllowed(nextWritesAllowed);
      pushTimeline({
        channel: "local",
        event: "mode_changed",
        summary: `writes_allowed set to ${String(nextWritesAllowed)}.`,
      });
    } catch (exc) {
      setError(String(exc));
    } finally {
      setIsBusy(false);
    }
  }

  async function sendMessage(): Promise<void> {
    if (!sessionId || !messageText.trim()) return;
    setError(null);
    setIsBusy(true);
    try {
      const response = await fetch(`${apiBase()}/urm/copilot/send`, {
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
            params: { text: messageText.trim() },
          },
        }),
      });
      if (!response.ok) {
        setError(await parseErrorMessage(response));
        return;
      }
      pushTimeline({
        channel: "local",
        event: "message_sent",
        summary: `Sent user message (${messageText.trim().length} chars).`,
        payload: { text: messageText.trim() },
      });
      setMessageText("");
    } catch (exc) {
      setError(String(exc));
    } finally {
      setIsBusy(false);
    }
  }

  async function callTool(toolName: string, argumentsValue: Record<string, unknown>): Promise<unknown> {
    setError(null);
    const response = await fetch(`${apiBase()}/urm/tools/call`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        provider: "codex",
        role: "copilot",
        session_id: sessionId,
        tool_name: toolName,
        arguments: argumentsValue,
      }),
    });
    if (!response.ok) {
      throw new Error(await parseErrorMessage(response));
    }
    const body = (await response.json()) as ToolCallResponse;
    pushTimeline({
      channel: "local",
      event: `tool_call:${toolName}`,
      summary: `${toolName} -> warrant=${body.warrant}`,
      payload: body.result,
    });
    return body.result;
  }

  async function refreshAppState(): Promise<void> {
    setIsBusy(true);
    try {
      const result = (await callTool("adeu.get_app_state", {})) as AppStateSnapshot;
      setAppState(result);
    } catch (exc) {
      setError(String(exc));
    } finally {
      setIsBusy(false);
    }
  }

  async function refreshTemplates(): Promise<void> {
    setIsBusy(true);
    try {
      const result = (await callTool("adeu.list_templates", {})) as { templates?: TemplateMeta[] };
      const nextTemplates = result.templates ?? [];
      setTemplates(nextTemplates);
      if (nextTemplates.length > 0 && !nextTemplates.some((item) => item.template_id === templateId)) {
        setTemplateId(nextTemplates[0].template_id);
      }
    } catch (exc) {
      setError(String(exc));
    } finally {
      setIsBusy(false);
    }
  }

  async function runWorkflow(): Promise<void> {
    if (!workerPrompt.trim()) return;
    setIsBusy(true);
    try {
      const result = (await callTool("adeu.run_workflow", {
        template_id: templateId,
        inputs: { prompt: workerPrompt.trim() },
        mode: "read_only",
        client_request_id: requestId(),
      })) as { evidence_id?: string; worker_id?: string; status?: string };
      const nextEvidenceId = result.evidence_id;
      if (typeof nextEvidenceId === "string" && nextEvidenceId.length > 0) {
        setEvidenceId(nextEvidenceId);
        await loadEvidence(nextEvidenceId);
      }
    } catch (exc) {
      setError(String(exc));
    } finally {
      setIsBusy(false);
    }
  }

  async function loadEvidence(requestedEvidenceId?: string): Promise<void> {
    const targetEvidenceId = requestedEvidenceId ?? evidenceId.trim();
    if (!targetEvidenceId) return;
    setIsBusy(true);
    try {
      const result = (await callTool("adeu.read_evidence", {
        evidence_id: targetEvidenceId,
        max_bytes: 200_000,
      })) as EvidenceBundle;
      setEvidence(result);
    } catch (exc) {
      setError(String(exc));
    } finally {
      setIsBusy(false);
    }
  }

  useEffect(() => {
    if (!sessionId) {
      setConnection("disconnected");
      return;
    }
    setConnection("connecting");
    const url = `${apiBase()}/urm/copilot/events?provider=codex&session_id=${encodeURIComponent(sessionId)}&after_seq=0`;
    const stream = new EventSource(url);

    stream.onopen = () => {
      setConnection("connected");
    };

    stream.addEventListener("heartbeat", (event) => {
      setLastHeartbeatAt(new Date().toISOString());
      const payload = JSON.parse((event as MessageEvent).data) as { ts?: string };
      pushTimeline({
        channel: "sse",
        event: "heartbeat",
        summary: payload.ts ? `Heartbeat ${payload.ts}` : "Heartbeat",
      });
    });

    stream.addEventListener("codex_event", (event) => {
      const payload = JSON.parse((event as MessageEvent).data) as SSECodexEvent;
      const seq = typeof payload.seq === "number" ? payload.seq : null;
      if (seq !== null) {
        if (seq <= lastSeqRef.current) return;
        lastSeqRef.current = seq;
      }
      pushTimeline({
        channel: "sse",
        event: payload.event_kind ?? "codex_event",
        summary: `seq=${seq ?? "?"} ${payload.event_kind ?? "event"}`,
        payload,
      });
    });

    stream.addEventListener("session_status", (event) => {
      const payload = JSON.parse((event as MessageEvent).data) as SESSessionStatus;
      if (typeof payload.status === "string") {
        const nextStatus = payload.status as CopilotStatus;
        setStatus(nextStatus);
      }
      if (typeof payload.last_seq === "number" && payload.last_seq > lastSeqRef.current) {
        lastSeqRef.current = payload.last_seq;
      }
      pushTimeline({
        channel: "sse",
        event: "session_status",
        summary: `Session status: ${payload.status ?? "unknown"}`,
        payload,
      });
    });

    stream.onerror = () => {
      setConnection("disconnected");
    };

    return () => {
      stream.close();
      setConnection("disconnected");
    };
  }, [sessionId]);

  useEffect(() => {
    void refreshTemplates();
    void refreshAppState();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  const parsedEvidenceLines = useMemo(() => {
    const raw = evidence?.raw_jsonl ?? "";
    return raw
      .split("\n")
      .map((line) => line.trim())
      .filter((line) => line.length > 0)
      .slice(0, 200)
      .map((line, index) => {
        try {
          const parsed = JSON.parse(line) as Record<string, unknown>;
          const kind = typeof parsed.event === "string" ? parsed.event : typeof parsed.type === "string" ? parsed.type : "json";
          return {
            id: `${index + 1}`,
            kind,
            preview: stringify(parsed),
          };
        } catch {
          return {
            id: `${index + 1}`,
            kind: "raw",
            preview: line,
          };
        }
      });
  }, [evidence]);

  return (
    <div className="app">
      <div className="panel">
        <h2>Copilot Runtime</h2>
        <div className="row" style={{ marginBottom: 8 }}>
          <Link href="/" className="muted" style={{ marginLeft: "auto" }}>
            ADEU Studio
          </Link>
          <Link href="/concepts" className="muted">
            Concepts
          </Link>
          <Link href="/puzzles" className="muted">
            Puzzles
          </Link>
          <Link href="/papers" className="muted">
            Papers
          </Link>
          <Link href="/artifacts" className="muted">
            Artifacts
          </Link>
        </div>

        {workerOnlyMode ? (
          <div className="muted" style={{ marginBottom: 8 }}>
            Worker-only mode: app-server is unavailable for this Codex install.
          </div>
        ) : null}
        {error ? <div className="muted">Error: {error}</div> : null}

        <div className="row" style={{ marginTop: 8 }}>
          <span className="muted">session</span>
          <span className="mono">{sessionId ?? "none"}</span>
        </div>
        <div className="row">
          <span className="muted">status</span>
          <span className="mono">{status}</span>
          <span className="muted">SSE</span>
          <span className="mono">{connection}</span>
        </div>
        <div className="row">
          <span className="muted">writes_allowed</span>
          <span className="mono">{String(writesAllowed)}</span>
          <span className="muted">last_heartbeat</span>
          <span className="mono">{lastHeartbeatAt ?? "n/a"}</span>
        </div>

        <div className="row" style={{ marginTop: 8 }}>
          <button onClick={() => void startSession()} disabled={isBusy || status === "running" || status === "starting"}>
            Start Copilot
          </button>
          <button onClick={() => void stopSession()} disabled={isBusy || !sessionId}>
            Stop
          </button>
          <button onClick={() => void setMode(!writesAllowed)} disabled={isBusy || !sessionId}>
            {writesAllowed ? "Set Read-Only" : "Enable Writes"}
          </button>
        </div>

        <textarea
          value={messageText}
          onChange={(event) => setMessageText(event.target.value)}
          placeholder="Send a message payload through codex app-server..."
          style={{ minHeight: 90, marginTop: 8 }}
        />
        <div className="row">
          <button onClick={() => void sendMessage()} disabled={isBusy || !sessionId || !messageText.trim()}>
            Send Message
          </button>
        </div>

        <div className="row" style={{ marginTop: 8 }}>
          <span className="muted">Capabilities</span>
          <span className="mono">role=copilot</span>
          <span className="mono">provider=codex</span>
        </div>
        <pre>{stringify(TOOL_ALLOWLIST)}</pre>
      </div>

      <div className="panel">
        <h2>Tool Actions</h2>
        <div className="row" style={{ marginBottom: 8 }}>
          <button onClick={() => void refreshAppState()} disabled={isBusy}>
            adeu.get_app_state
          </button>
          <button onClick={() => void refreshTemplates()} disabled={isBusy}>
            adeu.list_templates
          </button>
        </div>

        <div className="row">
          <label className="muted">
            template_id{" "}
            <select value={templateId} onChange={(event) => setTemplateId(event.target.value)}>
              {(templates.length > 0 ? templates : [{ template_id: DEFAULT_TEMPLATE_ID } as TemplateMeta]).map(
                (item) => (
                  <option key={item.template_id} value={item.template_id}>
                    {item.template_id}
                  </option>
                )
              )}
            </select>
          </label>
        </div>
        <textarea
          value={workerPrompt}
          onChange={(event) => setWorkerPrompt(event.target.value)}
          placeholder="Worker prompt"
          style={{ minHeight: 90, marginTop: 8 }}
        />
        <div className="row">
          <button onClick={() => void runWorkflow()} disabled={isBusy || !workerPrompt.trim()}>
            adeu.run_workflow
          </button>
        </div>

        <div className="row" style={{ marginTop: 8 }}>
          <label className="muted">
            evidence_id{" "}
            <input
              value={evidenceId}
              onChange={(event) => setEvidenceId(event.target.value)}
              placeholder="Evidence id..."
            />
          </label>
          <button onClick={() => void loadEvidence()} disabled={isBusy || !evidenceId.trim()}>
            adeu.read_evidence
          </button>
        </div>

        <div className="row" style={{ marginTop: 8 }}>
          <span className="muted">Current app state</span>
        </div>
        <pre>{appState ? stringify(appState) : "No app-state snapshot yet."}</pre>
      </div>

      <div className="panel">
        <h2>Timeline + Evidence</h2>
        <div className="muted">Timeline entries: {timeline.length}</div>
        <pre>
          {timeline.length > 0
            ? stringify(
                timeline.map((item) => ({
                  at: item.at,
                  channel: item.channel,
                  event: item.event,
                  summary: item.summary,
                }))
              )
            : "No events yet."}
        </pre>

        <div className="muted">Evidence bundle</div>
        <pre>{evidence ? stringify(evidence) : "No evidence loaded yet."}</pre>

        <div className="muted">Evidence lines (parsed preview)</div>
        <pre>
          {parsedEvidenceLines.length > 0
            ? stringify(
                parsedEvidenceLines.map((line) => ({
                  id: line.id,
                  kind: line.kind,
                  preview: line.preview,
                }))
              )
            : "No JSONL lines to preview."}
        </pre>
      </div>
    </div>
  );
}
