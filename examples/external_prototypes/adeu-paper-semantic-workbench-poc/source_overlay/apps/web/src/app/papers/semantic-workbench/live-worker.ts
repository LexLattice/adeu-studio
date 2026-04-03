import { apiBase } from "../../lib/api-base";
import type {
  PaperSemanticWorkbenchArtifact,
  PaperSemanticWorkbenchRequest,
  PaperSemanticWorkbenchResponse,
  WorkbenchDepth,
} from "./schema";

const LIVE_TEMPLATE_ID = "adeu.paper.semantic_decomposition.v0";
const LIVE_TEMPLATE_VERSION = "v0";
const LIVE_RETURN_SCHEMA = "paper_semantic_workbench@1";

export type HarnessStatus = {
  reachable: boolean;
  appState?: {
    codex_exec_available?: boolean | null;
    codex_app_server_available?: boolean | null;
    active_copilot_session_id?: string | null;
  };
  templates: Array<{ template_id: string; description?: string }>;
  templateRegistered: boolean;
  error?: string | null;
};

export type WorkflowRunRef = {
  worker_id?: string | null;
  evidence_id?: string | null;
  status?: "ok" | "failed" | "cancelled" | string;
  template_id?: string | null;
  template_version?: string | null;
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

export function requestId(): string {
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
      detail?: { code?: string; message?: string } | string;
      message?: string;
      error?: string;
    };
    if (typeof parsed.detail === "string") return parsed.detail;
    if (parsed.detail && typeof parsed.detail === "object") {
      const code = "code" in parsed.detail ? parsed.detail.code : undefined;
      const message = "message" in parsed.detail ? parsed.detail.message : undefined;
      if (code && message) return `${code}: ${message}`;
      if (message) return String(message);
    }
    if (typeof parsed.message === "string") return parsed.message;
    if (typeof parsed.error === "string") return parsed.error;
  } catch {
    // fall through
  }
  return text;
}

export function buildResidentCodexRequest(args: {
  title?: string;
  sourceText: string;
  depth: WorkbenchDepth;
}): PaperSemanticWorkbenchRequest {
  return {
    schema: "paper_semantic_worker_request@1",
    request_id: requestId(),
    title: args.title?.trim() || undefined,
    source_text: args.sourceText.trim(),
    source_kind: "paper.abstract",
    requested_depth: args.depth,
    return_schema: LIVE_RETURN_SCHEMA,
    operator_posture: {
      analysis_mode: "evidence-first",
      authority_mode: "advisory-only",
      preserve_source_anchor: true,
    },
    constraints: {
      anchor_explicit_claims_to_source_spans: true,
      infer_missing_odeu_lanes: true,
      mark_inferred_and_contested_content: true,
      include_diagnostics: true,
      max_top_level_claims: 6,
      max_subclaims_per_claim: 4,
    },
  };
}

export function buildResidentCodexPrompt(request: PaperSemanticWorkbenchRequest): string {
  return [
    "You are the resident ADEU Codex worker for abstract-size paper semantic decomposition.",
    "Return exactly one JSON object matching paper_semantic_workbench@1.",
    "Do not emit markdown, commentary, or code fences.",
    "",
    "Required discipline:",
    "1. Preserve the original source text as the authoritative anchor artifact.",
    "2. Identify top-level claims and anchor every explicit claim to source spans.",
    "3. Decompose each claim into O / E / D / U lane fragments.",
    "4. Mark each fragment as explicit or inferred, with confidence and warrant.",
    "5. Infer missing D or U content when needed, but mark it advisory, inferred, and lower confidence.",
    "6. Emit diagnostics when you detect contradiction, underdetermination, missing bridge, overloaded term, implicit assumption, or U-overreach beyond E support.",
    "7. If requested_depth is 2, decompose meaningful subclaims recursively one level deeper.",
    "8. Keep claims bounded to abstract-size semantics only. Do not invent outside evidence.",
    "",
    "Output shape notes:",
    "- schema must equal paper_semantic_workbench@1",
    "- source.source_text must reproduce the input text verbatim",
    "- spans must use character offsets into source.source_text",
    "- claims, lane_fragments, inference_bridges, diagnostics, and visual_projection must be internally consistent",
    "- authority posture must remain advisory-only for all inferred content",
    "",
    "Worker request:",
    stringify(request),
  ].join("\n");
}

async function callTool(toolName: string, argumentsPayload: Record<string, unknown>): Promise<unknown> {
  const response = await fetch(`${apiBase()}/urm/tools/call`, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      provider: "codex",
      role: "copilot",
      session_id: `paper-semantic-workbench-${requestId()}`,
      tool_name: toolName,
      arguments: argumentsPayload,
    }),
  });
  if (!response.ok) {
    throw new Error(await parseErrorMessage(response));
  }
  const payload = (await response.json()) as { result?: unknown };
  return payload.result;
}

export async function fetchHarnessStatus(): Promise<HarnessStatus> {
  try {
    const [templateResult, appStateResult] = await Promise.all([
      callTool("adeu.list_templates", {}),
      callTool("adeu.get_app_state", {}),
    ]);

    const templates = Array.isArray((templateResult as { templates?: unknown[] } | null)?.templates)
      ? ((templateResult as { templates?: Array<{ template_id?: string; description?: string }> }).templates ?? [])
          .filter((item): item is { template_id: string; description?: string } =>
            Boolean(item && typeof item.template_id === "string"),
          )
      : [];

    const templateRegistered = templates.some((item) => item.template_id === LIVE_TEMPLATE_ID);
    const appState = (appStateResult as HarnessStatus["appState"]) ?? undefined;

    return {
      reachable: true,
      appState,
      templates,
      templateRegistered,
      error: null,
    };
  } catch (error) {
    return {
      reachable: false,
      templates: [],
      templateRegistered: false,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

export async function startResidentCodexWorkflow(args: {
  request: PaperSemanticWorkbenchRequest;
  timeoutSecs?: number;
}): Promise<{ runRef: WorkflowRunRef; prompt: string }> {
  const prompt = buildResidentCodexPrompt(args.request);
  const result = (await callTool("adeu.run_workflow", {
    template_id: LIVE_TEMPLATE_ID,
    mode: "read_only",
    timeout_secs: args.timeoutSecs ?? 120,
    inputs: {
      prompt,
    },
  })) as WorkflowRunRef;

  return {
    runRef: result,
    prompt,
  };
}

export async function loadEvidence(evidenceId: string): Promise<EvidenceBundle> {
  const result = (await callTool("adeu.read_evidence", {
    evidence_id: evidenceId,
    max_bytes: 400_000,
  })) as EvidenceBundle;
  return result;
}

export function extractArtifactFromEvidence(
  evidence: EvidenceBundle | null,
): PaperSemanticWorkbenchResponse | null {
  if (!evidence?.raw_jsonl) return null;
  const lines = evidence.raw_jsonl.split(/\n+/).map((line) => line.trim()).filter(Boolean);
  for (const line of lines.reverse()) {
    try {
      const parsed = JSON.parse(line) as { schema?: string };
      if (parsed.schema === LIVE_RETURN_SCHEMA) {
        return parsed as PaperSemanticWorkbenchArtifact;
      }
    } catch {
      // ignore non-JSON lines
    }
  }
  return null;
}

export const LIVE_TEMPLATE_META = {
  template_id: LIVE_TEMPLATE_ID,
  template_version: LIVE_TEMPLATE_VERSION,
  description: "Resident ADEU Codex worker scaffold for abstract-size ODEU semantic decomposition.",
};
