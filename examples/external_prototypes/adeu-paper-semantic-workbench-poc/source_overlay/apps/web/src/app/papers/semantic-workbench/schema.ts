export type LaneId = "O" | "E" | "D" | "U";

export type FragmentSourceKind = "explicit" | "inferred";

export type FragmentStatus =
  | "explicit"
  | "inferred"
  | "contested"
  | "underdetermined"
  | "missing";

export type ClaimStatus = "stable" | "contested" | "underdetermined";

export type BridgeKind =
  | "canonical_bridge"
  | "supporting_bridge"
  | "missing_bridge"
  | "contested_bridge"
  | "projection_bridge"
  | "contradiction_bridge";

export type DiagnosticKind =
  | "contradiction"
  | "underdetermination"
  | "missing_bridge"
  | "overloaded_term"
  | "implicit_assumption"
  | "u_overreach";

export type DiagnosticSeverity = "critical" | "warning" | "advisory";

export type ProcessingPipelineMode = "mock-curated" | "mock-heuristic" | "resident-codex";

export type SurfaceView = "artifact" | "local" | "spatial";

export type WorkbenchDepth = 1 | 2;

export type PaperSemanticSource = {
  schema: "paper_claim_source@1";
  source_id: string;
  artifact_kind: "paper.abstract" | "paper.abstract_digest" | "pasted.paragraph";
  title: string;
  authors: string[];
  year: number | null;
  venue?: string;
  source_text: string;
  source_notes?: string[];
};

export type PaperClaimSpan = {
  schema: "paper_claim_span@1";
  span_id: string;
  start: number;
  end: number;
  quote: string;
  sentence_index: number;
  paragraph_index: number;
};

export type ODEULaneFragment = {
  schema: "odeu_lane_fragment@1";
  fragment_id: string;
  claim_id: string;
  lane: LaneId;
  short_label: string;
  text: string;
  source_kind: FragmentSourceKind;
  status: FragmentStatus;
  confidence: number;
  warrant: string;
  span_ids: string[];
  bridge_ids: string[];
  diagnostic_ids: string[];
};

export type ODEUClaimDecomposition = {
  schema: "odeu_claim_decomposition@1";
  claim_id: string;
  parent_claim_id: string | null;
  depth: WorkbenchDepth;
  claim_text: string;
  summary: string;
  span_ids: string[];
  explicitness: FragmentSourceKind;
  confidence: number;
  status: ClaimStatus;
  lane_fragment_ids: string[];
  subclaim_ids: string[];
  diagnostic_ids: string[];
};

export type ODEUInferenceBridge = {
  schema: "odeu_inference_bridge@1";
  bridge_id: string;
  claim_id: string;
  from_fragment_id: string;
  to_fragment_id: string;
  kind: BridgeKind;
  rationale: string;
  confidence: number;
  diagnostic_ids: string[];
};

export type ODEUSemanticDiagnostic = {
  schema: "odeu_semantic_diagnostics@1";
  diagnostic_id: string;
  claim_id: string;
  kind: DiagnosticKind;
  severity: DiagnosticSeverity;
  summary: string;
  lane_ids: LaneId[];
  related_fragment_ids: string[];
  span_ids: string[];
};

export type ODEUVisualProjection = {
  schema: "odeu_visual_projection@1";
  default_view: SurfaceView;
  lane_order: LaneId[];
  inline_claim_order: string[];
  recommended_focus_claim_id: string | null;
  lane_node_order: Record<LaneId, string[]>;
};

export type WorkbenchAuthorityPosture = {
  source_artifact_authority: "reference-anchor";
  semantic_projection_authority: "advisory-only";
  inferred_content_authority: "non-authoritative";
};

export type WorkerHandle = {
  template_id: string;
  template_version: string;
  evidence_id?: string | null;
  worker_id?: string | null;
  status: "idle" | "starting" | "ok" | "failed" | "cancelled" | "unavailable";
  status_detail?: string | null;
};

export type PaperSemanticWorkbenchArtifact = {
  schema: "paper_semantic_workbench@1";
  artifact_id: string;
  source: PaperSemanticSource;
  processing: {
    pipeline_mode: ProcessingPipelineMode;
    processor_version: string;
    depth_requested: WorkbenchDepth;
    generated_at: string;
    authority_posture: WorkbenchAuthorityPosture;
    worker?: WorkerHandle;
  };
  spans: PaperClaimSpan[];
  claims: ODEUClaimDecomposition[];
  lane_fragments: ODEULaneFragment[];
  inference_bridges: ODEUInferenceBridge[];
  diagnostics: ODEUSemanticDiagnostic[];
  visual_projection: ODEUVisualProjection;
};

export type PaperSemanticWorkbenchRequest = {
  schema: "paper_semantic_worker_request@1";
  request_id: string;
  title?: string;
  source_text: string;
  source_kind: "paper.abstract" | "pasted.paragraph";
  requested_depth: WorkbenchDepth;
  return_schema: "paper_semantic_workbench@1";
  operator_posture: {
    analysis_mode: "evidence-first";
    authority_mode: "advisory-only";
    preserve_source_anchor: true;
  };
  constraints: {
    anchor_explicit_claims_to_source_spans: true;
    infer_missing_odeu_lanes: true;
    mark_inferred_and_contested_content: true;
    include_diagnostics: true;
    max_top_level_claims: number;
    max_subclaims_per_claim: number;
  };
};

export type PaperSemanticWorkbenchResponse = PaperSemanticWorkbenchArtifact;

export type ClaimMap = Record<string, ODEUClaimDecomposition>;
export type FragmentMap = Record<string, ODEULaneFragment>;
export type DiagnosticMap = Record<string, ODEUSemanticDiagnostic>;
export type BridgeMap = Record<string, ODEUInferenceBridge>;

export const LANE_ORDER: LaneId[] = ["O", "E", "D", "U"];

export const LANE_META: Record<
  LaneId,
  {
    title: string;
    short: string;
    subtitle: string;
    color: string;
    softColor: string;
    glow: string;
  }
> = {
  O: {
    title: "Ontology",
    short: "O",
    subtitle: "what entities / structures are being posited",
    color: "#38bdf8",
    softColor: "rgba(56, 189, 248, 0.16)",
    glow: "rgba(56, 189, 248, 0.45)",
  },
  E: {
    title: "Epistemics",
    short: "E",
    subtitle: "what support, evidence, or warrant is actually present",
    color: "#a855f7",
    softColor: "rgba(168, 85, 247, 0.16)",
    glow: "rgba(168, 85, 247, 0.45)",
  },
  D: {
    title: "Deontics",
    short: "D",
    subtitle: "what rules, constraints, or must/should structure is implied",
    color: "#f59e0b",
    softColor: "rgba(245, 158, 11, 0.16)",
    glow: "rgba(245, 158, 11, 0.45)",
  },
  U: {
    title: "Utility",
    short: "U",
    subtitle: "what objective, payoff, or optimization target is in play",
    color: "#22c55e",
    softColor: "rgba(34, 197, 94, 0.16)",
    glow: "rgba(34, 197, 94, 0.45)",
  },
};

export const DIAGNOSTIC_META: Record<
  DiagnosticKind,
  { title: string; color: string; borderStyle?: "solid" | "dashed" | "dotted" }
> = {
  contradiction: {
    title: "Contradiction",
    color: "#ef4444",
    borderStyle: "solid",
  },
  underdetermination: {
    title: "Underdetermination",
    color: "#94a3b8",
    borderStyle: "dashed",
  },
  missing_bridge: {
    title: "Missing bridge",
    color: "#f97316",
    borderStyle: "dashed",
  },
  overloaded_term: {
    title: "Overloaded term",
    color: "#ec4899",
    borderStyle: "dotted",
  },
  implicit_assumption: {
    title: "Implicit assumption",
    color: "#22d3ee",
    borderStyle: "dotted",
  },
  u_overreach: {
    title: "U-overreach beyond E",
    color: "#ef4444",
    borderStyle: "solid",
  },
};

export function clampConfidence(value: number): number {
  return Math.max(0, Math.min(1, Number.isFinite(value) ? value : 0));
}

export function confidenceBand(value: number): "high" | "medium" | "low" {
  if (value >= 0.8) return "high";
  if (value >= 0.55) return "medium";
  return "low";
}
