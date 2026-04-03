"use client";

import dynamic from "next/dynamic";
import Link from "next/link";
import { AnimatePresence, LayoutGroup, motion } from "framer-motion";
import { useEffect, useMemo, useState, type ReactNode } from "react";

import {
  buildResidentCodexPrompt,
  buildResidentCodexRequest,
  extractArtifactFromEvidence,
  fetchHarnessStatus,
  LIVE_TEMPLATE_META,
  loadEvidence,
  startResidentCodexWorkflow,
  type EvidenceBundle,
  type HarnessStatus,
  type WorkflowRunRef,
} from "./live-worker";
import {
  getSamplePaper,
  runMockSemanticProcessing,
  SAMPLE_PAPERS,
  summarizeProcessingSource,
} from "./mock-processing";
import {
  confidenceBand,
  DIAGNOSTIC_META,
  type DiagnosticKind,
  type LaneId,
  LANE_META,
  LANE_ORDER,
  type ODEUClaimDecomposition,
  type ODEUInferenceBridge,
  type ODEULaneFragment,
  type ODEUSemanticDiagnostic,
  type PaperClaimSpan,
  type PaperSemanticWorkbenchArtifact,
  type PaperSemanticWorkbenchRequest,
  type SurfaceView,
  type WorkbenchDepth,
} from "./schema";

const SpatialLaneScene = dynamic(() => import("./spatial-lane-scene"), {
  ssr: false,
  loading: () => (
    <div className="flex h-full min-h-[420px] items-center justify-center rounded-3xl border border-white/10 bg-[#040b12] text-sm text-slate-400">
      Initializing spatial lane projection…
    </div>
  ),
});

const PANEL =
  "rounded-[28px] border border-white/10 bg-[rgba(6,12,22,0.88)] shadow-[0_24px_90px_rgba(2,8,23,0.55)] backdrop-blur-xl";
const SUBPANEL =
  "rounded-[22px] border border-white/10 bg-[rgba(7,15,26,0.86)] shadow-[inset_0_1px_0_rgba(255,255,255,0.04)] backdrop-blur-xl";

function cn(...parts: Array<string | false | null | undefined>): string {
  return parts.filter(Boolean).join(" ");
}

function prettyConfidence(value: number): string {
  return `${Math.round(value * 100)}%`;
}

function sentenceCase(value: string): string {
  return value.replace(/[_-]+/g, " ");
}

function statusTone(status: string): string {
  if (status === "explicit") return "text-emerald-200";
  if (status === "inferred") return "text-cyan-100";
  if (status === "underdetermined") return "text-slate-200/80";
  if (status === "missing") return "text-slate-300/60";
  return "text-rose-200";
}

function isClaimTopLevel(claim: ODEUClaimDecomposition): boolean {
  return claim.parent_claim_id === null;
}

function buildMaps(artifact: PaperSemanticWorkbenchArtifact) {
  const claimById = Object.fromEntries(
    artifact.claims.map((claim) => [claim.claim_id, claim]),
  ) as Record<string, ODEUClaimDecomposition>;
  const fragmentById = Object.fromEntries(
    artifact.lane_fragments.map((fragment) => [fragment.fragment_id, fragment]),
  ) as Record<string, ODEULaneFragment>;
  const diagnosticById = Object.fromEntries(
    artifact.diagnostics.map((diagnostic) => [diagnostic.diagnostic_id, diagnostic]),
  ) as Record<string, ODEUSemanticDiagnostic>;
  const spanById = Object.fromEntries(
    artifact.spans.map((span) => [span.span_id, span]),
  ) as Record<string, PaperClaimSpan>;
  const bridgeById = Object.fromEntries(
    artifact.inference_bridges.map((bridge) => [bridge.bridge_id, bridge]),
  ) as Record<string, ODEUInferenceBridge>;

  return { claimById, fragmentById, diagnosticById, spanById, bridgeById };
}

function focusClaimIdForSelection(
  claimId: string | null,
  claimById: Record<string, ODEUClaimDecomposition>,
): string | null {
  if (!claimId) return null;
  const claim = claimById[claimId];
  if (!claim) return null;
  return claim.parent_claim_id ?? claim.claim_id;
}

function firstSpanForClaim(
  claim: ODEUClaimDecomposition,
  spanById: Record<string, PaperClaimSpan>,
): PaperClaimSpan | null {
  const spanId = claim.span_ids[0];
  return spanId ? spanById[spanId] ?? null : null;
}

function sortClaimsByTextOrder(
  claims: ODEUClaimDecomposition[],
  spanById: Record<string, PaperClaimSpan>,
): ODEUClaimDecomposition[] {
  return [...claims].sort((left, right) => {
    const leftSpan = firstSpanForClaim(left, spanById);
    const rightSpan = firstSpanForClaim(right, spanById);
    return (leftSpan?.start ?? 0) - (rightSpan?.start ?? 0);
  });
}

function claimInferredCount(
  claim: ODEUClaimDecomposition,
  fragmentById: Record<string, ODEULaneFragment>,
): number {
  return claim.lane_fragment_ids.filter((id) => fragmentById[id]?.source_kind === "inferred").length;
}

function claimExplicitCount(
  claim: ODEUClaimDecomposition,
  fragmentById: Record<string, ODEULaneFragment>,
): number {
  return claim.lane_fragment_ids.filter((id) => fragmentById[id]?.source_kind === "explicit").length;
}

function claimDiagnostics(
  claim: ODEUClaimDecomposition,
  diagnosticById: Record<string, ODEUSemanticDiagnostic>,
): ODEUSemanticDiagnostic[] {
  return claim.diagnostic_ids
    .map((id) => diagnosticById[id])
    .filter((item): item is ODEUSemanticDiagnostic => Boolean(item));
}

function fragmentsForLane(
  claim: ODEUClaimDecomposition,
  lane: LaneId,
  fragmentById: Record<string, ODEULaneFragment>,
): ODEULaneFragment[] {
  return claim.lane_fragment_ids
    .map((id) => fragmentById[id])
    .filter((fragment): fragment is ODEULaneFragment => Boolean(fragment && fragment.lane === lane));
}

function bridgesForClaim(
  claim: ODEUClaimDecomposition,
  bridgeById: Record<string, ODEUInferenceBridge>,
): ODEUInferenceBridge[] {
  return Object.values(bridgeById).filter((bridge) => bridge.claim_id === claim.claim_id);
}

function diagnosticSummaryKind(diagnostics: ODEUSemanticDiagnostic[]): DiagnosticKind | null {
  return diagnostics[0]?.kind ?? null;
}

function BridgeLegend() {
  return (
    <div className={cn(SUBPANEL, "grid gap-3 p-4 text-xs text-slate-300/80")}> 
      <div className="flex items-center justify-between">
        <span className="font-medium text-slate-100">Diagnostics legend</span>
        <span className="text-[11px] uppercase tracking-[0.24em] text-slate-400">overlay</span>
      </div>
      <div className="grid gap-2 sm:grid-cols-2">
        {Object.entries(DIAGNOSTIC_META).map(([key, meta]) => (
          <div key={key} className="flex items-center gap-2 rounded-2xl border border-white/8 bg-white/[0.03] px-3 py-2">
            <span
              className="inline-flex h-2.5 w-7 rounded-full"
              style={{
                backgroundColor: meta.color,
                borderStyle: meta.borderStyle ?? "solid",
                borderWidth: 1,
                borderColor: meta.color,
              }}
            />
            <span>{meta.title}</span>
          </div>
        ))}
      </div>
    </div>
  );
}

function ConfidenceBar({ value, color }: { value: number; color: string }) {
  return (
    <div className="h-1.5 w-full overflow-hidden rounded-full bg-white/8">
      <div className="h-full rounded-full transition-all" style={{ width: `${Math.round(value * 100)}%`, backgroundColor: color }} />
    </div>
  );
}

function StatusChip({ label, tone }: { label: string; tone?: string }) {
  return (
    <span
      className={cn(
        "inline-flex items-center rounded-full border px-2.5 py-1 text-[11px] uppercase tracking-[0.18em]",
        tone ?? "border-white/10 bg-white/[0.04] text-slate-300",
      )}
    >
      {label}
    </span>
  );
}

function LaneToggleButton({
  lane,
  active,
  onToggle,
}: {
  lane: LaneId;
  active: boolean;
  onToggle: () => void;
}) {
  const meta = LANE_META[lane];
  return (
    <button
      type="button"
      onClick={onToggle}
      className="group rounded-2xl border px-3 py-2 text-left transition"
      style={{
        borderColor: active ? `${meta.color}88` : "rgba(255,255,255,0.12)",
        backgroundColor: active ? meta.softColor : "rgba(255,255,255,0.03)",
        boxShadow: active ? `0 0 0 1px ${meta.color}22 inset, 0 0 24px ${meta.glow}` : undefined,
      }}
    >
      <div className="flex items-center justify-between gap-3">
        <div>
          <div className="text-xs uppercase tracking-[0.26em] text-slate-300/70">{meta.short}</div>
          <div className="mt-1 text-sm font-medium text-slate-100">{meta.title}</div>
        </div>
        <div
          className="h-2.5 w-2.5 rounded-full"
          style={{ backgroundColor: active ? meta.color : "rgba(255,255,255,0.18)" }}
        />
      </div>
      <p className="mt-2 line-clamp-2 text-[11px] leading-5 text-slate-400">{meta.subtitle}</p>
    </button>
  );
}

function DiagnosticPill({ diagnostic }: { diagnostic: ODEUSemanticDiagnostic }) {
  const meta = DIAGNOSTIC_META[diagnostic.kind];
  return (
    <span
      className="inline-flex items-center gap-2 rounded-full border px-2.5 py-1 text-[11px]"
      style={{ borderColor: `${meta.color}88`, color: meta.color, backgroundColor: `${meta.color}16` }}
      title={diagnostic.summary}
    >
      <span className="h-1.5 w-1.5 rounded-full" style={{ backgroundColor: meta.color }} />
      {meta.title}
    </span>
  );
}

function ClaimCard({
  claim,
  selected,
  code,
  fragmentById,
  diagnosticById,
  onClick,
}: {
  claim: ODEUClaimDecomposition;
  selected: boolean;
  code: string;
  fragmentById: Record<string, ODEULaneFragment>;
  diagnosticById: Record<string, ODEUSemanticDiagnostic>;
  onClick: () => void;
}) {
  const diagnostics = claimDiagnostics(claim, diagnosticById);
  const summaryKind = diagnosticSummaryKind(diagnostics);
  const summaryMeta = summaryKind ? DIAGNOSTIC_META[summaryKind] : null;

  return (
    <motion.button
      layoutId={`claim-focus-${claim.claim_id}`}
      type="button"
      onClick={onClick}
      className="min-w-[220px] rounded-[24px] border p-4 text-left transition"
      style={{
        borderColor: selected ? "rgba(103, 232, 249, 0.55)" : "rgba(255,255,255,0.12)",
        background: selected
          ? "linear-gradient(180deg, rgba(9,25,38,0.96) 0%, rgba(5,18,30,0.92) 100%)"
          : "linear-gradient(180deg, rgba(8,18,31,0.88) 0%, rgba(4,12,20,0.78) 100%)",
        boxShadow: selected ? "0 0 0 1px rgba(103,232,249,0.22) inset, 0 0 32px rgba(34,211,238,0.18)" : undefined,
      }}
    >
      <div className="flex items-start justify-between gap-3">
        <div>
          <div className="text-[11px] uppercase tracking-[0.24em] text-cyan-200/70">{code}</div>
          <h3 className="mt-2 text-sm font-semibold text-slate-50">{claim.summary}</h3>
        </div>
        <StatusChip label={claim.status} tone="border-white/10 bg-white/[0.04] text-slate-200/80" />
      </div>
      <p className="mt-3 line-clamp-3 text-sm leading-6 text-slate-300/90">{claim.claim_text}</p>
      <div className="mt-4 flex flex-wrap items-center gap-2">
        <StatusChip label={`${claimExplicitCount(claim, fragmentById)} explicit`} tone="border-emerald-400/30 bg-emerald-400/10 text-emerald-100" />
        <StatusChip label={`${claimInferredCount(claim, fragmentById)} inferred`} tone="border-sky-400/30 bg-sky-400/10 text-sky-100" />
        <StatusChip label={prettyConfidence(claim.confidence)} tone="border-white/10 bg-white/[0.04] text-slate-200" />
        {summaryMeta ? (
          <span className="inline-flex items-center gap-2 text-[11px]" style={{ color: summaryMeta.color }}>
            <span className="h-1.5 w-1.5 rounded-full" style={{ backgroundColor: summaryMeta.color }} />
            {summaryMeta.title}
          </span>
        ) : null}
      </div>
    </motion.button>
  );
}

function ArtifactAnchorText({
  artifact,
  topLevelClaims,
  selectedClaimId,
  hoveredClaimId,
  claimById,
  spanById,
  fragmentById,
  diagnosticById,
  showDiagnostics,
  onSelectClaim,
  onHoverClaim,
}: {
  artifact: PaperSemanticWorkbenchArtifact;
  topLevelClaims: ODEUClaimDecomposition[];
  selectedClaimId: string | null;
  hoveredClaimId: string | null;
  claimById: Record<string, ODEUClaimDecomposition>;
  spanById: Record<string, PaperClaimSpan>;
  fragmentById: Record<string, ODEULaneFragment>;
  diagnosticById: Record<string, ODEUSemanticDiagnostic>;
  showDiagnostics: boolean;
  onSelectClaim: (claimId: string) => void;
  onHoverClaim: (claimId: string | null) => void;
}) {
  const spans = useMemo(() => {
    return topLevelClaims
      .map((claim) => ({ claim, span: firstSpanForClaim(claim, spanById) }))
      .filter((item): item is { claim: ODEUClaimDecomposition; span: PaperClaimSpan } => Boolean(item.span))
      .sort((left, right) => left.span.start - right.span.start);
  }, [spanById, topLevelClaims]);

  const nodes: ReactNode[] = [];
  let cursor = 0;
  spans.forEach(({ claim, span }, index) => {
    const isSelected = claim.claim_id === focusClaimIdForSelection(selectedClaimId, claimById);
    const isHovered = claim.claim_id === hoveredClaimId;
    if (span.start > cursor) {
      nodes.push(
        <span key={`text-${index}-${cursor}`} className="whitespace-pre-wrap text-slate-200/90">
          {artifact.source.source_text.slice(cursor, span.start)}
        </span>,
      );
    }
    const diagnostics = claimDiagnostics(claim, diagnosticById);
    nodes.push(
      <motion.button
        key={claim.claim_id}
        layoutId={`anchor-${claim.claim_id}`}
        type="button"
        onMouseEnter={() => onHoverClaim(claim.claim_id)}
        onMouseLeave={() => onHoverClaim(null)}
        onFocus={() => onHoverClaim(claim.claim_id)}
        onBlur={() => onHoverClaim(null)}
        onClick={() => onSelectClaim(claim.claim_id)}
        className="relative mx-[1px] inline rounded-xl px-1.5 py-0.5 text-left align-baseline transition"
        style={{
          backgroundColor: isSelected
            ? "rgba(34,211,238,0.16)"
            : isHovered
              ? "rgba(148,163,184,0.18)"
              : "rgba(255,255,255,0.06)",
          outline: isSelected ? "1px solid rgba(34,211,238,0.55)" : "1px solid rgba(255,255,255,0.05)",
          boxShadow: isSelected ? "0 0 24px rgba(34,211,238,0.18)" : undefined,
        }}
      >
        <span className="text-slate-50">{artifact.source.source_text.slice(span.start, span.end)}</span>
        <span className="ml-2 inline-flex items-center rounded-full border border-cyan-400/25 bg-cyan-400/12 px-2 py-0.5 text-[10px] uppercase tracking-[0.22em] text-cyan-100">
          C{index + 1}
        </span>
        {showDiagnostics && diagnostics.length > 0 ? (
          <span className="ml-2 inline-flex items-center gap-1 rounded-full border border-rose-400/18 bg-rose-400/10 px-2 py-0.5 text-[10px] uppercase tracking-[0.16em] text-rose-100">
            {diagnostics.length} diag
          </span>
        ) : null}
        <span className="ml-2 inline-flex items-center rounded-full border border-sky-300/20 bg-sky-300/10 px-2 py-0.5 text-[10px] uppercase tracking-[0.16em] text-sky-100">
          {claimInferredCount(claim, fragmentById)} inf
        </span>
      </motion.button>,
    );
    cursor = span.end;
  });

  if (cursor < artifact.source.source_text.length) {
    nodes.push(
      <span key={`tail-${cursor}`} className="whitespace-pre-wrap text-slate-200/90">
        {artifact.source.source_text.slice(cursor)}
      </span>,
    );
  }

  return <div className="whitespace-pre-wrap text-[15px] leading-8 text-slate-100/90">{nodes}</div>;
}

function LanePanel({
  lane,
  fragments,
  visible,
  diagnosticsById,
}: {
  lane: LaneId;
  fragments: ODEULaneFragment[];
  visible: boolean;
  diagnosticsById: Record<string, ODEUSemanticDiagnostic>;
}) {
  const meta = LANE_META[lane];
  return (
    <div
      className="rounded-[24px] border p-4 transition"
      style={{
        borderColor: visible ? `${meta.color}66` : "rgba(255,255,255,0.08)",
        backgroundColor: visible ? meta.softColor : "rgba(255,255,255,0.025)",
        boxShadow: visible ? `inset 0 0 0 1px ${meta.color}22, 0 0 24px ${meta.glow}` : undefined,
        opacity: visible ? 1 : 0.5,
      }}
    >
      <div className="flex items-start justify-between gap-3">
        <div>
          <div className="text-[11px] uppercase tracking-[0.28em]" style={{ color: meta.color }}>
            {meta.short}
          </div>
          <h4 className="mt-1 text-sm font-semibold text-slate-50">{meta.title}</h4>
          <p className="mt-1 text-[12px] leading-5 text-slate-300/70">{meta.subtitle}</p>
        </div>
        <StatusChip label={`${fragments.length} frag`} tone="border-white/10 bg-white/[0.04] text-slate-200/80" />
      </div>
      <div className="mt-4 grid gap-3">
        {fragments.map((fragment) => {
          const diagnostics = fragment.diagnostic_ids
            .map((id) => diagnosticsById[id])
            .filter((item): item is ODEUSemanticDiagnostic => Boolean(item));
          return (
            <div key={fragment.fragment_id} className="rounded-2xl border border-white/8 bg-black/15 p-3">
              <div className="flex flex-wrap items-center gap-2">
                <span className="text-sm font-medium text-slate-50">{fragment.short_label}</span>
                <StatusChip label={fragment.source_kind} tone="border-sky-300/20 bg-sky-300/10 text-sky-100" />
                <span className={cn("text-[11px] uppercase tracking-[0.2em]", statusTone(fragment.status))}>
                  {sentenceCase(fragment.status)}
                </span>
              </div>
              <p className="mt-3 text-sm leading-6 text-slate-200/90">{fragment.text}</p>
              <div className="mt-3 grid gap-2">
                <div className="flex items-center justify-between text-[11px] uppercase tracking-[0.18em] text-slate-400">
                  <span>{confidenceBand(fragment.confidence)} confidence</span>
                  <span>{prettyConfidence(fragment.confidence)}</span>
                </div>
                <ConfidenceBar value={fragment.confidence} color={meta.color} />
              </div>
              <p className="mt-3 text-[12px] leading-5 text-slate-400">{fragment.warrant}</p>
              {diagnostics.length > 0 ? (
                <div className="mt-3 flex flex-wrap gap-2">
                  {diagnostics.map((diagnostic) => (
                    <DiagnosticPill key={diagnostic.diagnostic_id} diagnostic={diagnostic} />
                  ))}
                </div>
              ) : null}
            </div>
          );
        })}
      </div>
    </div>
  );
}

function LiveScaffoldPanel({
  pipelineMode,
  harnessStatus,
  requestPreview,
  promptPreview,
  runRef,
  evidence,
  liveError,
  onReloadEvidence,
  isLoadingEvidence,
}: {
  pipelineMode: "mock" | "live";
  harnessStatus: HarnessStatus | null;
  requestPreview: PaperSemanticWorkbenchRequest | null;
  promptPreview: string;
  runRef: WorkflowRunRef | null;
  evidence: EvidenceBundle | null;
  liveError: string | null;
  onReloadEvidence: () => void;
  isLoadingEvidence: boolean;
}) {
  return (
    <div className={cn(SUBPANEL, "grid gap-4 p-4")}> 
      <div className="flex items-center justify-between gap-3">
        <div>
          <div className="text-[11px] uppercase tracking-[0.28em] text-amber-200/70">Live scaffold</div>
          <h3 className="mt-1 text-sm font-semibold text-slate-50">Resident Codex harness path</h3>
        </div>
        <StatusChip
          label={pipelineMode === "live" ? "active lane" : "preview only"}
          tone={pipelineMode === "live" ? "border-amber-300/30 bg-amber-300/10 text-amber-100" : "border-white/10 bg-white/[0.04] text-slate-300"}
        />
      </div>
      <div className="grid gap-3 text-sm text-slate-300/80">
        <div className="rounded-2xl border border-white/8 bg-white/[0.03] p-3">
          <div className="flex items-center justify-between">
            <span className="text-[11px] uppercase tracking-[0.22em] text-slate-400">template</span>
            <span className="font-mono text-[12px] text-slate-200">{LIVE_TEMPLATE_META.template_id}</span>
          </div>
          <p className="mt-2 text-[12px] leading-5 text-slate-400">{LIVE_TEMPLATE_META.description}</p>
        </div>
        <div className="rounded-2xl border border-white/8 bg-white/[0.03] p-3">
          <div className="flex items-center justify-between">
            <span className="text-[11px] uppercase tracking-[0.22em] text-slate-400">harness status</span>
            <span className="text-[12px] text-slate-200">
              {harnessStatus?.reachable ? "reachable" : harnessStatus ? "unreachable" : "not checked"}
            </span>
          </div>
          <p className="mt-2 text-[12px] leading-5 text-slate-400">
            {harnessStatus?.reachable
              ? `template registered: ${String(harnessStatus.templateRegistered)} · codex exec: ${String(harnessStatus.appState?.codex_exec_available ?? "n/a")}`
              : harnessStatus?.error ?? "The workbench checks the existing ADEU /urm tool surface before trying a live run."}
          </p>
        </div>
        {requestPreview ? (
          <details className="rounded-2xl border border-white/8 bg-black/15 p-3">
            <summary className="cursor-pointer text-[11px] uppercase tracking-[0.22em] text-slate-400">worker request preview</summary>
            <pre className="mt-3 overflow-auto rounded-2xl border border-white/6 bg-[#020610] p-3 text-[11px] leading-5 text-slate-200">{JSON.stringify(requestPreview, null, 2)}</pre>
          </details>
        ) : null}
        {promptPreview ? (
          <details className="rounded-2xl border border-white/8 bg-black/15 p-3">
            <summary className="cursor-pointer text-[11px] uppercase tracking-[0.22em] text-slate-400">prompt contract</summary>
            <pre className="mt-3 overflow-auto rounded-2xl border border-white/6 bg-[#020610] p-3 text-[11px] leading-5 text-slate-200">{promptPreview}</pre>
          </details>
        ) : null}
        {runRef ? (
          <div className="rounded-2xl border border-white/8 bg-white/[0.03] p-3 text-[12px] leading-5 text-slate-300/80">
            <div className="flex flex-wrap gap-3">
              <span>status: {runRef.status ?? "unknown"}</span>
              <span>worker_id: {runRef.worker_id ?? "n/a"}</span>
            </div>
            <div className="mt-2 font-mono text-[11px] text-slate-400">evidence_id: {runRef.evidence_id ?? "n/a"}</div>
            {runRef.evidence_id ? (
              <button
                type="button"
                onClick={onReloadEvidence}
                className="mt-3 rounded-full border border-white/12 bg-white/[0.04] px-3 py-1 text-[11px] uppercase tracking-[0.18em] text-slate-200"
              >
                {isLoadingEvidence ? "Refreshing evidence…" : "Reload evidence"}
              </button>
            ) : null}
          </div>
        ) : null}
        {evidence ? (
          <details className="rounded-2xl border border-white/8 bg-black/15 p-3">
            <summary className="cursor-pointer text-[11px] uppercase tracking-[0.22em] text-slate-400">evidence preview</summary>
            <pre className="mt-3 max-h-[280px] overflow-auto rounded-2xl border border-white/6 bg-[#020610] p-3 text-[11px] leading-5 text-slate-200">
              {evidence.raw_jsonl || "No raw evidence returned yet."}
            </pre>
          </details>
        ) : null}
        {liveError ? (
          <div className="rounded-2xl border border-rose-400/25 bg-rose-400/10 p-3 text-[12px] leading-5 text-rose-100">
            {liveError}
          </div>
        ) : null}
      </div>
    </div>
  );
}

export default function PaperSemanticWorkbenchPage() {
  const [selectedPaperId, setSelectedPaperId] = useState<string>(SAMPLE_PAPERS[0].paper_id);
  const [pastedTitle, setPastedTitle] = useState<string>("");
  const [pastedText, setPastedText] = useState<string>("");
  const [depth, setDepth] = useState<WorkbenchDepth>(1);
  const [pipelineMode, setPipelineMode] = useState<"mock" | "live">("mock");
  const [surfaceView, setSurfaceView] = useState<SurfaceView>("artifact");
  const [showDiagnostics, setShowDiagnostics] = useState<boolean>(true);
  const [visibleLanes, setVisibleLanes] = useState<Record<LaneId, boolean>>({
    O: true,
    E: true,
    D: true,
    U: true,
  });
  const [hoveredClaimId, setHoveredClaimId] = useState<string | null>(null);
  const [isProcessing, setIsProcessing] = useState<boolean>(false);
  const [isLoadingEvidence, setIsLoadingEvidence] = useState<boolean>(false);
  const [harnessStatus, setHarnessStatus] = useState<HarnessStatus | null>(null);
  const [currentArtifact, setCurrentArtifact] = useState<PaperSemanticWorkbenchArtifact>(() =>
    runMockSemanticProcessing({
      samplePaperId: SAMPLE_PAPERS[0].paper_id,
      pastedText: "",
      depth: 1,
    }),
  );
  const [selectedClaimId, setSelectedClaimId] = useState<string | null>(
    currentArtifact.visual_projection.recommended_focus_claim_id,
  );

  const [liveRequestPreview, setLiveRequestPreview] = useState<PaperSemanticWorkbenchRequest | null>(null);
  const [livePromptPreview, setLivePromptPreview] = useState<string>("");
  const [liveRunRef, setLiveRunRef] = useState<WorkflowRunRef | null>(null);
  const [liveEvidence, setLiveEvidence] = useState<EvidenceBundle | null>(null);
  const [liveError, setLiveError] = useState<string | null>(null);

  const selectedSample = useMemo(() => getSamplePaper(selectedPaperId) ?? SAMPLE_PAPERS[0], [selectedPaperId]);
  const sourceTextForProcessing = pastedText.trim() || selectedSample.source_text;
  const titleForProcessing = pastedTitle.trim() || selectedSample.title;

  useEffect(() => {
    if (pipelineMode !== "live") return;
    let active = true;
    void fetchHarnessStatus().then((status) => {
      if (!active) return;
      setHarnessStatus(status);
    });
    return () => {
      active = false;
    };
  }, [pipelineMode]);

  useEffect(() => {
    const maps = buildMaps(currentArtifact);
    if (selectedClaimId && maps.claimById[selectedClaimId]) return;
    setSelectedClaimId(currentArtifact.visual_projection.recommended_focus_claim_id);
  }, [currentArtifact, selectedClaimId]);

  const { claimById, fragmentById, diagnosticById, spanById, bridgeById } = useMemo(
    () => buildMaps(currentArtifact),
    [currentArtifact],
  );

  const topLevelClaims = useMemo(
    () => sortClaimsByTextOrder(currentArtifact.claims.filter(isClaimTopLevel), spanById),
    [currentArtifact.claims, spanById],
  );

  const selectedClaim = selectedClaimId ? claimById[selectedClaimId] ?? null : null;
  const selectedFocusClaim = useMemo(() => {
    const focusId = focusClaimIdForSelection(selectedClaimId, claimById);
    return focusId ? claimById[focusId] ?? null : null;
  }, [claimById, selectedClaimId]);
  const selectedClaimDiagnostics = selectedClaim ? claimDiagnostics(selectedClaim, diagnosticById) : [];
  const selectedClaimSubclaims = selectedClaim?.subclaim_ids
    .map((id) => claimById[id])
    .filter((item): item is ODEUClaimDecomposition => Boolean(item)) ?? [];
  const visibleLaneIds = LANE_ORDER.filter((lane) => visibleLanes[lane]);

  const selectedClaimBridges = selectedClaim ? bridgesForClaim(selectedClaim, bridgeById) : [];

  const artifactHeaderNote = useMemo(() => {
    if (currentArtifact.source.artifact_kind === "paper.abstract_digest") {
      return "Sample paper digests are concise paraphrase artifacts for demo shipping; paste source-authored text locally to inspect the original wording.";
    }
    if (currentArtifact.source.artifact_kind === "pasted.paragraph") {
      return "Pasted source text is the active reference artifact for this run.";
    }
    return "Source abstract is the active reference artifact for this run.";
  }, [currentArtifact.source.artifact_kind]);

  async function refreshEvidence() {
    if (!liveRunRef?.evidence_id) return;
    setIsLoadingEvidence(true);
    setLiveError(null);
    try {
      const evidence = await loadEvidence(liveRunRef.evidence_id);
      setLiveEvidence(evidence);
      const extracted = extractArtifactFromEvidence(evidence);
      if (extracted) {
        setCurrentArtifact(extracted);
        setSelectedClaimId(extracted.visual_projection.recommended_focus_claim_id);
      } else {
        setLiveError(
          "Live evidence was captured, but no structured paper_semantic_workbench@1 payload was found in the evidence stream yet.",
        );
      }
    } catch (error) {
      setLiveError(error instanceof Error ? error.message : String(error));
    } finally {
      setIsLoadingEvidence(false);
    }
  }

  async function handleSemanticProcessing() {
    setIsProcessing(true);
    setLiveError(null);
    setLiveRequestPreview(null);
    setLivePromptPreview("");
    setLiveRunRef(null);
    setLiveEvidence(null);
    try {
      if (pipelineMode === "mock") {
        const artifact = runMockSemanticProcessing({
          samplePaperId: selectedPaperId,
          pastedText,
          title: titleForProcessing,
          depth,
        });
        setCurrentArtifact(artifact);
        setSelectedClaimId(artifact.visual_projection.recommended_focus_claim_id);
        setSurfaceView(pastedText.trim() ? "local" : surfaceView);
        return;
      }

      const request = buildResidentCodexRequest({
        title: titleForProcessing,
        sourceText: sourceTextForProcessing,
        depth,
      });
      const prompt = buildResidentCodexPrompt(request);
      setLiveRequestPreview(request);
      setLivePromptPreview(prompt);

      const status = await fetchHarnessStatus();
      setHarnessStatus(status);

      const { runRef, prompt: resolvedPrompt } = await startResidentCodexWorkflow({ request });
      setLiveRunRef(runRef);
      setLivePromptPreview(resolvedPrompt);

      if (runRef.evidence_id) {
        const evidence = await loadEvidence(runRef.evidence_id);
        setLiveEvidence(evidence);
        const extracted = extractArtifactFromEvidence(evidence);
        if (extracted) {
          setCurrentArtifact(extracted);
          setSelectedClaimId(extracted.visual_projection.recommended_focus_claim_id);
          setSurfaceView("local");
        } else {
          setLiveError(
            "The workflow started and evidence was captured, but the worker did not yet return a structured paper_semantic_workbench@1 object.",
          );
        }
      } else {
        setLiveError("The harness returned a workflow reference without an evidence_id.");
      }
    } catch (error) {
      setLiveError(error instanceof Error ? error.message : String(error));
    } finally {
      setIsProcessing(false);
    }
  }

  return (
    <main
      className="min-h-screen bg-[radial-gradient(circle_at_top,rgba(14,165,233,0.12),transparent_24%),linear-gradient(180deg,#020611_0%,#07121f_55%,#020611_100%)] text-slate-100"
      data-route-id="paper_semantic_workbench"
      data-route-path="/papers/semantic-workbench"
      data-surface-family="paper_semantic_inspection_workbench"
      data-authority-posture="source_anchor_projection_advisory"
    >
      <div className="mx-auto flex max-w-[1780px] flex-col gap-4 px-4 py-4 sm:px-6 lg:px-8">
        <header className={cn(PANEL, "overflow-hidden p-5 sm:p-6")}> 
          <div className="flex flex-col gap-5 xl:flex-row xl:items-start xl:justify-between">
            <div className="max-w-4xl">
              <div className="text-[11px] uppercase tracking-[0.34em] text-cyan-200/70">ADEU Studio · Paper Semantic Workbench</div>
              <h1 className="mt-3 text-3xl font-semibold tracking-tight text-white sm:text-4xl">
                Morphic abstract analysis with O / E / D / U anchored to source text
              </h1>
              <p className="mt-4 max-w-3xl text-sm leading-7 text-slate-300/86 sm:text-[15px]">
                This route is grounded in the repo’s existing <span className="font-mono text-slate-100">/papers</span> document flow,
                <span className="font-mono text-slate-100"> /artifact-inspector</span> evidence posture,
                <span className="font-mono text-slate-100"> /explain</span> diagnostics linkage, and
                <span className="font-mono text-slate-100"> /copilot</span> / URM workflow surfaces.
                The source abstract stays authoritative; the semantic projection remains advisory.
              </p>
            </div>
            <div className="grid min-w-[280px] gap-3 text-sm text-slate-300/80 sm:grid-cols-2 xl:w-[420px] xl:grid-cols-1">
              <div className="rounded-[24px] border border-white/10 bg-white/[0.04] p-4">
                <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">authority posture</div>
                <div className="mt-2 flex flex-wrap gap-2">
                  <StatusChip label="source = anchor" tone="border-emerald-300/30 bg-emerald-300/10 text-emerald-100" />
                  <StatusChip label="projection = advisory" tone="border-amber-300/30 bg-amber-300/10 text-amber-100" />
                </div>
                <p className="mt-3 text-[12px] leading-5 text-slate-400">
                  The UI may express interpretive structure but may not mint authority beyond the source artifact.
                </p>
              </div>
              <div className="rounded-[24px] border border-white/10 bg-white/[0.04] p-4">
                <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">route lineage</div>
                <div className="mt-3 flex flex-wrap gap-2 text-[12px] text-slate-200/85">
                  <Link href="/papers" className="rounded-full border border-white/10 px-3 py-1 hover:bg-white/[0.04]">
                    /papers
                  </Link>
                  <Link href="/artifact-inspector" className="rounded-full border border-white/10 px-3 py-1 hover:bg-white/[0.04]">
                    /artifact-inspector
                  </Link>
                  <Link href="/explain" className="rounded-full border border-white/10 px-3 py-1 hover:bg-white/[0.04]">
                    /explain
                  </Link>
                  <Link href="/copilot" className="rounded-full border border-white/10 px-3 py-1 hover:bg-white/[0.04]">
                    /copilot
                  </Link>
                </div>
              </div>
            </div>
          </div>
        </header>

        <LayoutGroup>
          <div className="grid gap-4 xl:grid-cols-[320px_minmax(0,1fr)_380px]">
            <aside className="grid gap-4">
              <section className={cn(PANEL, "grid gap-4 p-4")}> 
                <div className="flex items-center justify-between">
                  <div>
                    <div className="text-[11px] uppercase tracking-[0.28em] text-cyan-200/70">input lane</div>
                    <h2 className="mt-1 text-lg font-semibold text-white">Artifact selection</h2>
                  </div>
                  <StatusChip
                    label={pipelineMode === "mock" ? "demo path" : "live scaffold"}
                    tone={pipelineMode === "mock" ? "border-cyan-300/30 bg-cyan-300/10 text-cyan-100" : "border-amber-300/30 bg-amber-300/10 text-amber-100"}
                  />
                </div>
                <div className="grid gap-2">
                  {SAMPLE_PAPERS.map((paper) => (
                    <button
                      key={paper.paper_id}
                      type="button"
                      onClick={() => setSelectedPaperId(paper.paper_id)}
                      className="rounded-[22px] border p-3 text-left transition"
                      style={{
                        borderColor:
                          selectedPaperId === paper.paper_id ? "rgba(103,232,249,0.55)" : "rgba(255,255,255,0.08)",
                        backgroundColor:
                          selectedPaperId === paper.paper_id ? "rgba(8,26,38,0.88)" : "rgba(255,255,255,0.03)",
                      }}
                    >
                      <div className="text-[11px] uppercase tracking-[0.24em] text-slate-400">{paper.year}</div>
                      <div className="mt-1 text-sm font-semibold text-slate-50">{paper.title}</div>
                      <p className="mt-2 line-clamp-2 text-[12px] leading-5 text-slate-400">{paper.authors.join(", ")}</p>
                    </button>
                  ))}
                </div>
              </section>

              <section className={cn(PANEL, "grid gap-4 p-4")}> 
                <div className="flex items-center justify-between">
                  <div>
                    <div className="text-[11px] uppercase tracking-[0.28em] text-cyan-200/70">execution lane</div>
                    <h2 className="mt-1 text-lg font-semibold text-white">Processing controls</h2>
                  </div>
                  <StatusChip label={`depth ${depth}`} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                </div>

                <div className="grid grid-cols-2 gap-2 rounded-[22px] border border-white/8 bg-white/[0.03] p-1">
                  <button
                    type="button"
                    onClick={() => setPipelineMode("mock")}
                    className={cn(
                      "rounded-[18px] px-3 py-2 text-sm transition",
                      pipelineMode === "mock" ? "bg-cyan-400/12 text-cyan-100" : "text-slate-400",
                    )}
                  >
                    Mock / demo
                  </button>
                  <button
                    type="button"
                    onClick={() => setPipelineMode("live")}
                    className={cn(
                      "rounded-[18px] px-3 py-2 text-sm transition",
                      pipelineMode === "live" ? "bg-amber-400/12 text-amber-100" : "text-slate-400",
                    )}
                  >
                    Resident Codex
                  </button>
                </div>

                <div className="grid grid-cols-2 gap-2">
                  {[1, 2].map((value) => (
                    <button
                      key={value}
                      type="button"
                      onClick={() => setDepth(value as WorkbenchDepth)}
                      className={cn(
                        "rounded-2xl border px-3 py-2 text-sm transition",
                        depth === value
                          ? "border-cyan-400/35 bg-cyan-400/10 text-cyan-100"
                          : "border-white/10 bg-white/[0.03] text-slate-300",
                      )}
                    >
                      Depth {value}
                    </button>
                  ))}
                </div>

                <button
                  type="button"
                  onClick={() => void handleSemanticProcessing()}
                  disabled={isProcessing || !sourceTextForProcessing.trim()}
                  className="rounded-[22px] border border-cyan-300/35 bg-[linear-gradient(180deg,rgba(34,211,238,0.2),rgba(14,116,144,0.16))] px-4 py-3 text-sm font-medium text-cyan-50 shadow-[0_0_30px_rgba(34,211,238,0.18)] transition hover:border-cyan-200/55 disabled:cursor-not-allowed disabled:opacity-60"
                >
                  {isProcessing ? "Semantic Processing…" : "Semantic Processing"}
                </button>

                <p className="text-[12px] leading-5 text-slate-400">
                  Mock mode is runnable now. Resident Codex mode uses the existing <span className="font-mono text-slate-200">/urm/tools/call</span>
                  → <span className="font-mono text-slate-200">adeu.run_workflow</span> harness path and remains visibly scaffolded.
                </p>
              </section>

              <section className={cn(PANEL, "grid gap-3 p-4")}>
                <div>
                  <div className="text-[11px] uppercase tracking-[0.28em] text-cyan-200/70">overlay controls</div>
                  <h2 className="mt-1 text-lg font-semibold text-white">O / E / D / U visibility</h2>
                </div>
                <div className="grid gap-2">
                  {LANE_ORDER.map((lane) => (
                    <LaneToggleButton
                      key={lane}
                      lane={lane}
                      active={visibleLanes[lane]}
                      onToggle={() =>
                        setVisibleLanes((current) => ({
                          ...current,
                          [lane]: !current[lane],
                        }))
                      }
                    />
                  ))}
                </div>
                <button
                  type="button"
                  onClick={() => setShowDiagnostics((current) => !current)}
                  className={cn(
                    "rounded-2xl border px-3 py-2 text-sm transition",
                    showDiagnostics
                      ? "border-rose-300/30 bg-rose-300/10 text-rose-100"
                      : "border-white/10 bg-white/[0.03] text-slate-300",
                  )}
                >
                  {showDiagnostics ? "Diagnostics overlay on" : "Diagnostics overlay off"}
                </button>
              </section>

              <BridgeLegend />
            </aside>

            <section className="grid gap-4">
              <div className={cn(PANEL, "grid gap-4 p-4 sm:p-5")}> 
                <div className="flex flex-col gap-4 lg:flex-row lg:items-center lg:justify-between">
                  <div>
                    <div className="text-[11px] uppercase tracking-[0.28em] text-cyan-200/70">morphic surface</div>
                    <h2 className="mt-1 text-xl font-semibold text-white">Reference artifact and recomposition views</h2>
                  </div>
                  <div className="flex flex-wrap gap-2">
                    {([
                      ["artifact", "Artifact"],
                      ["local", "Local"],
                      ["spatial", "Spatial"],
                    ] as Array<[SurfaceView, string]>).map(([view, label]) => (
                      <button
                        key={view}
                        type="button"
                        onClick={() => setSurfaceView(view)}
                        className={cn(
                          "rounded-full border px-4 py-2 text-sm transition",
                          surfaceView === view
                            ? "border-cyan-400/35 bg-cyan-400/10 text-cyan-100"
                            : "border-white/10 bg-white/[0.03] text-slate-300",
                        )}
                      >
                        {label}
                      </button>
                    ))}
                  </div>
                </div>

                <div className="grid gap-4 lg:grid-cols-[minmax(0,0.92fr)_minmax(0,1.08fr)]">
                  <motion.section layout className={cn(SUBPANEL, "grid gap-4 p-4 sm:p-5")}>
                    <div className="flex flex-wrap items-center justify-between gap-3">
                      <div>
                        <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">reference artifact</div>
                        <h3 className="mt-1 text-lg font-semibold text-white">{currentArtifact.source.title}</h3>
                        <p className="mt-1 text-[12px] leading-5 text-slate-400">
                          {currentArtifact.source.authors.length > 0 ? currentArtifact.source.authors.join(", ") : "Operator pasted text"}
                          {currentArtifact.source.year ? ` · ${currentArtifact.source.year}` : ""}
                          {currentArtifact.source.venue ? ` · ${currentArtifact.source.venue}` : ""}
                        </p>
                      </div>
                      <div className="flex flex-wrap gap-2">
                        <StatusChip label={summarizeProcessingSource(currentArtifact)} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                        <StatusChip label={currentArtifact.processing.authority_posture.semantic_projection_authority} tone="border-amber-300/30 bg-amber-300/10 text-amber-100" />
                      </div>
                    </div>
                    <div className="rounded-[22px] border border-cyan-300/12 bg-cyan-300/[0.06] px-4 py-3 text-[12px] leading-5 text-cyan-50/80">
                      {artifactHeaderNote}
                    </div>
                    <ArtifactAnchorText
                      artifact={currentArtifact}
                      topLevelClaims={topLevelClaims}
                      selectedClaimId={selectedClaimId}
                      hoveredClaimId={hoveredClaimId}
                      claimById={claimById}
                      spanById={spanById}
                      fragmentById={fragmentById}
                      diagnosticById={diagnosticById}
                      showDiagnostics={showDiagnostics}
                      onSelectClaim={(claimId) => setSelectedClaimId(claimId)}
                      onHoverClaim={setHoveredClaimId}
                    />
                    <div className="grid gap-2 text-[12px] leading-5 text-slate-400">
                      <div className="flex flex-wrap gap-2">
                        <StatusChip label="source = authoritative anchor" tone="border-emerald-300/30 bg-emerald-300/10 text-emerald-100" />
                        <StatusChip label="inferred D / U = advisory only" tone="border-amber-300/30 bg-amber-300/10 text-amber-100" />
                      </div>
                      <p>
                        Hover or click a marked region to expose the local ODEU decomposition. The source text remains fixed while the semantic surface morphs around it.
                      </p>
                    </div>
                  </motion.section>

                  <AnimatePresence mode="wait">
                    {surfaceView === "artifact" ? (
                      <motion.section
                        key="artifact-view"
                        initial={{ opacity: 0, y: 12 }}
                        animate={{ opacity: 1, y: 0 }}
                        exit={{ opacity: 0, y: -10 }}
                        transition={{ duration: 0.22 }}
                        className={cn(SUBPANEL, "grid gap-4 p-4 sm:p-5")}
                      >
                        <div className="flex items-center justify-between gap-3">
                          <div>
                            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">artifact view</div>
                            <h3 className="mt-1 text-lg font-semibold text-white">Top-level claim anchors</h3>
                          </div>
                          <StatusChip label={`${topLevelClaims.length} claims`} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                        </div>
                        <div className="grid gap-3 xl:grid-cols-2">
                          {topLevelClaims.map((claim, index) => (
                            <ClaimCard
                              key={claim.claim_id}
                              claim={claim}
                              selected={focusClaimIdForSelection(selectedClaimId, claimById) === claim.claim_id}
                              code={`C${index + 1}`}
                              fragmentById={fragmentById}
                              diagnosticById={diagnosticById}
                              onClick={() => setSelectedClaimId(claim.claim_id)}
                            />
                          ))}
                        </div>
                      </motion.section>
                    ) : null}

                    {surfaceView === "local" ? (
                      <motion.section
                        key="local-view"
                        initial={{ opacity: 0, y: 12 }}
                        animate={{ opacity: 1, y: 0 }}
                        exit={{ opacity: 0, y: -10 }}
                        transition={{ duration: 0.22 }}
                        className={cn(SUBPANEL, "grid gap-4 p-4 sm:p-5")}
                      >
                        <div className="flex items-center justify-between gap-3">
                          <div>
                            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">local decomposition</div>
                            <h3 className="mt-1 text-lg font-semibold text-white">Selected claim through O / E / D / U</h3>
                          </div>
                          {selectedClaim ? (
                            <StatusChip label={prettyConfidence(selectedClaim.confidence)} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                          ) : null}
                        </div>
                        {selectedClaim ? (
                          <>
                            <motion.div layoutId={`claim-focus-${selectedClaim.claim_id}`} className="rounded-[24px] border border-cyan-400/20 bg-cyan-400/[0.08] p-4">
                              <div className="flex flex-wrap items-center gap-2">
                                <StatusChip label={selectedClaim.status} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                                <StatusChip label={selectedClaim.explicitness} tone="border-sky-300/25 bg-sky-300/10 text-sky-100" />
                                <StatusChip label={`${selectedClaimSubclaims.length} subclaims`} tone="border-white/10 bg-white/[0.04] text-slate-300" />
                              </div>
                              <p className="mt-3 text-sm leading-7 text-slate-100/90">{selectedClaim.claim_text}</p>
                            </motion.div>
                            <div className="grid gap-3 xl:grid-cols-2">
                              {LANE_ORDER.map((lane) => (
                                <LanePanel
                                  key={lane}
                                  lane={lane}
                                  fragments={fragmentsForLane(selectedClaim, lane, fragmentById)}
                                  visible={visibleLanes[lane]}
                                  diagnosticsById={diagnosticById}
                                />
                              ))}
                            </div>
                            {selectedClaimSubclaims.length > 0 ? (
                              <div className="grid gap-3">
                                <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">Depth 2 subclaims</div>
                                <div className="grid gap-3 xl:grid-cols-2">
                                  {selectedClaimSubclaims.map((claim, index) => (
                                    <ClaimCard
                                      key={claim.claim_id}
                                      claim={claim}
                                      selected={selectedClaimId === claim.claim_id}
                                      code={`S${index + 1}`}
                                      fragmentById={fragmentById}
                                      diagnosticById={diagnosticById}
                                      onClick={() => setSelectedClaimId(claim.claim_id)}
                                    />
                                  ))}
                                </div>
                              </div>
                            ) : null}
                          </>
                        ) : (
                          <div className="rounded-[24px] border border-white/8 bg-white/[0.03] p-4 text-sm text-slate-400">
                            Select a claim anchor to inspect its local decomposition.
                          </div>
                        )}
                      </motion.section>
                    ) : null}

                    {surfaceView === "spatial" ? (
                      <motion.section
                        key="spatial-view"
                        initial={{ opacity: 0, y: 12 }}
                        animate={{ opacity: 1, y: 0 }}
                        exit={{ opacity: 0, y: -10 }}
                        transition={{ duration: 0.22 }}
                        className={cn(SUBPANEL, "grid min-h-[540px] gap-4 p-4 sm:p-5")}
                      >
                        <div className="flex flex-col gap-2 sm:flex-row sm:items-center sm:justify-between">
                          <div>
                            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">spatial recomposition</div>
                            <h3 className="mt-1 text-lg font-semibold text-white">Same artifact, redistributed across O / E / D / U lanes</h3>
                          </div>
                          <div className="flex flex-wrap gap-2">
                            <StatusChip label={`${visibleLaneIds.length} lanes visible`} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                            <StatusChip label={selectedFocusClaim ? "focused claim" : "all claims"} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                          </div>
                        </div>
                        <div className="grid min-h-[430px] gap-4 lg:grid-cols-[minmax(0,0.86fr)_minmax(0,1.14fr)]">
                          <div className="rounded-[24px] border border-white/8 bg-black/10 p-4">
                            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">lane summary</div>
                            <div className="mt-4 grid gap-3">
                              {LANE_ORDER.map((lane) => {
                                const laneMeta = LANE_META[lane];
                                const count = currentArtifact.lane_fragments.filter(
                                  (fragment) => fragment.lane === lane,
                                ).length;
                                return (
                                  <div
                                    key={lane}
                                    className="rounded-[22px] border p-3"
                                    style={{
                                      borderColor: visibleLanes[lane] ? `${laneMeta.color}44` : "rgba(255,255,255,0.08)",
                                      backgroundColor: visibleLanes[lane] ? laneMeta.softColor : "rgba(255,255,255,0.03)",
                                    }}
                                  >
                                    <div className="flex items-center justify-between gap-3">
                                      <div>
                                        <div className="text-[11px] uppercase tracking-[0.24em]" style={{ color: laneMeta.color }}>
                                          {laneMeta.short}
                                        </div>
                                        <div className="mt-1 text-sm font-medium text-slate-100">{laneMeta.title}</div>
                                      </div>
                                      <StatusChip label={`${count} nodes`} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                                    </div>
                                    <p className="mt-2 text-[12px] leading-5 text-slate-400">{laneMeta.subtitle}</p>
                                  </div>
                                );
                              })}
                            </div>
                          </div>
                          <div className="overflow-hidden rounded-[24px] border border-white/8 bg-[#020914]">
                            <SpatialLaneScene
                              artifact={currentArtifact}
                              selectedClaimId={selectedClaimId}
                              visibleLanes={visibleLaneIds}
                              onSelectClaim={(claimId) => setSelectedClaimId(claimId)}
                            />
                          </div>
                        </div>
                      </motion.section>
                    ) : null}
                  </AnimatePresence>
                </div>
              </div>
            </section>

            <aside className="grid gap-4">
              <section className={cn(PANEL, "grid gap-4 p-4")}> 
                <div className="flex items-start justify-between gap-3">
                  <div>
                    <div className="text-[11px] uppercase tracking-[0.28em] text-cyan-200/70">inspector</div>
                    <h2 className="mt-1 text-lg font-semibold text-white">Selected concept</h2>
                  </div>
                  {selectedClaim ? <StatusChip label={selectedClaim.claim_id.split("::").slice(-1)[0]} tone="border-white/10 bg-white/[0.04] text-slate-300" /> : null}
                </div>
                {selectedClaim ? (
                  <div className="grid gap-4">
                    <motion.div layoutId={`claim-focus-${selectedClaim.claim_id}`} className="rounded-[24px] border border-white/8 bg-white/[0.03] p-4">
                      <div className="flex flex-wrap gap-2">
                        <StatusChip label={selectedClaim.explicitness} tone="border-sky-300/25 bg-sky-300/10 text-sky-100" />
                        <StatusChip label={prettyConfidence(selectedClaim.confidence)} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                        <StatusChip label={selectedClaim.status} tone="border-white/10 bg-white/[0.04] text-slate-300" />
                      </div>
                      <p className="mt-3 text-sm leading-7 text-slate-100/90">{selectedClaim.claim_text}</p>
                      <p className="mt-3 text-[12px] leading-5 text-slate-400">{selectedClaim.summary}</p>
                    </motion.div>

                    <div className="rounded-[24px] border border-white/8 bg-white/[0.03] p-4">
                      <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">local diagnostics</div>
                      <div className="mt-3 flex flex-wrap gap-2">
                        {selectedClaimDiagnostics.length > 0 ? (
                          selectedClaimDiagnostics.map((diagnostic) => (
                            <DiagnosticPill key={diagnostic.diagnostic_id} diagnostic={diagnostic} />
                          ))
                        ) : (
                          <span className="text-sm text-slate-400">No claim-local diagnostics emitted.</span>
                        )}
                      </div>
                    </div>

                    <div className="rounded-[24px] border border-white/8 bg-white/[0.03] p-4">
                      <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">cross-lane bridges</div>
                      <div className="mt-3 grid gap-3">
                        {selectedClaimBridges.length > 0 ? (
                          selectedClaimBridges.map((bridge) => {
                            const bridgeDiagnostics = bridge.diagnostic_ids
                              .map((id) => diagnosticById[id])
                              .filter((item): item is ODEUSemanticDiagnostic => Boolean(item));
                            return (
                              <div key={bridge.bridge_id} className="rounded-2xl border border-white/8 bg-black/15 p-3">
                                <div className="flex items-center justify-between gap-3">
                                  <span className="text-[11px] uppercase tracking-[0.2em] text-slate-400">{sentenceCase(bridge.kind)}</span>
                                  <StatusChip label={prettyConfidence(bridge.confidence)} tone="border-white/10 bg-white/[0.04] text-slate-200" />
                                </div>
                                <p className="mt-2 text-[12px] leading-5 text-slate-300/85">{bridge.rationale}</p>
                                {bridgeDiagnostics.length > 0 ? (
                                  <div className="mt-3 flex flex-wrap gap-2">
                                    {bridgeDiagnostics.map((diagnostic) => (
                                      <DiagnosticPill key={diagnostic.diagnostic_id} diagnostic={diagnostic} />
                                    ))}
                                  </div>
                                ) : null}
                              </div>
                            );
                          })
                        ) : (
                          <span className="text-sm text-slate-400">No bridge metadata recorded for this claim yet.</span>
                        )}
                      </div>
                    </div>
                  </div>
                ) : (
                  <div className="rounded-[24px] border border-white/8 bg-white/[0.03] p-4 text-sm text-slate-400">
                    Select a claim region or claim card to inspect its ODEU structure.
                  </div>
                )}
              </section>

              <LiveScaffoldPanel
                pipelineMode={pipelineMode}
                harnessStatus={harnessStatus}
                requestPreview={liveRequestPreview}
                promptPreview={livePromptPreview}
                runRef={liveRunRef}
                evidence={liveEvidence}
                liveError={liveError}
                onReloadEvidence={() => void refreshEvidence()}
                isLoadingEvidence={isLoadingEvidence}
              />
            </aside>
          </div>
        </LayoutGroup>

        <section className={cn(PANEL, "grid gap-4 p-4 sm:p-5")}>
          <div className="flex flex-col gap-3 sm:flex-row sm:items-center sm:justify-between">
            <div>
              <div className="text-[11px] uppercase tracking-[0.28em] text-cyan-200/70">bottom input panel</div>
              <h2 className="mt-1 text-lg font-semibold text-white">Paste a new abstract or paragraph</h2>
            </div>
            <p className="max-w-xl text-[12px] leading-5 text-slate-400">
              The mock path will heuristically decompose arbitrary abstract-size text. The live path packages the same input into a typed resident-worker request through the existing ADEU harness.
            </p>
          </div>
          <div className="grid gap-4 xl:grid-cols-[minmax(0,1fr)_340px]">
            <div className="grid gap-3">
              <label className="grid gap-2 text-sm text-slate-300/80">
                <span className="text-[11px] uppercase tracking-[0.22em] text-slate-400">title override</span>
                <input
                  value={pastedTitle}
                  onChange={(event) => setPastedTitle(event.target.value)}
                  placeholder={selectedSample.title}
                  className="rounded-2xl border border-white/10 bg-white/[0.04] px-4 py-3 text-sm text-slate-50 outline-none placeholder:text-slate-500"
                />
              </label>
              <label className="grid gap-2 text-sm text-slate-300/80">
                <span className="text-[11px] uppercase tracking-[0.22em] text-slate-400">source text</span>
                <textarea
                  value={pastedText}
                  onChange={(event) => setPastedText(event.target.value)}
                  placeholder="Paste a paper abstract or a bounded paragraph here."
                  className="min-h-[220px] rounded-[24px] border border-white/10 bg-white/[0.04] px-4 py-4 text-sm leading-7 text-slate-100 outline-none placeholder:text-slate-500"
                />
              </label>
            </div>
            <div className="grid gap-3">
              <div className="rounded-[24px] border border-white/8 bg-white/[0.03] p-4">
                <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">active source preview</div>
                <h3 className="mt-2 text-base font-semibold text-slate-50">{titleForProcessing}</h3>
                <p className="mt-3 text-[12px] leading-6 text-slate-300/80">{sourceTextForProcessing.slice(0, 320)}{sourceTextForProcessing.length > 320 ? "…" : ""}</p>
              </div>
              <div className="rounded-[24px] border border-white/8 bg-white/[0.03] p-4 text-[12px] leading-5 text-slate-400">
                <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">processing doctrine</div>
                <ul className="mt-3 grid gap-2 pl-4">
                  <li>Anchor explicit claims to spans before projecting structure.</li>
                  <li>Infer D and U only when needed, and mark them as inferred.</li>
                  <li>Expose bridge weakness instead of laundering certainty.</li>
                  <li>Keep the module bounded to abstract-size artifacts only.</li>
                </ul>
              </div>
            </div>
          </div>
        </section>

        <footer className={cn(PANEL, "grid gap-3 p-4 text-[12px] text-slate-300/80 sm:grid-cols-2 xl:grid-cols-5")}>
          <div>
            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">morph profile</div>
            <div className="mt-1 font-mono text-slate-100">paper_semantic_workbench@1</div>
          </div>
          <div>
            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">mode</div>
            <div className="mt-1">{surfaceView} · {pipelineMode}</div>
          </div>
          <div>
            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">selected concept</div>
            <div className="mt-1 font-mono text-slate-100">{selectedClaimId ?? "none"}</div>
          </div>
          <div>
            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">diagnostics</div>
            <div className="mt-1">{showDiagnostics ? `${currentArtifact.diagnostics.length} active overlay findings` : "overlay hidden"}</div>
          </div>
          <div>
            <div className="text-[11px] uppercase tracking-[0.22em] text-slate-400">authority</div>
            <div className="mt-1">source anchor preserved · no commit surface</div>
          </div>
        </footer>
      </div>
    </main>
  );
}
