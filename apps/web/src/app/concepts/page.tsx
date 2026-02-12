"use client";

import Link from "next/link";
import { useMemo, useState } from "react";

import { apiBase } from "../lib/api-base";
import { SolverDiffPanel, type KernelMode } from "../components/solver-diff-panel";
import type { CheckReason, CheckReport } from "../../gen/check_report";

type SourceSpan = { start: number; end: number };

type ConceptProvenance = {
  doc_ref?: string | null;
  span?: SourceSpan | null;
};

type ConceptPatchOp = {
  op: "add" | "remove" | "replace" | "move" | "copy" | "test";
  path: string;
  from?: string;
  value?: unknown;
};

type ConceptClaim = {
  id: string;
  sense_id: string;
  text: string;
  provenance?: ConceptProvenance | null;
};

type ConceptLink = {
  id: string;
  kind: "commitment" | "incompatibility" | "presupposition";
  src_sense_id: string;
  dst_sense_id: string;
  provenance?: ConceptProvenance | null;
};

type ConceptAmbiguity = {
  id: string;
  term_id: string;
  options: string[];
  option_details_by_id?: Record<string, ConceptAmbiguityOption>;
  option_labels_by_id?: Record<string, string> | null;
};

type ConceptAmbiguityOption = {
  option_id: string;
  label: string;
  variant_ir_id?: string | null;
  patch?: ConceptPatchOp[];
};

type ConceptSense = {
  id: string;
  term_id: string;
  gloss: string;
  provenance?: ConceptProvenance | null;
};

type ConceptTerm = {
  id: string;
  label: string;
  provenance?: ConceptProvenance | null;
};

type ConceptIR = {
  schema_version: string;
  concept_id: string;
  context: { doc_id: string; domain_tags?: string[] };
  terms: ConceptTerm[];
  senses: ConceptSense[];
  claims: ConceptClaim[];
  links: ConceptLink[];
  ambiguity: ConceptAmbiguity[];
  bridges?: unknown[];
};

type ProposeCandidate = {
  ir: ConceptIR;
  check_report: CheckReport;
  rank: number;
};

type ProposerAttempt = {
  attempt_idx: number;
  status: "PASS" | "WARN" | "REFUSE" | "PARSE_ERROR";
  reason_codes_summary: string[];
};

type ProposerLog = {
  provider: string;
  api?: string | null;
  model?: string | null;
  created_at: string;
  attempts: ProposerAttempt[];
};

type ProposeResponse = {
  provider: { kind: string; api?: string | null; model?: string | null };
  candidates: ProposeCandidate[];
  proposer_log: ProposerLog;
};

type AnalyzeConstraint = {
  atom_name: string;
  object_id?: string | null;
  json_path?: string | null;
  label?: string | null;
};

type AnalyzeClosureEdge = {
  src_sense_id: string;
  dst_sense_id: string;
  kind: "commitment" | "presupposition";
};

type ConceptAnalysis = {
  closure: {
    status: "COMPLETE" | "PARTIAL" | "UNAVAILABLE";
    edge_count: number;
    edges: AnalyzeClosureEdge[];
    details?: string | null;
  };
  mic: {
    status: "COMPLETE" | "PARTIAL" | "UNAVAILABLE";
    constraint_count: number;
    constraints: AnalyzeConstraint[];
    shrink_iters: number;
    solver_calls: number;
    details?: string | null;
  };
};

type ConceptAnalyzeResponse = {
  ir: ConceptIR;
  check_report: CheckReport;
  analysis: ConceptAnalysis;
};

type ConceptApplyResponse = {
  patched_ir: ConceptIR;
  check_report: CheckReport;
};

type ConceptQuestionAnchor = {
  object_id?: string | null;
  json_path?: string | null;
  label?: string | null;
  span?: SourceSpan | null;
};

type ConceptQuestionAnswer = {
  option_id: string;
  label: string;
  variant_ir_id?: string | null;
  patch?: ConceptPatchOp[];
};

type ConceptQuestion = {
  question_id: string;
  signal: "mic" | "forced_countermodel" | "disconnected_clusters";
  prompt: string;
  anchors: ConceptQuestionAnchor[];
  answers: ConceptQuestionAnswer[];
};

type TournamentMode = "live_generation" | "replay_candidates";

type ConceptTournamentCandidateInput = {
  question_id: string;
  patch_ops: ConceptPatchOp[];
};

type BridgeLossSignal = {
  signal_kind: string;
  affected_anchors: string[];
  severity: "low" | "medium" | "high";
};

type TournamentScoreMetadata = {
  score_version: "concepts.tscore.v2";
  objective_dimensions: string[];
  tie_break_order: "objective_vector_desc_then_stable_id_asc";
};

type TournamentTieBreakProvenance = {
  stable_id: string;
  objective_dimensions: string[];
  tie_break_order: "objective_vector_desc_then_stable_id_asc";
};

type ConceptTournamentCandidateResult = {
  candidate_id: string;
  question_id: string;
  rank: number;
  improved: boolean;
  objective_vector: number[];
  patch_ops: ConceptPatchOp[];
  check_report: CheckReport;
  analysis?: ConceptAnalysis | null;
  diff_report: {
    summary?: {
      status_flip?: string;
      solver_pairing_state?: string;
      structural_patch_count?: string;
      solver_touched_atom_count?: string;
      causal_atom_count?: string;
    };
  };
  score_version: "concepts.tscore.v2";
  tie_break_provenance: TournamentTieBreakProvenance;
  bridge_loss_signals: BridgeLossSignal[];
  mapping_trust?: string | null;
  solver_trust?: "kernel_only" | "solver_backed" | "proof_checked";
  proof_trust?: string | null;
};

type ConceptTournamentResponse = {
  tournament_mode: TournamentMode;
  provider: "mock" | "openai";
  tournament_score_version: "concepts.tscore.v2";
  base_ir_hash: string;
  base_objective_vector: number[];
  score_metadata: TournamentScoreMetadata;
  no_safe_improvement: boolean;
  selected_candidate_id?: string | null;
  candidate_count: number;
  evaluated_count: number;
  candidates: ConceptTournamentCandidateResult[];
  budget_report: ConceptQuestionsBudgetReport;
  bridge_loss_signals: BridgeLossSignal[];
  mapping_trust?: string | null;
  solver_trust?: "kernel_only" | "solver_backed" | "proof_checked";
  proof_trust?: string | null;
};

type ConceptQuestionsBudgetReport = {
  budget_version: "budget.v1";
  max_solver_calls: number;
  used_solver_calls: number;
  max_dry_runs: number;
  used_dry_runs: number;
  truncated: boolean;
  truncation_reason?: string | null;
};

type ConceptQuestionsMeta = {
  question_count: number;
  max_questions: number;
  max_answers_per_question: number;
  question_rank_version: "concepts.qrank.v2";
  budget_report: ConceptQuestionsBudgetReport;
  bridge_loss_signals: BridgeLossSignal[];
  mapping_trust?: string | null;
  solver_trust?: "kernel_only" | "solver_backed" | "proof_checked";
  proof_trust?: string | null;
};

type ConceptQuestionsResponse = {
  check_report: CheckReport;
  questions: ConceptQuestion[];
} & ConceptQuestionsMeta;

type ConceptAlignmentArtifactRef = {
  artifact_id: string;
  doc_id?: string | null;
  concept_id: string;
};

type ConceptAlignmentTermRef = {
  artifact_id: string;
  doc_id?: string | null;
  concept_id: string;
  term_id: string;
  label: string;
  normalized_label: string;
};

type ConceptAlignmentSenseRef = {
  artifact_id: string;
  doc_id?: string | null;
  concept_id: string;
  sense_id: string;
  term_id: string;
  gloss: string;
  gloss_signature: string;
};

type ConceptAlignmentSuggestion = {
  suggestion_id: string;
  suggestion_fingerprint: string;
  kind: "merge_candidate" | "conflict_candidate";
  vocabulary_key: string;
  reason: string;
  artifact_ids: string[];
  doc_ids: string[];
  term_refs: ConceptAlignmentTermRef[];
  sense_refs: ConceptAlignmentSenseRef[];
};

type ConceptAlignmentStats = {
  merge_candidate_count: number;
  conflict_candidate_count: number;
};

type ConceptAlignmentCoherenceDiagnostics = {
  vocabulary_drift_count: number;
  suggestion_stability_count: number;
  term_use_consistency_count: number;
};

type ConceptAlignResponse = {
  artifacts: ConceptAlignmentArtifactRef[];
  suggestion_count: number;
  suggestions: ConceptAlignmentSuggestion[];
  alignment_stats: ConceptAlignmentStats;
  coherence_diagnostics: ConceptAlignmentCoherenceDiagnostics;
  mapping_trust: string;
  solver_trust: "kernel_only" | "solver_backed" | "proof_checked";
  proof_trust?: string | null;
};

type QuestionLifecycleStatus = "applied" | "resolved";

type QuestionLifecycleEntry = {
  key: string;
  signal_kind: ConceptQuestion["signal"];
  prompt: string;
  answer_option_id: string;
  answer_label: string;
  status: QuestionLifecycleStatus;
};

type ConceptArtifactCreateResponse = {
  artifact_id: string;
  created_at: string;
  check_report: CheckReport;
  analysis?: ConceptAnalysis | null;
};

type Highlight = { span: SourceSpan; label: string } | null;
const ALIGNMENT_MAX_SUGGESTIONS_MIN = 1;
const ALIGNMENT_MAX_SUGGESTIONS_MAX = 500;
const ALIGNMENT_MAX_SUGGESTIONS_DEFAULT = 100;
const ALIGNMENT_SENSE_REFS_PREVIEW_LIMIT = 6;
const TOURNAMENT_TOP_K_DEFAULT = 4;

function stableJson(value: unknown): string {
  if (value === null || typeof value !== "object") {
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => stableJson(item)).join(",")}]`;
  }
  const entries = Object.entries(value as Record<string, unknown>)
    .filter(([, item]) => item !== undefined)
    .sort(([left], [right]) => left.localeCompare(right));
  return `{${entries.map(([key, item]) => `${JSON.stringify(key)}:${stableJson(item)}`).join(",")}}`;
}

async function sha256Hex(value: string): Promise<string> {
  const digest = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(value));
  return Array.from(new Uint8Array(digest), (byte) => byte.toString(16).padStart(2, "0")).join(
    "",
  );
}

async function conceptIrHash(ir: ConceptIR): Promise<string> {
  return sha256Hex(stableJson(ir));
}

function questionResolutionKey(question: ConceptQuestion, optionId: string): string {
  const anchorObjectIds = Array.from(
    new Set(
      question.anchors
        .map((anchor) => anchor.object_id ?? null)
        .filter((value): value is string => typeof value === "string" && value.length > 0),
    ),
  ).sort();
  const anchorJsonPaths = Array.from(
    new Set(
      question.anchors
        .map((anchor) => anchor.json_path ?? null)
        .filter((value): value is string => typeof value === "string" && value.length > 0),
    ),
  ).sort();
  return stableJson({
    signal_kind: question.signal,
    anchor_object_ids: anchorObjectIds,
    anchor_json_paths: anchorJsonPaths,
    selected_answer_option_id: optionId,
  });
}

function questionAnswerKeys(questions: ConceptQuestion[]): Set<string> {
  const keys = new Set<string>();
  for (const question of questions) {
    for (const answer of question.answers) {
      keys.add(questionResolutionKey(question, answer.option_id));
    }
  }
  return keys;
}

function conceptApiErrorMessage(raw: string): string {
  try {
    const parsed = JSON.parse(raw) as {
      detail?: {
        code?: string;
        message?: string;
        errors?: Array<{ code?: string; path?: string; message?: string }>;
      };
    };
    const detail = parsed.detail;
    if (detail?.errors?.length) {
      return detail.errors
        .map((item) => `${item.code ?? "ERROR"} ${item.path ?? ""} ${item.message ?? ""}`.trim())
        .join("\n");
    }
    if (
      detail?.code === "STALE_IR" ||
      detail?.code === "TOURNAMENT_STALE_IR_HASH_MISMATCH"
    ) {
      return `${detail.code} ${detail.message ?? ""}`.trim();
    }
  } catch {
    // fall back to raw response body for non-JSON payloads
  }
  return raw;
}

function clampSpan(text: string, span: SourceSpan): SourceSpan | null {
  const start = Math.max(0, Math.min(text.length, span.start));
  const end = Math.max(0, Math.min(text.length, span.end));
  if (start >= end) return null;
  return { start, end };
}

function spanFromConceptRef(
  ir: ConceptIR,
  objectId?: string | null,
  jsonPath?: string | null,
): SourceSpan | null {
  if (objectId) {
    const claim = ir.claims?.find((item) => item.id === objectId);
    if (claim?.provenance?.span) return claim.provenance.span;

    const link = ir.links?.find((item) => item.id === objectId);
    if (link?.provenance?.span) return link.provenance.span;

    const sense = ir.senses?.find((item) => item.id === objectId);
    if (sense?.provenance?.span) return sense.provenance.span;

    const term = ir.terms?.find((item) => item.id === objectId);
    if (term?.provenance?.span) return term.provenance.span;
  }

  const path = jsonPath ?? "";
  const claimPrefix = "/claims/";
  if (path.startsWith(claimPrefix)) {
    const idx = Number.parseInt(path.slice(claimPrefix.length).split("/")[0], 10);
    const claim = Number.isFinite(idx) ? ir.claims?.[idx] : undefined;
    if (claim?.provenance?.span) return claim.provenance.span;
  }

  const linkPrefix = "/links/";
  if (path.startsWith(linkPrefix)) {
    const idx = Number.parseInt(path.slice(linkPrefix.length).split("/")[0], 10);
    const link = Number.isFinite(idx) ? ir.links?.[idx] : undefined;
    if (link?.provenance?.span) return link.provenance.span;
  }

  return null;
}

function spanFromReason(ir: ConceptIR, reason: CheckReason): SourceSpan | null {
  const provenance = reason.provenance?.span ?? null;
  if (provenance) return provenance;
  return spanFromConceptRef(ir, reason.object_id ?? null, reason.json_path ?? null);
}

function parseScopeIds(raw: string): string[] {
  return Array.from(
    new Set(
      raw
        .split(/[\n,\s]+/)
        .map((item) => item.trim())
        .filter((item) => item.length > 0),
    ),
  ).sort();
}

type QuestionCardProps = {
  question: ConceptQuestion;
  selectedIr: ConceptIR | null;
  questionHistoryMap: ReadonlyMap<string, QuestionLifecycleStatus>;
  activeQuestionOptionKey: string | null;
  activeTournamentQuestionId: string | null;
  tournamentResult: ConceptTournamentResponse | null;
  onApplyAnswer: (
    question: ConceptQuestion,
    answer: ConceptQuestionAnswer,
  ) => void | Promise<void>;
  onRunTournament: (question: ConceptQuestion) => void | Promise<void>;
  onClearTournament: (questionId: string) => void;
  onAnchorHighlight: (span: SourceSpan, label: string) => void;
};

function QuestionCard({
  question,
  selectedIr,
  questionHistoryMap,
  activeQuestionOptionKey,
  activeTournamentQuestionId,
  tournamentResult,
  onApplyAnswer,
  onRunTournament,
  onClearTournament,
  onAnchorHighlight,
}: QuestionCardProps) {
  const patchAnswerCount = question.answers.filter(
    (answer) => Array.isArray(answer.patch) && answer.patch.length > 0,
  ).length;
  const isRunningTournament = activeTournamentQuestionId === question.question_id;

  return (
    <div
      style={{
        marginTop: 8,
        border: "1px solid var(--border)",
        borderRadius: 8,
        background: "#fff",
        padding: 8,
      }}
    >
      <div className="muted mono">
        {question.signal} · {question.question_id}
      </div>
      <div style={{ marginTop: 4 }}>{question.prompt}</div>
      {question.anchors.length ? (
        <div className="row" style={{ marginTop: 6 }}>
          {question.anchors.map((anchor, idx) => {
            const span =
              anchor.span ??
              (selectedIr
                ? spanFromConceptRef(
                    selectedIr,
                    anchor.object_id ?? null,
                    anchor.json_path ?? null,
                  )
                : null);
            const label =
              anchor.label ||
              anchor.json_path ||
              anchor.object_id ||
              `anchor_${idx + 1}`;
            return (
              <button
                key={`${question.question_id}:anchor:${idx}`}
                onClick={() => {
                  if (!span) return;
                  onAnchorHighlight(span, `question:${label}`);
                }}
                disabled={!span}
              >
                Anchor {idx + 1}
              </button>
            );
          })}
        </div>
      ) : null}
      <div className="row" style={{ marginTop: 6 }}>
        {question.answers.map((answer) => {
          const resolutionKey = questionResolutionKey(question, answer.option_id);
          const lifecycle = questionHistoryMap.get(resolutionKey);
          const statusLabel =
            lifecycle === "applied"
              ? "Applied"
              : lifecycle === "resolved"
                ? "Resolved"
                : "Open";
          const hasPatch = Boolean(answer.patch?.length);
          return (
            <button
              key={`${question.question_id}:${answer.option_id}`}
              onClick={() => onApplyAnswer(question, answer)}
              disabled={
                !hasPatch ||
                (activeQuestionOptionKey !== null &&
                  activeQuestionOptionKey !== resolutionKey)
              }
              title={!hasPatch ? "Answer does not provide a patch action" : undefined}
            >
              {activeQuestionOptionKey === resolutionKey
                ? "Applying..."
                : `${statusLabel}: ${answer.label}`}
            </button>
          );
        })}
      </div>
      <div className="row" style={{ marginTop: 6 }}>
        <button
          onClick={() => onRunTournament(question)}
          disabled={
            patchAnswerCount === 0 ||
            (activeTournamentQuestionId !== null &&
              activeTournamentQuestionId !== question.question_id)
          }
          title={
            patchAnswerCount === 0
              ? "Need at least one patch-actionable answer"
              : undefined
          }
        >
          {isRunningTournament
            ? "Running tournament..."
            : `Run tournament (${patchAnswerCount})`}
        </button>
        <button
          onClick={() => onClearTournament(question.question_id)}
          disabled={!tournamentResult || isRunningTournament}
        >
          Clear tournament
        </button>
      </div>
      {tournamentResult ? (
        <div style={{ marginTop: 6 }}>
          <div className="muted mono">
            score={tournamentResult.tournament_score_version} mode=
            {tournamentResult.tournament_mode} selected=
            {tournamentResult.selected_candidate_id ?? "none"} safe=
            {tournamentResult.no_safe_improvement
              ? "no_safe_improvement"
              : "improvement_found"}
          </div>
          <div className="muted mono" style={{ marginTop: 2 }}>
            candidates={tournamentResult.candidate_count} evaluated=
            {tournamentResult.evaluated_count} top_k=
            {tournamentResult.candidates.length} dry_runs=
            {tournamentResult.budget_report.used_dry_runs}/
            {tournamentResult.budget_report.max_dry_runs} solver_calls=
            {tournamentResult.budget_report.used_solver_calls}/
            {tournamentResult.budget_report.max_solver_calls}
            {tournamentResult.budget_report.truncated
              ? ` truncated:${tournamentResult.budget_report.truncation_reason ?? "unknown"}`
              : ""}
          </div>
          <div style={{ marginTop: 4 }}>
            {tournamentResult.candidates.map((candidate) => (
              <div
                key={candidate.candidate_id}
                className="muted mono"
                style={{ marginTop: 2 }}
              >
                #{candidate.rank} {candidate.improved ? "improved" : "no_change"} ·{" "}
                {candidate.candidate_id} · status={candidate.check_report.status} · obj=
                [{candidate.objective_vector.join(",")}]
                {candidate.diff_report.summary
                  ? ` · flip=${candidate.diff_report.summary.status_flip ?? "n/a"}`
                  : ""}
              </div>
            ))}
          </div>
        </div>
      ) : null}
    </div>
  );
}

export default function ConceptsPage() {
  const [sourceText, setSourceText] = useState<string>("");
  const [provider, setProvider] = useState<"mock" | "openai">("mock");
  const [mode, setMode] = useState<KernelMode>("LAX");
  const [isProposing, setIsProposing] = useState<boolean>(false);
  const [isLoadingQuestions, setIsLoadingQuestions] = useState<boolean>(false);
  const [isLoadingAlignment, setIsLoadingAlignment] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);
  const [artifactId, setArtifactId] = useState<string | null>(null);
  const [activeOptionKey, setActiveOptionKey] = useState<string | null>(null);
  const [activeQuestionOptionKey, setActiveQuestionOptionKey] = useState<string | null>(null);
  const [alignmentArtifactIdsInput, setAlignmentArtifactIdsInput] = useState<string>("");
  const [alignmentDocIdsInput, setAlignmentDocIdsInput] = useState<string>("");
  const [alignmentMaxSuggestions, setAlignmentMaxSuggestions] = useState<number>(
    ALIGNMENT_MAX_SUGGESTIONS_DEFAULT,
  );
  const [alignmentResult, setAlignmentResult] = useState<ConceptAlignResponse | null>(null);

  const [proposerLog, setProposerLog] = useState<ProposerLog | null>(null);
  const [candidates, setCandidates] = useState<ProposeCandidate[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [compareIdx, setCompareIdx] = useState<number | null>(null);
  const [analyses, setAnalyses] = useState<Array<ConceptAnalysis | null>>([]);
  const [questionsByVariant, setQuestionsByVariant] = useState<Array<ConceptQuestion[] | null>>([]);
  const [questionsMetaByVariant, setQuestionsMetaByVariant] = useState<
    Array<ConceptQuestionsMeta | null>
  >([]);
  const [questionHistoryByVariant, setQuestionHistoryByVariant] = useState<
    Array<QuestionLifecycleEntry[]>
  >([]);
  const [tournamentByVariant, setTournamentByVariant] = useState<
    Array<Record<string, ConceptTournamentResponse>>
  >([]);
  const [activeTournamentQuestionId, setActiveTournamentQuestionId] = useState<string | null>(
    null,
  );
  const [highlight, setHighlight] = useState<Highlight>(null);

  const selected = useMemo(() => candidates[selectedIdx] ?? null, [candidates, selectedIdx]);
  const selectedIr = useMemo(() => selected?.ir ?? null, [selected]);
  const selectedReport = useMemo(() => selected?.check_report ?? null, [selected]);
  const selectedAnalysis = useMemo(() => analyses[selectedIdx] ?? null, [analyses, selectedIdx]);
  const selectedQuestions = useMemo(
    () => questionsByVariant[selectedIdx] ?? null,
    [questionsByVariant, selectedIdx],
  );
  const selectedQuestionsMeta = useMemo(
    () => questionsMetaByVariant[selectedIdx] ?? null,
    [questionsMetaByVariant, selectedIdx],
  );
  const selectedQuestionHistory = useMemo(
    () => questionHistoryByVariant[selectedIdx] ?? [],
    [questionHistoryByVariant, selectedIdx],
  );
  const selectedTournamentByQuestion = useMemo(
    () => tournamentByVariant[selectedIdx] ?? {},
    [tournamentByVariant, selectedIdx],
  );
  const selectedQuestionHistoryMap = useMemo(
    () => new Map(selectedQuestionHistory.map((entry) => [entry.key, entry.status])),
    [selectedQuestionHistory],
  );
  const questionLifecycleSummary = useMemo(() => {
    const totalResolved = selectedQuestionHistory.filter((entry) => entry.status === "resolved").length;
    if (!selectedQuestions) {
      return { open: 0, applied: 0, resolved: totalResolved };
    }
    let open = 0;
    let applied = 0;
    for (const question of selectedQuestions) {
      for (const answer of question.answers) {
        const key = questionResolutionKey(question, answer.option_id);
        const status = selectedQuestionHistoryMap.get(key);
        if (status === "applied") {
          applied += 1;
        } else if (status !== "resolved") {
          open += 1;
        }
      }
    }
    return { open, applied, resolved: totalResolved };
  }, [selectedQuestionHistory, selectedQuestionHistoryMap, selectedQuestions]);

  const compared = useMemo(
    () => (compareIdx === null ? null : candidates[compareIdx] ?? null),
    [candidates, compareIdx],
  );

  function setQuestionHistoryForVariant(
    variantIdx: number,
    updater: (current: QuestionLifecycleEntry[]) => QuestionLifecycleEntry[],
  ) {
    setQuestionHistoryByVariant((prev) => {
      const next = [...prev];
      while (next.length <= variantIdx) next.push([]);
      next[variantIdx] = updater(next[variantIdx] ?? []);
      return next;
    });
  }

  function setTournamentForVariant(
    variantIdx: number,
    questionId: string,
    response: ConceptTournamentResponse | null,
  ) {
    setTournamentByVariant((prev) => {
      const next = [...prev];
      while (next.length <= variantIdx) next.push({});
      const current = { ...(next[variantIdx] ?? {}) };
      if (response === null) {
        delete current[questionId];
      } else {
        current[questionId] = response;
      }
      next[variantIdx] = current;
      return next;
    });
  }

  function setQuestionsForVariant(
    variantIdx: number,
    questions: ConceptQuestion[],
    meta: ConceptQuestionsMeta,
  ) {
    const updateVariantSlot =
      <T,>(value: T) =>
      (prev: Array<T | null>): Array<T | null> => {
        const next = [...prev];
        while (next.length <= variantIdx) next.push(null);
        next[variantIdx] = value;
        return next;
      };

    setQuestionsByVariant(updateVariantSlot(questions));
    setQuestionsMetaByVariant(updateVariantSlot(meta));

    const activeKeys = questionAnswerKeys(questions);
    setQuestionHistoryForVariant(variantIdx, (current) =>
      current.map((entry) =>
        entry.status === "applied" && !activeKeys.has(entry.key)
          ? { ...entry, status: "resolved" }
          : entry,
      ),
    );
    const questionIds = new Set(questions.map((question) => question.question_id));
    setTournamentByVariant((prev) => {
      const next = [...prev];
      while (next.length <= variantIdx) next.push({});
      const current = next[variantIdx] ?? {};
      next[variantIdx] = Object.fromEntries(
        Object.entries(current).filter(([questionId]) => questionIds.has(questionId)),
      );
      return next;
    });
  }

  async function runAnalyzeForVariant(variantIdx: number, ir: ConceptIR): Promise<ConceptAnalyzeResponse | null> {
    const res = await fetch(`${apiBase()}/concepts/analyze`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        ir,
        source_text: sourceText || null,
        mode,
        include_analysis_details: true,
      }),
    });
    if (!res.ok) {
      setError(await res.text());
      return null;
    }
    const data = (await res.json()) as ConceptAnalyzeResponse;
    setCandidates((prev) =>
      prev.map((candidate, idx) =>
        idx === variantIdx ? { ...candidate, check_report: data.check_report } : candidate,
      ),
    );
    setAnalyses((prev) => prev.map((value, idx) => (idx === variantIdx ? data.analysis : value)));
    return data;
  }

  async function runQuestionsForVariant(
    variantIdx: number,
    ir: ConceptIR,
  ): Promise<ConceptQuestionsResponse | null> {
    setIsLoadingQuestions(true);
    try {
      const expectedIrHash = await conceptIrHash(ir);
      const res = await fetch(`${apiBase()}/concepts/questions`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          ir,
          source_text: sourceText || null,
          mode,
          include_forced_details: true,
          expected_ir_hash: expectedIrHash,
        }),
      });
      if (!res.ok) {
        setError(await res.text());
        return null;
      }
      const data = (await res.json()) as ConceptQuestionsResponse;
      setCandidates((prev) =>
        prev.map((candidate, idx) =>
          idx === variantIdx ? { ...candidate, check_report: data.check_report } : candidate,
        ),
      );
      setQuestionsForVariant(variantIdx, data.questions ?? [], {
        question_count: data.question_count,
        max_questions: data.max_questions,
        max_answers_per_question: data.max_answers_per_question,
        question_rank_version: data.question_rank_version,
        budget_report: data.budget_report,
        bridge_loss_signals: data.bridge_loss_signals ?? [],
        mapping_trust: data.mapping_trust ?? null,
        solver_trust: data.solver_trust,
        proof_trust: data.proof_trust ?? null,
      });
      return data;
    } catch (e) {
      setError(String(e));
      return null;
    } finally {
      setIsLoadingQuestions(false);
    }
  }

  async function refreshVariantFromStaleGuard(variantIdx: number, ir: ConceptIR): Promise<void> {
    await runAnalyzeForVariant(variantIdx, ir);
    await runQuestionsForVariant(variantIdx, ir);
  }

  async function applyChangeAndRefresh(
    variantIdx: number,
    baseIr: ConceptIR,
    endpoint: "/concepts/apply_ambiguity_option" | "/concepts/apply_patch",
    payload: Record<string, unknown>,
  ): Promise<boolean> {
    const applyRes = await fetch(`${apiBase()}${endpoint}`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify(payload),
    });

    if (!applyRes.ok) {
      const detailText = conceptApiErrorMessage(await applyRes.text());
      setError(detailText);
      if (applyRes.status === 409 && detailText.includes("STALE_IR")) {
        await refreshVariantFromStaleGuard(variantIdx, baseIr);
      }
      return false;
    }

    const applyData = (await applyRes.json()) as ConceptApplyResponse;
    setCandidates((prev) =>
      prev.map((candidate, idx) =>
        idx === variantIdx
          ? {
              ...candidate,
              ir: applyData.patched_ir,
              check_report: applyData.check_report,
            }
          : candidate,
      ),
    );
    setAnalyses((prev) => prev.map((value, idx) => (idx === variantIdx ? null : value)));
    setQuestionsByVariant((prev) => prev.map((value, idx) => (idx === variantIdx ? null : value)));
    setQuestionsMetaByVariant((prev) => prev.map((value, idx) => (idx === variantIdx ? null : value)));
    setTournamentByVariant((prev) =>
      prev.map((value, idx) => (idx === variantIdx ? {} : value)),
    );

    await runAnalyzeForVariant(variantIdx, applyData.patched_ir);
    await runQuestionsForVariant(variantIdx, applyData.patched_ir);
    return true;
  }

  async function propose() {
    setError(null);
    setArtifactId(null);
    setHighlight(null);
    setAlignmentResult(null);
    setIsProposing(true);
    setProposerLog(null);
    try {
      const res = await fetch(`${apiBase()}/concepts/propose`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ source_text: sourceText, provider, mode }),
      });
      if (!res.ok) {
        setError(await res.text());
        return;
      }
      const data = (await res.json()) as ProposeResponse;
      setCandidates(data.candidates ?? []);
      setAnalyses((data.candidates ?? []).map(() => null));
      setQuestionsByVariant((data.candidates ?? []).map(() => null));
      setQuestionsMetaByVariant((data.candidates ?? []).map(() => null));
      setQuestionHistoryByVariant((data.candidates ?? []).map(() => []));
      setTournamentByVariant((data.candidates ?? []).map(() => ({})));
      setSelectedIdx(0);
      setCompareIdx(null);
      setProposerLog(data.proposer_log ?? null);
    } catch (e) {
      setError(String(e));
    } finally {
      setIsProposing(false);
    }
  }

  async function runCheck() {
    if (!selectedIr) return;
    setError(null);
    setArtifactId(null);
    setAlignmentResult(null);
    const res = await fetch(`${apiBase()}/concepts/check`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ ir: selectedIr, source_text: sourceText || null, mode }),
    });
    if (!res.ok) {
      setError(await res.text());
      return;
    }
    const report = (await res.json()) as CheckReport;
    setCandidates((prev) =>
      prev.map((candidate, idx) =>
        idx === selectedIdx ? { ...candidate, check_report: report } : candidate,
      ),
    );
  }

  async function runAnalyze() {
    if (!selectedIr) return;
    setError(null);
    setArtifactId(null);
    setAlignmentResult(null);
    await runAnalyzeForVariant(selectedIdx, selectedIr);
  }

  async function runQuestions() {
    if (!selectedIr) return;
    setError(null);
    setArtifactId(null);
    setAlignmentResult(null);
    await runQuestionsForVariant(selectedIdx, selectedIr);
  }

  async function runAlignment() {
    const artifactIds = parseScopeIds(alignmentArtifactIdsInput);
    const docIds = parseScopeIds(alignmentDocIdsInput);
    if (artifactIds.length === 0 && docIds.length === 0) {
      setError("ALIGNMENT_SCOPE_EMPTY Provide artifact_ids and/or doc_ids.");
      return;
    }

    setError(null);
    setIsLoadingAlignment(true);
    try {
      const boundedMaxSuggestions = Math.max(
        ALIGNMENT_MAX_SUGGESTIONS_MIN,
        Math.min(
          ALIGNMENT_MAX_SUGGESTIONS_MAX,
          Number.isFinite(alignmentMaxSuggestions)
            ? Math.round(alignmentMaxSuggestions)
            : ALIGNMENT_MAX_SUGGESTIONS_DEFAULT,
        ),
      );
      const res = await fetch(`${apiBase()}/concepts/align`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          artifact_ids: artifactIds,
          doc_ids: docIds,
          max_suggestions: boundedMaxSuggestions,
        }),
      });
      if (!res.ok) {
        setError(await res.text());
        setAlignmentResult(null);
        return;
      }
      const data = (await res.json()) as ConceptAlignResponse;
      setAlignmentResult(data);
      setAlignmentMaxSuggestions(boundedMaxSuggestions);
    } catch (e) {
      setError(String(e));
      setAlignmentResult(null);
    } finally {
      setIsLoadingAlignment(false);
    }
  }

  async function applyConceptAmbiguityOption(ambiguityId: string, optionId: string) {
    if (!selectedIr) return;
    const variantIdx = selectedIdx;
    const baseIr = selectedIr;
    setError(null);
    setArtifactId(null);
    setAlignmentResult(null);
    setActiveTournamentQuestionId(null);
    setActiveOptionKey(`${ambiguityId}:${optionId}`);

    try {
      const irHash = await conceptIrHash(baseIr);
      await applyChangeAndRefresh(
        variantIdx,
        baseIr,
        "/concepts/apply_ambiguity_option",
        {
          ir: baseIr,
          ir_hash: irHash,
          ambiguity_id: ambiguityId,
          option_id: optionId,
          variants_by_id: Object.fromEntries(candidates.map((candidate) => [candidate.ir.concept_id, candidate.ir])),
          source_text: sourceText || null,
          mode,
          dry_run: false,
          include_validator_runs: false,
        },
      );
    } catch (e) {
      setError(String(e));
    } finally {
      setActiveOptionKey(null);
    }
  }

  async function applyQuestionAnswer(question: ConceptQuestion, answer: ConceptQuestionAnswer) {
    if (!selectedIr) return;
    const variantIdx = selectedIdx;
    const baseIr = selectedIr;
    if (!answer.patch?.length) {
      setError(`Question answer ${answer.option_id} is not patch-actionable`);
      return;
    }

    const resolutionKey = questionResolutionKey(question, answer.option_id);
    setError(null);
    setArtifactId(null);
    setAlignmentResult(null);
    setActiveTournamentQuestionId(null);
    setActiveQuestionOptionKey(resolutionKey);
    setTournamentForVariant(variantIdx, question.question_id, null);
    setQuestionHistoryForVariant(variantIdx, (current) => {
      const withoutCurrent = current.filter((entry) => entry.key !== resolutionKey);
      return [
        ...withoutCurrent,
        {
          key: resolutionKey,
          signal_kind: question.signal,
          prompt: question.prompt,
          answer_option_id: answer.option_id,
          answer_label: answer.label,
          status: "applied",
        },
      ];
    });

    try {
      const irHash = await conceptIrHash(baseIr);
      await applyChangeAndRefresh(variantIdx, baseIr, "/concepts/apply_patch", {
          ir: baseIr,
          ir_hash: irHash,
          patch_ops: answer.patch,
          source_text: sourceText || null,
          mode,
          dry_run: false,
          include_validator_runs: false,
      });
    } catch (e) {
      setError(String(e));
    } finally {
      setActiveQuestionOptionKey(null);
    }
  }

  async function runQuestionTournament(question: ConceptQuestion) {
    if (!selectedIr) return;
    const variantIdx = selectedIdx;
    const baseIr = selectedIr;
    const replayCandidates: ConceptTournamentCandidateInput[] = question.answers
      .filter(
        (answer): answer is ConceptQuestionAnswer & { patch: ConceptPatchOp[] } =>
          Array.isArray(answer.patch) && answer.patch.length > 0,
      )
      .map((answer) => ({
        question_id: question.question_id,
        patch_ops: answer.patch,
      }));

    if (replayCandidates.length === 0) {
      setError(`Question ${question.question_id} has no patch-actionable answers`);
      setTournamentForVariant(variantIdx, question.question_id, null);
      return;
    }

    setError(null);
    setArtifactId(null);
    setAlignmentResult(null);
    setActiveTournamentQuestionId(question.question_id);

    try {
      const expectedIrHash = await conceptIrHash(baseIr);
      const topK = Math.max(1, Math.min(TOURNAMENT_TOP_K_DEFAULT, replayCandidates.length));
      const res = await fetch(`${apiBase()}/concepts/tournament`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          ir: baseIr,
          source_text: sourceText || null,
          mode,
          tournament_mode: "replay_candidates" as TournamentMode,
          provider: "mock",
          candidates: replayCandidates,
          max_candidates: replayCandidates.length,
          top_k: topK,
          include_analysis_details: false,
          include_forced_details: false,
          expected_ir_hash: expectedIrHash,
        }),
      });
      if (!res.ok) {
        const detailText = conceptApiErrorMessage(await res.text());
        setError(detailText);
        if (
          res.status === 409 &&
          (detailText.includes("STALE_IR") ||
            detailText.includes("TOURNAMENT_STALE_IR_HASH_MISMATCH"))
        ) {
          await refreshVariantFromStaleGuard(variantIdx, baseIr);
        }
        return;
      }
      const data = (await res.json()) as ConceptTournamentResponse;
      setTournamentForVariant(variantIdx, question.question_id, data);
    } catch (e) {
      setError(String(e));
    } finally {
      setActiveTournamentQuestionId(null);
    }
  }

  async function accept() {
    if (!selectedIr) return;
    setError(null);
    const res = await fetch(`${apiBase()}/concepts/artifacts`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ source_text: sourceText, ir: selectedIr, mode: "STRICT" }),
    });
    if (!res.ok) {
      setError(await res.text());
      return;
    }
    const data = (await res.json()) as ConceptArtifactCreateResponse;
    setArtifactId(data.artifact_id);
    setAlignmentArtifactIdsInput((prev) => {
      const merged = Array.from(new Set([...parseScopeIds(prev), data.artifact_id])).sort();
      return merged.join("\n");
    });
    if (data.analysis) {
      setAnalyses((prev) => prev.map((value, idx) => (idx === selectedIdx ? data.analysis ?? value : value)));
    }
  }

  return (
    <div className="app">
      <div className="panel">
        <h2>Concept Text</h2>
        <textarea
          value={sourceText}
          onChange={(event) => setSourceText(event.target.value)}
          placeholder="Paste paper snippet here…"
        />
        <div className="row" style={{ marginTop: 8 }}>
          <span className="muted">Spans</span>
          <button onClick={() => setHighlight(null)} disabled={!highlight}>
            Clear highlight
          </button>
          {highlight ? <span className="muted mono">{highlight.label}</span> : null}
        </div>
        <div className="clause-preview" style={{ marginTop: 8 }}>
          {(() => {
            if (!highlight) return sourceText;
            const clamped = clampSpan(sourceText, highlight.span);
            if (!clamped) return sourceText;
            return (
              <>
                <span>{sourceText.slice(0, clamped.start)}</span>
                <mark>{sourceText.slice(clamped.start, clamped.end)}</mark>
                <span>{sourceText.slice(clamped.end)}</span>
              </>
            );
          })()}
        </div>

        <div className="row" style={{ marginTop: 8 }}>
          <span className="muted">Provider</span>
          <button onClick={() => setProvider("mock")} disabled={provider === "mock"}>
            mock
          </button>
          <button onClick={() => setProvider("openai")} disabled={provider === "openai"}>
            openai
          </button>
          <button onClick={propose} disabled={!sourceText.trim() || isProposing}>
            Propose variants
          </button>
          <Link href="/" className="muted" style={{ marginLeft: "auto" }}>
            ADEU Studio
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
          <Link href="/copilot" className="muted">
            Copilot
          </Link>
        </div>

        {isProposing ? <div className="muted">Proposing…</div> : null}
        {proposerLog ? (
          <div className="muted" style={{ marginTop: 8 }}>
            Proposer: {proposerLog.provider}
            {proposerLog.api ? `/${proposerLog.api}` : ""}
            {proposerLog.model ? ` (${proposerLog.model})` : ""} — attempts: {proposerLog.attempts.length}
          </div>
        ) : null}
        {error ? <div className="muted">Error: {error}</div> : null}
        {artifactId ? <div className="muted">Accepted concept artifact: {artifactId}</div> : null}
      </div>

      <div className="panel">
        <h2>Concept IR</h2>
        <div className="row">
          {candidates.map((candidate, idx) => (
            <button
              key={idx}
              onClick={() => {
                setSelectedIdx(idx);
                if (compareIdx === idx) setCompareIdx(null);
              }}
              disabled={idx === selectedIdx}
            >
              Variant {idx + 1} ({candidate.check_report.status})
            </button>
          ))}
          {candidates.length === 0 ? <span className="muted">No candidates yet.</span> : null}
          {candidates.length > 1 ? (
            <>
              <span className="muted" style={{ marginLeft: "auto" }}>
                Compare
              </span>
              <select
                value={compareIdx === null ? "" : String(compareIdx)}
                onChange={(event) =>
                  setCompareIdx(
                    event.target.value === "" ? null : Number.parseInt(event.target.value, 10),
                  )
                }
              >
                <option value="">(none)</option>
                {candidates.map((_, idx) => (
                  <option key={idx} value={String(idx)} disabled={idx === selectedIdx}>
                    Variant {idx + 1}
                  </option>
                ))}
              </select>
            </>
          ) : null}
        </div>

        {compared ? (
          <div className="row" style={{ marginTop: 8 }}>
            <span className="muted">Selected: {selectedReport?.status ?? "n/a"}</span>
            <span className="muted">Compared: {compared.check_report.status}</span>
          </div>
        ) : null}

        <SolverDiffPanel
          domain="concepts"
          mode={mode}
          leftIr={selectedIr}
          rightIr={compared?.ir ?? null}
          leftSourceText={sourceText || null}
          rightSourceText={sourceText || null}
          includeAnalysisDelta
          onSelectSpan={(span, label) => setHighlight({ span, label })}
        />

        <pre>{selectedIr ? JSON.stringify(selectedIr, null, 2) : ""}</pre>
      </div>

      <div className="panel">
        <h2>Checker / Analyzer</h2>
        <div className="row">
          <span className="muted">Mode</span>
          <button onClick={() => setMode("LAX")} disabled={mode === "LAX"}>
            LAX
          </button>
          <button onClick={() => setMode("STRICT")} disabled={mode === "STRICT"}>
            STRICT
          </button>
          <button onClick={runCheck} disabled={!selectedIr}>
            Check ({mode})
          </button>
          <button onClick={runAnalyze} disabled={!selectedIr}>
            Analyze
          </button>
          <button onClick={runQuestions} disabled={!selectedIr || isLoadingQuestions}>
            {isLoadingQuestions ? "Generating..." : "Generate questions"}
          </button>
          <button onClick={runAlignment} disabled={isLoadingAlignment}>
            {isLoadingAlignment ? "Aligning..." : "Generate alignment"}
          </button>
          <button onClick={accept} disabled={!selectedIr}>
            Accept (STRICT)
          </button>
        </div>

        <div style={{ marginTop: 10, border: "1px solid var(--border)", borderRadius: 8, padding: 8 }}>
          <div className="muted">Alignment scope</div>
          <div className="row" style={{ marginTop: 6 }}>
            <label className="muted" htmlFor="alignment-artifact-ids">
              artifact_ids
            </label>
            <textarea
              id="alignment-artifact-ids"
              rows={2}
              style={{ minHeight: 52 }}
              value={alignmentArtifactIdsInput}
              onChange={(event) => setAlignmentArtifactIdsInput(event.target.value)}
              placeholder="artifact_a, artifact_b"
            />
          </div>
          <div className="row" style={{ marginTop: 6 }}>
            <label className="muted" htmlFor="alignment-doc-ids">
              doc_ids
            </label>
            <textarea
              id="alignment-doc-ids"
              rows={2}
              style={{ minHeight: 52 }}
              value={alignmentDocIdsInput}
              onChange={(event) => setAlignmentDocIdsInput(event.target.value)}
              placeholder="doc_1, doc_2"
            />
          </div>
          <div className="row" style={{ marginTop: 6 }}>
            <label className="muted" htmlFor="alignment-max-suggestions">
              max_suggestions
            </label>
            <input
              id="alignment-max-suggestions"
              type="number"
              min={ALIGNMENT_MAX_SUGGESTIONS_MIN}
              max={ALIGNMENT_MAX_SUGGESTIONS_MAX}
              value={alignmentMaxSuggestions}
              onChange={(event) => {
                const value = Number.parseInt(event.target.value, 10);
                setAlignmentMaxSuggestions(
                  Number.isFinite(value) ? value : ALIGNMENT_MAX_SUGGESTIONS_DEFAULT,
                );
              }}
            />
            <button
              onClick={() =>
                setAlignmentArtifactIdsInput((prev) => {
                  if (!artifactId) return prev;
                  const merged = Array.from(new Set([...parseScopeIds(prev), artifactId])).sort();
                  return merged.join("\n");
                })
              }
              disabled={!artifactId}
            >
              Add accepted artifact
            </button>
            <button onClick={runAlignment} disabled={isLoadingAlignment}>
              {isLoadingAlignment ? "Aligning..." : "Run alignment"}
            </button>
            <button onClick={() => setAlignmentResult(null)} disabled={!alignmentResult}>
              Clear
            </button>
          </div>
          {alignmentResult ? (
            <div style={{ marginTop: 8 }}>
              <div className="muted">
                Alignment suggestions ({alignmentResult.suggestion_count}) merge=
                {alignmentResult.alignment_stats.merge_candidate_count} conflict=
                {alignmentResult.alignment_stats.conflict_candidate_count}
              </div>
              <div className="muted mono" style={{ marginTop: 2 }}>
                trust mapping={alignmentResult.mapping_trust} solver={alignmentResult.solver_trust}
                {" "}proof={alignmentResult.proof_trust ?? "none"}
              </div>
              {alignmentResult.artifacts.length ? (
                <div className="muted mono" style={{ marginTop: 4 }}>
                  Scope artifacts:{" "}
                  {alignmentResult.artifacts
                    .map((item) => `${item.artifact_id}${item.doc_id ? `@${item.doc_id}` : ""}`)
                    .join(", ")}
                </div>
              ) : null}
              {alignmentResult.suggestions.length === 0 ? (
                <div className="muted" style={{ marginTop: 4 }}>
                  No merge/conflict candidates in current scope.
                </div>
              ) : null}
              {alignmentResult.suggestions.map((suggestion) => (
                <div
                  key={suggestion.suggestion_id}
                  style={{
                    marginTop: 8,
                    border: "1px solid var(--border)",
                    borderRadius: 8,
                    background: "#fff",
                    padding: 8,
                  }}
                >
                  <div className="muted mono">
                    {suggestion.kind} · {suggestion.suggestion_id} · fp={suggestion.suggestion_fingerprint}
                  </div>
                  <div className="muted mono" style={{ marginTop: 2 }}>
                    vocabulary_key={suggestion.vocabulary_key}
                  </div>
                  <div style={{ marginTop: 4 }}>{suggestion.reason}</div>
                  <div className="muted mono" style={{ marginTop: 4 }}>
                    artifacts={suggestion.artifact_ids.join(", ") || "(none)"} docs=
                    {suggestion.doc_ids.join(", ") || "(none)"}
                  </div>
                  <div className="muted mono" style={{ marginTop: 2 }}>
                    terms=
                    {suggestion.term_refs
                      .map((term) => `${term.artifact_id}/${term.term_id}:${term.normalized_label}`)
                      .join(" | ")}
                  </div>
                  {suggestion.sense_refs.length ? (
                    <div className="muted mono" style={{ marginTop: 2 }}>
                      senses=
                      {suggestion.sense_refs
                        .slice(0, ALIGNMENT_SENSE_REFS_PREVIEW_LIMIT)
                        .map((sense) => `${sense.artifact_id}/${sense.sense_id}:${sense.gloss_signature}`)
                        .join(" | ")}
                      {suggestion.sense_refs.length > ALIGNMENT_SENSE_REFS_PREVIEW_LIMIT
                        ? ` | +${suggestion.sense_refs.length - ALIGNMENT_SENSE_REFS_PREVIEW_LIMIT} more`
                        : ""}
                    </div>
                  ) : null}
                </div>
              ))}
            </div>
          ) : null}
        </div>

        {selectedIr?.claims?.length ? (
          <div style={{ marginTop: 8 }}>
            <div className="muted">Claims</div>
            {selectedIr.claims.map((claim, idx) => (
              <div key={claim.id} className="row" style={{ marginTop: 4 }}>
                <button
                  onClick={() => {
                    const span = claim.provenance?.span ?? null;
                    if (!span) return;
                    setHighlight({ span, label: `claim:${claim.id} (/claims/${idx})` });
                  }}
                  disabled={!claim.provenance?.span}
                >
                  Highlight
                </button>
                <span className="muted mono">
                  {claim.id} {"->"} {claim.sense_id}
                </span>
              </div>
            ))}
          </div>
        ) : null}

        {selectedIr?.ambiguity?.length ? (
          <div style={{ marginTop: 10 }}>
            <div className="muted">Ambiguity options</div>
            {selectedIr.ambiguity.map((ambiguity) => (
              <div key={ambiguity.id} style={{ marginTop: 8 }}>
                <div className="muted mono">
                  {ambiguity.id} term={ambiguity.term_id}
                </div>
                <div className="row" style={{ marginTop: 4 }}>
                  {ambiguity.options.map((optionId) => {
                    const detail = ambiguity.option_details_by_id?.[optionId];
                    const label =
                      ambiguity.option_labels_by_id?.[optionId] ?? detail?.label ?? optionId;
                    const optionKey = `${ambiguity.id}:${optionId}`;
                    return (
                      <button
                        key={optionId}
                        onClick={() => applyConceptAmbiguityOption(ambiguity.id, optionId)}
                        disabled={!detail || activeOptionKey === optionKey}
                        title={!detail ? "No actionable patch for this option" : undefined}
                      >
                        {activeOptionKey === optionKey ? "Applying..." : `Apply ${label}`}
                      </button>
                    );
                  })}
                </div>
              </div>
            ))}
          </div>
        ) : null}

        {selectedQuestions ? (
          <div style={{ marginTop: 12 }}>
            <div className="muted">
              Questions ({selectedQuestions.length}) open={questionLifecycleSummary.open} applied=
              {questionLifecycleSummary.applied} resolved={questionLifecycleSummary.resolved}
            </div>
            {selectedQuestionsMeta ? (
              <div className="muted mono" style={{ marginTop: 4 }}>
                rank={selectedQuestionsMeta.question_rank_version} dry_runs=
                {selectedQuestionsMeta.budget_report.used_dry_runs}/
                {selectedQuestionsMeta.budget_report.max_dry_runs} solver_calls=
                {selectedQuestionsMeta.budget_report.used_solver_calls}/
                {selectedQuestionsMeta.budget_report.max_solver_calls}
                {selectedQuestionsMeta.budget_report.truncated
                  ? ` truncated:${selectedQuestionsMeta.budget_report.truncation_reason ?? "unknown"}`
                  : ""}
              </div>
            ) : null}
            {selectedQuestions.length === 0 ? (
              <div className="muted" style={{ marginTop: 4 }}>
                No actionable questions for current IR.
              </div>
            ) : null}
            {selectedQuestions.map((question) => (
              <QuestionCard
                key={question.question_id}
                question={question}
                selectedIr={selectedIr}
                questionHistoryMap={selectedQuestionHistoryMap}
                activeQuestionOptionKey={activeQuestionOptionKey}
                activeTournamentQuestionId={activeTournamentQuestionId}
                tournamentResult={selectedTournamentByQuestion[question.question_id] ?? null}
                onApplyAnswer={applyQuestionAnswer}
                onRunTournament={runQuestionTournament}
                onClearTournament={(questionId) =>
                  setTournamentForVariant(selectedIdx, questionId, null)
                }
                onAnchorHighlight={(span, label) => setHighlight({ span, label })}
              />
            ))}
            {selectedQuestionHistory.some((entry) => entry.status === "resolved") ? (
              <div style={{ marginTop: 8 }}>
                <div className="muted">Resolved answers</div>
                <div style={{ marginTop: 4 }}>
                  {selectedQuestionHistory
                    .filter((entry) => entry.status === "resolved")
                    .map((entry) => (
                      <div key={entry.key} className="muted mono" style={{ marginTop: 2 }}>
                        {entry.signal_kind} · {entry.answer_option_id} · {entry.answer_label}
                      </div>
                    ))}
                </div>
              </div>
            ) : null}
          </div>
        ) : null}

        {selectedReport?.reason_codes?.length ? (
          <div style={{ marginTop: 8, overflow: "auto" }}>
            <div className="muted">Reasons ({selectedReport.reason_codes.length})</div>
            <table className="table" style={{ marginTop: 8 }}>
              <thead>
                <tr>
                  <th>sev</th>
                  <th>code</th>
                  <th>json_path</th>
                  <th>object_id</th>
                  <th>message</th>
                  <th></th>
                </tr>
              </thead>
              <tbody>
                {selectedReport.reason_codes.map((reason, idx) => {
                  const span = selectedIr ? spanFromReason(selectedIr, reason) : null;
                  return (
                    <tr key={idx}>
                      <td className="mono">{reason.severity}</td>
                      <td className="mono">{reason.code}</td>
                      <td className="mono">{reason.json_path ?? ""}</td>
                      <td className="mono">{reason.object_id ?? ""}</td>
                      <td>{reason.message}</td>
                      <td>
                        <button
                          onClick={() => {
                            if (!span) return;
                            setHighlight({
                              span,
                              label: `reason:${reason.code} ${reason.json_path ?? ""}`.trim(),
                            });
                          }}
                          disabled={!span}
                        >
                          Highlight
                        </button>
                      </td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        ) : null}

        {selectedAnalysis ? (
          <div style={{ marginTop: 8 }}>
            <div className="muted">
              Closure: {selectedAnalysis.closure.status} ({selectedAnalysis.closure.edge_count} edges)
            </div>
            {selectedAnalysis.closure.edges.length ? (
              <table className="table" style={{ marginTop: 6 }}>
                <thead>
                  <tr>
                    <th>src</th>
                    <th>dst</th>
                    <th>kind</th>
                  </tr>
                </thead>
                <tbody>
                  {selectedAnalysis.closure.edges.map((edge) => (
                    <tr key={`${edge.src_sense_id}-${edge.dst_sense_id}-${edge.kind}`}>
                      <td className="mono">{edge.src_sense_id}</td>
                      <td className="mono">{edge.dst_sense_id}</td>
                      <td className="mono">{edge.kind}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            ) : null}

            <div className="muted" style={{ marginTop: 8 }}>
              MIC: {selectedAnalysis.mic.status} ({selectedAnalysis.mic.constraint_count} constraints)
              {` calls=${selectedAnalysis.mic.solver_calls} shrink_iters=${selectedAnalysis.mic.shrink_iters}`}
            </div>
            {selectedAnalysis.mic.constraints.length ? (
              <table className="table" style={{ marginTop: 6 }}>
                <thead>
                  <tr>
                    <th>atom</th>
                    <th>label</th>
                    <th>object_id</th>
                    <th>json_path</th>
                    <th></th>
                  </tr>
                </thead>
                <tbody>
                  {selectedAnalysis.mic.constraints.map((constraint) => {
                    const span = selectedIr
                      ? spanFromConceptRef(selectedIr, constraint.object_id, constraint.json_path)
                      : null;
                    return (
                      <tr key={constraint.atom_name}>
                        <td className="mono">{constraint.atom_name}</td>
                        <td className="mono">{constraint.label ?? ""}</td>
                        <td className="mono">{constraint.object_id ?? ""}</td>
                        <td className="mono">{constraint.json_path ?? ""}</td>
                        <td>
                          <button
                            onClick={() => {
                              if (!span) return;
                              setHighlight({
                                span,
                                label: `mic:${constraint.atom_name} ${constraint.json_path ?? ""}`.trim(),
                              });
                            }}
                            disabled={!span}
                          >
                            Highlight
                          </button>
                        </td>
                      </tr>
                    );
                  })}
                </tbody>
              </table>
            ) : null}
          </div>
        ) : null}

        <pre>{selectedReport ? JSON.stringify(selectedReport, null, 2) : ""}</pre>
      </div>
    </div>
  );
}
