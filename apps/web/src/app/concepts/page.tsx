"use client";

import Link from "next/link";
import { useMemo, useState } from "react";

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

type ConceptApplyAmbiguityOptionResponse = {
  patched_ir: ConceptIR;
  check_report: CheckReport;
};

type ConceptApplyPatchResponse = {
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

type ConceptQuestionsResponse = {
  check_report: CheckReport;
  questions: ConceptQuestion[];
  question_count: number;
  max_questions: number;
  max_answers_per_question: number;
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

function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}

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
    if (detail?.code === "STALE_IR") {
      return `STALE_IR ${detail.message ?? ""}`.trim();
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

export default function ConceptsPage() {
  const [sourceText, setSourceText] = useState<string>("");
  const [provider, setProvider] = useState<"mock" | "openai">("mock");
  const [mode, setMode] = useState<KernelMode>("LAX");
  const [isProposing, setIsProposing] = useState<boolean>(false);
  const [isLoadingQuestions, setIsLoadingQuestions] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);
  const [artifactId, setArtifactId] = useState<string | null>(null);
  const [activeOptionKey, setActiveOptionKey] = useState<string | null>(null);
  const [activeQuestionOptionKey, setActiveQuestionOptionKey] = useState<string | null>(null);

  const [proposerLog, setProposerLog] = useState<ProposerLog | null>(null);
  const [candidates, setCandidates] = useState<ProposeCandidate[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [compareIdx, setCompareIdx] = useState<number | null>(null);
  const [analyses, setAnalyses] = useState<Array<ConceptAnalysis | null>>([]);
  const [questionsByVariant, setQuestionsByVariant] = useState<Array<ConceptQuestion[] | null>>([]);
  const [questionHistoryByVariant, setQuestionHistoryByVariant] = useState<
    Array<QuestionLifecycleEntry[]>
  >([]);
  const [highlight, setHighlight] = useState<Highlight>(null);

  const selected = useMemo(() => candidates[selectedIdx] ?? null, [candidates, selectedIdx]);
  const selectedIr = useMemo(() => selected?.ir ?? null, [selected]);
  const selectedReport = useMemo(() => selected?.check_report ?? null, [selected]);
  const selectedAnalysis = useMemo(() => analyses[selectedIdx] ?? null, [analyses, selectedIdx]);
  const selectedQuestions = useMemo(
    () => questionsByVariant[selectedIdx] ?? null,
    [questionsByVariant, selectedIdx],
  );
  const selectedQuestionHistory = useMemo(
    () => questionHistoryByVariant[selectedIdx] ?? [],
    [questionHistoryByVariant, selectedIdx],
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

  function setQuestionsForVariant(variantIdx: number, questions: ConceptQuestion[]) {
    setQuestionsByVariant((prev) => {
      const next = [...prev];
      while (next.length <= variantIdx) next.push(null);
      next[variantIdx] = questions;
      return next;
    });

    const activeKeys = questionAnswerKeys(questions);
    setQuestionHistoryForVariant(variantIdx, (current) =>
      current.map((entry) =>
        entry.status === "applied" && !activeKeys.has(entry.key)
          ? { ...entry, status: "resolved" }
          : entry,
      ),
    );
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
      const res = await fetch(`${apiBase()}/concepts/questions`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          ir,
          source_text: sourceText || null,
          mode,
          include_forced_details: true,
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
      setQuestionsForVariant(variantIdx, data.questions ?? []);
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

  async function propose() {
    setError(null);
    setArtifactId(null);
    setHighlight(null);
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
      setQuestionHistoryByVariant((data.candidates ?? []).map(() => []));
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
    await runAnalyzeForVariant(selectedIdx, selectedIr);
  }

  async function runQuestions() {
    if (!selectedIr) return;
    setError(null);
    setArtifactId(null);
    await runQuestionsForVariant(selectedIdx, selectedIr);
  }

  async function applyConceptAmbiguityOption(ambiguityId: string, optionId: string) {
    if (!selectedIr) return;
    const variantIdx = selectedIdx;
    const baseIr = selectedIr;
    setError(null);
    setArtifactId(null);
    setActiveOptionKey(`${ambiguityId}:${optionId}`);

    try {
      const irHash = await conceptIrHash(baseIr);
      const applyRes = await fetch(`${apiBase()}/concepts/apply_ambiguity_option`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          ir: baseIr,
          ir_hash: irHash,
          ambiguity_id: ambiguityId,
          option_id: optionId,
          variants_by_id: Object.fromEntries(candidates.map((candidate) => [candidate.ir.concept_id, candidate.ir])),
          source_text: sourceText || null,
          mode,
          dry_run: false,
          include_validator_runs: false,
        }),
      });

      if (!applyRes.ok) {
        const detailText = conceptApiErrorMessage(await applyRes.text());
        setError(detailText);
        if (applyRes.status === 409 && detailText.includes("STALE_IR")) {
          await refreshVariantFromStaleGuard(variantIdx, baseIr);
        }
        return;
      }

      const applyData = (await applyRes.json()) as ConceptApplyAmbiguityOptionResponse;
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

      await runAnalyzeForVariant(variantIdx, applyData.patched_ir);
      await runQuestionsForVariant(variantIdx, applyData.patched_ir);
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
    setActiveQuestionOptionKey(resolutionKey);
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
      const applyRes = await fetch(`${apiBase()}/concepts/apply_patch`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          ir: baseIr,
          ir_hash: irHash,
          patch_ops: answer.patch,
          source_text: sourceText || null,
          mode,
          dry_run: false,
          include_validator_runs: false,
        }),
      });

      if (!applyRes.ok) {
        const detailText = conceptApiErrorMessage(await applyRes.text());
        setError(detailText);
        if (applyRes.status === 409 && detailText.includes("STALE_IR")) {
          await refreshVariantFromStaleGuard(variantIdx, baseIr);
        }
        return;
      }

      const applyData = (await applyRes.json()) as ConceptApplyPatchResponse;
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

      await runAnalyzeForVariant(variantIdx, applyData.patched_ir);
      await runQuestionsForVariant(variantIdx, applyData.patched_ir);
    } catch (e) {
      setError(String(e));
    } finally {
      setActiveQuestionOptionKey(null);
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
          <Link href="/artifacts" className="muted">
            Artifacts
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
          <button onClick={accept} disabled={!selectedIr}>
            Accept (STRICT)
          </button>
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
            {selectedQuestions.length === 0 ? (
              <div className="muted" style={{ marginTop: 4 }}>
                No actionable questions for current IR.
              </div>
            ) : null}
            {selectedQuestions.map((question) => (
              <div
                key={question.question_id}
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
                      const label = anchor.label || anchor.json_path || anchor.object_id || `anchor_${idx + 1}`;
                      return (
                        <button
                          key={`${question.question_id}:anchor:${idx}`}
                          onClick={() => {
                            if (!span) return;
                            setHighlight({ span, label: `question:${label}` });
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
                    const lifecycle = selectedQuestionHistoryMap.get(resolutionKey);
                    const statusLabel =
                      lifecycle === "applied" ? "Applied" : lifecycle === "resolved" ? "Resolved" : "Open";
                    const hasPatch = Boolean(answer.patch?.length);
                    return (
                      <button
                        key={`${question.question_id}:${answer.option_id}`}
                        onClick={() => applyQuestionAnswer(question, answer)}
                        disabled={!hasPatch || (activeQuestionOptionKey !== null && activeQuestionOptionKey !== resolutionKey)}
                        title={!hasPatch ? "Answer does not provide a patch action" : undefined}
                      >
                        {activeQuestionOptionKey === resolutionKey
                          ? "Applying..."
                          : `${statusLabel}: ${answer.label}`}
                      </button>
                    );
                  })}
                </div>
              </div>
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
