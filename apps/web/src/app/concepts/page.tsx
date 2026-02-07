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
  const [error, setError] = useState<string | null>(null);
  const [artifactId, setArtifactId] = useState<string | null>(null);

  const [proposerLog, setProposerLog] = useState<ProposerLog | null>(null);
  const [candidates, setCandidates] = useState<ProposeCandidate[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [compareIdx, setCompareIdx] = useState<number | null>(null);
  const [analyses, setAnalyses] = useState<Array<ConceptAnalysis | null>>([]);
  const [highlight, setHighlight] = useState<Highlight>(null);

  const selected = useMemo(() => candidates[selectedIdx] ?? null, [candidates, selectedIdx]);
  const selectedIr = useMemo(() => selected?.ir ?? null, [selected]);
  const selectedReport = useMemo(() => selected?.check_report ?? null, [selected]);
  const selectedAnalysis = useMemo(() => analyses[selectedIdx] ?? null, [analyses, selectedIdx]);

  const compared = useMemo(
    () => (compareIdx === null ? null : candidates[compareIdx] ?? null),
    [candidates, compareIdx],
  );
  const diffPayload = useMemo(
    () => ({
      left_source_text: sourceText || null,
      right_source_text: sourceText || null,
    }),
    [sourceText],
  );

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
    const res = await fetch(`${apiBase()}/concepts/analyze`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        ir: selectedIr,
        source_text: sourceText || null,
        mode,
        include_analysis_details: true,
      }),
    });
    if (!res.ok) {
      setError(await res.text());
      return;
    }
    const data = (await res.json()) as ConceptAnalyzeResponse;
    setCandidates((prev) =>
      prev.map((candidate, idx) =>
        idx === selectedIdx ? { ...candidate, check_report: data.check_report } : candidate,
      ),
    );
    setAnalyses((prev) => prev.map((value, idx) => (idx === selectedIdx ? data.analysis : value)));
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
          endpoint="/concepts/diff"
          mode={mode}
          leftIr={selectedIr}
          rightIr={compared?.ir ?? null}
          extraPayload={diffPayload}
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
