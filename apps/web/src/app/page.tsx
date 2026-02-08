"use client";

import Link from "next/link";
import { useEffect, useMemo, useState } from "react";

import { SolverDiffPanel } from "./components/solver-diff-panel";
import type { AdeuIR, SourceSpan } from "../gen/adeu_ir";
import type { CheckReason, CheckReport } from "../gen/check_report";

type KernelMode = "STRICT" | "LAX";

type ProposeCandidate = {
  ir: AdeuIR;
  check_report: CheckReport;
  rank: number;
};

type ProposerAttempt = {
  attempt_idx: number;
  status: "PASS" | "WARN" | "REFUSE" | "PARSE_ERROR";
  reason_codes_summary: string[];
  score_key?: [number, number, number, number] | number[] | null;
  accepted_by_gate?: boolean | null;
  candidate_rank?: number | null;
};

type ProposerLog = {
  provider: string;
  api?: string | null;
  model?: string | null;
  created_at: string;
  k?: number | null;
  n?: number | null;
  attempts: ProposerAttempt[];
  prompt_hash?: string | null;
  response_hash?: string | null;
};

type ProposeResponse = {
  provider: { kind: string; api?: string | null; model?: string | null };
  candidates: ProposeCandidate[];
  proposer_log: ProposerLog;
};

type ArtifactCreateResponse = {
  artifact_id: string;
  created_at: string;
  check_report: CheckReport;
};

type ApplyAmbiguityOptionResponse = {
  patched_ir: AdeuIR;
  check_report: CheckReport;
};

type ConceptProvenance = {
  doc_ref?: string | null;
  span?: SourceSpan | null;
};

type BridgeConceptTerm = {
  id: string;
  label: string;
  provenance?: ConceptProvenance | null;
};

type BridgeConceptClaim = {
  id: string;
  sense_id: string;
  text: string;
  provenance?: ConceptProvenance | null;
};

type BridgeConceptIR = {
  schema_version: string;
  concept_id: string;
  terms: BridgeConceptTerm[];
  claims: BridgeConceptClaim[];
};

type BridgeConceptAnalysis = {
  closure: {
    status: "COMPLETE" | "PARTIAL" | "UNAVAILABLE";
    edge_count: number;
  };
  mic: {
    status: "COMPLETE" | "PARTIAL" | "UNAVAILABLE";
    constraint_count: number;
    solver_calls: number;
    shrink_iters: number;
  };
  forced: {
    status: "COMPLETE" | "PARTIAL" | "UNAVAILABLE";
    candidate_count: number;
    forced_count: number;
    countermodel_count: number;
    solver_calls: number;
  };
};

type AdeuAnalyzeConceptsResponse = {
  concept_ir: BridgeConceptIR;
  check_report: CheckReport;
  analysis: BridgeConceptAnalysis;
  bridge_mapping_version: string;
  mapping_hash: string;
  mapping_trust: string;
  solver_trust: "kernel_only" | "solver_backed" | "proof_checked";
  proof_trust?: string | null;
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

function _firstSpan(span: SourceSpan | null | undefined): SourceSpan | null {
  return span ? span : null;
}

function spanFromReason(ir: AdeuIR, reason: CheckReason): SourceSpan | null {
  const provSpan = _firstSpan(reason.provenance?.span);
  if (provSpan) return provSpan;

  const objectId = reason.object_id ?? null;
  if (objectId) {
    const stmt = ir.D_norm?.statements?.find((s) => s.id === objectId);
    const stmtSpan = _firstSpan(stmt?.provenance?.span);
    if (stmtSpan) return stmtSpan;

    const ex = ir.D_norm?.exceptions?.find((e) => e.id === objectId);
    const exSpan = _firstSpan(ex?.provenance?.span);
    if (exSpan) return exSpan;

    const amb = ir.ambiguity?.find((a) => a.id === objectId);
    const ambSpan = _firstSpan(amb?.span);
    if (ambSpan) return ambSpan;

    const bridge = ir.bridges?.find((b) => b.id === objectId);
    const bridgeSpan = _firstSpan(bridge?.provenance?.span);
    if (bridgeSpan) return bridgeSpan;
  }

  const path = reason.json_path ?? "";
  const stmtPrefix = "/D_norm/statements/";
  if (path.startsWith(stmtPrefix)) {
    const seg = path.slice(stmtPrefix.length).split("/")[0];
    const idx = Number.parseInt(seg, 10);
    const stmt = Number.isFinite(idx) ? ir.D_norm?.statements?.[idx] : undefined;
    const span = _firstSpan(stmt?.provenance?.span);
    if (span) return span;
  }

  const exPrefix = "/D_norm/exceptions/";
  if (path.startsWith(exPrefix)) {
    const seg = path.slice(exPrefix.length).split("/")[0];
    const idx = Number.parseInt(seg, 10);
    const ex = Number.isFinite(idx) ? ir.D_norm?.exceptions?.[idx] : undefined;
    const span = _firstSpan(ex?.provenance?.span);
    if (span) return span;
  }

  return null;
}

function solverStatusFromReport(report: CheckReport | null): string | null {
  if (!report?.trace?.length) return null;
  for (const traceItem of report.trace) {
    for (const because of traceItem.because ?? []) {
      if (because.startsWith("solver:")) return because.slice("solver:".length);
    }
  }
  return null;
}

export default function HomePage() {
  const [clauseText, setClauseText] = useState<string>("");
  const [provider, setProvider] = useState<"mock" | "openai">("mock");
  const [proposerLog, setProposerLog] = useState<ProposerLog | null>(null);
  const [isProposing, setIsProposing] = useState<boolean>(false);
  const [docId, setDocId] = useState<string>("web:adhoc");
  const [jurisdiction, setJurisdiction] = useState<string>("US-CA");
  const [timeEval, setTimeEval] = useState<string>(() => new Date().toISOString());
  const [candidates, setCandidates] = useState<ProposeCandidate[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [compareIdx, setCompareIdx] = useState<number | null>(null);
  const [mode, setMode] = useState<KernelMode>("LAX");
  const [highlight, setHighlight] = useState<Highlight>(null);
  const [artifactId, setArtifactId] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [isAnalyzingConcepts, setIsAnalyzingConcepts] = useState<boolean>(false);
  const [conceptBridge, setConceptBridge] = useState<AdeuAnalyzeConceptsResponse | null>(null);

  const selected = useMemo(() => candidates[selectedIdx] ?? null, [candidates, selectedIdx]);
  const selectedIr = useMemo(() => selected?.ir ?? null, [selected]);
  const selectedReport = useMemo(() => selected?.check_report ?? null, [selected]);
  const selectedSolverStatus = useMemo(
    () => solverStatusFromReport(selectedReport),
    [selectedReport]
  );
  const compared = useMemo(
    () => (compareIdx === null ? null : candidates[compareIdx] ?? null),
    [candidates, compareIdx]
  );
  const comparedIr = useMemo(() => compared?.ir ?? null, [compared]);
  const comparedSolverStatus = useMemo(
    () => solverStatusFromReport(compared?.check_report ?? null),
    [compared]
  );
  const conceptTerms = useMemo(
    () => [...(conceptBridge?.concept_ir.terms ?? [])].sort((left, right) => left.id.localeCompare(right.id)),
    [conceptBridge]
  );
  const conceptClaims = useMemo(
    () =>
      [...(conceptBridge?.concept_ir.claims ?? [])].sort((left, right) =>
        left.id.localeCompare(right.id)
      ),
    [conceptBridge]
  );

  useEffect(() => {
    setConceptBridge(null);
  }, [selectedIdx, mode]);

  async function propose() {
    setError(null);
    setArtifactId(null);
    setConceptBridge(null);
    setHighlight(null);
    setProposerLog(null);
    setIsProposing(true);
    try {
      const context = {
        doc_id: docId.trim() || "web:adhoc",
        jurisdiction: jurisdiction.trim() || "US-CA",
        time_eval: timeEval.trim() || new Date().toISOString()
      };
      const res = await fetch(`${apiBase()}/propose`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ clause_text: clauseText, provider, mode, context })
      });
      if (!res.ok) {
        setError(await res.text());
        return;
      }
      const data = (await res.json()) as ProposeResponse;
      setCandidates(data.candidates ?? []);
      setProposerLog(data.proposer_log ?? null);
      setSelectedIdx(0);
      setCompareIdx(null);
    } catch (e) {
      setError(String(e));
    } finally {
      setIsProposing(false);
    }
  }

  async function runCheck() {
    setError(null);
    setArtifactId(null);
    if (!selectedIr) return;
    const res = await fetch(`${apiBase()}/check`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ ir: selectedIr, mode })
    });
    const report = (await res.json()) as CheckReport;
    setCandidates((prev) =>
      prev.map((c, idx) => (idx === selectedIdx ? { ...c, check_report: report } : c))
    );
  }

  async function analyzeAsConcepts() {
    setError(null);
    if (!selectedIr) return;
    setIsAnalyzingConcepts(true);
    try {
      const res = await fetch(`${apiBase()}/adeu/analyze_concepts`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          ir: selectedIr,
          source_text: clauseText || null,
          mode,
          include_analysis_details: true,
          include_forced_details: true
        })
      });
      if (!res.ok) {
        setError(await res.text());
        return;
      }
      const data = (await res.json()) as AdeuAnalyzeConceptsResponse;
      setConceptBridge(data);
    } catch (e) {
      setError(String(e));
    } finally {
      setIsAnalyzingConcepts(false);
    }
  }

  async function accept() {
    setError(null);
    if (!selectedIr) return;
    const res = await fetch(`${apiBase()}/artifacts`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ clause_text: clauseText, ir: selectedIr, mode: "STRICT" })
    });
    if (!res.ok) {
      const detail = await res.text();
      setError(detail);
      return;
    }
    const data = (await res.json()) as ArtifactCreateResponse;
    setArtifactId(data.artifact_id);
  }

  async function applyAmbiguityOption(ambiguityId: string, optionId: string) {
    setError(null);
    setArtifactId(null);
    setConceptBridge(null);
    if (!selectedIr) return;

    const variantsById = Object.fromEntries(candidates.map((c) => [c.ir.ir_id, c.ir])) as Record<
      string,
      AdeuIR
    >;

    const res = await fetch(`${apiBase()}/apply_ambiguity_option`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        ir: selectedIr,
        ambiguity_id: ambiguityId,
        option_id: optionId,
        variants_by_id: variantsById,
        mode
      })
    });
    if (!res.ok) {
      const detail = await res.text();
      setError(detail);
      return;
    }
    const data = (await res.json()) as ApplyAmbiguityOptionResponse;
    setCandidates((prev) =>
      prev.map((c, idx) =>
        idx === selectedIdx ? { ...c, ir: data.patched_ir, check_report: data.check_report } : c
      )
    );
  }

  return (
    <div className="app">
      <div className="panel">
        <h2>Text</h2>
        <textarea
          value={clauseText}
          onChange={(e) => setClauseText(e.target.value)}
          placeholder="Paste a clause here…"
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
            if (!highlight) return clauseText;
            const clamped = clampSpan(clauseText, highlight.span);
            if (!clamped) return clauseText;
            return (
              <>
                <span>{clauseText.slice(0, clamped.start)}</span>
                <mark>{clauseText.slice(clamped.start, clamped.end)}</mark>
                <span>{clauseText.slice(clamped.end)}</span>
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
          <button onClick={propose} disabled={!clauseText.trim() || isProposing}>
            Propose variants
          </button>
          <Link href="/artifacts" className="muted" style={{ marginLeft: "auto" }}>
            Artifacts
          </Link>
          <Link href="/concepts" className="muted">
            Concepts
          </Link>
          <Link href="/puzzles" className="muted">
            Puzzles
          </Link>
          <span className="muted">Try pasting one of the fixture clauses.</span>
        </div>
        <div className="row" style={{ marginTop: 8 }}>
          <span className="muted">Context</span>
          <label className="muted">
            doc_id{" "}
            <input value={docId} onChange={(e) => setDocId(e.target.value)} placeholder="doc:..." />
          </label>
          <label className="muted">
            jurisdiction{" "}
            <input
              value={jurisdiction}
              onChange={(e) => setJurisdiction(e.target.value)}
              placeholder="US-CA"
            />
          </label>
          <label className="muted">
            time_eval{" "}
            <input
              value={timeEval}
              onChange={(e) => setTimeEval(e.target.value)}
              placeholder="2026-02-05T00:00:00Z"
            />
          </label>
          <button onClick={() => setTimeEval(new Date().toISOString())}>Now</button>
        </div>
        {isProposing ? <div className="muted">Proposing…</div> : null}
        {proposerLog ? (
          <div className="muted" style={{ marginTop: 8 }}>
            Proposer: {proposerLog.provider}
            {proposerLog.api ? `/${proposerLog.api}` : ""}
            {proposerLog.model ? ` (${proposerLog.model})` : ""} — attempts:{" "}
            {proposerLog.attempts.length}
          </div>
        ) : null}
        {error ? <div className="muted">Error: {error}</div> : null}
        {artifactId ? <div className="muted">Accepted artifact: {artifactId}</div> : null}
      </div>

      <div className="panel">
        <h2>IR</h2>
        <div className="row">
          {candidates.map((c, idx) => (
            <button
              key={idx}
              onClick={() => {
                setSelectedIdx(idx);
                if (compareIdx === idx) setCompareIdx(null);
              }}
              disabled={idx === selectedIdx}
            >
              Variant {idx + 1} ({c.check_report.status}
              {solverStatusFromReport(c.check_report) ? `/${solverStatusFromReport(c.check_report)}` : ""}
              )
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
                onChange={(e) =>
                  setCompareIdx(e.target.value === "" ? null : Number.parseInt(e.target.value, 10))
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
            <span className="muted">
              Selected: {selectedReport?.status ?? "n/a"}
              {selectedSolverStatus ? `/${selectedSolverStatus}` : ""}
            </span>
            <span className="muted">
              Compared: {compared.check_report.status}
              {comparedSolverStatus ? `/${comparedSolverStatus}` : ""}
            </span>
          </div>
        ) : null}
        <SolverDiffPanel
          domain="adeu"
          mode={mode}
          leftIr={selectedIr}
          rightIr={comparedIr}
          onSelectSpan={(span, label) => setHighlight({ span, label })}
        />
        <pre>{selectedIr ? JSON.stringify(selectedIr, null, 2) : ""}</pre>
      </div>

      <div className="panel">
        <h2>Checker</h2>
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
          <button onClick={analyzeAsConcepts} disabled={!selectedIr || isAnalyzingConcepts}>
            {isAnalyzingConcepts ? "Analyzing..." : "Analyze as Concepts"}
          </button>
          <button onClick={accept} disabled={!selectedIr}>
            Accept (STRICT)
          </button>
        </div>
        {selectedIr?.D_norm?.statements?.length ? (
          <div style={{ marginTop: 8 }}>
            <div className="muted">Statements</div>
            {selectedIr.D_norm.statements.map((stmt, idx) => (
              <div key={stmt.id} className="row" style={{ marginTop: 4 }}>
                <button
                  onClick={() => {
                    const span = stmt.provenance?.span ?? null;
                    if (!span) return;
                    setHighlight({ span, label: `stmt:${stmt.id} (/D_norm/statements/${idx})` });
                  }}
                  disabled={!stmt.provenance?.span}
                >
                  Highlight
                </button>
                <span className="muted mono">
                  {stmt.id} ({stmt.kind})
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
                {selectedReport.reason_codes.map((r, idx) => {
                  const span = selectedIr ? spanFromReason(selectedIr, r) : null;
                  return (
                    <tr key={idx}>
                      <td className="mono">{r.severity}</td>
                      <td className="mono">{r.code}</td>
                      <td className="mono">{r.json_path ?? ""}</td>
                      <td className="mono">{r.object_id ?? ""}</td>
                      <td>{r.message}</td>
                      <td>
                        <button
                          onClick={() => {
                            if (!span) return;
                            setHighlight({
                              span,
                              label: `reason:${r.code} ${r.json_path ?? ""}`.trim()
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
        {selectedIr?.ambiguity?.length ? (
          <div style={{ marginTop: 8 }}>
            <div className="muted">Ambiguity options</div>
            {selectedIr.ambiguity.map((a) => (
              <div key={a.id} style={{ marginTop: 8 }}>
                <div className="muted">
                  <strong>{a.issue}</strong> ({a.id})
                </div>
                <div className="row" style={{ marginTop: 4 }}>
                  <button
                    onClick={() =>
                      setHighlight({ span: a.span, label: `amb:${a.id} (issue:${a.issue})` })
                    }
                  >
                    Highlight
                  </button>
                </div>
                <div className="row" style={{ flexWrap: "wrap", gap: 8, marginTop: 4 }}>
                  {a.options.map((opt) => (
                    <button
                      key={opt.option_id}
                      onClick={() => applyAmbiguityOption(a.id, opt.option_id)}
                      disabled={!selectedIr}
                      title={opt.effect}
                    >
                      Apply: {opt.label}
                    </button>
                  ))}
                </div>
              </div>
            ))}
          </div>
        ) : null}
        <pre>{selectedReport ? JSON.stringify(selectedReport, null, 2) : ""}</pre>
      </div>

      <div className="panel">
        <h2>Concept Analysis</h2>
        <div className="row">
          <span className="muted">
            {conceptBridge
              ? `Concept ID: ${conceptBridge.concept_ir.concept_id}`
              : "Run Analyze as Concepts on the selected variant."}
          </span>
        </div>
        {conceptBridge ? (
          <>
            <div className="muted" style={{ marginTop: 8 }}>
              Trust: mapping={conceptBridge.mapping_trust} / solver={conceptBridge.solver_trust} / proof=
              {conceptBridge.proof_trust ?? "n/a"}
            </div>
            <div className="muted mono" style={{ marginTop: 4 }}>
              Mapping: {conceptBridge.bridge_mapping_version} {conceptBridge.mapping_hash.slice(0, 16)}
              ...
            </div>
            <div className="muted" style={{ marginTop: 4 }}>
              Check status: {conceptBridge.check_report.status}
            </div>

            <table className="table" style={{ marginTop: 8 }}>
              <thead>
                <tr>
                  <th>analysis</th>
                  <th>status</th>
                  <th>summary</th>
                </tr>
              </thead>
              <tbody>
                <tr>
                  <td className="mono">closure</td>
                  <td className="mono">{conceptBridge.analysis.closure.status}</td>
                  <td className="mono">edges={conceptBridge.analysis.closure.edge_count}</td>
                </tr>
                <tr>
                  <td className="mono">mic</td>
                  <td className="mono">{conceptBridge.analysis.mic.status}</td>
                  <td className="mono">
                    constraints={conceptBridge.analysis.mic.constraint_count} calls=
                    {conceptBridge.analysis.mic.solver_calls} shrink={conceptBridge.analysis.mic.shrink_iters}
                  </td>
                </tr>
                <tr>
                  <td className="mono">forced</td>
                  <td className="mono">{conceptBridge.analysis.forced.status}</td>
                  <td className="mono">
                    candidates={conceptBridge.analysis.forced.candidate_count} forced=
                    {conceptBridge.analysis.forced.forced_count} countermodels=
                    {conceptBridge.analysis.forced.countermodel_count} calls=
                    {conceptBridge.analysis.forced.solver_calls}
                  </td>
                </tr>
              </tbody>
            </table>

            <div style={{ marginTop: 10, overflow: "auto" }}>
              <div className="muted">Terms ({conceptTerms.length})</div>
              <table className="table" style={{ marginTop: 6 }}>
                <thead>
                  <tr>
                    <th>id</th>
                    <th>label</th>
                    <th></th>
                  </tr>
                </thead>
                <tbody>
                  {conceptTerms.map((term) => {
                    const span = _firstSpan(term.provenance?.span);
                    return (
                      <tr key={term.id}>
                        <td className="mono">{term.id}</td>
                        <td>{term.label}</td>
                        <td>
                          <button
                            onClick={() => {
                              if (!span) return;
                              setHighlight({ span, label: `concept-term:${term.id}` });
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

            <div style={{ marginTop: 10, overflow: "auto" }}>
              <div className="muted">Claims ({conceptClaims.length})</div>
              <table className="table" style={{ marginTop: 6 }}>
                <thead>
                  <tr>
                    <th>id</th>
                    <th>sense</th>
                    <th>text</th>
                    <th></th>
                  </tr>
                </thead>
                <tbody>
                  {conceptClaims.map((claim) => {
                    const span = _firstSpan(claim.provenance?.span);
                    return (
                      <tr key={claim.id}>
                        <td className="mono">{claim.id}</td>
                        <td className="mono">{claim.sense_id}</td>
                        <td>{claim.text}</td>
                        <td>
                          <button
                            onClick={() => {
                              if (!span) return;
                              setHighlight({ span, label: `concept-claim:${claim.id}` });
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
          </>
        ) : null}
      </div>
    </div>
  );
}
