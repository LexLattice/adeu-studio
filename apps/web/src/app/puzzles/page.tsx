"use client";

import Link from "next/link";
import { useMemo, useState } from "react";

import { apiBase } from "../lib/api-base";
import { SolverDiffPanel, type KernelMode } from "../components/solver-diff-panel";
import type { CheckReport } from "../../gen/check_report";

type PuzzleRole = "knight" | "knave";

type PuzzlePerson = {
  id: string;
  name: string;
};

type PuzzlePredicate =
  | {
      op: "is_role";
      person_id: string;
      role: PuzzleRole;
    }
  | {
      op: string;
      [key: string]: unknown;
    };

type PuzzleStatement = {
  id: string;
  speaker_id: string;
  claim: PuzzlePredicate;
};

type PuzzleAssumption = {
  id: string;
  claim: PuzzlePredicate;
};

type PuzzleIR = {
  schema_version: string;
  puzzle_id: string;
  family: string;
  people: PuzzlePerson[];
  statements: PuzzleStatement[];
  assumptions: PuzzleAssumption[];
};

type ProposeCandidate = {
  ir: PuzzleIR;
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

type PuzzleSolveResult = {
  puzzle_id: string;
  assignments: Array<{ person_id: string; role: PuzzleRole }>;
  validator_result: {
    status: string;
    backend: string;
  };
};

export default function PuzzlesPage() {
  const [puzzleText, setPuzzleText] = useState<string>("");
  const [provider, setProvider] = useState<"mock" | "openai">("mock");
  const [mode, setMode] = useState<KernelMode>("LAX");

  const [isProposing, setIsProposing] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);

  const [proposerLog, setProposerLog] = useState<ProposerLog | null>(null);
  const [candidates, setCandidates] = useState<ProposeCandidate[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [compareIdx, setCompareIdx] = useState<number | null>(null);

  const [solveResult, setSolveResult] = useState<PuzzleSolveResult | null>(null);

  const selected = useMemo(() => candidates[selectedIdx] ?? null, [candidates, selectedIdx]);
  const selectedIr = useMemo(() => selected?.ir ?? null, [selected]);
  const selectedReport = useMemo(() => selected?.check_report ?? null, [selected]);

  const compared = useMemo(
    () => (compareIdx === null ? null : candidates[compareIdx] ?? null),
    [candidates, compareIdx],
  );

  async function propose() {
    setError(null);
    setSolveResult(null);
    setIsProposing(true);
    setProposerLog(null);
    try {
      const res = await fetch(`${apiBase()}/puzzles/propose`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ puzzle_text: puzzleText, provider, mode }),
      });
      if (!res.ok) {
        setError(await res.text());
        return;
      }
      const data = (await res.json()) as ProposeResponse;
      setCandidates(data.candidates ?? []);
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
    setSolveResult(null);
    const res = await fetch(`${apiBase()}/puzzles/check`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ puzzle: selectedIr, mode }),
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

  async function runSolve() {
    if (!selectedIr) return;
    setError(null);
    const res = await fetch(`${apiBase()}/puzzles/solve`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ puzzle: selectedIr, backend: "z3" }),
    });
    if (!res.ok) {
      setError(await res.text());
      return;
    }
    const data = (await res.json()) as PuzzleSolveResult;
    setSolveResult(data);
  }

  return (
    <div className="app">
      <div className="panel">
        <h2>Puzzle Text</h2>
        <textarea
          value={puzzleText}
          onChange={(event) => setPuzzleText(event.target.value)}
          placeholder="Paste a knights/knaves puzzle here…"
        />

        <div className="row" style={{ marginTop: 8 }}>
          <span className="muted">Provider</span>
          <button onClick={() => setProvider("mock")} disabled={provider === "mock"}>
            mock
          </button>
          <button onClick={() => setProvider("openai")} disabled={provider === "openai"}>
            openai
          </button>
          <button onClick={propose} disabled={!puzzleText.trim() || isProposing}>
            Propose variants
          </button>
          <Link href="/" className="muted" style={{ marginLeft: "auto" }}>
            ADEU Studio
          </Link>
          <Link href="/concepts" className="muted">
            Concepts
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
      </div>

      <div className="panel">
        <h2>Puzzle IR</h2>
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
          domain="puzzles"
          mode={mode}
          leftIr={selectedIr}
          rightIr={compared?.ir ?? null}
        />

        <pre>{selectedIr ? JSON.stringify(selectedIr, null, 2) : ""}</pre>
      </div>

      <div className="panel">
        <h2>Checker / Solver</h2>
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
          <button onClick={runSolve} disabled={!selectedIr}>
            Solve (z3)
          </button>
        </div>

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
                </tr>
              </thead>
              <tbody>
                {selectedReport.reason_codes.map((reason, idx) => (
                  <tr key={idx}>
                    <td className="mono">{reason.severity}</td>
                    <td className="mono">{reason.code}</td>
                    <td className="mono">{reason.json_path ?? ""}</td>
                    <td className="mono">{reason.object_id ?? ""}</td>
                    <td>{reason.message}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        ) : null}

        {solveResult ? (
          <div style={{ marginTop: 8 }}>
            <div className="muted">
              Solve status: {solveResult.validator_result.status} ({solveResult.validator_result.backend})
            </div>
            <table className="table" style={{ marginTop: 8 }}>
              <thead>
                <tr>
                  <th>person</th>
                  <th>role</th>
                </tr>
              </thead>
              <tbody>
                {solveResult.assignments.map((assignment) => (
                  <tr key={`${assignment.person_id}:${assignment.role}`}>
                    <td className="mono">{assignment.person_id}</td>
                    <td className="mono">{assignment.role}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        ) : null}
      </div>
    </div>
  );
}
