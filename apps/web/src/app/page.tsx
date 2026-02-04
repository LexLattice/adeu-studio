"use client";

import { useMemo, useState } from "react";

type KernelMode = "STRICT" | "LAX";

type ProposeResponse = {
  candidates: any[];
  provider: string;
};

type CheckReport = any;

function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}

export default function HomePage() {
  const [clauseText, setClauseText] = useState<string>("");
  const [candidates, setCandidates] = useState<any[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [checkReport, setCheckReport] = useState<CheckReport | null>(null);
  const [artifactId, setArtifactId] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);

  const selected = useMemo(() => candidates[selectedIdx] ?? null, [candidates, selectedIdx]);

  async function propose() {
    setError(null);
    setArtifactId(null);
    setCheckReport(null);
    const res = await fetch(`${apiBase()}/propose`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ clause_text: clauseText, provider: "mock" })
    });
    const data = (await res.json()) as ProposeResponse;
    setCandidates(data.candidates || []);
    setSelectedIdx(0);
  }

  async function runCheck(mode: KernelMode) {
    setError(null);
    setArtifactId(null);
    if (!selected) return;
    const res = await fetch(`${apiBase()}/check`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ ir: selected, mode })
    });
    setCheckReport(await res.json());
  }

  async function accept() {
    setError(null);
    if (!selected) return;
    const res = await fetch(`${apiBase()}/artifacts`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ clause_text: clauseText, ir: selected, mode: "STRICT" })
    });
    if (!res.ok) {
      const detail = await res.text();
      setError(detail);
      return;
    }
    const data = await res.json();
    setArtifactId(data.artifact_id);
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
          <button onClick={propose} disabled={!clauseText.trim()}>
            Propose variants (mock)
          </button>
          <span className="muted">Try pasting one of the fixture clauses.</span>
        </div>
        {error ? <div className="muted">Error: {error}</div> : null}
        {artifactId ? <div className="muted">Accepted artifact: {artifactId}</div> : null}
      </div>

      <div className="panel">
        <h2>IR</h2>
        <div className="row">
          {candidates.map((c, idx) => (
            <button key={idx} onClick={() => setSelectedIdx(idx)} disabled={idx === selectedIdx}>
              Variant {idx + 1}
            </button>
          ))}
          {candidates.length === 0 ? <span className="muted">No candidates yet.</span> : null}
        </div>
        <pre>{selected ? JSON.stringify(selected, null, 2) : ""}</pre>
      </div>

      <div className="panel">
        <h2>Checker</h2>
        <div className="row">
          <button onClick={() => runCheck("LAX")} disabled={!selected}>
            Check (LAX)
          </button>
          <button onClick={() => runCheck("STRICT")} disabled={!selected}>
            Check (STRICT)
          </button>
          <button onClick={accept} disabled={!selected}>
            Accept (STRICT)
          </button>
        </div>
        <pre>{checkReport ? JSON.stringify(checkReport, null, 2) : ""}</pre>
      </div>
    </div>
  );
}

