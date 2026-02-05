"use client";

import Link from "next/link";
import { useMemo, useState } from "react";

import type { AdeuIR } from "../gen/adeu_ir";
import type { CheckReport } from "../gen/check_report";

type KernelMode = "STRICT" | "LAX";

type ProposeResponse = {
  candidates: AdeuIR[];
  provider: string;
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

function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}

export default function HomePage() {
  const [clauseText, setClauseText] = useState<string>("");
  const [candidates, setCandidates] = useState<AdeuIR[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [mode, setMode] = useState<KernelMode>("LAX");
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
    setCandidates(data.candidates ?? []);
    setSelectedIdx(0);
  }

  async function runCheck() {
    setError(null);
    setArtifactId(null);
    if (!selected) return;
    const res = await fetch(`${apiBase()}/check`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ ir: selected, mode })
    });
    setCheckReport((await res.json()) as CheckReport);
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
    const data = (await res.json()) as ArtifactCreateResponse;
    setArtifactId(data.artifact_id);
  }

  async function applyAmbiguityOption(ambiguityId: string, optionId: string) {
    setError(null);
    setArtifactId(null);
    if (!selected) return;

    const variantsById = Object.fromEntries(candidates.map((c) => [c.ir_id, c])) as Record<
      string,
      AdeuIR
    >;

    const res = await fetch(`${apiBase()}/apply_ambiguity_option`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        ir: selected,
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
    setCandidates((prev) => prev.map((c, idx) => (idx === selectedIdx ? data.patched_ir : c)));
    setCheckReport(data.check_report);
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
          <Link href="/artifacts" className="muted" style={{ marginLeft: "auto" }}>
            Artifacts
          </Link>
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
          <span className="muted">Mode</span>
          <button onClick={() => setMode("LAX")} disabled={mode === "LAX"}>
            LAX
          </button>
          <button onClick={() => setMode("STRICT")} disabled={mode === "STRICT"}>
            STRICT
          </button>
          <button onClick={runCheck} disabled={!selected}>
            Check ({mode})
          </button>
          <button onClick={accept} disabled={!selected}>
            Accept (STRICT)
          </button>
        </div>
        {selected?.ambiguity?.length ? (
          <div style={{ marginTop: 8 }}>
            <div className="muted">Ambiguity options</div>
            {selected.ambiguity.map((a) => (
              <div key={a.id} style={{ marginTop: 8 }}>
                <div className="muted">
                  <strong>{a.issue}</strong> ({a.id})
                </div>
                <div className="row" style={{ flexWrap: "wrap", gap: 8, marginTop: 4 }}>
                  {a.options.map((opt) => (
                    <button
                      key={opt.option_id}
                      onClick={() => applyAmbiguityOption(a.id, opt.option_id)}
                      disabled={!selected}
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
        <pre>{checkReport ? JSON.stringify(checkReport, null, 2) : ""}</pre>
      </div>
    </div>
  );
}
