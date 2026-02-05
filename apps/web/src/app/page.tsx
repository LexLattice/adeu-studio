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

type DiffKind = "add" | "remove" | "change";

type DiffItem = {
  path: string;
  kind: DiffKind;
  before: unknown;
  after: unknown;
};

function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function diffJson(
  before: unknown,
  after: unknown,
  path: string,
  out: DiffItem[],
  limit: number
): void {
  if (out.length >= limit) return;
  if (before === after) return;

  if (Array.isArray(before) && Array.isArray(after)) {
    const max = Math.max(before.length, after.length);
    for (let i = 0; i < max; i++) {
      if (out.length >= limit) return;
      const nextPath = `${path}/${i}`;
      if (i >= before.length) {
        out.push({ path: nextPath, kind: "add", before: undefined, after: after[i] });
        continue;
      }
      if (i >= after.length) {
        out.push({ path: nextPath, kind: "remove", before: before[i], after: undefined });
        continue;
      }
      diffJson(before[i], after[i], nextPath, out, limit);
    }
    return;
  }

  if (isRecord(before) && isRecord(after)) {
    const keys = Array.from(new Set([...Object.keys(before), ...Object.keys(after)])).sort();
    for (const key of keys) {
      if (out.length >= limit) return;
      const nextPath = `${path}/${key}`;
      if (!(key in after)) {
        out.push({ path: nextPath, kind: "remove", before: before[key], after: undefined });
        continue;
      }
      if (!(key in before)) {
        out.push({ path: nextPath, kind: "add", before: undefined, after: after[key] });
        continue;
      }
      diffJson(before[key], after[key], nextPath, out, limit);
    }
    return;
  }

  out.push({ path, kind: "change", before, after });
}

export default function HomePage() {
  const [clauseText, setClauseText] = useState<string>("");
  const [candidates, setCandidates] = useState<AdeuIR[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [compareIdx, setCompareIdx] = useState<number | null>(null);
  const [mode, setMode] = useState<KernelMode>("LAX");
  const [checkReport, setCheckReport] = useState<CheckReport | null>(null);
  const [artifactId, setArtifactId] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);

  const selected = useMemo(() => candidates[selectedIdx] ?? null, [candidates, selectedIdx]);
  const compared = useMemo(
    () => (compareIdx === null ? null : candidates[compareIdx] ?? null),
    [candidates, compareIdx]
  );
  const diffItems = useMemo(() => {
    if (!selected || !compared) return [];
    const out: DiffItem[] = [];
    diffJson(selected, compared, "", out, 200);
    out.sort((a, b) => a.path.localeCompare(b.path));
    return out;
  }, [selected, compared]);

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
    setCompareIdx(null);
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
            <button
              key={idx}
              onClick={() => {
                setSelectedIdx(idx);
                if (compareIdx === idx) setCompareIdx(null);
              }}
              disabled={idx === selectedIdx}
            >
              Variant {idx + 1}
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
        {diffItems.length ? (
          <pre style={{ flex: "unset" }}>
            {diffItems
              .map((d) => {
                const before = d.before === undefined ? "" : JSON.stringify(d.before);
                const after = d.after === undefined ? "" : JSON.stringify(d.after);
                return `${d.kind.toUpperCase()} ${d.path}\n  - ${before}\n  + ${after}`;
              })
              .join("\n")}
          </pre>
        ) : null}
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
