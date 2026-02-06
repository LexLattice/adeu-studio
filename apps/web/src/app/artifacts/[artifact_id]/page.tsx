"use client";

import Link from "next/link";
import { useEffect, useState } from "react";

import type { AdeuIR, SourceSpan } from "../../../gen/adeu_ir";
import type { CheckReport } from "../../../gen/check_report";

type ArtifactGetResponse = {
  artifact_id: string;
  created_at: string;
  clause_text: string;
  ir: AdeuIR;
  check_report: CheckReport;
};

type ValidatorRun = {
  run_id: string;
  artifact_id: string | null;
  created_at: string;
  backend: string;
  backend_version: string | null;
  timeout_ms: number;
  options_json: Record<string, unknown>;
  request_hash: string;
  formula_hash: string;
  status: string;
  evidence_json: Record<string, unknown>;
  atom_map_json: Record<string, unknown>;
};

type ArtifactValidatorRunsResponse = {
  items: ValidatorRun[];
};

type Highlight = { span: SourceSpan; label: string } | null;

function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function clampSpan(text: string, span: SourceSpan): SourceSpan | null {
  const start = Math.max(0, Math.min(text.length, span.start));
  const end = Math.max(0, Math.min(text.length, span.end));
  if (start >= end) return null;
  return { start, end };
}

function spanFromRunRef(ir: AdeuIR, objectId?: string | null, jsonPath?: string | null): SourceSpan | null {
  if (objectId) {
    const stmt = ir.D_norm?.statements?.find((s) => s.id === objectId);
    if (stmt?.provenance?.span) return stmt.provenance.span;
    const ex = ir.D_norm?.exceptions?.find((e) => e.id === objectId);
    if (ex?.provenance?.span) return ex.provenance.span;
    const amb = ir.ambiguity?.find((a) => a.id === objectId);
    if (amb?.span) return amb.span;
    const bridge = ir.bridges?.find((b) => b.id === objectId);
    if (bridge?.provenance?.span) return bridge.provenance.span;
  }

  const path = jsonPath ?? "";
  const stmtPrefix = "/D_norm/statements/";
  if (path.startsWith(stmtPrefix)) {
    const idx = Number.parseInt(path.slice(stmtPrefix.length).split("/")[0], 10);
    const stmt = Number.isFinite(idx) ? ir.D_norm?.statements?.[idx] : undefined;
    if (stmt?.provenance?.span) return stmt.provenance.span;
  }

  const exPrefix = "/D_norm/exceptions/";
  if (path.startsWith(exPrefix)) {
    const idx = Number.parseInt(path.slice(exPrefix.length).split("/")[0], 10);
    const ex = Number.isFinite(idx) ? ir.D_norm?.exceptions?.[idx] : undefined;
    if (ex?.provenance?.span) return ex.provenance.span;
  }
  return null;
}

export default function ArtifactDetailPage({ params }: { params: { artifact_id: string } }) {
  const [item, setItem] = useState<ArtifactGetResponse | null>(null);
  const [runs, setRuns] = useState<ValidatorRun[]>([]);
  const [selectedRunIdx, setSelectedRunIdx] = useState<number>(-1);
  const [highlight, setHighlight] = useState<Highlight>(null);
  const [error, setError] = useState<string | null>(null);
  const [loading, setLoading] = useState<boolean>(false);

  useEffect(() => {
    async function load() {
      setError(null);
      setLoading(true);
      setHighlight(null);
      try {
        const [artifactRes, runsRes] = await Promise.all([
          fetch(`${apiBase()}/artifacts/${params.artifact_id}`, { method: "GET" }),
          fetch(`${apiBase()}/artifacts/${params.artifact_id}/validator-runs`, { method: "GET" })
        ]);

        if (!artifactRes.ok) {
          setError(await artifactRes.text());
          return;
        }
        if (!runsRes.ok) {
          setError(await runsRes.text());
          return;
        }
        const artifactData = (await artifactRes.json()) as ArtifactGetResponse;
        const runsData = (await runsRes.json()) as ArtifactValidatorRunsResponse;
        setItem(artifactData);
        setRuns(runsData.items ?? []);
        setSelectedRunIdx((runsData.items?.length ?? 0) - 1);
      } catch (e) {
        setError(String(e));
      } finally {
        setLoading(false);
      }
    }
    void load();
  }, [params.artifact_id]);

  const selectedRun =
    selectedRunIdx >= 0 && selectedRunIdx < runs.length ? runs[selectedRunIdx] : null;

  const selectedRunModel = isRecord(selectedRun?.evidence_json.model)
    ? (selectedRun?.evidence_json.model as Record<string, unknown>)
    : null;
  const selectedRunUnsatCore = Array.isArray(selectedRun?.evidence_json.unsat_core)
    ? (selectedRun?.evidence_json.unsat_core as unknown[])
    : [];
  const selectedRunStats = isRecord(selectedRun?.evidence_json.stats)
    ? (selectedRun?.evidence_json.stats as Record<string, unknown>)
    : null;

  return (
    <div style={{ padding: 12 }}>
      <div className="row" style={{ justifyContent: "space-between" }}>
        <h2 style={{ margin: 0 }}>Artifact</h2>
        <Link href="/artifacts" className="muted">
          Back to list
        </Link>
      </div>

      {loading ? <div className="muted">Loading…</div> : null}
      {error ? <div className="muted">Error: {error}</div> : null}

      {item ? (
        <div className="panel" style={{ marginTop: 12 }}>
          <div className="muted">
            <div className="row" style={{ justifyContent: "space-between" }}>
              <span className="mono">{item.artifact_id}</span>
              <span className="mono">{item.created_at}</span>
            </div>
          </div>

          <h3 className="muted" style={{ margin: "12px 0 6px 0" }}>
            Clause text
          </h3>
          <div className="clause-preview">
            {(() => {
              if (!highlight) return item.clause_text;
              const clamped = clampSpan(item.clause_text, highlight.span);
              if (!clamped) return item.clause_text;
              return (
                <>
                  <span>{item.clause_text.slice(0, clamped.start)}</span>
                  <mark>{item.clause_text.slice(clamped.start, clamped.end)}</mark>
                  <span>{item.clause_text.slice(clamped.end)}</span>
                </>
              );
            })()}
          </div>
          <div className="row" style={{ marginTop: 6 }}>
            <span className="muted">Highlight</span>
            <button onClick={() => setHighlight(null)} disabled={!highlight}>
              Clear
            </button>
            {highlight ? <span className="muted mono">{highlight.label}</span> : null}
          </div>

          <h3 className="muted" style={{ margin: "12px 0 6px 0" }}>
            IR
          </h3>
          <pre>{JSON.stringify(item.ir, null, 2)}</pre>

          <h3 className="muted" style={{ margin: "12px 0 6px 0" }}>
            Check report
          </h3>
          <pre>{JSON.stringify(item.check_report, null, 2)}</pre>

          <h3 className="muted" style={{ margin: "12px 0 6px 0" }}>
            Solver evidence
          </h3>
          {runs.length === 0 ? (
            <div className="muted">No persisted validator runs for this artifact.</div>
          ) : (
            <div>
              <div className="row" style={{ marginBottom: 8 }}>
                {runs.map((run, idx) => (
                  <button
                    key={run.run_id}
                    onClick={() => setSelectedRunIdx(idx)}
                    disabled={idx === selectedRunIdx}
                  >
                    Run {idx + 1} ({run.status})
                  </button>
                ))}
              </div>
              {selectedRun ? (
                <div>
                  <div className="row">
                    <span className="mono">
                      {selectedRun.backend}
                      {selectedRun.backend_version ? `:${selectedRun.backend_version}` : ""}
                    </span>
                    <span className="mono">status={selectedRun.status}</span>
                    <span className="mono">timeout_ms={selectedRun.timeout_ms}</span>
                    <span className="mono">formula={selectedRun.formula_hash.slice(0, 12)}</span>
                  </div>

                  {selectedRun.status === "SAT" && selectedRunModel ? (
                    <div style={{ marginTop: 8 }}>
                      <div className="muted">Model assignments</div>
                      <table className="table" style={{ marginTop: 6 }}>
                        <thead>
                          <tr>
                            <th>symbol</th>
                            <th>value</th>
                          </tr>
                        </thead>
                        <tbody>
                          {Object.entries(selectedRunModel)
                            .sort((a, b) => a[0].localeCompare(b[0]))
                            .map(([symbol, value]) => (
                              <tr key={symbol}>
                                <td className="mono">{symbol}</td>
                                <td className="mono">{String(value)}</td>
                              </tr>
                            ))}
                        </tbody>
                      </table>
                    </div>
                  ) : null}

                  {selectedRun.status === "UNSAT" ? (
                    <div style={{ marginTop: 8 }}>
                      <div className="muted">Unsat core (mapped)</div>
                      {selectedRunUnsatCore.length === 0 ? (
                        <div className="muted">No unsat core atoms returned.</div>
                      ) : (
                        <table className="table" style={{ marginTop: 6 }}>
                          <thead>
                            <tr>
                              <th>atom</th>
                              <th>object_id</th>
                              <th>json_path</th>
                              <th></th>
                            </tr>
                          </thead>
                          <tbody>
                            {selectedRunUnsatCore.map((rawAtom) => {
                              const atom = String(rawAtom);
                              const rawRef = selectedRun.atom_map_json[atom];
                              const ref = isRecord(rawRef) ? rawRef : {};
                              const objectId =
                                typeof ref.object_id === "string" ? ref.object_id : null;
                              const jsonPath =
                                typeof ref.json_path === "string" ? ref.json_path : null;
                              const span = spanFromRunRef(item.ir, objectId, jsonPath);
                              return (
                                <tr key={atom}>
                                  <td className="mono">{atom}</td>
                                  <td className="mono">{objectId ?? ""}</td>
                                  <td className="mono">{jsonPath ?? ""}</td>
                                  <td>
                                    <button
                                      onClick={() => {
                                        if (!span) return;
                                        setHighlight({
                                          span,
                                          label:
                                            `unsat:${atom}` +
                                            (jsonPath ? ` ${jsonPath}` : "") +
                                            (objectId ? ` (${objectId})` : "")
                                        });
                                      }}
                                      disabled={!span}
                                    >
                                      Jump to clause
                                    </button>
                                  </td>
                                </tr>
                              );
                            })}
                          </tbody>
                        </table>
                      )}
                    </div>
                  ) : null}

                  {selectedRunStats ? (
                    <div style={{ marginTop: 8 }}>
                      <div className="muted">Solver stats</div>
                      <pre style={{ flex: "unset" }}>{JSON.stringify(selectedRunStats, null, 2)}</pre>
                    </div>
                  ) : null}
                </div>
              ) : null}
            </div>
          )}
        </div>
      ) : null}
    </div>
  );
}
