"use client";

import Link from "next/link";
import { useCallback, useEffect, useMemo, useState } from "react";

import { apiBase } from "../lib/api-base";

type CheckStatus = "PASS" | "WARN" | "REFUSE";

type ArtifactSummary = {
  artifact_id: string;
  created_at: string;
  doc_id: string | null;
  jurisdiction: string | null;
  status: CheckStatus | null;
  num_errors: number | null;
  num_warns: number | null;
  solver_trust: "kernel_only" | "solver_backed" | "proof_checked";
  proof_trust?: string | null;
};

type ArtifactListResponse = {
  items: ArtifactSummary[];
};

export default function ArtifactsPage() {
  const [docId, setDocId] = useState<string>("");
  const [status, setStatus] = useState<string>("");
  const [items, setItems] = useState<ArtifactSummary[]>([]);
  const [error, setError] = useState<string | null>(null);
  const [loading, setLoading] = useState<boolean>(false);

  const query = useMemo(() => {
    const params = new URLSearchParams();
    params.set("limit", "50");
    if (docId.trim()) params.set("doc_id", docId.trim());
    if (status) params.set("status", status);
    return params.toString();
  }, [docId, status]);

  const load = useCallback(async () => {
    setError(null);
    setLoading(true);
    try {
      const res = await fetch(`${apiBase()}/artifacts?${query}`, { method: "GET" });
      if (!res.ok) {
        setError(await res.text());
        return;
      }
      const data = (await res.json()) as ArtifactListResponse;
      setItems(data.items ?? []);
    } catch (e) {
      setError(String(e));
    } finally {
      setLoading(false);
    }
  }, [query]);

  useEffect(() => {
    void load();
  }, [load]);

  return (
    <div style={{ padding: 12 }}>
      <div className="row" style={{ justifyContent: "space-between" }}>
        <h2 style={{ margin: 0 }}>Artifacts</h2>
        <div className="row">
          <Link href="/" className="muted">
            ADEU Studio
          </Link>
          <Link href="/concepts" className="muted">
            Concepts
          </Link>
          <Link href="/papers" className="muted">
            Papers
          </Link>
        </div>
      </div>

      <div className="panel" style={{ marginTop: 12 }}>
        <div className="row">
          <label className="muted">
            doc_id{" "}
            <input
              value={docId}
              onChange={(e) => setDocId(e.target.value)}
              placeholder="fixture:..."
            />
          </label>

          <label className="muted">
            status{" "}
            <select value={status} onChange={(e) => setStatus(e.target.value)}>
              <option value="">(any)</option>
              <option value="PASS">PASS</option>
              <option value="WARN">WARN</option>
              <option value="REFUSE">REFUSE</option>
            </select>
          </label>

          <button onClick={load} disabled={loading}>
            Refresh
          </button>

          {loading ? <span className="muted">Loading…</span> : null}
          {error ? <span className="muted">Error: {error}</span> : null}
        </div>

        {items.length === 0 ? (
          <div className="muted" style={{ marginTop: 12 }}>
            No artifacts found.
          </div>
        ) : (
          <div style={{ marginTop: 12, overflow: "auto" }}>
            <table className="table">
              <thead>
                <tr>
                  <th>created</th>
                  <th>status</th>
                  <th>doc_id</th>
                  <th>jurisdiction</th>
                  <th>errors</th>
                  <th>warns</th>
                  <th>solver_trust</th>
                  <th>proof_trust</th>
                  <th>id</th>
                </tr>
              </thead>
              <tbody>
                {items.map((it) => (
                  <tr key={it.artifact_id}>
                    <td className="mono">{it.created_at}</td>
                    <td className="mono">{it.status ?? ""}</td>
                    <td className="mono">{it.doc_id ?? ""}</td>
                    <td className="mono">{it.jurisdiction ?? ""}</td>
                    <td className="mono">{it.num_errors ?? ""}</td>
                    <td className="mono">{it.num_warns ?? ""}</td>
                    <td className="mono">{it.solver_trust}</td>
                    <td className="mono">{it.proof_trust ?? ""}</td>
                    <td className="mono">
                      <Link href={`/artifacts/${it.artifact_id}`}>
                        {it.artifact_id.slice(0, 12)}
                      </Link>
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        )}
      </div>
    </div>
  );
}
