"use client";

import Link from "next/link";
import { useEffect, useState } from "react";

import type { AdeuIR } from "../../../gen/adeu_ir";
import type { CheckReport } from "../../../gen/check_report";

type ArtifactGetResponse = {
  artifact_id: string;
  created_at: string;
  clause_text: string;
  ir: AdeuIR;
  check_report: CheckReport;
};

function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}

export default function ArtifactDetailPage({ params }: { params: { artifact_id: string } }) {
  const [item, setItem] = useState<ArtifactGetResponse | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [loading, setLoading] = useState<boolean>(false);

  useEffect(() => {
    async function load() {
      setError(null);
      setLoading(true);
      try {
        const res = await fetch(`${apiBase()}/artifacts/${params.artifact_id}`, { method: "GET" });
        if (!res.ok) {
          setError(await res.text());
          return;
        }
        setItem((await res.json()) as ArtifactGetResponse);
      } catch (e) {
        setError(String(e));
      } finally {
        setLoading(false);
      }
    }
    void load();
  }, [params.artifact_id]);

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
          <pre style={{ flex: "unset" }}>{item.clause_text}</pre>

          <h3 className="muted" style={{ margin: "12px 0 6px 0" }}>
            IR
          </h3>
          <pre>{JSON.stringify(item.ir, null, 2)}</pre>

          <h3 className="muted" style={{ margin: "12px 0 6px 0" }}>
            Check report
          </h3>
          <pre>{JSON.stringify(item.check_report, null, 2)}</pre>
        </div>
      ) : null}
    </div>
  );
}
