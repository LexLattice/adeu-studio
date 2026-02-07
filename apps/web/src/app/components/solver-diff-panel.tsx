"use client";

import { useEffect, useMemo, useState } from "react";

export type KernelMode = "STRICT" | "LAX";

export type SourceSpanLike = { start: number; end: number };

type JsonPatchOp = {
  op: string;
  path: string;
  from_path?: string | null;
  value?: unknown;
};

type CoreDelta = {
  added_atoms: string[];
  removed_atoms: string[];
};

type ModelAssignment = {
  atom: string;
  value: string;
};

type ModelAssignmentChange = {
  atom: string;
  left_value: string;
  right_value: string;
};

type ModelDelta = {
  added_assignments: ModelAssignment[];
  removed_assignments: ModelAssignment[];
  changed_assignments: ModelAssignmentChange[];
  changed_atoms: string[];
};

type SolverDiff = {
  status_flip: string;
  core_delta: CoreDelta;
  model_delta: ModelDelta;
  unpaired_left_hashes?: string[];
  unpaired_right_hashes?: string[];
};

type StructuralDiff = {
  json_patches: JsonPatchOp[];
  changed_paths: string[];
  changed_object_ids: string[];
};

type CausalSlice = {
  touched_atoms: string[];
  touched_object_ids: string[];
  touched_json_paths: string[];
  explanation_items: Array<{
    atom_name: string;
    object_id?: string | null;
    json_path?: string | null;
    span?: SourceSpanLike | null;
  }>;
};

type DiffSummary = {
  status_flip: string;
  structural_patch_count: string;
  solver_touched_atom_count: string;
  causal_atom_count: string;
  run_source?: string;
  recompute_mode?: string | null;
  left_backend?: string | null;
  right_backend?: string | null;
  left_timeout_ms?: number | null;
  right_timeout_ms?: number | null;
};

type DiffReport = {
  left_id: string;
  right_id: string;
  structural: StructuralDiff;
  solver: SolverDiff;
  causal_slice: CausalSlice;
  summary: DiffSummary;
};

function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}

type Props = {
  endpoint: "/diff" | "/concepts/diff" | "/puzzles/diff";
  mode: KernelMode;
  leftIr: unknown | null;
  rightIr: unknown | null;
  extraPayload?: Record<string, unknown>;
  onSelectSpan?: (span: SourceSpanLike, label: string) => void;
};

export function SolverDiffPanel({
  endpoint,
  mode,
  leftIr,
  rightIr,
  extraPayload,
  onSelectSpan,
}: Props) {
  const [report, setReport] = useState<DiffReport | null>(null);
  const [isLoading, setIsLoading] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    if (!leftIr || !rightIr) {
      setReport(null);
      setError(null);
      setIsLoading(false);
      return;
    }

    const controller = new AbortController();
    let active = true;

    async function loadDiff(): Promise<void> {
      setError(null);
      setIsLoading(true);
      try {
        const res = await fetch(`${apiBase()}${endpoint}`, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ left_ir: leftIr, right_ir: rightIr, mode, ...(extraPayload ?? {}) }),
          signal: controller.signal,
        });
        if (!res.ok) {
          if (active) {
            setError(await res.text());
            setReport(null);
          }
          return;
        }
        const data = (await res.json()) as DiffReport;
        if (active) setReport(data);
      } catch (e) {
        if (!active) return;
        if (e instanceof Error && e.name === "AbortError") return;
        setError(String(e));
        setReport(null);
      } finally {
        if (active) setIsLoading(false);
      }
    }

    void loadDiff();
    return () => {
      active = false;
      controller.abort();
    };
  }, [endpoint, leftIr, rightIr, mode, extraPayload]);

  const solverFlip = useMemo(() => {
    const flip = report?.solver.status_flip ?? "";
    if (!flip.includes("→")) return false;
    const [left, right] = flip.split("→");
    return left !== right;
  }, [report]);

  if (!leftIr || !rightIr) {
    return <div className="muted">Select two variants to compare.</div>;
  }

  return (
    <div style={{ marginTop: 8 }}>
      {isLoading ? <div className="muted">Computing solver-aware diff…</div> : null}
      {error ? <div className="muted">Diff error: {error}</div> : null}
      {report ? (
        <>
          <div className="muted">
            Diff: {report.solver.status_flip}
            {solverFlip ? " (satisfiability flipped)" : ""}
          </div>
          <div className="muted">
            Run source: {report.summary.run_source ?? "unknown"}
            {report.summary.recompute_mode ? ` (${report.summary.recompute_mode})` : ""}
          </div>
          <div className="muted">
            Backends: L={report.summary.left_backend ?? "n/a"} / R={report.summary.right_backend ?? "n/a"}
          </div>
          <div className="muted">
            Timeouts: L=
            {report.summary.left_timeout_ms !== null && report.summary.left_timeout_ms !== undefined
              ? report.summary.left_timeout_ms
              : "n/a"}
            {" / "}
            R=
            {report.summary.right_timeout_ms !== null && report.summary.right_timeout_ms !== undefined
              ? report.summary.right_timeout_ms
              : "n/a"}
          </div>
          <div className="muted">
            Solver core delta: +{report.solver.core_delta.added_atoms.length} / -
            {report.solver.core_delta.removed_atoms.length}
          </div>
          <div className="muted">
            Solver model changed atoms: {report.solver.model_delta.changed_atoms.length}
          </div>
          <div className="muted">Causal atoms: {report.causal_slice.touched_atoms.length}</div>

          {report.structural?.json_patches?.length ? (
            <pre style={{ flex: "unset" }}>
              {report.structural.json_patches
                .map((patch) => {
                  const fromPath = patch.from_path ? ` from=${patch.from_path}` : "";
                  const value = patch.value === undefined ? "" : ` value=${JSON.stringify(patch.value)}`;
                  return `${patch.op.toUpperCase()} ${patch.path}${fromPath}${value}`;
                })
                .join("\n")}
            </pre>
          ) : null}

          {report.causal_slice?.explanation_items?.length ? (
            <div style={{ marginTop: 8 }}>
              <div className="muted">Causal slice</div>
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
                  {report.causal_slice.explanation_items.map((item) => (
                    <tr key={`${item.atom_name}-${item.object_id ?? ""}-${item.json_path ?? ""}`}>
                      <td className="mono">{item.atom_name}</td>
                      <td className="mono">{item.object_id ?? ""}</td>
                      <td className="mono">{item.json_path ?? ""}</td>
                      <td>
                        <button
                          onClick={() => {
                            if (!item.span || !onSelectSpan) return;
                            onSelectSpan(item.span, `diff:${item.atom_name} ${item.json_path ?? ""}`.trim());
                          }}
                          disabled={!item.span || !onSelectSpan}
                        >
                          Highlight
                        </button>
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          ) : null}
        </>
      ) : null}
    </div>
  );
}
