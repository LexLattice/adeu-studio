"use client";

import { useEffect, useMemo, useState } from "react";

export type KernelMode = "STRICT" | "LAX";
export type DiffDomain = "adeu" | "concepts" | "puzzles";

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

type CauseChainItem = {
  severity: "ERROR" | "WARN" | "INFO";
  object_kind: string;
  object_id?: string | null;
  json_path?: string | null;
  atom_name: string;
  evidence_kind: string;
  message: string;
  left_span?: SourceSpanLike | null;
  right_span?: SourceSpanLike | null;
};

type FlipExplanation = {
  flip_kind: string;
  check_status_flip: string;
  solver_status_flip: string;
  cause_chain: CauseChainItem[];
  repair_hints: Array<{
    object_kind: string;
    object_id?: string | null;
    json_path?: string | null;
    hint: string;
  }>;
};

type ForcedEdgeKey = {
  src_sense_id: string;
  dst_sense_id: string;
  kind: string;
};

type ConceptAnalysisDelta = {
  mic_delta_status?: string | null;
  forced_delta_status?: string | null;
  mic_atoms_added: string[];
  mic_atoms_removed: string[];
  forced_edges_added: ForcedEdgeKey[];
  forced_edges_removed: ForcedEdgeKey[];
  countermodel_edges_changed: ForcedEdgeKey[];
};

type ExplainFlipResponse = {
  diff_report: DiffReport;
  flip_explanation: FlipExplanation;
  analysis_delta?: ConceptAnalysisDelta | null;
  run_ir_mismatch: boolean;
  left_mismatch: boolean;
  right_mismatch: boolean;
};

function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}

type Props = {
  domain: DiffDomain;
  mode: KernelMode;
  leftIr: unknown | null;
  rightIr: unknown | null;
  leftSourceText?: string | null;
  rightSourceText?: string | null;
  includeAnalysisDelta?: boolean;
  includeForcedDetails?: boolean;
  onSelectSpan?: (span: SourceSpanLike, label: string) => void;
};

export function SolverDiffPanel({
  domain,
  mode,
  leftIr,
  rightIr,
  leftSourceText,
  rightSourceText,
  includeAnalysisDelta = false,
  includeForcedDetails = false,
  onSelectSpan,
}: Props) {
  const [response, setResponse] = useState<ExplainFlipResponse | null>(null);
  const [isLoading, setIsLoading] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    if (!leftIr || !rightIr) {
      setResponse(null);
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
        const res = await fetch(`${apiBase()}/explain_flip`, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({
            domain,
            left_ir: leftIr,
            right_ir: rightIr,
            mode,
            include_analysis_delta: includeAnalysisDelta,
            include_forced_details: includeForcedDetails,
            left_source_text: leftSourceText ?? null,
            right_source_text: rightSourceText ?? null,
          }),
          signal: controller.signal,
        });
        if (!res.ok) {
          if (active) {
            setError(await res.text());
            setResponse(null);
          }
          return;
        }
        const data = (await res.json()) as ExplainFlipResponse;
        if (active) setResponse(data);
      } catch (e) {
        if (!active) return;
        if (e instanceof Error && e.name === "AbortError") return;
        setError(String(e));
        setResponse(null);
      } finally {
        if (active) setIsLoading(false);
      }
    }

    void loadDiff();
    return () => {
      active = false;
      controller.abort();
    };
  }, [
    domain,
    leftIr,
    rightIr,
    mode,
    includeAnalysisDelta,
    includeForcedDetails,
    leftSourceText,
    rightSourceText,
  ]);

  const report = response?.diff_report ?? null;
  const explanation = response?.flip_explanation ?? null;

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
      {isLoading ? <div className="muted">Computing solver-aware explanation…</div> : null}
      {error ? <div className="muted">Explain error: {error}</div> : null}
      {report && explanation ? (
        <>
          <div className="muted">
            Flip: {explanation.flip_kind}
            {solverFlip ? " (solver status flipped)" : ""}
          </div>
          <div className="muted">Check: {explanation.check_status_flip}</div>
          <div className="muted">Solver: {explanation.solver_status_flip}</div>
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
          {response?.run_ir_mismatch ? (
            <div className="muted">
              Inline run mismatch: left={String(response.left_mismatch)} / right={String(response.right_mismatch)}
            </div>
          ) : null}

          <div className="muted">
            Solver core delta: +{report.solver.core_delta.added_atoms.length} / -
            {report.solver.core_delta.removed_atoms.length}
          </div>
          <div className="muted">
            Solver model changed atoms: {report.solver.model_delta.changed_atoms.length}
          </div>
          <div className="muted">Causal atoms: {report.causal_slice.touched_atoms.length}</div>

          {response.analysis_delta ? (
            <div style={{ marginTop: 8 }}>
              <div className="muted">Concepts analysis delta</div>
              <div className="muted">
                MIC: +{response.analysis_delta.mic_atoms_added.length} / -
                {response.analysis_delta.mic_atoms_removed.length}
                {response.analysis_delta.mic_delta_status
                  ? ` (${response.analysis_delta.mic_delta_status})`
                  : ""}
              </div>
              <div className="muted">
                Forced edges: +{response.analysis_delta.forced_edges_added.length} / -
                {response.analysis_delta.forced_edges_removed.length}
                {response.analysis_delta.forced_delta_status
                  ? ` (${response.analysis_delta.forced_delta_status})`
                  : ""}
              </div>
              <div className="muted">
                Countermodel edges changed: {response.analysis_delta.countermodel_edges_changed.length}
              </div>
            </div>
          ) : null}

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

          {explanation.cause_chain?.length ? (
            <div style={{ marginTop: 8 }}>
              <div className="muted">Causal chain</div>
              <table className="table" style={{ marginTop: 6 }}>
                <thead>
                  <tr>
                    <th>sev</th>
                    <th>atom</th>
                    <th>kind</th>
                    <th>object_id</th>
                    <th>json_path</th>
                    <th>message</th>
                    <th></th>
                  </tr>
                </thead>
                <tbody>
                  {explanation.cause_chain.map((item) => (
                    <tr
                      key={`${item.severity}-${item.atom_name}-${item.object_id ?? ""}-${item.json_path ?? ""}`}
                    >
                      <td className="mono">{item.severity}</td>
                      <td className="mono">{item.atom_name}</td>
                      <td className="mono">{item.evidence_kind}</td>
                      <td className="mono">{item.object_id ?? ""}</td>
                      <td className="mono">{item.json_path ?? ""}</td>
                      <td>{item.message}</td>
                      <td>
                        <button
                          onClick={() => {
                            const span = item.right_span ?? item.left_span;
                            if (!span || !onSelectSpan) return;
                            onSelectSpan(
                              span,
                              `flip:${item.atom_name} ${item.json_path ?? ""}`.trim(),
                            );
                          }}
                          disabled={(!item.right_span && !item.left_span) || !onSelectSpan}
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

          {explanation.repair_hints?.length ? (
            <div style={{ marginTop: 8 }}>
              <div className="muted">Repair hints</div>
              <ul style={{ marginTop: 6 }}>
                {explanation.repair_hints.map((hint, idx) => (
                  <li key={`${hint.object_kind}-${hint.object_id ?? ""}-${hint.json_path ?? ""}-${idx}`}>
                    <span className="mono">{hint.object_kind}</span>
                    {hint.object_id ? ` ${hint.object_id}: ` : ": "}
                    {hint.hint}
                  </li>
                ))}
              </ul>
            </div>
          ) : null}
        </>
      ) : null}
    </div>
  );
}
