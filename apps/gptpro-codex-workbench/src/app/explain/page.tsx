"use client";

import Link from "next/link";
import { useMemo, useState } from "react";

import { apiBase } from "../lib/api-base";
import type { AdeuIR } from "../../gen/adeu_ir";

type KernelMode = "STRICT" | "LAX";
type SolverTrustLevel = "kernel_only" | "solver_backed" | "proof_checked";

type ArtifactGetResponse = {
  artifact_id: string;
  ir: AdeuIR;
  solver_trust: SolverTrustLevel;
  proof_trust?: string | null;
};

type ExplainKind = "semantic_diff" | "concepts_diff" | "puzzles_diff" | "flip_explain";

type ExplainDiffPacketResponse = {
  schema: "explain_diff@1";
  explain_kind: ExplainKind;
  builder_version: string;
  explain_hash: string;
  input_artifact_refs: string[];
  diff_refs: string[];
  witness_refs: string[];
  sections: Record<string, unknown>;
  semantics_diagnostics_ref?: string | null;
  validator_evidence_packet_refs?: string[] | null;
  hash_excluded_fields?: string[];
};

type SemanticsWitnessRef = {
  assertion_name: string;
  object_id?: string | null;
  json_path?: string | null;
};

type SemanticsDiagnosticsRecord = {
  validator_run_id: string;
  status: string;
  validator_evidence_packet_ref: string;
  witness_refs: SemanticsWitnessRef[];
};

type SemanticsDiagnosticsResponse = {
  schema: "semantics_diagnostics@1";
  artifact_ref: string;
  semantics_diagnostics_hash: string;
  records: SemanticsDiagnosticsRecord[];
};

type PolicyActiveResponse = {
  profile_id: string;
  profile_version: string;
  policy_hash: string;
  source: "activation_log" | "profile_default";
  activation_seq?: number | null;
  activation_ts?: string | null;
};

type WitnessDrilldownRow = {
  atom_name: string;
  object_id: string;
  json_path: string;
  evidence_kind: string;
  severity: string;
};

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function asRecord(value: unknown): Record<string, unknown> | null {
  return isRecord(value) ? value : null;
}

function asArray(value: unknown): unknown[] {
  return Array.isArray(value) ? value : [];
}

function asString(value: unknown): string {
  return typeof value === "string" ? value : "";
}

function asStringList(value: unknown): string[] {
  if (!Array.isArray(value)) return [];
  return value
    .filter((item): item is string => typeof item === "string")
    .slice()
    .sort((a, b) => a.localeCompare(b));
}

function formatScalar(value: unknown): string {
  if (value === null || value === undefined) return "";
  if (typeof value === "string" || typeof value === "number" || typeof value === "boolean") {
    return String(value);
  }
  try {
    return JSON.stringify(value);
  } catch {
    return String(value);
  }
}

async function parseErrorMessage(response: Response): Promise<string> {
  const text = await response.text();
  if (!text) return `HTTP ${response.status}`;
  try {
    const parsed = JSON.parse(text) as {
      detail?: { code?: string; message?: string } | string;
      message?: string;
      error?: string;
    };
    if (typeof parsed.detail === "string") return parsed.detail;
    if (parsed.detail?.code && parsed.detail.message) {
      return `${parsed.detail.code}: ${parsed.detail.message}`;
    }
    if (typeof parsed.message === "string") return parsed.message;
    if (typeof parsed.error === "string") return parsed.error;
  } catch {
    // fall through
  }
  return text;
}

function settledReasonMessage(reason: unknown): string {
  return reason instanceof Error ? reason.message : String(reason);
}

function applySettledResult<T>(
  result: PromiseSettledResult<T>,
  setValue: (value: T | null) => void,
  setError: (value: string | null) => void,
): void {
  if (result.status === "fulfilled") {
    setValue(result.value);
    setError(null);
    return;
  }
  setValue(null);
  setError(settledReasonMessage(result.reason));
}

async function fetchArtifact(artifactId: string): Promise<ArtifactGetResponse> {
  const response = await fetch(`${apiBase()}/artifacts/${encodeURIComponent(artifactId)}`, {
    method: "GET",
  });
  if (!response.ok) {
    throw new Error(await parseErrorMessage(response));
  }
  return (await response.json()) as ArtifactGetResponse;
}

async function fetchExplainDiffPacket(
  leftArtifact: ArtifactGetResponse,
  rightArtifact: ArtifactGetResponse,
  mode: KernelMode,
): Promise<ExplainDiffPacketResponse> {
  const response = await fetch(`${apiBase()}/diff?format=explain_diff@1`, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      left_ir: leftArtifact.ir,
      right_ir: rightArtifact.ir,
      left_artifact_id: leftArtifact.artifact_id,
      right_artifact_id: rightArtifact.artifact_id,
      mode,
    }),
  });
  if (!response.ok) {
    throw new Error(await parseErrorMessage(response));
  }
  return (await response.json()) as ExplainDiffPacketResponse;
}

async function fetchSemanticsDiagnostics(
  artifactId: string,
): Promise<SemanticsDiagnosticsResponse> {
  const response = await fetch(
    `${apiBase()}/artifacts/${encodeURIComponent(artifactId)}/semantics-diagnostics`,
    {
      method: "GET",
    },
  );
  if (!response.ok) {
    throw new Error(await parseErrorMessage(response));
  }
  return (await response.json()) as SemanticsDiagnosticsResponse;
}

async function fetchPolicyActive(profileId: string): Promise<PolicyActiveResponse> {
  const response = await fetch(
    `${apiBase()}/urm/policy/active?profile_id=${encodeURIComponent(profileId)}`,
    {
      method: "GET",
    },
  );
  if (!response.ok) {
    throw new Error(await parseErrorMessage(response));
  }
  return (await response.json()) as PolicyActiveResponse;
}

function normalizeWitnessRows(packet: ExplainDiffPacketResponse | null): WitnessDrilldownRow[] {
  if (!packet) return [];
  const diffReport = asRecord(packet.sections.diff_report);
  const causalSlice = asRecord(diffReport?.causal_slice);
  const explanationItems = asArray(causalSlice?.explanation_items);
  const rows = explanationItems
    .map((value) => {
      const item = asRecord(value);
      return {
        atom_name: asString(item?.atom_name),
        object_id: asString(item?.object_id),
        json_path: asString(item?.json_path),
        evidence_kind: asString(item?.evidence_kind),
        severity: asString(item?.severity),
      };
    })
    .sort((a, b) => {
      if (a.atom_name !== b.atom_name) return a.atom_name.localeCompare(b.atom_name);
      if (a.object_id !== b.object_id) return a.object_id.localeCompare(b.object_id);
      return a.json_path.localeCompare(b.json_path);
    });
  return rows;
}

function normalizeSummaryRows(packet: ExplainDiffPacketResponse | null): Array<[string, string]> {
  if (!packet) return [];
  const diffReport = asRecord(packet.sections.diff_report);
  const summary = asRecord(diffReport?.summary);
  if (!summary) return [];
  return Object.entries(summary)
    .map(([key, value]) => [key, formatScalar(value)] as [string, string])
    .sort((a, b) => a[0].localeCompare(b[0]));
}

function sortedSemanticsRecords(
  response: SemanticsDiagnosticsResponse | null,
): SemanticsDiagnosticsRecord[] {
  if (!response) return [];
  return response.records
    .slice()
    .sort((a, b) => a.validator_run_id.localeCompare(b.validator_run_id));
}

function sortedRefs(values: string[] | null | undefined): string[] {
  return (values ?? []).slice().sort((a, b) => a.localeCompare(b));
}

export default function ExplainPage() {
  const [leftArtifactId, setLeftArtifactId] = useState<string>("");
  const [rightArtifactId, setRightArtifactId] = useState<string>("");
  const [mode, setMode] = useState<KernelMode>("LAX");
  const [policyProfileId, setPolicyProfileId] = useState<string>("default");

  const [leftArtifact, setLeftArtifact] = useState<ArtifactGetResponse | null>(null);
  const [rightArtifact, setRightArtifact] = useState<ArtifactGetResponse | null>(null);
  const [packet, setPacket] = useState<ExplainDiffPacketResponse | null>(null);

  const [leftSemantics, setLeftSemantics] = useState<SemanticsDiagnosticsResponse | null>(null);
  const [rightSemantics, setRightSemantics] = useState<SemanticsDiagnosticsResponse | null>(null);
  const [leftSemanticsError, setLeftSemanticsError] = useState<string | null>(null);
  const [rightSemanticsError, setRightSemanticsError] = useState<string | null>(null);

  const [policyActive, setPolicyActive] = useState<PolicyActiveResponse | null>(null);
  const [policyError, setPolicyError] = useState<string | null>(null);

  const [loading, setLoading] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);

  const inputRefs = useMemo(() => sortedRefs(packet?.input_artifact_refs), [packet]);
  const diffRefs = useMemo(() => sortedRefs(packet?.diff_refs), [packet]);
  const witnessRefs = useMemo(() => sortedRefs(packet?.witness_refs), [packet]);
  const validatorRefs = useMemo(
    () => sortedRefs(packet?.validator_evidence_packet_refs ?? []),
    [packet],
  );
  const hashExcludedFields = useMemo(() => sortedRefs(packet?.hash_excluded_fields), [packet]);

  const summaryRows = useMemo(() => normalizeSummaryRows(packet), [packet]);
  const witnessRows = useMemo(() => normalizeWitnessRows(packet), [packet]);

  const diffReport = useMemo(() => asRecord(packet?.sections.diff_report), [packet]);
  const diffReportLeftId = asString(diffReport?.left_id);
  const diffReportRightId = asString(diffReport?.right_id);
  const solver = asRecord(diffReport?.solver);
  const structural = asRecord(diffReport?.structural);
  const causalSlice = asRecord(diffReport?.causal_slice);

  const touchedAtoms = asStringList(causalSlice?.touched_atoms);
  const touchedObjectIds = asStringList(causalSlice?.touched_object_ids);
  const touchedJsonPaths = asStringList(causalSlice?.touched_json_paths);
  const changedPaths = asStringList(structural?.changed_paths);

  async function buildExplainView(): Promise<void> {
    const leftId = leftArtifactId.trim();
    const rightId = rightArtifactId.trim();
    const profileId = policyProfileId.trim() || "default";

    setError(null);
    setPolicyError(null);
    setLeftSemanticsError(null);
    setRightSemanticsError(null);

    if (!leftId || !rightId) {
      setError("Provide both left and right artifact IDs.");
      return;
    }

    setLeftArtifact(null);
    setRightArtifact(null);
    setPacket(null);
    setLeftSemantics(null);
    setRightSemantics(null);
    setPolicyActive(null);

    setLoading(true);
    try {
      const [left, right] = await Promise.all([fetchArtifact(leftId), fetchArtifact(rightId)]);
      setLeftArtifact(left);
      setRightArtifact(right);

      const explainPacket = await fetchExplainDiffPacket(left, right, mode);
      setPacket(explainPacket);

      const [leftDiag, rightDiag, policy] = await Promise.allSettled([
        fetchSemanticsDiagnostics(leftId),
        fetchSemanticsDiagnostics(rightId),
        fetchPolicyActive(profileId),
      ]);

      applySettledResult(leftDiag, setLeftSemantics, setLeftSemanticsError);
      applySettledResult(rightDiag, setRightSemantics, setRightSemanticsError);
      applySettledResult(policy, setPolicyActive, setPolicyError);
    } catch (exc) {
      setPacket(null);
      setLeftSemantics(null);
      setRightSemantics(null);
      setPolicyActive(null);
      setError(exc instanceof Error ? exc.message : String(exc));
    } finally {
      setLoading(false);
    }
  }

  return (
    <div style={{ padding: 12 }}>
      <div className="row" style={{ justifyContent: "space-between" }}>
        <h2 style={{ margin: 0 }}>Explain Evidence Studio</h2>
        <div className="row">
          <Link href="/" className="muted">
            ADEU Studio
          </Link>
          <Link href="/artifacts" className="muted">
            Artifacts
          </Link>
          <Link href="/concepts" className="muted">
            Concepts
          </Link>
          <Link href="/papers" className="muted">
            Papers
          </Link>
          <Link href="/puzzles" className="muted">
            Puzzles
          </Link>
          <Link href="/copilot" className="muted">
            Copilot
          </Link>
        </div>
      </div>

      <div className="panel" style={{ marginTop: 12 }}>
        <div className="row">
          <label className="muted">
            left artifact_id{" "}
            <input
              value={leftArtifactId}
              onChange={(event) => setLeftArtifactId(event.target.value)}
              placeholder="artifact id"
            />
          </label>

          <label className="muted">
            right artifact_id{" "}
            <input
              value={rightArtifactId}
              onChange={(event) => setRightArtifactId(event.target.value)}
              placeholder="artifact id"
            />
          </label>

          <label className="muted">
            mode{" "}
            <select value={mode} onChange={(event) => setMode(event.target.value as KernelMode)}>
              <option value="LAX">LAX</option>
              <option value="STRICT">STRICT</option>
            </select>
          </label>

          <label className="muted">
            policy profile{" "}
            <input
              value={policyProfileId}
              onChange={(event) => setPolicyProfileId(event.target.value)}
              placeholder="default"
            />
          </label>

          <button onClick={() => void buildExplainView()} disabled={loading}>
            {loading ? "Building..." : "Build explain view"}
          </button>
        </div>

        <div className="muted" style={{ marginTop: 8 }}>
          Read-only flow: fetch persisted artifacts, derive explain packet via <span className="mono">/diff?format=explain_diff@1</span>,
          then resolve policy/semantics linkage refs.
        </div>

        {error ? <div className="muted" style={{ marginTop: 8 }}>Error: {error}</div> : null}
      </div>

      {packet ? (
        <>
          <div className="panel" style={{ marginTop: 12 }}>
            <h2>Semantic Diff</h2>
            <div className="row">
              <span className="muted">schema</span>
              <span className="mono">{packet.schema}</span>
              <span className="muted">kind</span>
              <span className="mono">{packet.explain_kind}</span>
              <span className="muted">builder</span>
              <span className="mono">{packet.builder_version}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">explain_hash</span>
              <span className="mono">{packet.explain_hash}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">left_id</span>
              <span className="mono">{diffReportLeftId || "n/a"}</span>
              <span className="muted">right_id</span>
              <span className="mono">{diffReportRightId || "n/a"}</span>
              <span className="muted">status_flip</span>
              <span className="mono">{asString(solver?.status_flip) || "n/a"}</span>
            </div>

            {summaryRows.length ? (
              <div style={{ marginTop: 12, overflow: "auto" }}>
                <table className="table">
                  <thead>
                    <tr>
                      <th>summary key</th>
                      <th>value</th>
                    </tr>
                  </thead>
                  <tbody>
                    {summaryRows.map(([key, value]) => (
                      <tr key={key}>
                        <td className="mono">{key}</td>
                        <td className="mono">{value}</td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            ) : null}

            <div className="row" style={{ marginTop: 10 }}>
              <span className="muted">changed paths</span>
              <span className="mono">{changedPaths.join(", ") || "none"}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">touched atoms</span>
              <span className="mono">{touchedAtoms.join(", ") || "none"}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">touched object ids</span>
              <span className="mono">{touchedObjectIds.join(", ") || "none"}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">touched json paths</span>
              <span className="mono">{touchedJsonPaths.join(", ") || "none"}</span>
            </div>
          </div>

          <div className="panel" style={{ marginTop: 12 }}>
            <h2>Conflict Witness Drilldown</h2>
            {witnessRows.length === 0 ? (
              <div className="muted">No witness rows in causal slice.</div>
            ) : (
              <div style={{ overflow: "auto" }}>
                <table className="table">
                  <thead>
                    <tr>
                      <th>atom</th>
                      <th>object_id</th>
                      <th>json_path</th>
                      <th>evidence_kind</th>
                      <th>severity</th>
                    </tr>
                  </thead>
                  <tbody>
                    {witnessRows.map((row, idx) => (
                      <tr key={`${row.atom_name}:${row.object_id}:${row.json_path}:${idx}`}>
                        <td className="mono">{row.atom_name || ""}</td>
                        <td className="mono">{row.object_id || ""}</td>
                        <td className="mono">{row.json_path || ""}</td>
                        <td className="mono">{row.evidence_kind || ""}</td>
                        <td className="mono">{row.severity || ""}</td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            )}
          </div>

          <div className="panel" style={{ marginTop: 12 }}>
            <h2>Policy/Semantics Evidence Linkage</h2>

            <div className="row">
              <span className="muted">input_artifact_refs</span>
              <span className="mono">{inputRefs.join(", ") || "none"}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">diff_refs</span>
              <span className="mono">{diffRefs.join(", ") || "none"}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">witness_refs</span>
              <span className="mono">{witnessRefs.join(", ") || "none"}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">validator_evidence_packet_refs</span>
              <span className="mono">{validatorRefs.join(", ") || "none"}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">semantics_diagnostics_ref</span>
              <span className="mono">{packet.semantics_diagnostics_ref ?? "none"}</span>
            </div>
            <div className="row" style={{ marginTop: 6 }}>
              <span className="muted">hash_excluded_fields</span>
              <span className="mono">{hashExcludedFields.join(", ") || "none"}</span>
            </div>

            <div style={{ marginTop: 10 }}>
              <div className="row">
                <span className="muted">left artifact</span>
                <Link href={`/artifacts/${leftArtifact?.artifact_id ?? ""}`} className="mono">
                  {leftArtifact?.artifact_id ?? ""}
                </Link>
                <span className="muted">solver_trust={leftArtifact?.solver_trust ?? "n/a"}</span>
                <span className="muted">proof_trust={leftArtifact?.proof_trust ?? "n/a"}</span>
              </div>
              <div className="row" style={{ marginTop: 4 }}>
                <span className="muted">right artifact</span>
                <Link href={`/artifacts/${rightArtifact?.artifact_id ?? ""}`} className="mono">
                  {rightArtifact?.artifact_id ?? ""}
                </Link>
                <span className="muted">solver_trust={rightArtifact?.solver_trust ?? "n/a"}</span>
                <span className="muted">proof_trust={rightArtifact?.proof_trust ?? "n/a"}</span>
              </div>
            </div>

            <div style={{ marginTop: 12 }}>
              <div className="muted">Policy active snapshot</div>
              {policyError ? <div className="muted">Policy lookup error: {policyError}</div> : null}
              {policyActive ? (
                <div className="row" style={{ marginTop: 4 }}>
                  <span className="mono">profile={policyActive.profile_id}</span>
                  <span className="mono">version={policyActive.profile_version}</span>
                  <span className="mono">source={policyActive.source}</span>
                  <span className="mono">policy_hash={policyActive.policy_hash}</span>
                </div>
              ) : null}
            </div>

            <div style={{ marginTop: 12, overflow: "auto" }}>
              <table className="table">
                <thead>
                  <tr>
                    <th>artifact side</th>
                    <th>semantics hash</th>
                    <th>record count</th>
                    <th>status</th>
                  </tr>
                </thead>
                <tbody>
                  <tr>
                    <td className="mono">left</td>
                    <td className="mono">{leftSemantics?.semantics_diagnostics_hash ?? ""}</td>
                    <td className="mono">{leftSemantics?.records.length ?? 0}</td>
                    <td className="mono">{leftSemanticsError ?? "ok"}</td>
                  </tr>
                  <tr>
                    <td className="mono">right</td>
                    <td className="mono">{rightSemantics?.semantics_diagnostics_hash ?? ""}</td>
                    <td className="mono">{rightSemantics?.records.length ?? 0}</td>
                    <td className="mono">{rightSemanticsError ?? "ok"}</td>
                  </tr>
                </tbody>
              </table>
            </div>

            <div style={{ marginTop: 12, overflow: "auto" }}>
              <table className="table">
                <thead>
                  <tr>
                    <th>side</th>
                    <th>validator_run_id</th>
                    <th>status</th>
                    <th>validator packet ref</th>
                    <th>witness refs</th>
                  </tr>
                </thead>
                <tbody>
                  {sortedSemanticsRecords(leftSemantics).map((record) => (
                    <tr key={`left:${record.validator_run_id}`}>
                      <td className="mono">left</td>
                      <td className="mono">{record.validator_run_id}</td>
                      <td className="mono">{record.status}</td>
                      <td className="mono">{record.validator_evidence_packet_ref}</td>
                      <td className="mono">{record.witness_refs.length}</td>
                    </tr>
                  ))}
                  {sortedSemanticsRecords(rightSemantics).map((record) => (
                    <tr key={`right:${record.validator_run_id}`}>
                      <td className="mono">right</td>
                      <td className="mono">{record.validator_run_id}</td>
                      <td className="mono">{record.status}</td>
                      <td className="mono">{record.validator_evidence_packet_ref}</td>
                      <td className="mono">{record.witness_refs.length}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        </>
      ) : null}
    </div>
  );
}
