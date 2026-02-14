"use client";

import Link from "next/link";
import { useCallback, useEffect, useMemo, useState } from "react";

import { apiBase } from "../lib/api-base";
import type { CheckReport } from "../../gen/check_report";

type KernelMode = "STRICT" | "LAX";

type DocumentSummary = {
  doc_id: string;
  domain: string;
  created_at: string;
};

type DocumentRecord = {
  doc_id: string;
  domain: string;
  source_text: string;
  created_at: string;
  metadata: Record<string, unknown>;
};

type DocumentListResponse = {
  items: DocumentSummary[];
};

type ProposeCandidate = {
  ir: unknown;
  check_report: CheckReport;
  rank: number;
};

type ProposeResponse = {
  candidates: ProposeCandidate[];
};

type ConceptAnalyzeResponse = {
  ir: unknown;
  check_report: CheckReport;
  analysis: Record<string, unknown>;
};

type ConceptArtifactCreateResponse = {
  artifact_id: string;
  created_at: string;
  check_report: CheckReport;
  analysis?: Record<string, unknown> | null;
};

type ConceptAlignmentArtifactRef = {
  artifact_id: string;
  doc_id?: string | null;
  concept_id: string;
};

type ConceptAlignmentSuggestion = {
  suggestion_id: string;
  suggestion_fingerprint: string;
  kind: "merge_candidate" | "conflict_candidate";
  vocabulary_key: string;
  reason: string;
  artifact_ids: string[];
  doc_ids: string[];
};

type ConceptAlignResponse = {
  artifacts: ConceptAlignmentArtifactRef[];
  suggestion_count: number;
  suggestions: ConceptAlignmentSuggestion[];
  alignment_stats: {
    merge_candidate_count: number;
    conflict_candidate_count: number;
  };
  mapping_trust: string | null;
  solver_trust: "kernel_only" | "solver_backed" | "proof_checked";
  proof_trust?: string | null;
};

const PAPER_DOMAIN = "paper.abstract";
const DOCUMENT_LIST_LIMIT = 100;
const ALIGN_MAX_SUGGESTIONS_DEFAULT = 100;
const ALIGN_MAX_SUGGESTIONS_MIN = 1;
const ALIGN_MAX_SUGGESTIONS_MAX = 500;

async function responseErrorText(res: Response): Promise<string> {
  const body = await res.text();
  if (!body) {
    return `${res.status} ${res.statusText}`;
  }
  try {
    const parsed = JSON.parse(body) as unknown;
    return typeof parsed === "string" ? parsed : JSON.stringify(parsed);
  } catch {
    return body;
  }
}

export default function PapersPage() {
  const [provider, setProvider] = useState<"mock" | "openai">("mock");
  const [mode, setMode] = useState<KernelMode>("LAX");
  const [docIdInput, setDocIdInput] = useState<string>("");
  const [sourceTextInput, setSourceTextInput] = useState<string>("");
  const [metadataInput, setMetadataInput] = useState<string>('{"title": "", "authors": []}');

  const [documents, setDocuments] = useState<DocumentSummary[]>([]);
  const [selectedDocId, setSelectedDocId] = useState<string>("");
  const [selectedDoc, setSelectedDoc] = useState<DocumentRecord | null>(null);
  const [alignDocIds, setAlignDocIds] = useState<string[]>([]);
  const [alignmentMaxSuggestions, setAlignmentMaxSuggestions] = useState<number>(
    ALIGN_MAX_SUGGESTIONS_DEFAULT,
  );

  const [candidates, setCandidates] = useState<ProposeCandidate[]>([]);
  const [selectedIdx, setSelectedIdx] = useState<number>(0);
  const [analysisByIdx, setAnalysisByIdx] = useState<Record<number, Record<string, unknown>>>({});
  const [alignmentResult, setAlignmentResult] = useState<ConceptAlignResponse | null>(null);
  const [acceptedArtifactId, setAcceptedArtifactId] = useState<string | null>(null);

  const [isLoadingDocs, setIsLoadingDocs] = useState<boolean>(false);
  const [isLoadingDocDetail, setIsLoadingDocDetail] = useState<boolean>(false);
  const [isCreatingDoc, setIsCreatingDoc] = useState<boolean>(false);
  const [isProposing, setIsProposing] = useState<boolean>(false);
  const [isAnalyzing, setIsAnalyzing] = useState<boolean>(false);
  const [isAccepting, setIsAccepting] = useState<boolean>(false);
  const [isAligning, setIsAligning] = useState<boolean>(false);

  const [error, setError] = useState<string | null>(null);
  const [statusMessage, setStatusMessage] = useState<string | null>(null);

  const selectedCandidate = useMemo(
    () => candidates[selectedIdx] ?? null,
    [candidates, selectedIdx],
  );

  const selectedAnalysis = useMemo(
    () => (selectedCandidate ? analysisByIdx[selectedIdx] ?? null : null),
    [analysisByIdx, selectedCandidate, selectedIdx],
  );

  const sortedAlignDocIds = useMemo(() => [...alignDocIds].sort(), [alignDocIds]);

  const clearActionMessages = useCallback(() => {
    setError(null);
    setStatusMessage(null);
  }, []);

  const clearDerivedOutputs = useCallback(() => {
    setAlignmentResult(null);
    setAcceptedArtifactId(null);
  }, []);

  const replaceCandidates = useCallback((nextCandidates: ProposeCandidate[]) => {
    setCandidates(nextCandidates);
    setSelectedIdx(0);
    setAnalysisByIdx({});
  }, []);

  const loadDocumentDetail = useCallback(async (docId: string) => {
    setIsLoadingDocDetail(true);
    try {
      const res = await fetch(`${apiBase()}/documents/${encodeURIComponent(docId)}`, {
        method: "GET",
      });
      if (!res.ok) {
        throw new Error(await responseErrorText(res));
      }
      const data = (await res.json()) as DocumentRecord;
      setSelectedDoc(data);
    } finally {
      setIsLoadingDocDetail(false);
    }
  }, []);

  const loadDocuments = useCallback(async () => {
    setIsLoadingDocs(true);
    try {
      const params = new URLSearchParams();
      params.set("domain", PAPER_DOMAIN);
      params.set("limit", String(DOCUMENT_LIST_LIMIT));
      params.set("offset", "0");
      const res = await fetch(`${apiBase()}/documents?${params.toString()}`, { method: "GET" });
      if (!res.ok) {
        throw new Error(await responseErrorText(res));
      }
      const data = (await res.json()) as DocumentListResponse;
      const items = data.items ?? [];
      const nextDocIdSet = new Set(items.map((item) => item.doc_id));
      setDocuments(items);
      setAlignDocIds((prev) => prev.filter((docId) => nextDocIdSet.has(docId)).sort());
      setSelectedDocId((prev) => {
        if (prev && nextDocIdSet.has(prev)) {
          return prev;
        }
        return items[0]?.doc_id ?? "";
      });
    } catch (e) {
      setError(String(e));
    } finally {
      setIsLoadingDocs(false);
    }
  }, []);

  useEffect(() => {
    void loadDocuments();
  }, [loadDocuments]);

  useEffect(() => {
    if (!selectedDocId) {
      setSelectedDoc(null);
      return;
    }
    void loadDocumentDetail(selectedDocId).catch((e) => {
      setError(String(e));
      setSelectedDoc(null);
    });
  }, [loadDocumentDetail, selectedDocId]);

  useEffect(() => {
    if (!selectedDocId) return;
    setAlignDocIds((prev) => (prev.length === 0 ? [selectedDocId] : prev));
  }, [selectedDocId]);

  function toggleAlignDoc(docId: string) {
    setAlignDocIds((prev) => {
      if (prev.includes(docId)) {
        return prev.filter((value) => value !== docId).sort();
      }
      return [...prev, docId].sort();
    });
  }

  async function createDocument() {
    const docId = docIdInput.trim();
    const sourceText = sourceTextInput.trim();
    if (!docId || !sourceText) {
      setError("doc_id and source_text are required.");
      return;
    }

    let metadata: Record<string, unknown> | undefined;
    const metadataRaw = metadataInput.trim();
    if (metadataRaw) {
      try {
        const parsed = JSON.parse(metadataRaw) as unknown;
        if (parsed === null || Array.isArray(parsed) || typeof parsed !== "object") {
          setError("metadata must be a JSON object.");
          return;
        }
        metadata = parsed as Record<string, unknown>;
      } catch (e) {
        setError(`metadata parse error: ${String(e)}`);
        return;
      }
    }

    clearActionMessages();
    setIsCreatingDoc(true);
    try {
      const res = await fetch(`${apiBase()}/documents`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          doc_id: docId,
          domain: PAPER_DOMAIN,
          source_text: sourceText,
          metadata,
        }),
      });
      if (!res.ok) {
        setError(await responseErrorText(res));
        return;
      }
      const data = (await res.json()) as DocumentRecord;
      setSelectedDocId(data.doc_id);
      setStatusMessage(`Created document ${data.doc_id}`);
      clearDerivedOutputs();
      replaceCandidates([]);
      await loadDocuments();
    } catch (e) {
      setError(String(e));
    } finally {
      setIsCreatingDoc(false);
    }
  }

  async function proposeConcepts() {
    if (!selectedDocId) return;
    clearActionMessages();
    clearDerivedOutputs();
    setIsProposing(true);
    try {
      const res = await fetch(`${apiBase()}/concepts/propose`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          doc_id: selectedDocId,
          provider,
          mode,
        }),
      });
      if (!res.ok) {
        setError(await responseErrorText(res));
        return;
      }
      const data = (await res.json()) as ProposeResponse;
      replaceCandidates(data.candidates ?? []);
      setStatusMessage(
        `Generated ${data.candidates?.length ?? 0} concept variant(s) for ${selectedDocId}`,
      );
    } catch (e) {
      setError(String(e));
    } finally {
      setIsProposing(false);
    }
  }

  async function analyzeSelected() {
    if (!selectedDocId || !selectedCandidate) return;
    clearActionMessages();
    setIsAnalyzing(true);
    try {
      const res = await fetch(`${apiBase()}/concepts/analyze`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          ir: selectedCandidate.ir,
          doc_id: selectedDocId,
          mode,
          include_analysis_details: true,
          include_forced_details: true,
        }),
      });
      if (!res.ok) {
        setError(await responseErrorText(res));
        return;
      }
      const data = (await res.json()) as ConceptAnalyzeResponse;
      setCandidates((prev) =>
        prev.map((candidate, idx) =>
          idx === selectedIdx
            ? { ...candidate, ir: data.ir, check_report: data.check_report }
            : candidate,
        ),
      );
      setAnalysisByIdx((prev) => ({ ...prev, [selectedIdx]: data.analysis }));
      setStatusMessage(`Analyzed selected variant in ${mode} mode.`);
    } catch (e) {
      setError(String(e));
    } finally {
      setIsAnalyzing(false);
    }
  }

  async function acceptSelected() {
    if (!selectedDocId || !selectedCandidate) return;
    clearActionMessages();
    setIsAccepting(true);
    try {
      const res = await fetch(`${apiBase()}/concepts/artifacts`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          doc_id: selectedDocId,
          ir: selectedCandidate.ir,
          mode: "STRICT",
        }),
      });
      if (!res.ok) {
        setError(await responseErrorText(res));
        return;
      }
      const data = (await res.json()) as ConceptArtifactCreateResponse;
      setAcceptedArtifactId(data.artifact_id);
      setCandidates((prev) =>
        prev.map((candidate, idx) =>
          idx === selectedIdx
            ? { ...candidate, check_report: data.check_report }
            : candidate,
        ),
      );
      if (data.analysis) {
        setAnalysisByIdx((prev) => ({ ...prev, [selectedIdx]: data.analysis ?? {} }));
      }
      setStatusMessage(`Accepted concept artifact ${data.artifact_id}`);
    } catch (e) {
      setError(String(e));
    } finally {
      setIsAccepting(false);
    }
  }

  async function alignSelectedDocs() {
    const scope = sortedAlignDocIds;
    if (scope.length === 0) {
      setError("Select at least one document for alignment.");
      return;
    }
    clearActionMessages();
    setIsAligning(true);
    try {
      const res = await fetch(`${apiBase()}/concepts/align`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          doc_ids: scope,
          max_suggestions: alignmentMaxSuggestions,
        }),
      });
      if (!res.ok) {
        setError(await responseErrorText(res));
        return;
      }
      const data = (await res.json()) as ConceptAlignResponse;
      setAlignmentResult(data);
      setStatusMessage(
        `Alignment returned ${data.suggestion_count} suggestion(s) across ${scope.length} doc(s).`,
      );
    } catch (e) {
      setError(String(e));
    } finally {
      setIsAligning(false);
    }
  }

  return (
    <div className="app">
      <div className="panel">
        <h2>Paper Abstract Studio</h2>
        <div className="row" style={{ marginBottom: 8 }}>
          <Link href="/" className="muted" style={{ marginLeft: "auto" }}>
            ADEU Studio
          </Link>
          <Link href="/explain" className="muted">
            Explain
          </Link>
          <Link href="/concepts" className="muted">
            Concepts
          </Link>
          <Link href="/puzzles" className="muted">
            Puzzles
          </Link>
          <Link href="/artifacts" className="muted">
            Artifacts
          </Link>
          <Link href="/copilot" className="muted">
            Copilot
          </Link>
        </div>
        <div className="row">
          <label className="muted">
            domain <span className="mono">{PAPER_DOMAIN}</span>
          </label>
          <button onClick={() => void loadDocuments()} disabled={isLoadingDocs}>
            {isLoadingDocs ? "Refreshing..." : "Refresh list"}
          </button>
        </div>
        <div className="row" style={{ marginTop: 8 }}>
          <label className="muted">
            doc_id{" "}
            <input
              value={docIdInput}
              onChange={(event) => setDocIdInput(event.target.value)}
              placeholder="doc:paper:example:v1"
            />
          </label>
          <button onClick={createDocument} disabled={isCreatingDoc || !docIdInput.trim() || !sourceTextInput.trim()}>
            {isCreatingDoc ? "Creating..." : "Create document"}
          </button>
        </div>
        <div className="muted" style={{ marginTop: 8 }}>
          Abstract text
        </div>
        <textarea
          value={sourceTextInput}
          onChange={(event) => setSourceTextInput(event.target.value)}
          placeholder="Paste a paper abstract..."
        />
        <div className="muted" style={{ marginTop: 8 }}>
          metadata (JSON object)
        </div>
        <textarea
          value={metadataInput}
          onChange={(event) => setMetadataInput(event.target.value)}
          placeholder='{"title": "..." }'
          style={{ minHeight: 120 }}
        />

        {error ? <div className="muted" style={{ marginTop: 8 }}>Error: {error}</div> : null}
        {statusMessage ? <div className="muted" style={{ marginTop: 8 }}>{statusMessage}</div> : null}
      </div>

      <div className="panel">
        <h2>Documents + Concepts</h2>
        <div className="muted">
          Select a document, then propose/analyze/accept concept variants using <span className="mono">doc_id</span>.
        </div>
        <div style={{ marginTop: 8, overflow: "auto", maxHeight: 240 }}>
          <table className="table">
            <thead>
              <tr>
                <th>selected</th>
                <th>align</th>
                <th>doc_id</th>
                <th>created_at</th>
              </tr>
            </thead>
            <tbody>
              {documents.map((doc) => (
                <tr key={doc.doc_id}>
                  <td>
                    <input
                      type="radio"
                      name="selected-paper-doc"
                      checked={doc.doc_id === selectedDocId}
                      onChange={() => setSelectedDocId(doc.doc_id)}
                    />
                  </td>
                  <td>
                    <input
                      type="checkbox"
                      checked={alignDocIds.includes(doc.doc_id)}
                      onChange={() => toggleAlignDoc(doc.doc_id)}
                    />
                  </td>
                  <td className="mono">{doc.doc_id}</td>
                  <td className="mono">{doc.created_at}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        {documents.length === 0 ? (
          <div className="muted" style={{ marginTop: 8 }}>
            No paper.abstract documents yet.
          </div>
        ) : null}
        {isLoadingDocDetail ? <div className="muted">Loading selected document…</div> : null}

        <div className="muted" style={{ marginTop: 8 }}>
          Selected doc: <span className="mono">{selectedDocId || "(none)"}</span>
        </div>
        <div className="clause-preview" style={{ marginTop: 8 }}>
          {selectedDoc?.source_text ?? ""}
        </div>
        {selectedDoc ? (
          <pre style={{ marginTop: 8 }}>{JSON.stringify(selectedDoc.metadata ?? {}, null, 2)}</pre>
        ) : null}

        <div className="row" style={{ marginTop: 8 }}>
          <span className="muted">Provider</span>
          <button onClick={() => setProvider("mock")} disabled={provider === "mock"}>
            mock
          </button>
          <button onClick={() => setProvider("openai")} disabled={provider === "openai"}>
            openai
          </button>
          <span className="muted" style={{ marginLeft: 8 }}>
            Mode
          </span>
          <button onClick={() => setMode("LAX")} disabled={mode === "LAX"}>
            LAX
          </button>
          <button onClick={() => setMode("STRICT")} disabled={mode === "STRICT"}>
            STRICT
          </button>
          <button onClick={proposeConcepts} disabled={!selectedDocId || isProposing}>
            {isProposing ? "Proposing..." : "Propose concepts"}
          </button>
          <button onClick={analyzeSelected} disabled={!selectedCandidate || isAnalyzing}>
            {isAnalyzing ? "Analyzing..." : `Analyze (${mode})`}
          </button>
          <button onClick={acceptSelected} disabled={!selectedCandidate || isAccepting}>
            {isAccepting ? "Accepting..." : "Accept (STRICT)"}
          </button>
        </div>
        {acceptedArtifactId ? (
          <div className="muted" style={{ marginTop: 8 }}>
            Accepted artifact: <span className="mono">{acceptedArtifactId}</span>
          </div>
        ) : null}
      </div>

      <div className="panel">
        <h2>Variant + Alignment Output</h2>
        <div className="row">
          {candidates.map((candidate, idx) => (
            <button key={idx} onClick={() => setSelectedIdx(idx)} disabled={idx === selectedIdx}>
              Variant {idx + 1} ({candidate.check_report.status})
            </button>
          ))}
          {candidates.length === 0 ? <span className="muted">No concept variants yet.</span> : null}
        </div>
        <pre>{selectedCandidate ? JSON.stringify(selectedCandidate.ir, null, 2) : ""}</pre>
        <pre>{selectedAnalysis ? JSON.stringify(selectedAnalysis, null, 2) : ""}</pre>

        <div
          style={{
            marginTop: 10,
            border: "1px solid var(--border)",
            borderRadius: 8,
            padding: 8,
            background: "#fff",
          }}
        >
          <div className="row">
            <span className="muted">
              Align scope ({sortedAlignDocIds.length}) <span className="mono">{sortedAlignDocIds.join(", ")}</span>
            </span>
          </div>
          <div className="row" style={{ marginTop: 8 }}>
            <label className="muted">
              max_suggestions{" "}
              <input
                type="number"
                min={ALIGN_MAX_SUGGESTIONS_MIN}
                max={ALIGN_MAX_SUGGESTIONS_MAX}
                value={alignmentMaxSuggestions}
                onChange={(event) => {
                  const parsed = Number.parseInt(event.target.value, 10);
                  if (!Number.isFinite(parsed)) return;
                  const clamped = Math.min(
                    ALIGN_MAX_SUGGESTIONS_MAX,
                    Math.max(ALIGN_MAX_SUGGESTIONS_MIN, parsed),
                  );
                  setAlignmentMaxSuggestions(clamped);
                }}
              />
            </label>
            <button onClick={alignSelectedDocs} disabled={isAligning || sortedAlignDocIds.length === 0}>
              {isAligning ? "Aligning..." : "Align selected docs"}
            </button>
            <button onClick={() => setAlignmentResult(null)} disabled={!alignmentResult}>
              Clear
            </button>
          </div>
          {alignmentResult ? (
            <div style={{ marginTop: 8 }}>
              <div className="muted">
                suggestions={alignmentResult.suggestion_count} merge=
                {alignmentResult.alignment_stats.merge_candidate_count} conflict=
                {alignmentResult.alignment_stats.conflict_candidate_count}
              </div>
              <div className="muted mono" style={{ marginTop: 4 }}>
                trust mapping={alignmentResult.mapping_trust ?? "none"} solver=
                {alignmentResult.solver_trust} proof={alignmentResult.proof_trust ?? "none"}
              </div>
              <div style={{ marginTop: 8, overflow: "auto", maxHeight: 260 }}>
                <table className="table">
                  <thead>
                    <tr>
                      <th>kind</th>
                      <th>vocabulary_key</th>
                      <th>reason</th>
                      <th>doc_ids</th>
                      <th>artifact_ids</th>
                    </tr>
                  </thead>
                  <tbody>
                    {alignmentResult.suggestions.map((suggestion) => (
                      <tr key={suggestion.suggestion_id}>
                        <td className="mono">{suggestion.kind}</td>
                        <td className="mono">{suggestion.vocabulary_key}</td>
                        <td>{suggestion.reason}</td>
                        <td className="mono">{suggestion.doc_ids.join(", ")}</td>
                        <td className="mono">{suggestion.artifact_ids.join(", ")}</td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          ) : null}
        </div>
      </div>
    </div>
  );
}
