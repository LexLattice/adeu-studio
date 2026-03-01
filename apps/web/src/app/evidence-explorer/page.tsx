"use client";

import Link from "next/link";
import { Suspense, useCallback, useEffect, useMemo, useRef, useState } from "react";
import { useRouter, useSearchParams } from "next/navigation";

import { apiBase } from "../lib/api-base";

type EvidenceExplorerFamily =
  | "read_surface"
  | "normative_advice"
  | "proof_trust"
  | "semantics_v4_candidate"
  | "extraction_fidelity";

type EvidenceExplorerIdentityMode = "artifact_level" | "pair_level";

type EvidenceExplorerEndpointRef = {
  kind: "endpoint";
  path: string;
};

type EvidenceExplorerCatalogFamilySummary = {
  family: EvidenceExplorerFamily;
  identity_mode: EvidenceExplorerIdentityMode;
  entry_count: number;
  list_ref: EvidenceExplorerEndpointRef;
};

type EvidenceExplorerCatalogResponse = {
  schema: "evidence_explorer.catalog@0.1";
  families: EvidenceExplorerCatalogFamilySummary[];
};

type EvidenceExplorerCatalogEntry = {
  family: EvidenceExplorerFamily;
  entry_id: string;
  source_text_hash: string;
  core_ir_artifact_id: string;
  concept_artifact_id: string;
  artifact_id?: string;
  ref: EvidenceExplorerEndpointRef;
};

type EvidenceExplorerCatalogFamilyResponse = {
  schema: "evidence_explorer.catalog_family@0.1";
  family: EvidenceExplorerFamily;
  identity_mode: EvidenceExplorerIdentityMode;
  total_entries: number;
  truncated: boolean;
  entries: EvidenceExplorerCatalogEntry[];
  max_entries_per_family?: number;
  returned_entries?: number;
  remaining_entries?: number;
};

type ApiErrorDetail = {
  code?: string;
  reason?: string;
  message: string;
  status: number;
};

type PrefixFilters = {
  source: string;
  core: string;
  concept: string;
};

type DeepLinkState = "outside_current_list_window" | "entry_unavailable" | null;

function sortedEntries(
  entries: EvidenceExplorerCatalogEntry[],
): EvidenceExplorerCatalogEntry[] {
  return entries.slice().sort((a, b) => {
    const aArtifactId = a.artifact_id ?? "";
    const bArtifactId = b.artifact_id ?? "";
    if (a.source_text_hash !== b.source_text_hash) {
      return a.source_text_hash.localeCompare(b.source_text_hash);
    }
    if (a.core_ir_artifact_id !== b.core_ir_artifact_id) {
      return a.core_ir_artifact_id.localeCompare(b.core_ir_artifact_id);
    }
    if (a.concept_artifact_id !== b.concept_artifact_id) {
      return a.concept_artifact_id.localeCompare(b.concept_artifact_id);
    }
    if (aArtifactId !== bArtifactId) {
      return aArtifactId.localeCompare(bArtifactId);
    }
    return a.entry_id.localeCompare(b.entry_id);
  });
}

function encodeEntryId(value: string): string {
  const bytes = new TextEncoder().encode(value);
  let binary = "";
  bytes.forEach((item) => {
    binary += String.fromCharCode(item);
  });
  return btoa(binary).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/g, "");
}

function decodeEntryId(value: string | null): string | null {
  if (!value) return null;
  try {
    const normalized = value.replace(/-/g, "+").replace(/_/g, "/");
    const padded = normalized + "=".repeat((4 - (normalized.length % 4)) % 4);
    const binary = atob(padded);
    const bytes = Uint8Array.from(binary, (char) => char.charCodeAt(0));
    return new TextDecoder().decode(bytes);
  } catch {
    return null;
  }
}

function parsePairEntry(entryId: string): {
  source_text_hash: string;
  core_ir_artifact_id: string;
  concept_artifact_id: string;
} | null {
  const segments = entryId.split(":");
  if (segments.length !== 4 || segments[0] !== "pair") {
    return null;
  }
  const source_text_hash = segments[1] ?? "";
  const core_ir_artifact_id = segments[2] ?? "";
  const concept_artifact_id = segments[3] ?? "";
  if (!source_text_hash || !core_ir_artifact_id || !concept_artifact_id) {
    return null;
  }
  return { source_text_hash, core_ir_artifact_id, concept_artifact_id };
}

function derivePrimaryRefPath(
  family: EvidenceExplorerFamily,
  entryId: string,
): string | null {
  if (family === "read_surface") {
    const prefix = "artifact:";
    if (!entryId.startsWith(prefix)) return null;
    const artifactId = entryId.slice(prefix.length);
    if (!artifactId) return null;
    return `/urm/core-ir/artifacts/${encodeURIComponent(artifactId)}`;
  }

  if (family === "extraction_fidelity") {
    const pair = parsePairEntry(entryId);
    if (!pair) return null;
    return `/urm/extraction-fidelity/sources/${encodeURIComponent(pair.source_text_hash)}`;
  }

  const pair = parsePairEntry(entryId);
  if (!pair) return null;
  const source = encodeURIComponent(pair.source_text_hash);
  const core = encodeURIComponent(pair.core_ir_artifact_id);
  const concept = encodeURIComponent(pair.concept_artifact_id);

  if (family === "normative_advice") {
    return `/urm/normative-advice/pairs/${source}/${core}/${concept}`;
  }
  if (family === "proof_trust") {
    return `/urm/proof-trust/pairs/${source}/${core}/${concept}`;
  }
  if (family === "semantics_v4_candidate") {
    return `/urm/semantics-v4/pairs/${source}/${core}/${concept}`;
  }
  return null;
}

async function parseApiError(response: Response): Promise<ApiErrorDetail> {
  const fallback = {
    status: response.status,
    message: `HTTP ${response.status}`,
  } satisfies ApiErrorDetail;
  const text = await response.text();
  if (!text) return fallback;

  try {
    const parsed = JSON.parse(text) as {
      detail?: { code?: string; reason?: string; message?: string } | string;
      message?: string;
      error?: string;
    };

    if (typeof parsed.detail === "string") {
      return { status: response.status, message: parsed.detail };
    }

    if (parsed.detail && typeof parsed.detail === "object") {
      return {
        status: response.status,
        code: parsed.detail.code,
        reason: parsed.detail.reason,
        message:
          parsed.detail.message ?? parsed.detail.reason ?? parsed.detail.code ?? fallback.message,
      };
    }

    if (typeof parsed.message === "string") {
      return { status: response.status, message: parsed.message };
    }
    if (typeof parsed.error === "string") {
      return { status: response.status, message: parsed.error };
    }
  } catch {
    return { status: response.status, message: text };
  }
  return fallback;
}

async function fetchCatalog(): Promise<EvidenceExplorerCatalogResponse> {
  const response = await fetch(`${apiBase()}/urm/evidence-explorer/catalog`, {
    method: "GET",
  });
  if (!response.ok) {
    throw await parseApiError(response);
  }
  return (await response.json()) as EvidenceExplorerCatalogResponse;
}

async function fetchCatalogFamily(
  family: EvidenceExplorerFamily,
  filters: PrefixFilters,
): Promise<EvidenceExplorerCatalogFamilyResponse> {
  const params = new URLSearchParams();
  if (filters.source) params.set("source_text_hash_prefix", filters.source);
  if (filters.core) params.set("core_ir_artifact_id_prefix", filters.core);
  if (filters.concept) params.set("concept_artifact_id_prefix", filters.concept);
  const query = params.toString();
  const path = query
    ? `${apiBase()}/urm/evidence-explorer/catalog/${family}?${query}`
    : `${apiBase()}/urm/evidence-explorer/catalog/${family}`;

  const response = await fetch(path, { method: "GET" });
  if (!response.ok) {
    throw await parseApiError(response);
  }
  return (await response.json()) as EvidenceExplorerCatalogFamilyResponse;
}

async function probeEntry(path: string): Promise<{ ok: boolean; status: number }> {
  const response = await fetch(`${apiBase()}${path}`, { method: "GET" });
  return { ok: response.ok, status: response.status };
}

function familyErrorState(error: ApiErrorDetail | null): string | null {
  if (!error) return null;
  if (error.status === 400 && error.reason === "UNSUPPORTED_FAMILY") {
    return "unsupported_family";
  }
  if (error.status === 404 && (error.code ?? "").includes("ARTIFACT_NOT_FOUND")) {
    return "backing_data_unavailable";
  }
  if (error.status === 400 && (error.code ?? "").includes("PAYLOAD_INVALID")) {
    return "catalog_payload_invalid";
  }
  return "request_failed";
}

function EvidenceExplorerPageInner() {
  const router = useRouter();
  const searchParams = useSearchParams();

  const [isLoadingCatalog, setIsLoadingCatalog] = useState<boolean>(false);
  const [catalogError, setCatalogError] = useState<string | null>(null);
  const [families, setFamilies] = useState<EvidenceExplorerCatalogFamilySummary[]>([]);

  const [selectedFamily, setSelectedFamily] = useState<EvidenceExplorerFamily | null>(null);
  const [selectedEntryId, setSelectedEntryId] = useState<string | null>(null);
  const [deepLinkState, setDeepLinkState] = useState<DeepLinkState>(null);

  const [isLoadingFamily, setIsLoadingFamily] = useState<boolean>(false);
  const [familyError, setFamilyError] = useState<ApiErrorDetail | null>(null);
  const [familyPayload, setFamilyPayload] = useState<EvidenceExplorerCatalogFamilyResponse | null>(null);

  const [draftFilters, setDraftFilters] = useState<PrefixFilters>({
    source: "",
    core: "",
    concept: "",
  });
  const [appliedFilters, setAppliedFilters] = useState<PrefixFilters>({
    source: "",
    core: "",
    concept: "",
  });

  const selectedEntry = useMemo(() => {
    if (!familyPayload || !selectedEntryId) return null;
    return familyPayload.entries.find((entry) => entry.entry_id === selectedEntryId) ?? null;
  }, [familyPayload, selectedEntryId]);

  const replaceUrlState = useCallback(
    (family: EvidenceExplorerFamily, entryId: string | null) => {
      const currentFamily = searchParams.get("family") ?? "";
      const currentEntry = searchParams.get("entry") ?? "";
      const nextEntry = entryId ? encodeEntryId(entryId) : "";

      if (currentFamily === family && currentEntry === nextEntry) {
        return;
      }

      const params = new URLSearchParams();
      params.set("family", family);
      if (entryId) {
        params.set("entry", nextEntry);
      }
      router.replace(`/evidence-explorer?${params.toString()}`, { scroll: false });
    },
    [router, searchParams],
  );

  const loadFamily = useCallback(
    async (family: EvidenceExplorerFamily, filters: PrefixFilters) => {
      setIsLoadingFamily(true);
      setFamilyError(null);
      try {
        const payload = await fetchCatalogFamily(family, filters);
        const orderedEntries = sortedEntries(payload.entries);
        const normalizedPayload: EvidenceExplorerCatalogFamilyResponse = {
          ...payload,
          entries: orderedEntries,
        };
        setFamilyPayload(normalizedPayload);

        if (!selectedEntryId && orderedEntries.length > 0) {
          const firstEntryId = orderedEntries[0].entry_id;
          setSelectedEntryId(firstEntryId);
          setDeepLinkState(null);
          replaceUrlState(family, firstEntryId);
          return;
        }

        if (!selectedEntryId) {
          setDeepLinkState(null);
          replaceUrlState(family, null);
          return;
        }

        const inList = orderedEntries.some((entry) => entry.entry_id === selectedEntryId);
        if (inList) {
          setDeepLinkState(null);
          replaceUrlState(family, selectedEntryId);
          return;
        }

        const derivedPath = derivePrimaryRefPath(family, selectedEntryId);
        if (!derivedPath) {
          setDeepLinkState("entry_unavailable");
          replaceUrlState(family, selectedEntryId);
          return;
        }

        const probe = await probeEntry(derivedPath);
        if (probe.ok) {
          setDeepLinkState("outside_current_list_window");
        } else if (probe.status === 404) {
          setDeepLinkState("entry_unavailable");
        } else {
          setDeepLinkState("entry_unavailable");
        }
        replaceUrlState(family, selectedEntryId);
      } catch (error) {
        const parsed = error as ApiErrorDetail;
        setFamilyPayload(null);
        setFamilyError(parsed);
      } finally {
        setIsLoadingFamily(false);
      }
    },
    [replaceUrlState, selectedEntryId],
  );

  const initializedRef = useRef<boolean>(false);
  useEffect(() => {
    if (initializedRef.current) return;
    initializedRef.current = true;

    let isCancelled = false;
    const initialFamilyParam = searchParams.get("family");
    const initialEntryId = decodeEntryId(searchParams.get("entry"));

    if (searchParams.get("entry") && !initialEntryId) {
      setDeepLinkState("entry_unavailable");
    }

    setSelectedEntryId(initialEntryId);

    async function run() {
      setIsLoadingCatalog(true);
      setCatalogError(null);
      try {
        const payload = await fetchCatalog();
        if (isCancelled) return;

        const orderedFamilies = payload.families;
        setFamilies(orderedFamilies);

        if (orderedFamilies.length === 0) {
          setCatalogError("catalog_empty");
          return;
        }

        const orderedFamilyNames = orderedFamilies.map((item) => item.family);
        const selected =
          initialFamilyParam && orderedFamilyNames.includes(initialFamilyParam as EvidenceExplorerFamily)
            ? (initialFamilyParam as EvidenceExplorerFamily)
            : orderedFamilyNames[0];

        setSelectedFamily(selected);
        replaceUrlState(selected, initialEntryId);
      } catch (error) {
        const parsed = error as ApiErrorDetail;
        if (isCancelled) return;
        setCatalogError(parsed.message || "catalog_unavailable");
      } finally {
        if (!isCancelled) {
          setIsLoadingCatalog(false);
        }
      }
    }

    void run();

    return () => {
      isCancelled = true;
    };
  }, [replaceUrlState, searchParams]);

  useEffect(() => {
    if (!selectedFamily) return;
    void loadFamily(selectedFamily, appliedFilters);
  }, [appliedFilters, loadFamily, selectedFamily]);

  function onSelectFamily(family: EvidenceExplorerFamily): void {
    setSelectedFamily(family);
    setSelectedEntryId(null);
    setDeepLinkState(null);
    replaceUrlState(family, null);
  }

  function onSelectEntry(entryId: string): void {
    if (!selectedFamily) return;
    setSelectedEntryId(entryId);
    setDeepLinkState(null);
    replaceUrlState(selectedFamily, entryId);
  }

  const deterministicDefaultFamily = families[0]?.family ?? null;
  const familyState = familyErrorState(familyError);

  return (
    <div className="app">
      <div className="panel">
        <h2>Evidence Explorer</h2>
        <div className="row">
          <span className="muted">Read-only surface</span>
          <Link href="/" className="muted" style={{ marginLeft: "auto" }}>
            ADEU Studio
          </Link>
          <Link href="/explain" className="muted">
            Explain
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

        {isLoadingCatalog ? <div className="muted">catalog_state: loading</div> : null}
        {catalogError ? <div className="muted">catalog_state: {catalogError}</div> : null}
        {!isLoadingCatalog && !catalogError ? (
          <>
            <div className="muted">catalog_schema: evidence_explorer.catalog@0.1</div>
            <div className="muted">
              default_family_from_catalog_order: {deterministicDefaultFamily ?? "(none)"}
            </div>
          </>
        ) : null}

        <div className="row" style={{ marginTop: 8 }}>
          {families.map((family) => (
            <button
              key={family.family}
              disabled={selectedFamily === family.family}
              onClick={() => onSelectFamily(family.family)}
            >
              {family.family} ({family.entry_count})
            </button>
          ))}
        </div>

        <div className="row" style={{ marginTop: 8 }}>
          <label className="muted">
            source_text_hash_prefix{" "}
            <input
              value={draftFilters.source}
              onChange={(event) =>
                setDraftFilters((prev) => ({ ...prev, source: event.target.value }))
              }
              placeholder="optional"
            />
          </label>
          <label className="muted">
            core_ir_artifact_id_prefix{" "}
            <input
              value={draftFilters.core}
              onChange={(event) =>
                setDraftFilters((prev) => ({ ...prev, core: event.target.value }))
              }
              placeholder="optional"
            />
          </label>
          <label className="muted">
            concept_artifact_id_prefix{" "}
            <input
              value={draftFilters.concept}
              onChange={(event) =>
                setDraftFilters((prev) => ({ ...prev, concept: event.target.value }))
              }
              placeholder="optional"
            />
          </label>
          <button onClick={() => setAppliedFilters({ ...draftFilters })}>Apply filters</button>
          <button
            onClick={() => {
              const cleared: PrefixFilters = { source: "", core: "", concept: "" };
              setDraftFilters(cleared);
              setAppliedFilters(cleared);
            }}
          >
            Clear filters
          </button>
        </div>
      </div>

      <div className="panel">
        <h2>Catalog Family</h2>
        {selectedFamily ? <div className="muted mono">family: {selectedFamily}</div> : null}
        {isLoadingFamily ? <div className="muted">family_state: loading</div> : null}
        {familyState ? <div className="muted">family_state: {familyState}</div> : null}

        {!isLoadingFamily && !familyState && familyPayload ? (
          <>
            <div className="muted mono">schema: {familyPayload.schema}</div>
            <div className="muted mono">identity_mode: {familyPayload.identity_mode}</div>
            <div className="muted mono">total_entries: {String(familyPayload.total_entries)}</div>
            <div className="muted mono">truncated: {String(familyPayload.truncated)}</div>
            {familyPayload.truncated ? (
              <div className="muted mono">
                truncation: max={familyPayload.max_entries_per_family} returned={familyPayload.returned_entries} remaining={familyPayload.remaining_entries}
              </div>
            ) : null}

            {familyPayload.entries.length === 0 ? (
              <div className="muted">family_state: empty</div>
            ) : (
              <div style={{ marginTop: 8, maxHeight: 420, overflow: "auto" }}>
                <table className="table">
                  <thead>
                    <tr>
                      <th>entry_id</th>
                      <th>source_text_hash</th>
                      <th>core_ir_artifact_id</th>
                      <th>concept_artifact_id</th>
                    </tr>
                  </thead>
                  <tbody>
                    {familyPayload.entries.map((entry) => (
                      <tr
                        key={entry.entry_id}
                        onClick={() => onSelectEntry(entry.entry_id)}
                        style={{
                          background: selectedEntryId === entry.entry_id ? "#eef2ff" : "transparent",
                          cursor: "pointer",
                        }}
                      >
                        <td className="mono">{entry.entry_id}</td>
                        <td className="mono">{entry.source_text_hash}</td>
                        <td className="mono">{entry.core_ir_artifact_id}</td>
                        <td className="mono">{entry.concept_artifact_id || ""}</td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            )}
          </>
        ) : null}
      </div>

      <div className="panel">
        <h2>Selection State</h2>
        {selectedEntryId ? <div className="muted mono">selected_entry_id: {selectedEntryId}</div> : null}
        {selectedEntry ? (
          <>
            <div className="muted mono">selected_ref: {selectedEntry.ref.path}</div>
            <div className="muted mono">encoded_entry_id: {encodeEntryId(selectedEntry.entry_id)}</div>
          </>
        ) : null}

        {deepLinkState ? <div className="muted">deep_link_state: {deepLinkState}</div> : null}

        {!selectedEntryId && !isLoadingFamily ? (
          <div className="muted">entry_state: none_selected</div>
        ) : null}

        <div className="muted" style={{ marginTop: 8 }}>
          Deterministic view-state only: family selection, entry selection, ordering, empty/error states.
        </div>
        <div className="muted">
          Evidence-only surface; no automatic policy enforcement or mutation is performed.
        </div>
      </div>
    </div>
  );
}

function EvidenceExplorerLoadingFallback() {
  return (
    <div className="app">
      <div className="panel">
        <h2>Evidence Explorer</h2>
        <div className="muted">catalog_state: loading</div>
      </div>
    </div>
  );
}

export default function EvidenceExplorerPage() {
  return (
    <Suspense fallback={<EvidenceExplorerLoadingFallback />}>
      <EvidenceExplorerPageInner />
    </Suspense>
  );
}
