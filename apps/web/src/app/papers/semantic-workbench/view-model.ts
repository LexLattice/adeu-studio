export const PAPER_SEMANTIC_ARTIFACT_SCHEMA = "adeu_paper_semantic_artifact@1";
export const PAPER_SEMANTIC_SOURCE_ARTIFACT_SCHEMA = "adeu_paper_source_artifact@1";
export const PAPER_SEMANTIC_SOURCE_SPAN_SCHEMA = "adeu_paper_source_span@1";
export const PAPER_SEMANTIC_CLAIM_SCHEMA = "adeu_paper_semantic_claim@1";
export const PAPER_SEMANTIC_LANE_FRAGMENT_SCHEMA = "adeu_paper_semantic_lane_fragment@1";
export const PAPER_SEMANTIC_INFERENCE_BRIDGE_SCHEMA = "adeu_paper_semantic_inference_bridge@1";
export const PAPER_SEMANTIC_DIAGNOSTIC_SCHEMA = "adeu_paper_semantic_diagnostic@1";
export const PAPER_SEMANTIC_PROJECTION_SCHEMA = "adeu_paper_semantic_projection@1";
export const PAPER_SEMANTIC_WORKBENCH_VIEW_CONFIG_SCHEMA =
  "adeu_paper_semantic_workbench_view_config@1";
export const PAPER_SEMANTIC_WORKBENCH_VIEW_MODEL_SCHEMA =
  "adeu_paper_semantic_workbench_view_model@1";
export const PAPER_SEMANTIC_WORKBENCH_ROUTE_ID = "paper_semantic_mock_workbench_surface";
export const PAPER_SEMANTIC_WORKBENCH_ROUTE_CONTRACT_REF =
  "v52b_paper_semantic_mock_workbench_contract";

export const ROUTE_STATUS_VALUES = ["ready_clean", "fail_closed_invalid_fixture_stack"] as const;
export const SELECTED_SURFACE_VALUES = ["artifact", "local"] as const;
export const VISIBLE_LANE_VALUES = ["O", "E", "D", "U"] as const;
export const SOURCE_ARTIFACT_KIND_VALUES = ["paper.abstract", "pasted.paragraph"] as const;
export const DIAGNOSTIC_KIND_VALUES = [
  "contradiction",
  "underdetermination",
  "missing_bridge",
  "overloaded_term",
  "implicit_assumption",
  "u_overreach",
] as const;
export const DIAGNOSTIC_SEVERITY_VALUES = ["critical", "warning", "advisory"] as const;
export const SOURCE_AUTHORITY_POSTURE =
  "source_text_and_explicit_span_anchors_authoritative" as const;
export const INTERPRETATION_AUTHORITY_POSTURE = "advisory_only" as const;
export const SEMANTIC_IDENTITY_MODE = "v49_hash_law_with_explicit_paper_domain_delta" as const;

export type WorkbenchRouteStatus = (typeof ROUTE_STATUS_VALUES)[number];
export type SelectedSurface = (typeof SELECTED_SURFACE_VALUES)[number];
export type VisibleLaneId = (typeof VISIBLE_LANE_VALUES)[number];
export type SourceArtifactKind = (typeof SOURCE_ARTIFACT_KIND_VALUES)[number];
export type DiagnosticKind = (typeof DIAGNOSTIC_KIND_VALUES)[number];
export type DiagnosticSeverity = (typeof DIAGNOSTIC_SEVERITY_VALUES)[number];

export type PaperSourceArtifact = {
  schema: "adeu_paper_source_artifact@1";
  source_id: string;
  artifact_kind: SourceArtifactKind;
  title: string;
  authors: string[];
  year: number | null;
  venue?: string;
  source_text: string;
  source_text_hash: string;
  paragraph_index?: number;
  source_notes?: string[];
};

export type PaperSourceSpan = {
  schema: "adeu_paper_source_span@1";
  span_id: string;
  start: number;
  end: number;
  quote: string;
  sentence_index: number;
  paragraph_index: number;
};

export type PaperSemanticClaim = {
  schema: "adeu_paper_semantic_claim@1";
  claim_id: string;
  claim_text: string;
  status: string;
  span_ids: string[];
  lane_fragment_ids: string[];
  summary?: string;
  confidence?: number;
};

export type PaperSemanticLaneFragment = {
  schema: "adeu_paper_semantic_lane_fragment@1";
  fragment_id: string;
  claim_id: string;
  lane_id: VisibleLaneId;
  short_label: string;
  fragment_text: string;
  source_kind: string;
  status: string;
  confidence: number;
  warrant: string;
  span_ids: string[];
  bridge_ids: string[];
  diagnostic_ids: string[];
};

export type PaperSemanticInferenceBridge = {
  schema: "adeu_paper_semantic_inference_bridge@1";
  bridge_id: string;
  bridge_kind: string;
  from_fragment_ids: string[];
  to_fragment_ids: string[];
  rationale: string;
  confidence: number;
  diagnostic_ids: string[];
};

export type PaperSemanticDiagnostic = {
  schema: "adeu_paper_semantic_diagnostic@1";
  diagnostic_id: string;
  diagnostic_kind: DiagnosticKind;
  lane_ids: VisibleLaneId[];
  related_fragment_ids: string[];
  severity: DiagnosticSeverity;
  span_ids: string[];
  summary: string;
};

export type PaperSemanticProjection = {
  schema: "adeu_paper_semantic_projection@1";
  projection_id: string;
  surface: SelectedSurface;
  lane_order: VisibleLaneId[];
  claim_order: string[];
  recommended_focus_claim_id: string | null;
  diagnostic_summary: {
    critical: number;
    warning: number;
    advisory: number;
  };
};

export type PaperSemanticArtifact = {
  schema: "adeu_paper_semantic_artifact@1";
  artifact_id: string;
  source: PaperSourceArtifact;
  spans: PaperSourceSpan[];
  claims: PaperSemanticClaim[];
  lane_fragments: PaperSemanticLaneFragment[];
  inference_bridges: PaperSemanticInferenceBridge[];
  diagnostics: PaperSemanticDiagnostic[];
  projections: PaperSemanticProjection[];
  source_authority_posture: typeof SOURCE_AUTHORITY_POSTURE;
  interpretation_authority_posture: typeof INTERPRETATION_AUTHORITY_POSTURE;
  semantic_identity_mode: typeof SEMANTIC_IDENTITY_MODE;
  identity_field_names: string[];
  projection_field_names: string[];
  semantic_hash: string;
};

export type CommittedSampleArtifact = {
  ref: string;
  artifact: PaperSemanticArtifact;
};

export type PaperSemanticWorkbenchViewConfig = {
  schema: "adeu_paper_semantic_workbench_view_config@1";
  route_id: string;
  selected_sample_artifact_ref: string;
  selected_surface: SelectedSurface;
  focus_claim_id: string | null;
  visible_lane_ids: VisibleLaneId[];
};

export type PaperSemanticWorkbenchViewModel = {
  schema: "adeu_paper_semantic_workbench_view_model@1";
  route_status: WorkbenchRouteStatus;
  route_contract_ref: string;
  selected_sample_artifact_ref: string;
  available_sample_artifact_refs: string[];
  artifact_ref: string | null;
  artifact: PaperSemanticArtifact | null;
  semantic_hash: string | null;
  identity_field_names: string[] | null;
  projection_field_names: string[] | null;
  selected_surface: SelectedSurface;
  focus_claim_id: string | null;
  visible_lane_ids: VisibleLaneId[];
  ordered_claim_ids: string[];
  failure_code: string | null;
  view_hash: string;
};

type JsonRecord = Record<string, unknown>;

export function buildDefaultViewConfig(
  selectedSampleArtifactRef: string,
): PaperSemanticWorkbenchViewConfig {
  return {
    schema: PAPER_SEMANTIC_WORKBENCH_VIEW_CONFIG_SCHEMA,
    route_id: PAPER_SEMANTIC_WORKBENCH_ROUTE_ID,
    selected_sample_artifact_ref: selectedSampleArtifactRef,
    selected_surface: "artifact",
    focus_claim_id: null,
    visible_lane_ids: [...VISIBLE_LANE_VALUES],
  };
}

export function createViewModel(
  sampleArtifacts: readonly CommittedSampleArtifact[],
  config: PaperSemanticWorkbenchViewConfig,
): PaperSemanticWorkbenchViewModel {
  const availableRefs = sampleArtifacts.map((item) => item.ref);

  if (config.schema !== PAPER_SEMANTIC_WORKBENCH_VIEW_CONFIG_SCHEMA) {
    return buildFailureViewModel(config, availableRefs, "INVALID_VIEW_CONFIG_SCHEMA");
  }
  if (config.route_id !== PAPER_SEMANTIC_WORKBENCH_ROUTE_ID) {
    return buildFailureViewModel(config, availableRefs, "INVALID_ROUTE_ID");
  }
  if (!SELECTED_SURFACE_VALUES.includes(config.selected_surface)) {
    return buildFailureViewModel(config, availableRefs, "INVALID_SELECTED_SURFACE");
  }

  const visibleLaneIds = normalizeVisibleLaneIds(config.visible_lane_ids);
  if (!visibleLaneIds) {
    return buildFailureViewModel(config, availableRefs, "INVALID_VISIBLE_LANE_IDS");
  }

  const selectedArtifact = sampleArtifacts.find(
    (item) => item.ref === config.selected_sample_artifact_ref,
  );
  if (!selectedArtifact) {
    return buildFailureViewModel(config, availableRefs, "UNKNOWN_SAMPLE_ARTIFACT_REF");
  }

  const projection =
    selectedArtifact.artifact.projections.find((item) => item.surface === config.selected_surface) ??
    null;
  if (!projection) {
    return buildFailureViewModel(config, availableRefs, "INVALID_SELECTED_SURFACE_PROJECTION");
  }
  const claimIds = new Set(selectedArtifact.artifact.claims.map((item) => item.claim_id));
  const orderedClaimIds =
    projection && projection.claim_order.every((claimId) => claimIds.has(claimId))
      ? [...projection.claim_order]
      : [...selectedArtifact.artifact.claims]
          .map((item) => item.claim_id)
          .sort((left, right) => left.localeCompare(right));

  const focusClaimId =
    config.focus_claim_id && claimIds.has(config.focus_claim_id)
      ? config.focus_claim_id
      : projection?.recommended_focus_claim_id && claimIds.has(projection.recommended_focus_claim_id)
        ? projection.recommended_focus_claim_id
        : orderedClaimIds[0] ?? null;

  const subject = {
    route_status: "ready_clean",
    selected_sample_artifact_ref: config.selected_sample_artifact_ref,
    artifact_ref: selectedArtifact.artifact.artifact_id,
    selected_surface: config.selected_surface,
    focus_claim_id: focusClaimId,
    visible_lane_ids: visibleLaneIds,
    ordered_claim_ids: orderedClaimIds,
    failure_code: null,
  };

  return {
    schema: PAPER_SEMANTIC_WORKBENCH_VIEW_MODEL_SCHEMA,
    route_status: "ready_clean",
    route_contract_ref: PAPER_SEMANTIC_WORKBENCH_ROUTE_CONTRACT_REF,
    selected_sample_artifact_ref: config.selected_sample_artifact_ref,
    available_sample_artifact_refs: availableRefs,
    artifact_ref: selectedArtifact.artifact.artifact_id,
    artifact: selectedArtifact.artifact,
    semantic_hash: selectedArtifact.artifact.semantic_hash,
    identity_field_names: [...selectedArtifact.artifact.identity_field_names],
    projection_field_names: [...selectedArtifact.artifact.projection_field_names],
    selected_surface: config.selected_surface,
    focus_claim_id: focusClaimId,
    visible_lane_ids: visibleLaneIds,
    ordered_claim_ids: orderedClaimIds,
    failure_code: null,
    view_hash: computeStableViewHash(subject),
  };
}

export function createInvalidFixtureStackViewModel(params: {
  selectedSampleArtifactRef: string;
  availableSampleArtifactRefs: readonly string[];
  failureCode: string;
}): PaperSemanticWorkbenchViewModel {
  const config: PaperSemanticWorkbenchViewConfig = {
    schema: PAPER_SEMANTIC_WORKBENCH_VIEW_CONFIG_SCHEMA,
    route_id: PAPER_SEMANTIC_WORKBENCH_ROUTE_ID,
    selected_sample_artifact_ref: params.selectedSampleArtifactRef,
    selected_surface: "artifact",
    focus_claim_id: null,
    visible_lane_ids: [...VISIBLE_LANE_VALUES],
  };
  return buildFailureViewModel(
    config,
    params.availableSampleArtifactRefs,
    params.failureCode,
  );
}

export function parsePaperSemanticArtifact(value: unknown): PaperSemanticArtifact | null {
  if (!isJsonRecord(value) || value.schema !== PAPER_SEMANTIC_ARTIFACT_SCHEMA) return null;
  const source = parsePaperSourceArtifact(value.source);
  const spans = parseArray(value.spans, parsePaperSourceSpan);
  const claims = parseArray(value.claims, parsePaperSemanticClaim);
  const laneFragments = parseArray(value.lane_fragments, parsePaperSemanticLaneFragment);
  const inferenceBridges = parseArray(
    value.inference_bridges,
    parsePaperSemanticInferenceBridge,
  );
  const diagnostics = parseArray(value.diagnostics, parsePaperSemanticDiagnostic);
  const projections = parseArray(value.projections, parsePaperSemanticProjection);
  const identityFieldNames = parseStringArray(value.identity_field_names);
  const projectionFieldNames = parseStringArray(value.projection_field_names);
  if (
    !source ||
    !spans ||
    !claims ||
    !laneFragments ||
    !inferenceBridges ||
    !diagnostics ||
    !projections ||
    !identityFieldNames ||
    !projectionFieldNames ||
    typeof value.artifact_id !== "string" ||
    value.source_authority_posture !== SOURCE_AUTHORITY_POSTURE ||
    value.interpretation_authority_posture !== INTERPRETATION_AUTHORITY_POSTURE ||
    value.semantic_identity_mode !== SEMANTIC_IDENTITY_MODE ||
    !isSha256(value.semantic_hash)
  ) {
    return null;
  }

  if (
    !validateSourceSpans(source, spans) ||
    !validateArtifactReferences({
      claims,
      diagnostics,
      inferenceBridges,
      laneFragments,
      projections,
      spans,
    })
  ) {
    return null;
  }

  return {
    schema: PAPER_SEMANTIC_ARTIFACT_SCHEMA,
    artifact_id: value.artifact_id,
    source,
    spans,
    claims,
    lane_fragments: laneFragments,
    inference_bridges: inferenceBridges,
    diagnostics,
    projections,
    source_authority_posture: SOURCE_AUTHORITY_POSTURE,
    interpretation_authority_posture: INTERPRETATION_AUTHORITY_POSTURE,
    semantic_identity_mode: SEMANTIC_IDENTITY_MODE,
    identity_field_names: identityFieldNames,
    projection_field_names: projectionFieldNames,
    semantic_hash: value.semantic_hash,
  };
}

function validateSourceSpans(source: PaperSourceArtifact, spans: PaperSourceSpan[]): boolean {
  const spanIds = new Set<string>();
  for (const span of spans) {
    if (spanIds.has(span.span_id)) return false;
    spanIds.add(span.span_id);
    if (span.start < 0 || span.end < span.start) return false;
    if (source.source_text.slice(span.start, span.end) !== span.quote) return false;
    if (
      source.artifact_kind === "pasted.paragraph" &&
      (source.paragraph_index === undefined || span.paragraph_index !== source.paragraph_index)
    ) {
      return false;
    }
  }
  return true;
}

function validateArtifactReferences(params: {
  spans: PaperSourceSpan[];
  claims: PaperSemanticClaim[];
  laneFragments: PaperSemanticLaneFragment[];
  inferenceBridges: PaperSemanticInferenceBridge[];
  diagnostics: PaperSemanticDiagnostic[];
  projections: PaperSemanticProjection[];
}): boolean {
  const spanIds = new Set(params.spans.map((item) => item.span_id));
  const claimIds = new Set(params.claims.map((item) => item.claim_id));
  const fragmentIds = new Set(params.laneFragments.map((item) => item.fragment_id));
  const bridgeIds = new Set(params.inferenceBridges.map((item) => item.bridge_id));
  const diagnosticIds = new Set(params.diagnostics.map((item) => item.diagnostic_id));

  if (
    claimIds.size !== params.claims.length ||
    fragmentIds.size !== params.laneFragments.length ||
    bridgeIds.size !== params.inferenceBridges.length ||
    diagnosticIds.size !== params.diagnostics.length
  ) {
    return false;
  }

  for (const claim of params.claims) {
    if (
      !claim.span_ids.every((spanId) => spanIds.has(spanId)) ||
      !claim.lane_fragment_ids.every((fragmentId) => fragmentIds.has(fragmentId))
    ) {
      return false;
    }
  }

  for (const fragment of params.laneFragments) {
    if (
      !claimIds.has(fragment.claim_id) ||
      !fragment.span_ids.every((spanId) => spanIds.has(spanId)) ||
      !fragment.bridge_ids.every((bridgeId) => bridgeIds.has(bridgeId)) ||
      !fragment.diagnostic_ids.every((diagnosticId) => diagnosticIds.has(diagnosticId))
    ) {
      return false;
    }
  }

  for (const bridge of params.inferenceBridges) {
    if (
      !bridge.from_fragment_ids.every((fragmentId) => fragmentIds.has(fragmentId)) ||
      !bridge.to_fragment_ids.every((fragmentId) => fragmentIds.has(fragmentId)) ||
      !bridge.diagnostic_ids.every((diagnosticId) => diagnosticIds.has(diagnosticId))
    ) {
      return false;
    }
  }

  for (const diagnostic of params.diagnostics) {
    if (
      !diagnostic.related_fragment_ids.every((fragmentId) => fragmentIds.has(fragmentId)) ||
      !diagnostic.span_ids.every((spanId) => spanIds.has(spanId))
    ) {
      return false;
    }
  }

  for (const projection of params.projections) {
    if (
      !projection.claim_order.every((claimId) => claimIds.has(claimId)) ||
      (projection.recommended_focus_claim_id !== null &&
        !claimIds.has(projection.recommended_focus_claim_id))
    ) {
      return false;
    }
  }

  return true;
}

function buildFailureViewModel(
  config: PaperSemanticWorkbenchViewConfig,
  availableRefs: readonly string[],
  failureCode: string,
): PaperSemanticWorkbenchViewModel {
  const subject = {
    route_status: "fail_closed_invalid_fixture_stack",
    selected_sample_artifact_ref: config.selected_sample_artifact_ref,
    artifact_ref: null,
    selected_surface: config.selected_surface,
    focus_claim_id: config.focus_claim_id,
    visible_lane_ids: [...config.visible_lane_ids].sort(),
    ordered_claim_ids: [],
    failure_code: failureCode,
  };
  return {
    schema: PAPER_SEMANTIC_WORKBENCH_VIEW_MODEL_SCHEMA,
    route_status: "fail_closed_invalid_fixture_stack",
    route_contract_ref: PAPER_SEMANTIC_WORKBENCH_ROUTE_CONTRACT_REF,
    selected_sample_artifact_ref: config.selected_sample_artifact_ref,
    available_sample_artifact_refs: [...availableRefs],
    artifact_ref: null,
    artifact: null,
    semantic_hash: null,
    identity_field_names: null,
    projection_field_names: null,
    selected_surface: config.selected_surface,
    focus_claim_id: config.focus_claim_id,
    visible_lane_ids: [...config.visible_lane_ids],
    ordered_claim_ids: [],
    failure_code: failureCode,
    view_hash: computeStableViewHash(subject),
  };
}

function normalizeVisibleLaneIds(value: readonly string[]): VisibleLaneId[] | null {
  if (value.length === 0) return null;
  const unique = new Set<string>(value);
  if (unique.size !== value.length) return null;
  if ([...unique].some((item) => !VISIBLE_LANE_VALUES.includes(item as VisibleLaneId))) {
    return null;
  }
  return [...VISIBLE_LANE_VALUES].filter((lane) => unique.has(lane));
}

function parsePaperSourceArtifact(value: unknown): PaperSourceArtifact | null {
  if (!isJsonRecord(value) || value.schema !== PAPER_SEMANTIC_SOURCE_ARTIFACT_SCHEMA) return null;
  const authors = parseStringArray(value.authors);
  const sourceNotes = value.source_notes === undefined ? undefined : parseStringArray(value.source_notes);
  if (
    !authors ||
    (sourceNotes === null) ||
    !SOURCE_ARTIFACT_KIND_VALUES.includes(value.artifact_kind as SourceArtifactKind) ||
    typeof value.source_id !== "string" ||
    typeof value.title !== "string" ||
    !isNullableInteger(value.year) ||
    (value.venue !== undefined && typeof value.venue !== "string") ||
    typeof value.source_text !== "string" ||
    !isSha256(value.source_text_hash) ||
    (value.paragraph_index !== undefined && !isInteger(value.paragraph_index))
  ) {
    return null;
  }
  return {
    schema: PAPER_SEMANTIC_SOURCE_ARTIFACT_SCHEMA,
    source_id: value.source_id,
    artifact_kind: value.artifact_kind as SourceArtifactKind,
    title: value.title,
    authors,
    year: value.year,
    venue: typeof value.venue === "string" ? value.venue : undefined,
    source_text: value.source_text,
    source_text_hash: value.source_text_hash,
    paragraph_index: typeof value.paragraph_index === "number" ? value.paragraph_index : undefined,
    source_notes: sourceNotes ?? undefined,
  };
}

function parsePaperSourceSpan(value: unknown): PaperSourceSpan | null {
  if (!isJsonRecord(value) || value.schema !== PAPER_SEMANTIC_SOURCE_SPAN_SCHEMA) return null;
  if (
    typeof value.span_id !== "string" ||
    !isInteger(value.start) ||
    !isInteger(value.end) ||
    typeof value.quote !== "string" ||
    !isInteger(value.sentence_index) ||
    !isInteger(value.paragraph_index)
  ) {
    return null;
  }
  return {
    schema: PAPER_SEMANTIC_SOURCE_SPAN_SCHEMA,
    span_id: value.span_id,
    start: value.start,
    end: value.end,
    quote: value.quote,
    sentence_index: value.sentence_index,
    paragraph_index: value.paragraph_index,
  };
}

function parsePaperSemanticClaim(value: unknown): PaperSemanticClaim | null {
  if (!isJsonRecord(value) || value.schema !== PAPER_SEMANTIC_CLAIM_SCHEMA) return null;
  const spanIds = parseStringArray(value.span_ids);
  const laneFragmentIds = parseStringArray(value.lane_fragment_ids);
  if (
    !spanIds ||
    !laneFragmentIds ||
    typeof value.claim_id !== "string" ||
    typeof value.claim_text !== "string" ||
    typeof value.status !== "string" ||
    (value.summary !== undefined && typeof value.summary !== "string") ||
    (value.confidence !== undefined && typeof value.confidence !== "number")
  ) {
    return null;
  }
  return {
    schema: PAPER_SEMANTIC_CLAIM_SCHEMA,
    claim_id: value.claim_id,
    claim_text: value.claim_text,
    status: value.status,
    span_ids: spanIds,
    lane_fragment_ids: laneFragmentIds,
    summary: typeof value.summary === "string" ? value.summary : undefined,
    confidence: typeof value.confidence === "number" ? value.confidence : undefined,
  };
}

function parsePaperSemanticLaneFragment(value: unknown): PaperSemanticLaneFragment | null {
  if (!isJsonRecord(value) || value.schema !== PAPER_SEMANTIC_LANE_FRAGMENT_SCHEMA) return null;
  const spanIds = parseStringArray(value.span_ids);
  const bridgeIds = parseStringArray(value.bridge_ids);
  const diagnosticIds = parseStringArray(value.diagnostic_ids);
  if (
    !spanIds ||
    !bridgeIds ||
    !diagnosticIds ||
    typeof value.fragment_id !== "string" ||
    typeof value.claim_id !== "string" ||
    !VISIBLE_LANE_VALUES.includes(value.lane_id as VisibleLaneId) ||
    typeof value.short_label !== "string" ||
    typeof value.fragment_text !== "string" ||
    typeof value.source_kind !== "string" ||
    typeof value.status !== "string" ||
    typeof value.confidence !== "number" ||
    typeof value.warrant !== "string"
  ) {
    return null;
  }
  return {
    schema: PAPER_SEMANTIC_LANE_FRAGMENT_SCHEMA,
    fragment_id: value.fragment_id,
    claim_id: value.claim_id,
    lane_id: value.lane_id as VisibleLaneId,
    short_label: value.short_label,
    fragment_text: value.fragment_text,
    source_kind: value.source_kind,
    status: value.status,
    confidence: value.confidence,
    warrant: value.warrant,
    span_ids: spanIds,
    bridge_ids: bridgeIds,
    diagnostic_ids: diagnosticIds,
  };
}

function parsePaperSemanticInferenceBridge(value: unknown): PaperSemanticInferenceBridge | null {
  if (!isJsonRecord(value) || value.schema !== PAPER_SEMANTIC_INFERENCE_BRIDGE_SCHEMA) return null;
  const fromFragmentIds = parseStringArray(value.from_fragment_ids);
  const toFragmentIds = parseStringArray(value.to_fragment_ids);
  const diagnosticIds = parseStringArray(value.diagnostic_ids);
  if (
    !fromFragmentIds ||
    !toFragmentIds ||
    !diagnosticIds ||
    typeof value.bridge_id !== "string" ||
    typeof value.bridge_kind !== "string" ||
    typeof value.rationale !== "string" ||
    typeof value.confidence !== "number"
  ) {
    return null;
  }
  return {
    schema: PAPER_SEMANTIC_INFERENCE_BRIDGE_SCHEMA,
    bridge_id: value.bridge_id,
    bridge_kind: value.bridge_kind,
    from_fragment_ids: fromFragmentIds,
    to_fragment_ids: toFragmentIds,
    rationale: value.rationale,
    confidence: value.confidence,
    diagnostic_ids: diagnosticIds,
  };
}

function parsePaperSemanticDiagnostic(value: unknown): PaperSemanticDiagnostic | null {
  if (!isJsonRecord(value) || value.schema !== PAPER_SEMANTIC_DIAGNOSTIC_SCHEMA) return null;
  const laneIds = parseLaneIdArray(value.lane_ids);
  const relatedFragmentIds = parseStringArray(value.related_fragment_ids);
  const spanIds = parseStringArray(value.span_ids);
  if (
    !laneIds ||
    !relatedFragmentIds ||
    !spanIds ||
    typeof value.diagnostic_id !== "string" ||
    !DIAGNOSTIC_KIND_VALUES.includes(value.diagnostic_kind as DiagnosticKind) ||
    !DIAGNOSTIC_SEVERITY_VALUES.includes(value.severity as DiagnosticSeverity) ||
    typeof value.summary !== "string"
  ) {
    return null;
  }
  return {
    schema: PAPER_SEMANTIC_DIAGNOSTIC_SCHEMA,
    diagnostic_id: value.diagnostic_id,
    diagnostic_kind: value.diagnostic_kind as DiagnosticKind,
    lane_ids: laneIds,
    related_fragment_ids: relatedFragmentIds,
    severity: value.severity as DiagnosticSeverity,
    span_ids: spanIds,
    summary: value.summary,
  };
}

function parsePaperSemanticProjection(value: unknown): PaperSemanticProjection | null {
  if (!isJsonRecord(value) || value.schema !== PAPER_SEMANTIC_PROJECTION_SCHEMA) return null;
  const laneOrder = parseLaneIdArray(value.lane_order);
  const claimOrder = parseStringArray(value.claim_order);
  const diagnosticSummary = parseDiagnosticSummary(value.diagnostic_summary);
  if (
    !laneOrder ||
    !claimOrder ||
    !diagnosticSummary ||
    typeof value.projection_id !== "string" ||
    !SELECTED_SURFACE_VALUES.includes(value.surface as SelectedSurface) ||
    (value.recommended_focus_claim_id !== null &&
      value.recommended_focus_claim_id !== undefined &&
      typeof value.recommended_focus_claim_id !== "string")
  ) {
    return null;
  }
  return {
    schema: PAPER_SEMANTIC_PROJECTION_SCHEMA,
    projection_id: value.projection_id,
    surface: value.surface as SelectedSurface,
    lane_order: laneOrder,
    claim_order: claimOrder,
    recommended_focus_claim_id:
      typeof value.recommended_focus_claim_id === "string"
        ? value.recommended_focus_claim_id
        : null,
    diagnostic_summary: diagnosticSummary,
  };
}

function parseDiagnosticSummary(value: unknown): PaperSemanticProjection["diagnostic_summary"] | null {
  if (!isJsonRecord(value)) return null;
  if (!isInteger(value.critical) || !isInteger(value.warning) || !isInteger(value.advisory)) {
    return null;
  }
  return {
    critical: value.critical,
    warning: value.warning,
    advisory: value.advisory,
  };
}

function parseArray<T>(value: unknown, parser: (item: unknown) => T | null): T[] | null {
  if (!Array.isArray(value)) return null;
  const next: T[] = [];
  for (const item of value) {
    const parsed = parser(item);
    if (!parsed) return null;
    next.push(parsed);
  }
  return next;
}

function parseStringArray(value: unknown): string[] | null {
  if (!Array.isArray(value)) return null;
  if (value.some((item) => typeof item !== "string")) return null;
  return [...value];
}

function parseLaneIdArray(value: unknown): VisibleLaneId[] | null {
  const parsed = parseStringArray(value);
  if (!parsed) return null;
  if (parsed.some((item) => !VISIBLE_LANE_VALUES.includes(item as VisibleLaneId))) return null;
  return parsed as VisibleLaneId[];
}

function isJsonRecord(value: unknown): value is JsonRecord {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function isInteger(value: unknown): value is number {
  return typeof value === "number" && Number.isInteger(value);
}

function isNullableInteger(value: unknown): value is number | null {
  return value === null || isInteger(value);
}

function isSha256(value: unknown): value is string {
  return typeof value === "string" && /^[a-f0-9]{64}$/.test(value);
}

function computeStableViewHash(value: Record<string, unknown>): string {
  const serialized = stableStringify(value);
  let hash = 2166136261;
  for (let index = 0; index < serialized.length; index += 1) {
    hash ^= serialized.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return `view:${(hash >>> 0).toString(16).padStart(8, "0")}`;
}

function stableStringify(value: unknown): string {
  if (value === null || typeof value !== "object") {
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => stableStringify(item)).join(",")}]`;
  }
  const entries = Object.entries(value as Record<string, unknown>).sort(([left], [right]) =>
    left.localeCompare(right),
  );
  return `{${entries
    .map(([key, entryValue]) => `${JSON.stringify(key)}:${stableStringify(entryValue)}`)
    .join(",")}}`;
}
