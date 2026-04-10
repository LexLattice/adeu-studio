export const ODEU_RUN_VIEW_CONFIG_SCHEMA = "adeu_odeu_run_view_config@1";
export const ODEU_RUN_VIEW_MODEL_SCHEMA = "adeu_odeu_run_view_model@1";
export const ODEU_RUN_RESPONSE_SCHEMA = "adeu_odeu_run_response@1";
export const ODEU_RUN_SUMMARY_SCHEMA = "adeu_odeu_run_summary@1";
export const ODEU_RUN_ROUTE_ID = "odeu_sim_summary_surface";
export const ODEU_RUN_OUTPUT_MODE = "summary_only_json";
export const DEFAULT_SCENARIO_NAME = "healthy_baseline";
export const DEFAULT_SEED = 7;
export const DEFAULT_STEPS = 25;
export const MIN_SEED = 0;
export const MIN_STEPS = 1;
export const MAX_STEPS = 25;

export const RELEASED_SCENARIO_NAMES = ["healthy_baseline", "weak_d"] as const;
export type OdeuScenarioName = (typeof RELEASED_SCENARIO_NAMES)[number];

export const ROUTE_STATUS_VALUES = [
  "idle",
  "loading",
  "completed_clean",
  "fail_closed_invalid_request",
  "fail_closed_kernel_mismatch",
] as const;
export type OdeuRouteStatus = (typeof ROUTE_STATUS_VALUES)[number];

export const API_REQUEST_STATUS_VALUES = [
  "completed_clean",
  "fail_closed_invalid_request",
  "fail_closed_kernel_mismatch",
] as const;
export type OdeuApiRequestStatus = (typeof API_REQUEST_STATUS_VALUES)[number];

export type OdeuLaneSummary = {
  mean_legitimacy_belief: number;
  mean_uncertainty: number;
  mean_resources: number;
};

export type OdeuRunMeta = {
  scenario: OdeuScenarioName;
  seed: number;
  turn: number;
  regime_label: string;
};

export type OdeuScenarioConfig = {
  schema: "adeu_odeu_scenario_config@1";
  name: OdeuScenarioName;
  description: string;
  num_agents: number;
  scarcity: number;
  regeneration_rate: number;
  misinformation: number;
  verification_capacity: number;
  enforcement_capacity: number;
  sanction_severity: number;
  initial_legitimacy: number;
  initial_operativity: number;
  sanction_consistency: number;
  archive_capacity: number;
  appeal_availability: number;
  public_epistemics_level: number;
  ai_mode: string;
  ai_reliability: number;
  cooperator_share: number;
  opportunist_share: number;
  auditor_share: number;
  official_share: number;
  ai_dependent_share: number;
  max_turns: number;
};

export type OdeuMetricPoint = {
  schema: "adeu_odeu_metric_point@1";
  turn: number;
  cooperation_rate: number;
  commons_health: number;
  average_belief_accuracy: number;
  epistemic_integrity: number;
  institution_legitimacy: number;
  institution_operativity: number;
  symbolic_gap: number;
  sanction_consistency: number;
  utility_concentration: number;
  trust_fragmentation: number;
  regime_label: string;
};

export type OdeuRunSummary = {
  schema: "adeu_odeu_run_summary@1";
  meta: OdeuRunMeta;
  config_snapshot: OdeuScenarioConfig;
  scenario: OdeuScenarioName;
  seed: number;
  turn: number;
  current_metric: OdeuMetricPoint;
  lane_summary: OdeuLaneSummary;
  action_counts: Record<string, number>;
  event_record_count: number;
  evidence_record_count: number;
  sanction_event_count: number;
};

export type OdeuRunApiResponse = {
  schema: "adeu_odeu_run_response@1";
  request_status: OdeuApiRequestStatus;
  request_ref: string;
  kernel_contract_ref: string;
  run_summary: OdeuRunSummary | null;
  failure_code: string | null;
  response_hash: string;
};

export type OdeuRunViewConfig = {
  schema: "adeu_odeu_run_view_config@1";
  route_id: string;
  scenario_name: OdeuScenarioName;
  seed: number;
  steps: number;
  output_mode: "summary_only_json";
};

export type OdeuRunViewModel = {
  schema: "adeu_odeu_run_view_model@1";
  route_status: Exclude<OdeuRouteStatus, "idle" | "loading">;
  request_ref: string;
  kernel_contract_ref: string;
  response_hash: string;
  meta: OdeuRunMeta | null;
  config_snapshot: OdeuScenarioConfig | null;
  current_metric: OdeuMetricPoint | null;
  lane_summary: OdeuLaneSummary | null;
  action_counts: Record<string, number> | null;
  event_record_count: number | null;
  evidence_record_count: number | null;
  sanction_event_count: number | null;
  failure_code: string | null;
};

type JsonRecord = Record<string, unknown>;

export function buildDefaultViewConfig(): OdeuRunViewConfig {
  return {
    schema: ODEU_RUN_VIEW_CONFIG_SCHEMA,
    route_id: ODEU_RUN_ROUTE_ID,
    scenario_name: DEFAULT_SCENARIO_NAME,
    seed: DEFAULT_SEED,
    steps: DEFAULT_STEPS,
    output_mode: ODEU_RUN_OUTPUT_MODE,
  };
}

export function validateViewConfig(config: OdeuRunViewConfig): string | null {
  if (!RELEASED_SCENARIO_NAMES.includes(config.scenario_name)) {
    return "Scenario must remain inside the released V51-B route surface.";
  }
  if (!Number.isInteger(config.seed) || config.seed < MIN_SEED) {
    return "Seed must be a non-negative integer.";
  }
  if (!Number.isInteger(config.steps) || config.steps < MIN_STEPS || config.steps > MAX_STEPS) {
    return `Steps must stay between ${MIN_STEPS} and ${MAX_STEPS}.`;
  }
  return null;
}

export function mapApiRequestStatusToRouteStatus(
  status: OdeuApiRequestStatus,
): Exclude<OdeuRouteStatus, "idle" | "loading"> {
  return status;
}

export function buildApiPayload(config: OdeuRunViewConfig): Record<string, unknown> {
  return {
    scenario_name: config.scenario_name,
    seed: config.seed,
    steps: config.steps,
    output_mode: config.output_mode,
  };
}

export function createViewModelFromApiResponse(response: OdeuRunApiResponse): OdeuRunViewModel {
  return {
    schema: ODEU_RUN_VIEW_MODEL_SCHEMA,
    route_status: mapApiRequestStatusToRouteStatus(response.request_status),
    request_ref: response.request_ref,
    kernel_contract_ref: response.kernel_contract_ref,
    response_hash: response.response_hash,
    meta: response.run_summary?.meta ?? null,
    config_snapshot: response.run_summary?.config_snapshot ?? null,
    current_metric: response.run_summary?.current_metric ?? null,
    lane_summary: response.run_summary?.lane_summary ?? null,
    action_counts: response.run_summary?.action_counts ?? null,
    event_record_count: response.run_summary?.event_record_count ?? null,
    evidence_record_count: response.run_summary?.evidence_record_count ?? null,
    sanction_event_count: response.run_summary?.sanction_event_count ?? null,
    failure_code: response.failure_code,
  };
}

export function parseApiResponse(value: unknown): OdeuRunApiResponse | null {
  if (!isJsonRecord(value)) return null;
  if (value.schema !== ODEU_RUN_RESPONSE_SCHEMA) return null;
  if (!isApiRequestStatus(value.request_status)) return null;
  if (typeof value.request_ref !== "string" || typeof value.kernel_contract_ref !== "string") {
    return null;
  }
  if (!isSha256(value.response_hash)) return null;
  if (value.request_status === "completed_clean") {
    const summary = parseRunSummary(value.run_summary);
    if (!summary || value.failure_code !== null) return null;
    return {
      schema: ODEU_RUN_RESPONSE_SCHEMA,
      request_status: value.request_status,
      request_ref: value.request_ref,
      kernel_contract_ref: value.kernel_contract_ref,
      run_summary: summary,
      failure_code: null,
      response_hash: value.response_hash,
    };
  }
  if (value.run_summary !== null || typeof value.failure_code !== "string") {
    return null;
  }
  return {
    schema: ODEU_RUN_RESPONSE_SCHEMA,
    request_status: value.request_status,
    request_ref: value.request_ref,
    kernel_contract_ref: value.kernel_contract_ref,
    run_summary: null,
    failure_code: value.failure_code,
    response_hash: value.response_hash,
  };
}

function parseRunSummary(value: unknown): OdeuRunSummary | null {
  if (!isJsonRecord(value) || value.schema !== ODEU_RUN_SUMMARY_SCHEMA) return null;
  const meta = parseRunMeta(value.meta);
  const configSnapshot = parseScenarioConfig(value.config_snapshot);
  const currentMetric = parseMetricPoint(value.current_metric);
  const laneSummary = parseLaneSummary(value.lane_summary);
  const actionCounts = parseActionCounts(value.action_counts);
  if (
    !meta ||
    !configSnapshot ||
    !currentMetric ||
    !laneSummary ||
    !actionCounts ||
    !isReleasedScenarioName(value.scenario) ||
    !isInteger(value.seed) ||
    !isInteger(value.turn) ||
    !isInteger(value.event_record_count) ||
    !isInteger(value.evidence_record_count) ||
    !isInteger(value.sanction_event_count)
  ) {
    return null;
  }
  return {
    schema: ODEU_RUN_SUMMARY_SCHEMA,
    meta,
    config_snapshot: configSnapshot,
    scenario: value.scenario,
    seed: value.seed,
    turn: value.turn,
    current_metric: currentMetric,
    lane_summary: laneSummary,
    action_counts: actionCounts,
    event_record_count: value.event_record_count,
    evidence_record_count: value.evidence_record_count,
    sanction_event_count: value.sanction_event_count,
  };
}

function parseRunMeta(value: unknown): OdeuRunMeta | null {
  if (!isJsonRecord(value)) return null;
  if (
    !isReleasedScenarioName(value.scenario) ||
    !isInteger(value.seed) ||
    !isInteger(value.turn) ||
    typeof value.regime_label !== "string"
  ) {
    return null;
  }
  return {
    scenario: value.scenario,
    seed: value.seed,
    turn: value.turn,
    regime_label: value.regime_label,
  };
}

function parseScenarioConfig(value: unknown): OdeuScenarioConfig | null {
  if (!isJsonRecord(value) || value.schema !== "adeu_odeu_scenario_config@1") return null;
  if (
    !isReleasedScenarioName(value.name) ||
    typeof value.description !== "string" ||
    !isInteger(value.num_agents) ||
    !isNumber(value.scarcity) ||
    !isNumber(value.regeneration_rate) ||
    !isNumber(value.misinformation) ||
    !isNumber(value.verification_capacity) ||
    !isNumber(value.enforcement_capacity) ||
    !isNumber(value.sanction_severity) ||
    !isNumber(value.initial_legitimacy) ||
    !isNumber(value.initial_operativity) ||
    !isNumber(value.sanction_consistency) ||
    !isNumber(value.archive_capacity) ||
    !isNumber(value.appeal_availability) ||
    !isNumber(value.public_epistemics_level) ||
    typeof value.ai_mode !== "string" ||
    !isNumber(value.ai_reliability) ||
    !isNumber(value.cooperator_share) ||
    !isNumber(value.opportunist_share) ||
    !isNumber(value.auditor_share) ||
    !isNumber(value.official_share) ||
    !isNumber(value.ai_dependent_share) ||
    !isInteger(value.max_turns)
  ) {
    return null;
  }
  return {
    schema: "adeu_odeu_scenario_config@1",
    name: value.name,
    description: value.description,
    num_agents: value.num_agents,
    scarcity: value.scarcity,
    regeneration_rate: value.regeneration_rate,
    misinformation: value.misinformation,
    verification_capacity: value.verification_capacity,
    enforcement_capacity: value.enforcement_capacity,
    sanction_severity: value.sanction_severity,
    initial_legitimacy: value.initial_legitimacy,
    initial_operativity: value.initial_operativity,
    sanction_consistency: value.sanction_consistency,
    archive_capacity: value.archive_capacity,
    appeal_availability: value.appeal_availability,
    public_epistemics_level: value.public_epistemics_level,
    ai_mode: value.ai_mode,
    ai_reliability: value.ai_reliability,
    cooperator_share: value.cooperator_share,
    opportunist_share: value.opportunist_share,
    auditor_share: value.auditor_share,
    official_share: value.official_share,
    ai_dependent_share: value.ai_dependent_share,
    max_turns: value.max_turns,
  };
}

function parseMetricPoint(value: unknown): OdeuMetricPoint | null {
  if (!isJsonRecord(value) || value.schema !== "adeu_odeu_metric_point@1") return null;
  if (
    !isInteger(value.turn) ||
    !isNumber(value.cooperation_rate) ||
    !isNumber(value.commons_health) ||
    !isNumber(value.average_belief_accuracy) ||
    !isNumber(value.epistemic_integrity) ||
    !isNumber(value.institution_legitimacy) ||
    !isNumber(value.institution_operativity) ||
    !isNumber(value.symbolic_gap) ||
    !isNumber(value.sanction_consistency) ||
    !isNumber(value.utility_concentration) ||
    !isNumber(value.trust_fragmentation) ||
    typeof value.regime_label !== "string"
  ) {
    return null;
  }
  return {
    schema: "adeu_odeu_metric_point@1",
    turn: value.turn,
    cooperation_rate: value.cooperation_rate,
    commons_health: value.commons_health,
    average_belief_accuracy: value.average_belief_accuracy,
    epistemic_integrity: value.epistemic_integrity,
    institution_legitimacy: value.institution_legitimacy,
    institution_operativity: value.institution_operativity,
    symbolic_gap: value.symbolic_gap,
    sanction_consistency: value.sanction_consistency,
    utility_concentration: value.utility_concentration,
    trust_fragmentation: value.trust_fragmentation,
    regime_label: value.regime_label,
  };
}

function parseLaneSummary(value: unknown): OdeuLaneSummary | null {
  if (!isJsonRecord(value)) return null;
  const keys = Object.keys(value);
  if (
    keys.length !== 3 ||
    keys[0] !== "mean_legitimacy_belief" ||
    keys[1] !== "mean_uncertainty" ||
    keys[2] !== "mean_resources"
  ) {
    return null;
  }
  if (
    !isNumber(value.mean_legitimacy_belief) ||
    !isNumber(value.mean_uncertainty) ||
    !isNumber(value.mean_resources)
  ) {
    return null;
  }
  return {
    mean_legitimacy_belief: value.mean_legitimacy_belief,
    mean_uncertainty: value.mean_uncertainty,
    mean_resources: value.mean_resources,
  };
}

function parseActionCounts(value: unknown): Record<string, number> | null {
  if (!isJsonRecord(value)) return null;
  const entries = Object.entries(value);
  const keys = entries.map(([key]) => key);
  if (JSON.stringify(keys) !== JSON.stringify([...keys].sort())) {
    return null;
  }
  const counts: Record<string, number> = {};
  for (const [key, entryValue] of entries) {
    if (!isInteger(entryValue) || entryValue <= 0) return null;
    counts[key] = entryValue;
  }
  return counts;
}

function isJsonRecord(value: unknown): value is JsonRecord {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function isApiRequestStatus(value: unknown): value is OdeuApiRequestStatus {
  return typeof value === "string" && API_REQUEST_STATUS_VALUES.includes(value as OdeuApiRequestStatus);
}

function isReleasedScenarioName(value: unknown): value is OdeuScenarioName {
  return typeof value === "string" && RELEASED_SCENARIO_NAMES.includes(value as OdeuScenarioName);
}

function isNumber(value: unknown): value is number {
  return typeof value === "number" && Number.isFinite(value);
}

function isInteger(value: unknown): value is number {
  return typeof value === "number" && Number.isInteger(value);
}

function isSha256(value: unknown): value is string {
  return typeof value === "string" && /^[a-f0-9]{64}$/.test(value);
}
