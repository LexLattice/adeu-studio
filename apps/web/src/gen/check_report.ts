/*
 * GENERATED FILE — do not edit by hand.
 *
 * Regenerate:
 *   cd apps/web
 *   npm run gen:types
 */

export type NumAmbiguities = number;
export type NumBridges = number;
export type NumExceptions = number;
export type NumStatements = number;
export type ReasonCode =
  | "SCHEMA_INVALID"
  | "UNSUPPORTED_SCHEMA_VERSION"
  | "AMBIGUITY_OPTION_INVALID"
  | "MODALITY_AMBIGUOUS_UNRESOLVED"
  | "BRIDGE_REQUIRED_MISSING"
  | "BRIDGE_INVALID_CHANNEL_PAIR"
  | "BRIDGE_TYPE_UNSUPPORTED"
  | "BRIDGE_U_TO_DNORM_AUTHORITY_MISSING"
  | "BRIDGE_U_TO_E_CALIBRATION_MISSING"
  | "BRIDGE_CERTIFIED_VALIDATOR_MISSING"
  | "SCOPE_JURISDICTION_MISSING"
  | "SCOPE_TIME_MISSING"
  | "SCOPE_TIME_INVALID"
  | "PROVENANCE_MISSING"
  | "AUTHORITY_REF_MISSING"
  | "AUTHORITY_REF_UNPARSABLE"
  | "AUTHORITY_OUT_OF_SCOPE"
  | "NORM_SUBJECT_MISSING"
  | "NORM_ACTION_MISSING"
  | "NORM_SCOPE_MISSING"
  | "CONDITION_UNDISCHARGED"
  | "CONDITION_PREDICATE_INVALID"
  | "DEF_TERM_UNRESOLVED"
  | "DEF_ENTITY_UNRESOLVED"
  | "CONFLICT_OBLIGATION_VS_PROHIBITION"
  | "CONFLICT_OVERLAPPING_SCOPE_UNRESOLVED"
  | "EXCEPTION_ORPHANED"
  | "EXCEPTION_CONDITION_UNEVALUATED"
  | "EXCEPTION_PRECEDENCE_UNDETERMINED"
  | "VALIDATOR_UNKNOWN"
  | "VALIDATOR_TIMEOUT"
  | "VALIDATOR_INVALID_REQUEST"
  | "VALIDATOR_BACKEND_ERROR";
export type JsonPath = string | null;
export type Message = string;
export type ObjectId = string | null;
/**
 * E.g., 'MSA-2026#§3.2' or 'doc123#clause17'
 */
export type DocRef = string | null;
export type Quote = string | null;
export type End = number;
export type Start = number;
export type ReasonSeverity = "ERROR" | "WARN" | "INFO";
export type ReasonCodes = CheckReason[];
export type Status = "PASS" | "WARN" | "REFUSE";
export type AffectedIds = string[];
export type Because = string[];
export type Notes = string | null;
export type RuleId = string;
export type Trace = TraceItem[];

export interface CheckReport {
  metrics: CheckMetrics;
  reason_codes?: ReasonCodes;
  status: Status;
  trace?: Trace;
}
export interface CheckMetrics {
  num_ambiguities: NumAmbiguities;
  num_bridges: NumBridges;
  num_exceptions: NumExceptions;
  num_statements: NumStatements;
}
export interface CheckReason {
  code: ReasonCode;
  json_path?: JsonPath;
  message: Message;
  object_id?: ObjectId;
  provenance?: ProvenanceRef | null;
  severity: ReasonSeverity;
}
export interface ProvenanceRef {
  doc_ref?: DocRef;
  quote?: Quote;
  span?: SourceSpan | null;
}
export interface SourceSpan {
  end: End;
  start: Start;
}
export interface TraceItem {
  affected_ids?: AffectedIds;
  because?: Because;
  notes?: Notes;
  rule_id: RuleId;
}
