/*
 * GENERATED FILE — do not edit by hand.
 *
 * Regenerate:
 *   cd apps/web
 *   npm run gen:types
 */

/**
 * NormStatement.id targets
 */
export type AppliesTo = string[];
export type Kind = "text_only" | "predicate";
export type Predicate = string | null;
export type Text = string;
export type Effect = "defeats" | "narrows" | "clarifies";
export type Id = string;
/**
 * E.g., 'MSA-2026#§3.2' or 'doc123#clause17'
 */
export type DocRef = string | null;
export type Quote = string | null;
export type End = number;
export type Start = number;
export type Exceptions = ExceptionClause[];
export type Object = (EntityRef | DefinitionRef | DocRef1 | TextRef) | null;
export type EntityId = string;
export type RefType = "entity";
export type DefId = string;
export type RefType1 = "def";
export type DocRef2 = string;
export type RefType2 = "doc";
export type RefType3 = "text";
export type Text1 = string;
export type Qualifiers = string[];
export type Verb = string;
export type Kind1 = "text_only" | "predicate";
export type Predicate1 = string | null;
export type Text2 = string;
export type Id1 = string;
export type Kind2 = "obligation" | "prohibition" | "permission";
export type Jurisdiction = string;
export type End1 = string | null;
export type Kind3 = "between" | "before" | "after" | "at" | "during" | "unspecified";
export type Start1 = string | null;
export type Subject = EntityRef | DefinitionRef | DocRef1 | TextRef;
export type Statements = NormStatement[];
export type Id2 = string;
export type Kind4 = "mechanism" | "resource_limit" | "invariant" | "law" | "assumption";
export type Statement = string;
export type Constraints = DPhysConstraint[];
export type Id3 = string;
export type Kind5 = "obs" | "def" | "testimony" | "infer";
export type Statement1 = string;
export type Claims = EvidenceClaim[];
export type Id4 = string;
export type Meaning = string;
export type Term = string;
export type Definitions = Definition[];
export type Id5 = string;
/**
 * party|role|org|person|system|other
 */
export type Kind6 = string | null;
export type Name = string;
export type Entities = Entity[];
export type Id6 = string;
export type Kind7 = "moral" | "pref" | "policy" | "valence";
export type Statement2 = string;
export type Goals = Goal[];
export type Id7 = string;
export type Issue = string;
export type Effect1 = string;
export type Label = string;
export type OptionId = string;
export type From = string | null;
export type Op = "add" | "remove" | "replace" | "move" | "copy" | "test";
export type Path = string;
export type Patch = JsonPatchOp[];
export type VariantIrId = string | null;
export type Options = AmbiguityOption[];
export type Ambiguity = Ambiguity1[];
export type AuthorityRef = string | null;
export type BridgeType = "interpretation" | "u_to_dnorm" | "u_to_e" | "e_to_dnorm" | "o_to_dnorm";
export type CalibrationTag = string | null;
export type FromChannel = "O" | "D_phys" | "D_norm" | "E" | "U";
export type Id8 = string;
export type JustificationText = string;
export type Status = "provisional" | "certified" | "revoked";
export type ToChannel = "O" | "D_phys" | "D_norm" | "E" | "U";
export type Kind8 = "authority_doc" | "calibration" | "experiment_log" | "policy";
export type Ref = string;
export type Bridges = Bridge[];
export type DocId = string;
export type Jurisdiction1 = string;
export type TimeEval = string;
export type IrId = string;
export type SchemaVersion = "adeu.ir.v0";

export interface AdeuIR {
  D_norm?: DNormChannel;
  D_phys?: DPhysChannel;
  E?: EChannel;
  O?: OChannel;
  U?: UChannel;
  ambiguity?: Ambiguity;
  bridges?: Bridges;
  context: Context;
  ir_id: IrId;
  schema_version?: SchemaVersion;
}
export interface DNormChannel {
  exceptions?: Exceptions;
  statements?: Statements;
}
export interface ExceptionClause {
  applies_to: AppliesTo;
  condition: ExceptionCondition;
  effect: Effect;
  id: Id;
  provenance: ProvenanceRef;
}
export interface ExceptionCondition {
  kind: Kind;
  predicate?: Predicate;
  text: Text;
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
export interface NormStatement {
  action: Action;
  condition?: NormCondition | null;
  id: Id1;
  kind: Kind2;
  provenance: ProvenanceRef;
  scope: Scope;
  subject: Subject;
}
export interface Action {
  object?: Object;
  qualifiers?: Qualifiers;
  verb: Verb;
}
export interface EntityRef {
  entity_id: EntityId;
  ref_type?: RefType;
}
export interface DefinitionRef {
  def_id: DefId;
  ref_type?: RefType1;
}
export interface DocRef1 {
  doc_ref: DocRef2;
  ref_type?: RefType2;
}
export interface TextRef {
  ref_type?: RefType3;
  text: Text1;
}
export interface NormCondition {
  kind: Kind1;
  predicate?: Predicate1;
  text: Text2;
}
export interface Scope {
  jurisdiction: Jurisdiction;
  time_about: TimeScope;
}
export interface TimeScope {
  end?: End1;
  kind: Kind3;
  start?: Start1;
}
export interface DPhysChannel {
  constraints?: Constraints;
}
export interface DPhysConstraint {
  id: Id2;
  kind: Kind4;
  provenance?: ProvenanceRef | null;
  statement: Statement;
}
export interface EChannel {
  claims?: Claims;
}
export interface EvidenceClaim {
  id: Id3;
  kind: Kind5;
  provenance?: ProvenanceRef | null;
  statement: Statement1;
}
export interface OChannel {
  definitions?: Definitions;
  entities?: Entities;
}
export interface Definition {
  id: Id4;
  meaning: Meaning;
  provenance?: ProvenanceRef | null;
  term: Term;
}
export interface Entity {
  id: Id5;
  kind?: Kind6;
  name: Name;
  provenance?: ProvenanceRef | null;
}
export interface UChannel {
  goals?: Goals;
}
export interface Goal {
  id: Id6;
  kind: Kind7;
  provenance?: ProvenanceRef | null;
  statement: Statement2;
}
export interface Ambiguity1 {
  id: Id7;
  issue: Issue;
  options: Options;
  span: SourceSpan;
}
export interface AmbiguityOption {
  effect: Effect1;
  label: Label;
  option_id: OptionId;
  patch?: Patch;
  variant_ir_id?: VariantIrId;
}
export interface JsonPatchOp {
  from?: From;
  op: Op;
  path: Path;
  value?: unknown;
}
export interface Bridge {
  authority_ref?: AuthorityRef;
  bridge_type: BridgeType;
  calibration_tag?: CalibrationTag;
  from_channel: FromChannel;
  id: Id8;
  justification_text: JustificationText;
  provenance: ProvenanceRef;
  scope?: Scope | null;
  status: Status;
  to_channel: ToChannel;
  validator?: ValidatorRef | null;
}
export interface ValidatorRef {
  kind: Kind8;
  ref: Ref;
}
export interface Context {
  doc_id: DocId;
  jurisdiction: Jurisdiction1;
  time_eval: TimeEval;
}
