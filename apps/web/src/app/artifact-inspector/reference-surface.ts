import { readFile } from "node:fs/promises";
import path from "node:path";

const UX_GOVERNANCE_FIXTURE_ROOT = path.resolve(
  process.cwd(),
  "..",
  "api",
  "fixtures",
  "ux_governance",
);
const V36A_FIXTURE_ROOT = path.join(UX_GOVERNANCE_FIXTURE_ROOT, "vnext_plus61");
const V36B_FIXTURE_ROOT = path.join(UX_GOVERNANCE_FIXTURE_ROOT, "vnext_plus62");
const CANONICAL_REFERENCE_PROFILE_ID = "artifact_inspector_reference";
const ROUTE_PATH = "/artifact-inspector";
const ROUTE_ID = "artifact_inspector_reference_surface";
const REQUIRED_PROVENANCE_TARGETS = [
  "rendered_regions",
  "authority_bearing_controls",
  "evidence_bearing_regions",
  "state_distinction_surfaces",
  "explicit_commit_or_handoff_boundary",
] as const;
const REQUIRED_BINDING_TARGETS = [
  "commit_or_approval_gates",
  "advisory_vs_authoritative_actions",
  "disabled_or_unavailable_gated_states",
  "required_evidence_reachability_anchors",
  "salience_bearing_warning_status_and_diagnostic_surfaces",
] as const;

type ReferenceIdentity = {
  approved_profile_id: string;
  reference_instance_id: string;
  reference_surface_family: string;
};

type AuthorityBoundaryPolicy = {
  no_free_form_ui_codegen_without_ir: boolean;
  no_visual_authority_inflation: boolean;
  ui_artifacts_may_express_but_may_not_mint_authority: boolean;
};

type UXDomainPacket = ReferenceIdentity & {
  authority_boundary_policy: AuthorityBoundaryPolicy;
  interaction_mode: string;
  primary_user_archetype: string;
  required_evidence_visibility: string[];
  risk_level: string;
  tasks: string[];
  trust_sensitivity: string;
  utility_ranking: string[];
};

type UXMorphIR = ReferenceIdentity & {
  authority_boundary_policy: AuthorityBoundaryPolicy;
  context: {
    device_class: string;
    interaction_mode: string;
    primary_user_archetype: string;
    risk_level: string;
    trust_sensitivity: string;
  };
  deontics: {
    forbidden: string[];
    required: string[];
  };
  epistemics: {
    knowledge_states: string[];
    visibility_rules: string[];
  };
  invariants: string[];
  morph_axes: Record<string, string>;
  surface_compilation_units: string[];
  utility: {
    objectives: string[];
    priority_order: string[];
  };
};

type ApprovedProfileTable = {
  alternate_lawful_profile_id: string;
  canonical_reference_profile_id: string;
  profiles: Array<{
    label: string;
    morph_axes: Record<string, string>;
    profile_id: string;
  }>;
  reference_surface_family: string;
};

type SameContextReachabilityGlossary = {
  commit_or_destructive_barrier: string[];
  context_break: string[];
  forbidden_barrier: string[];
  reference_surface_family: string;
  same_context_reachable: string[];
};

type ProjectionRegion = {
  lane_ids: string[];
  placement_index: number;
  region_id: string;
  region_kind: string;
};

type ProjectionLane = {
  lane_id: string;
  lane_role: string;
  placement_index: number;
  region_id: string;
};

type ProjectionActionCluster = {
  authority_posture: string;
  cluster_id: string;
  cluster_kind: string;
  lane_id: string;
  primary_cluster: boolean;
};

type ProjectionStateSurface = {
  lane_id: string;
  surface_id: string;
  surface_kind: string;
};

type BindingEntry = {
  binding_id: string;
  binding_token: string;
  source_path: string;
  source_schema: string;
  target_kind: string;
  target_ref: string;
};

type ProvenanceHookEntry = {
  hook_id: string;
  source_path: string;
  source_schema: string;
  target_kind: string;
  target_ref: string;
};

type UXSurfaceProjection = ReferenceIdentity & {
  action_clusters: ProjectionActionCluster[];
  authority_boundary_policy: AuthorityBoundaryPolicy;
  bounded_workbench_id: string;
  evidence_before_commit: {
    commit_or_destructive_action_required: boolean;
    required_evidence_lane_ids: string[];
    required_evidence_region_ids: string[];
    route_change_required: boolean;
    same_context_reachability_glossary: SameContextReachabilityGlossary & {
      schema: string;
    };
  };
  implementation_observable_bindings: BindingEntry[];
  lanes: ProjectionLane[];
  regions: ProjectionRegion[];
  responsive_behaviors: string[];
  stable_provenance_hooks: ProvenanceHookEntry[];
  state_surfaces: ProjectionStateSurface[];
  surface_compilation_units: string[];
};

type UXInteractionEntry = {
  action_cluster_id: string;
  approval_bearing: boolean;
  authoritative: boolean;
  authoritative_gate_source?: {
    source_kind: string;
    source_ref: string;
  };
  committing: boolean;
  confirmation_required: boolean;
  evidence_required: boolean;
  failure_surface: string;
  gated: boolean;
  interaction_id: string;
  preconditions: string[];
  requested_runtime_effect: {
    descriptive_only: boolean;
    effect_kind: string;
  };
  reversible: boolean;
  rollback_path: string;
  runtime_visible_consequence: {
    outcome_kind: string;
    truth_posture: string;
  };
  success_surface: string;
  surface_event: string;
  ui_transition: string;
  user_visible_consequence: string;
};

type UXInteractionContract = ReferenceIdentity & {
  authority_boundary_policy: AuthorityBoundaryPolicy;
  implementation_observable_bindings: BindingEntry[];
  interaction_entries: UXInteractionEntry[];
  stable_provenance_hooks: ProvenanceHookEntry[];
};

type TargetMetadata = {
  bindingIds: string[];
  bindingKinds: string[];
  bindingTokens: string[];
  hookIds: string[];
  hookKinds: string[];
};

export type ReferenceSurfaceBundle = {
  approvedProfileTable: ApprovedProfileTable;
  domainPacket: UXDomainPacket;
  glossary: SameContextReachabilityGlossary;
  identity: ReferenceIdentity;
  interactionContract: UXInteractionContract;
  interactionsByClusterId: Map<string, UXInteractionEntry[]>;
  morphIr: UXMorphIR;
  projection: UXSurfaceProjection;
  regions: ProjectionRegion[];
  routeId: string;
  routePath: string;
  targetIndex: Map<string, TargetMetadata>;
};

function requireFieldEquality(
  field: keyof ReferenceIdentity,
  expected: string,
  candidate: ReferenceIdentity,
  label: string,
): void {
  if (candidate[field] !== expected) {
    throw new Error(
      `${label} drifted ${field}: expected "${expected}" but received "${candidate[field]}"`,
    );
  }
}

function assertSharedIdentity(
  domainPacket: UXDomainPacket,
  morphIr: UXMorphIR,
  projection: UXSurfaceProjection,
  interactionContract: UXInteractionContract,
  approvedProfileTable: ApprovedProfileTable,
  glossary: SameContextReachabilityGlossary,
): ReferenceIdentity {
  const identity: ReferenceIdentity = {
    approved_profile_id: domainPacket.approved_profile_id,
    reference_instance_id: domainPacket.reference_instance_id,
    reference_surface_family: domainPacket.reference_surface_family,
  };
  const candidates: Array<[ReferenceIdentity, string]> = [
    [morphIr, "ux_morph_ir@1"],
    [projection, "ux_surface_projection@1"],
    [interactionContract, "ux_interaction_contract@1"],
  ];

  for (const [candidate, label] of candidates) {
    requireFieldEquality("reference_surface_family", identity.reference_surface_family, candidate, label);
    requireFieldEquality("reference_instance_id", identity.reference_instance_id, candidate, label);
    requireFieldEquality("approved_profile_id", identity.approved_profile_id, candidate, label);
  }

  if (approvedProfileTable.reference_surface_family !== identity.reference_surface_family) {
    throw new Error("approved profile table does not match the rendered reference surface family");
  }
  if (glossary.reference_surface_family !== identity.reference_surface_family) {
    throw new Error("same-context glossary does not match the rendered reference surface family");
  }

  return identity;
}

function assertCanonicalReferenceProfile(
  identity: ReferenceIdentity,
  approvedProfileTable: ApprovedProfileTable,
): void {
  if (identity.approved_profile_id !== CANONICAL_REFERENCE_PROFILE_ID) {
    throw new Error("rendered route must use the canonical V36-A reference profile");
  }
  if (approvedProfileTable.canonical_reference_profile_id !== CANONICAL_REFERENCE_PROFILE_ID) {
    throw new Error("approved profile table canonical profile drifted");
  }
  if (!approvedProfileTable.profiles.some((profile) => profile.profile_id === identity.approved_profile_id)) {
    throw new Error("rendered reference profile is not present in the V36-A approved profile table");
  }
}

function assertAuthorityBoundaryPolicy(
  domainPacket: UXDomainPacket,
  morphIr: UXMorphIR,
  projection: UXSurfaceProjection,
  interactionContract: UXInteractionContract,
): void {
  const policies = [
    domainPacket.authority_boundary_policy,
    morphIr.authority_boundary_policy,
    projection.authority_boundary_policy,
    interactionContract.authority_boundary_policy,
  ];
  if (
    !policies.every(
      (policy) =>
        policy.no_free_form_ui_codegen_without_ir &&
        policy.no_visual_authority_inflation &&
        policy.ui_artifacts_may_express_but_may_not_mint_authority,
    )
  ) {
    throw new Error("authority boundary policy drifted from the accepted V36 substrate");
  }
}

function assertMinimumCoverage(
  label: string,
  actual: Iterable<string>,
  required: readonly string[],
): void {
  const actualSet = new Set(actual);
  for (const requiredValue of required) {
    if (!actualSet.has(requiredValue)) {
      throw new Error(`${label} is missing required target "${requiredValue}"`);
    }
  }
}

function buildTargetIndex(
  ...collections: Array<{
    bindings: BindingEntry[];
    hooks: ProvenanceHookEntry[];
  }>
): Map<string, TargetMetadata> {
  const index = new Map<string, TargetMetadata>();

  const ensure = (targetRef: string): TargetMetadata => {
    const existing = index.get(targetRef);
    if (existing) return existing;
    const created: TargetMetadata = {
      bindingIds: [],
      bindingKinds: [],
      bindingTokens: [],
      hookIds: [],
      hookKinds: [],
    };
    index.set(targetRef, created);
    return created;
  };

  for (const collection of collections) {
    for (const binding of collection.bindings) {
      const target = ensure(binding.target_ref);
      target.bindingIds.push(binding.binding_id);
      target.bindingKinds.push(binding.target_kind);
      target.bindingTokens.push(binding.binding_token);
    }
    for (const hook of collection.hooks) {
      const target = ensure(hook.target_ref);
      target.hookIds.push(hook.hook_id);
      target.hookKinds.push(hook.target_kind);
    }
  }

  return index;
}

function sortByPlacement<T extends { placement_index: number }>(items: T[]): T[] {
  return items
    .slice()
    .sort((left, right) => left.placement_index - right.placement_index);
}

async function readJsonFixture<T>(...segments: string[]): Promise<T> {
  const content = await readFile(path.join(...segments), "utf8");
  return JSON.parse(content) as T;
}

export async function loadReferenceSurfaceBundle(): Promise<ReferenceSurfaceBundle> {
  const [
    approvedProfileTable,
    glossary,
    domainPacket,
    morphIr,
    projection,
    interactionContract,
  ] = await Promise.all([
    readJsonFixture<ApprovedProfileTable>(V36A_FIXTURE_ROOT, "v36a_first_family_approved_profile_table.json"),
    readJsonFixture<SameContextReachabilityGlossary>(V36A_FIXTURE_ROOT, "v36a_same_context_reachability_glossary.json"),
    readJsonFixture<UXDomainPacket>(V36A_FIXTURE_ROOT, "ux_domain_packet_artifact_inspector_reference.json"),
    readJsonFixture<UXMorphIR>(V36A_FIXTURE_ROOT, "ux_morph_ir_artifact_inspector_reference.json"),
    readJsonFixture<UXSurfaceProjection>(V36B_FIXTURE_ROOT, "ux_surface_projection_artifact_inspector_reference.json"),
    readJsonFixture<UXInteractionContract>(
      V36B_FIXTURE_ROOT,
      "ux_interaction_contract_artifact_inspector_reference.json",
    ),
  ]);

  const identity = assertSharedIdentity(
    domainPacket,
    morphIr,
    projection,
    interactionContract,
    approvedProfileTable,
    glossary,
  );

  assertCanonicalReferenceProfile(identity, approvedProfileTable);
  assertAuthorityBoundaryPolicy(domainPacket, morphIr, projection, interactionContract);

  if (projection.evidence_before_commit.route_change_required) {
    throw new Error("reference surface cannot require a route change before required evidence");
  }
  if (projection.evidence_before_commit.commit_or_destructive_action_required) {
    throw new Error("reference surface cannot require a commit or destructive action before evidence");
  }
  if (
    JSON.stringify(projection.evidence_before_commit.same_context_reachability_glossary) !==
    JSON.stringify({
      ...glossary,
      schema: projection.evidence_before_commit.same_context_reachability_glossary.schema,
    })
  ) {
    throw new Error("projection glossary drifted from the accepted V36-A glossary");
  }

  assertMinimumCoverage(
    "rendered provenance hook targets",
    [
      "rendered_regions",
      "authority_bearing_controls",
      "evidence_bearing_regions",
      "state_distinction_surfaces",
      "explicit_commit_or_handoff_boundary",
    ],
    REQUIRED_PROVENANCE_TARGETS,
  );
  assertMinimumCoverage(
    "projection provenance hook target kinds",
    projection.stable_provenance_hooks.map((hook) => hook.target_kind),
    ["projection_unit", "evidence_bearing_region", "state_distinction_surface"],
  );
  assertMinimumCoverage(
    "interaction provenance hook target kinds",
    interactionContract.stable_provenance_hooks.map((hook) => hook.target_kind),
    ["action_cluster", "authority_bearing_control"],
  );
  assertMinimumCoverage(
    "rendered implementation binding targets",
    [
      "commit_or_approval_gates",
      "advisory_vs_authoritative_actions",
      "disabled_or_unavailable_gated_states",
      "required_evidence_reachability_anchors",
      "salience_bearing_warning_status_and_diagnostic_surfaces",
    ],
    REQUIRED_BINDING_TARGETS,
  );
  assertMinimumCoverage(
    "projection binding target kinds",
    projection.implementation_observable_bindings.map((binding) => binding.target_kind),
    [
      "required_evidence_reachability_anchor",
      "warning_surface",
      "status_surface",
      "diagnostic_surface",
    ],
  );
  assertMinimumCoverage(
    "interaction binding target kinds",
    interactionContract.implementation_observable_bindings.map((binding) => binding.target_kind),
    [
      "advisory_action",
      "authoritative_action",
      "commit_or_approval_gate",
      "disabled_or_unavailable_gated_state",
    ],
  );

  const interactionsByClusterId = new Map<string, UXInteractionEntry[]>();
  for (const interaction of interactionContract.interaction_entries) {
    const existing = interactionsByClusterId.get(interaction.action_cluster_id) ?? [];
    existing.push(interaction);
    interactionsByClusterId.set(interaction.action_cluster_id, existing);
  }

  const targetIndex = buildTargetIndex(
    {
      bindings: projection.implementation_observable_bindings,
      hooks: projection.stable_provenance_hooks,
    },
    {
      bindings: interactionContract.implementation_observable_bindings,
      hooks: interactionContract.stable_provenance_hooks,
    },
  );

  return {
    approvedProfileTable,
    domainPacket,
    glossary,
    identity,
    interactionContract,
    interactionsByClusterId,
    morphIr,
    projection,
    regions: sortByPlacement(projection.regions),
    routeId: ROUTE_ID,
    routePath: ROUTE_PATH,
    targetIndex,
  };
}
