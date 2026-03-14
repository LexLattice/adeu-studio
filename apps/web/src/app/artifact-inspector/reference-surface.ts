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
const V36C_FIXTURE_ROOT = path.join(UX_GOVERNANCE_FIXTURE_ROOT, "vnext_plus63");
const CANONICAL_REFERENCE_PROFILE_ID = "artifact_inspector_reference";
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
type RenderedProvenanceTarget = (typeof REQUIRED_PROVENANCE_TARGETS)[number];
type RenderedBindingTarget = (typeof REQUIRED_BINDING_TARGETS)[number];

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

type LaneClusterRendering = {
  cluster_ids: string[];
  lane_id: string;
};

export type RenderedReferenceSurfaceContract = ReferenceIdentity & {
  commit_boundary_id: string;
  commit_boundary_notice: string;
  diagnostics_lane_mode: string;
  diagnostics_lane_notice: string;
  diagnostics_lane_read_only_notice: string;
  epistemic_state_descriptions: Record<string, string>;
  lane_cluster_rendering: LaneClusterRendering[];
  rendered_binding_exposures: Record<RenderedBindingTarget, string[]>;
  rendered_provenance_exposures: Record<RenderedProvenanceTarget, string[]>;
  rendered_surface_snapshot_kind: string;
  route_id: string;
  route_path: string;
  route_payload_parity_mode: string;
  schema: string;
  truth_source_notice: string;
  truth_source_policy: string;
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
  clustersByLaneId: Map<string, ProjectionActionCluster[]>;
  domainPacket: UXDomainPacket;
  glossary: SameContextReachabilityGlossary;
  identity: ReferenceIdentity;
  interactionContract: UXInteractionContract;
  interactionsByClusterId: Map<string, UXInteractionEntry[]>;
  morphIr: UXMorphIR;
  projection: UXSurfaceProjection;
  renderedSurfaceContract: RenderedReferenceSurfaceContract;
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
  renderedSurfaceContract: RenderedReferenceSurfaceContract,
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
    [renderedSurfaceContract, "v36c_rendered_reference_surface_contract@1"],
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

function assertDefinedExposureTargets(
  label: string,
  actual: Record<string, string[]>,
  expected: readonly string[],
): void {
  assertMinimumCoverage(label, Object.keys(actual), expected);
  for (const [target, refs] of Object.entries(actual)) {
    if (refs.length === 0) {
      throw new Error(`${label} defines "${target}" without any rendered target refs`);
    }
  }
}

function assertExposureRefsPresent(
  label: string,
  actualRefs: readonly string[],
  expectedRefs: Iterable<string>,
): void {
  assertMinimumCoverage(label, actualRefs, [...expectedRefs]);
}

function assertLaneClusterRendering(
  clustersByLaneId: Map<string, ProjectionActionCluster[]>,
  renderedSurfaceContract: RenderedReferenceSurfaceContract,
): void {
  for (const clusterRendering of renderedSurfaceContract.lane_cluster_rendering) {
    const actual = (clustersByLaneId.get(clusterRendering.lane_id) ?? []).map(
      (cluster) => cluster.cluster_id,
    );
    if (JSON.stringify(actual) !== JSON.stringify(clusterRendering.cluster_ids)) {
      throw new Error(
        `rendered lane cluster mapping drifted for "${clusterRendering.lane_id}"`,
      );
    }
  }
}

function buildClustersByLaneId(
  actionClusters: ProjectionActionCluster[],
): Map<string, ProjectionActionCluster[]> {
  const clustersByLaneId = new Map<string, ProjectionActionCluster[]>();
  for (const cluster of actionClusters) {
    const existing = clustersByLaneId.get(cluster.lane_id) ?? [];
    existing.push(cluster);
    clustersByLaneId.set(cluster.lane_id, existing);
  }
  return clustersByLaneId;
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
    renderedSurfaceContract,
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
    readJsonFixture<RenderedReferenceSurfaceContract>(
      V36C_FIXTURE_ROOT,
      "v36c_rendered_reference_surface_contract.json",
    ),
  ]);

  const identity = assertSharedIdentity(
    domainPacket,
    morphIr,
    projection,
    interactionContract,
    renderedSurfaceContract,
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

  assertDefinedExposureTargets(
    "rendered provenance hook targets",
    renderedSurfaceContract.rendered_provenance_exposures,
    REQUIRED_PROVENANCE_TARGETS,
  );
  assertExposureRefsPresent(
    "rendered region exposure refs",
    renderedSurfaceContract.rendered_provenance_exposures.rendered_regions,
    projection.regions.map((region) => region.region_id),
  );
  assertExposureRefsPresent(
    "authority-bearing control exposure refs",
    renderedSurfaceContract.rendered_provenance_exposures.authority_bearing_controls,
    interactionContract.interaction_entries
      .filter((interaction) => interaction.authoritative || interaction.gated || interaction.approval_bearing)
      .map((interaction) => interaction.interaction_id),
  );
  assertExposureRefsPresent(
    "evidence-bearing region exposure refs",
    renderedSurfaceContract.rendered_provenance_exposures.evidence_bearing_regions,
    [
      ...projection.evidence_before_commit.required_evidence_region_ids,
      ...projection.evidence_before_commit.required_evidence_lane_ids,
    ],
  );
  assertExposureRefsPresent(
    "state distinction surface exposure refs",
    renderedSurfaceContract.rendered_provenance_exposures.state_distinction_surfaces,
    projection.state_surfaces.map((surface) => surface.surface_id),
  );
  assertExposureRefsPresent(
    "explicit commit boundary exposure refs",
    renderedSurfaceContract.rendered_provenance_exposures.explicit_commit_or_handoff_boundary,
    [renderedSurfaceContract.commit_boundary_id],
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
    Object.keys(renderedSurfaceContract.rendered_binding_exposures),
    REQUIRED_BINDING_TARGETS,
  );
  assertExposureRefsPresent(
    "commit or approval gate exposure refs",
    renderedSurfaceContract.rendered_binding_exposures.commit_or_approval_gates,
    ["open-commit-review", "submit-commit-request", "submit-commit-request-disabled"],
  );
  assertExposureRefsPresent(
    "advisory vs authoritative action exposure refs",
    renderedSurfaceContract.rendered_binding_exposures.advisory_vs_authoritative_actions,
    interactionContract.interaction_entries.map((interaction) => interaction.interaction_id),
  );
  assertExposureRefsPresent(
    "disabled gated state exposure refs",
    renderedSurfaceContract.rendered_binding_exposures.disabled_or_unavailable_gated_states,
    ["submit-commit-request-disabled"],
  );
  assertExposureRefsPresent(
    "required evidence reachability anchor exposure refs",
    renderedSurfaceContract.rendered_binding_exposures.required_evidence_reachability_anchors,
    projection.implementation_observable_bindings
      .filter((binding) => binding.target_kind === "required_evidence_reachability_anchor")
      .map((binding) => binding.target_ref.split(":").slice(1).join(":")),
  );
  assertExposureRefsPresent(
    "salience-bearing surface exposure refs",
    renderedSurfaceContract.rendered_binding_exposures.salience_bearing_warning_status_and_diagnostic_surfaces,
    projection.implementation_observable_bindings
      .filter((binding) =>
        ["warning_surface", "status_surface", "diagnostic_surface"].includes(binding.target_kind),
      )
      .map((binding) => binding.target_ref.split(":").slice(1).join(":")),
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

  const clustersByLaneId = buildClustersByLaneId(projection.action_clusters);
  assertLaneClusterRendering(clustersByLaneId, renderedSurfaceContract);
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
    clustersByLaneId,
    domainPacket,
    glossary,
    identity,
    interactionContract,
    interactionsByClusterId,
    morphIr,
    projection,
    renderedSurfaceContract,
    regions: sortByPlacement(projection.regions),
    routeId: renderedSurfaceContract.route_id,
    routePath: renderedSurfaceContract.route_path,
    targetIndex,
  };
}
