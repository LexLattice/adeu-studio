import Link from "next/link";

import styles from "./page.module.css";
import { loadReferenceSurfaceBundle } from "./reference-surface";

export const metadata = {
  title: "Artifact Inspector Reference Surface | ADEU Studio",
};
type ReferenceSurfaceBundle = Awaited<ReturnType<typeof loadReferenceSurfaceBundle>>;
const EPISTEMIC_STATE_DESCRIPTIONS: Record<string, string> = {
  authoritative: "Accepted truth remains distinct.",
  validated: "Validated but not automatically committing.",
  candidate: "Candidate context stays provisional.",
  draft: "Draft material remains clearly marked.",
  loading: "Loading never renders as success.",
  conflicted: "Conflicts remain surfaced.",
  stale: "Staleness stays visible.",
  ambiguous: "Ambiguity remains explicit.",
};

function humanize(value: string): string {
  return value
    .replace(/[_-]+/g, " ")
    .replace(/\b\w/g, (char) => char.toUpperCase());
}

function getEpistemicStateDescription(state: string): string {
  return EPISTEMIC_STATE_DESCRIPTIONS[state] ?? EPISTEMIC_STATE_DESCRIPTIONS.ambiguous;
}

function toTargetRef(referenceInstanceId: string, localId: string): string {
  return `${referenceInstanceId}:${localId}`;
}

function targetDataAttributes(
  referenceInstanceId: string,
  localId: string,
  targetIndex: ReferenceSurfaceBundle["targetIndex"],
): Record<string, string> {
  const targetRef = toTargetRef(referenceInstanceId, localId);
  const metadata = targetIndex.get(targetRef);
  return {
    "data-target-ref": targetRef,
    ...(metadata?.bindingIds.length
      ? { "data-binding-ids": metadata.bindingIds.join(" ") }
      : {}),
    ...(metadata?.bindingKinds.length
      ? { "data-binding-kinds": metadata.bindingKinds.join(" ") }
      : {}),
    ...(metadata?.bindingTokens.length
      ? { "data-binding-tokens": metadata.bindingTokens.join(" ") }
      : {}),
    ...(metadata?.hookIds.length ? { "data-hook-ids": metadata.hookIds.join(" ") } : {}),
    ...(metadata?.hookKinds.length ? { "data-hook-kinds": metadata.hookKinds.join(" ") } : {}),
  };
}

function renderTokenList(values: string[], accent: "default" | "muted" = "default") {
  return (
    <ul className={styles.tokenList}>
      {values.map((value) => (
        <li
          key={value}
          className={accent === "muted" ? styles.tokenMuted : styles.token}
        >
          {humanize(value)}
        </li>
      ))}
    </ul>
  );
}

type ActionClusterSectionProps = {
  bundle: ReferenceSurfaceBundle;
  clusters: ReferenceSurfaceBundle["projection"]["action_clusters"];
  referenceInstanceId: string;
};

function ActionClusterSection({
  bundle,
  clusters,
  referenceInstanceId,
}: ActionClusterSectionProps) {
  if (clusters.length === 0) return null;

  return (
    <div className={styles.actionClusterList}>
      {clusters.map((cluster) => {
        const interactions = bundle.interactionsByClusterId.get(cluster.cluster_id) ?? [];
        return (
          <article
            key={cluster.cluster_id}
            className={styles.actionCluster}
            data-cluster-id={cluster.cluster_id}
            data-authority-posture={cluster.authority_posture}
            {...targetDataAttributes(
              referenceInstanceId,
              cluster.cluster_id,
              bundle.targetIndex,
            )}
          >
            <div className={styles.clusterHeader}>
              <div>
                <p className={styles.clusterEyebrow}>{humanize(cluster.cluster_kind)}</p>
                <h4>{humanize(cluster.cluster_id)}</h4>
              </div>
              <span className={styles.clusterMarker}>{humanize(cluster.authority_posture)}</span>
            </div>
            <div className={styles.clusterBody}>
              {interactions.map((interaction) => {
                const interactionTarget = targetDataAttributes(
                  referenceInstanceId,
                  interaction.interaction_id,
                  bundle.targetIndex,
                );
                const isDisabledState =
                  interaction.interaction_id === "submit-commit-request"
                    ? targetDataAttributes(
                        referenceInstanceId,
                        "submit-commit-request-disabled",
                        bundle.targetIndex,
                      )
                    : null;
                return (
                  <div
                    key={interaction.interaction_id}
                    className={styles.actionCard}
                    data-interaction-id={interaction.interaction_id}
                    data-authoritative={String(interaction.authoritative)}
                    data-gated={String(interaction.gated)}
                    data-committing={String(interaction.committing)}
                    data-approval-bearing={String(interaction.approval_bearing)}
                    {...interactionTarget}
                  >
                    <div className={styles.actionHeader}>
                      <div>
                        <h5>{humanize(interaction.interaction_id)}</h5>
                        <p className="muted">{humanize(interaction.surface_event)}</p>
                      </div>
                      <span
                        className={
                          interaction.authoritative
                            ? styles.authoritativeMarker
                            : styles.advisoryMarker
                        }
                      >
                        {interaction.authoritative ? "Authoritative gate" : "Advisory"}
                      </span>
                    </div>
                    <dl className={styles.definitionGrid}>
                      <div>
                        <dt>Requested effect</dt>
                        <dd>{humanize(interaction.requested_runtime_effect.effect_kind)}</dd>
                      </div>
                      <div>
                        <dt>Visible consequence</dt>
                        <dd>{humanize(interaction.runtime_visible_consequence.outcome_kind)}</dd>
                      </div>
                      <div>
                        <dt>Truth posture</dt>
                        <dd>{humanize(interaction.runtime_visible_consequence.truth_posture)}</dd>
                      </div>
                      <div>
                        <dt>Transition</dt>
                        <dd>{humanize(interaction.ui_transition)}</dd>
                      </div>
                    </dl>
                    <div>
                      <p className={styles.subtleLabel}>Preconditions</p>
                      {renderTokenList(interaction.preconditions)}
                    </div>
                    {interaction.authoritative_gate_source ? (
                      <p className={styles.gateSource}>
                        Gate source:{" "}
                        <span className="mono">{interaction.authoritative_gate_source.source_kind}</span>{" "}
                        → <span className="mono">{interaction.authoritative_gate_source.source_ref}</span>
                      </p>
                    ) : null}
                    <div className={styles.controlRow}>
                      {interaction.interaction_id === "focus-source-artifact" ? (
                        <a href="#source-lane" className={styles.controlLink}>
                          Shift focus within the bounded workbench
                        </a>
                      ) : (
                        <button type="button" disabled>
                          {humanize(interaction.user_visible_consequence)}
                        </button>
                      )}
                      {isDisabledState ? (
                        <span
                          className={styles.disabledGate}
                          data-interaction-id="submit-commit-request-disabled"
                          {...isDisabledState}
                        >
                          Disabled gated state remains visible until review conditions are met
                        </span>
                      ) : null}
                    </div>
                  </div>
                );
              })}
            </div>
          </article>
        );
      })}
    </div>
  );
}

export default async function ArtifactInspectorReferenceSurfacePage() {
  const bundle = await loadReferenceSurfaceBundle();
  const projection = bundle.projection;
  const interactionContract = bundle.interactionContract;
  const identity = bundle.identity;
  const actionLaneClusters = bundle.clustersByLaneId.get("action-lane") ?? [];
  const workContextLaneClusters = bundle.clustersByLaneId.get("work-context-lane") ?? [];
  const rootTarget = targetDataAttributes(
    identity.reference_instance_id,
    "artifact-inspector-surface-root",
    bundle.targetIndex,
  );

  return (
    <div className={styles.pageShell}>
      <header className={styles.hero}>
        <div>
          <p className={styles.eyebrow}>V36-C / C1 Rendered Reference Surface</p>
          <h1 className={styles.title}>Artifact Inspector Reference Surface</h1>
          <p className={styles.subtitle}>
            One bounded rendered <span className="mono">artifact_inspector_advisory_workbench</span>{" "}
            that consumes the accepted V36-A domain/morph substrate and the accepted V36-B
            projection/interaction pair without minting authority locally.
          </p>
        </div>
        <div className={styles.identityStrip}>
          <div className={styles.identityCard}>
            <span className={styles.identityLabel}>Surface family</span>
            <span className="mono">{identity.reference_surface_family}</span>
          </div>
          <div className={styles.identityCard}>
            <span className={styles.identityLabel}>Reference instance</span>
            <span className="mono">{identity.reference_instance_id}</span>
          </div>
          <div className={styles.identityCard}>
            <span className={styles.identityLabel}>Approved profile</span>
            <span className="mono">{identity.approved_profile_id}</span>
          </div>
        </div>
        <nav className={styles.topNav} aria-label="ADEU studio routes">
          <Link href="/" className="muted">
            ADEU Studio
          </Link>
          <Link href="/artifacts" className="muted">
            Artifacts
          </Link>
          <Link href="/evidence-explorer" className="muted">
            Evidence Explorer
          </Link>
          <Link href="/copilot" className="muted">
            Copilot
          </Link>
        </nav>
      </header>

      <main
        className={styles.workbench}
        data-route-id={bundle.routeId}
        data-route-path={bundle.routePath}
        data-reference-surface-family={identity.reference_surface_family}
        data-reference-instance-id={identity.reference_instance_id}
        data-approved-profile-id={identity.approved_profile_id}
        data-route-payload-parity="presentational_transform_only"
        data-diagnostics-lane-mode="placeholder_or_existing_artifact_backed_read_only_only"
        {...rootTarget}
      >
        <section
          className={`${styles.region} ${styles.navigationRegion}`}
          data-region-id="navigation-region"
          data-region-kind="navigation_region"
        >
          <div className={styles.regionHeader}>
            <div>
              <p className={styles.regionEyebrow}>Bounded Navigation</p>
              <h2>Same-context reachability remains explicit</h2>
            </div>
            <span className={styles.regionMarker}>No route change before evidence</span>
          </div>
          <div className={styles.anchorRow}>
            <a href="#source-lane" className={styles.anchor}>
              Source Artifact
            </a>
            <a href="#work-context-lane" className={styles.anchor}>
              Candidate Context
            </a>
            <a href="#evidence-lane" className={styles.anchor}>
              Evidence Lane
            </a>
            <a href="#commit-boundary" className={styles.anchor}>
              Commit Boundary
            </a>
          </div>
          <div className={styles.glossaryGrid}>
            <article className={styles.glossaryCard}>
              <h3>Same-context reachable</h3>
              {renderTokenList(bundle.glossary.same_context_reachable)}
            </article>
            <article className={styles.glossaryCard}>
              <h3>Context break</h3>
              {renderTokenList(bundle.glossary.context_break, "muted")}
            </article>
            <article className={styles.glossaryCard}>
              <h3>Forbidden barrier</h3>
              {renderTokenList(bundle.glossary.forbidden_barrier, "muted")}
            </article>
            <article className={styles.glossaryCard}>
              <h3>Commit / destructive barrier</h3>
              {renderTokenList(bundle.glossary.commit_or_destructive_barrier, "muted")}
            </article>
          </div>
        </section>

        <section
          className={`${styles.region} ${styles.actionRegion}`}
          data-region-id="action-region"
          data-region-kind="action_region"
        >
          <div className={styles.regionHeader}>
            <div>
              <p className={styles.regionEyebrow}>Advisory / Authoritative Boundary</p>
              <h2>Action lane renders posture without widening authority</h2>
            </div>
            <span className={styles.regionMarker}>UI may express but may not mint authority</span>
          </div>

          <div
            className={styles.lane}
            id="action-lane"
            data-lane-id="action-lane"
            data-lane-role="action_lane"
            data-rendered-cluster-ids={actionLaneClusters.map((cluster) => cluster.cluster_id).join(" ")}
          >
            <div className={styles.laneHeader}>
              <h3>Advisory Action Lane</h3>
              <span className="mono">action-lane</span>
            </div>
            <ActionClusterSection
              bundle={bundle}
              clusters={actionLaneClusters}
              referenceInstanceId={identity.reference_instance_id}
            />
          </div>

          <details
            open
            className={styles.commitBoundary}
            id="commit-boundary"
            data-boundary-kind="explicit_commit_gate"
            {...targetDataAttributes(
              identity.reference_instance_id,
              "submit-commit-request",
              bundle.targetIndex,
            )}
          >
            <summary>Explicit Commit Gate</summary>
            <div className={styles.commitBoundaryBody}>
              <p>
                Commit review is a visible gate. Required evidence and the trust boundary remain in
                the same workbench context before any commit request can be expressed.
              </p>
              <div className={styles.commitActions}>
                <button type="button" disabled>
                  Open Commit Review
                </button>
                <button
                  type="button"
                  disabled
                  {...targetDataAttributes(
                    identity.reference_instance_id,
                    "submit-commit-request-disabled",
                    bundle.targetIndex,
                  )}
                >
                  Submit Commit Request
                </button>
              </div>
              <p className="muted">
                This route is descriptive only. It shows the accepted authoritative boundary and V35
                gate source, but does not execute runtime authority locally.
              </p>
            </div>
          </details>
        </section>

        <section
          className={`${styles.region} ${styles.primaryRegion}`}
          data-region-id="primary-work-region"
          data-region-kind="primary_work_region"
        >
          <div className={styles.regionHeader}>
            <div>
              <p className={styles.regionEyebrow}>Primary Work Region</p>
              <h2>Accepted source substrate and candidate context stay side by side</h2>
            </div>
            <span className={styles.regionMarker}>Split-pane preserved</span>
          </div>

          <article
            className={styles.lane}
            id="source-lane"
            data-lane-id="source-lane"
            data-lane-role="source_lane"
          >
            <div className={styles.laneHeader}>
              <h3>Source Artifact Region</h3>
              <span className="mono">source-lane</span>
            </div>
            <p className={styles.lead}>
              The rendered route is bound to the accepted V36-A substrate and exposes the same
              surface family, reference instance, and canonical profile id directly in the workbench.
            </p>
            <dl className={styles.definitionGrid}>
              <div>
                <dt>Interaction mode</dt>
                <dd>{humanize(bundle.domainPacket.interaction_mode)}</dd>
              </div>
              <div>
                <dt>Primary archetype</dt>
                <dd>{humanize(bundle.domainPacket.primary_user_archetype)}</dd>
              </div>
              <div>
                <dt>Risk level</dt>
                <dd>{humanize(bundle.domainPacket.risk_level)}</dd>
              </div>
              <div>
                <dt>Trust sensitivity</dt>
                <dd>{humanize(bundle.domainPacket.trust_sensitivity)}</dd>
              </div>
            </dl>
            <div className={styles.sourceGrid}>
              <article className={styles.infoCard}>
                <h4>Accepted tasks</h4>
                {renderTokenList(bundle.domainPacket.tasks)}
              </article>
              <article className={styles.infoCard}>
                <h4>Required evidence visibility</h4>
                {renderTokenList(bundle.domainPacket.required_evidence_visibility)}
              </article>
              <article className={styles.infoCard}>
                <h4>Utility ranking</h4>
                {renderTokenList(bundle.domainPacket.utility_ranking)}
              </article>
            </div>
          </article>

          <article
            className={styles.lane}
            id="work-context-lane"
            data-lane-id="work-context-lane"
            data-lane-role="work_context_lane"
            data-rendered-cluster-ids={workContextLaneClusters.map((cluster) => cluster.cluster_id).join(" ")}
          >
            <div className={styles.laneHeader}>
              <h3>Candidate / Proposed Artifact Region</h3>
              <span className="mono">work-context-lane</span>
            </div>
            <p className={styles.lead}>
              Projection and interaction law remain accepted artifacts. The rendered route is a
              presentational transform only and does not reinterpret authority-bearing meaning.
            </p>
            <div className={styles.sourceGrid}>
              <article className={styles.infoCard}>
                <h4>Morph axes</h4>
                <dl className={styles.axisGrid}>
                  {Object.entries(bundle.morphIr.morph_axes).map(([key, value]) => (
                    <div key={key}>
                      <dt>{humanize(key)}</dt>
                      <dd>{humanize(value)}</dd>
                    </div>
                  ))}
                </dl>
              </article>
              <article className={styles.infoCard}>
                <h4>Required invariants</h4>
                {renderTokenList(bundle.morphIr.invariants)}
              </article>
              <article className={styles.infoCard}>
                <h4>Surface compilation units</h4>
                {renderTokenList(bundle.morphIr.surface_compilation_units)}
              </article>
            </div>
            {workContextLaneClusters.length > 0 ? (
              <div className={styles.embeddedClusterSection}>
                <div className={styles.sectionHeader}>
                  <h4>Comparison / focus actions remain in the work-context lane</h4>
                  <p className="muted">
                    Lane placement stays faithful to the accepted V36-B projection instead of
                    flattening every action cluster into the advisory lane.
                  </p>
                </div>
                <ActionClusterSection
                  bundle={bundle}
                  clusters={workContextLaneClusters}
                  referenceInstanceId={identity.reference_instance_id}
                />
              </div>
            ) : null}
          </article>
        </section>

        <section
          className={`${styles.region} ${styles.evidenceRegion}`}
          data-region-id="evidence-region"
          data-region-kind="evidence_region"
          {...targetDataAttributes(
            identity.reference_instance_id,
            "evidence-region",
            bundle.targetIndex,
          )}
        >
          <div className={styles.regionHeader}>
            <div>
              <p className={styles.regionEyebrow}>Evidence Before Commit</p>
              <h2>Evidence and diagnostics remain visible before any gate</h2>
            </div>
            <span className={styles.regionMarker}>Same-context rule preserved</span>
          </div>

          <article
            className={styles.lane}
            id="diagnostics-lane"
            data-lane-id="diagnostics-lane"
            data-lane-role="diagnostics_lane"
          >
            <div className={styles.laneHeader}>
              <h3>Diagnostics Lane</h3>
              <span className="mono">placeholder / read-only only</span>
            </div>
            <div
              className={styles.stateSurface}
              data-surface-id="diagnostic-status-surface"
              data-surface-kind="diagnostic_state_surface"
              {...targetDataAttributes(
                identity.reference_instance_id,
                "diagnostic-status-surface",
                bundle.targetIndex,
              )}
            >
              <p className={styles.placeholderTitle}>Diagnostics lane remains read-only placeholder in v63.</p>
              <p className="muted">
                It references accepted visibility rules and bindings only. No new severity, no local
                conformance judgment, and no UI heuristic is presented as canonical diagnostics here.
              </p>
              {renderTokenList(bundle.morphIr.epistemics.visibility_rules)}
            </div>
          </article>

          <article
            className={styles.lane}
            id="evidence-lane"
            data-lane-id="evidence-lane"
            data-lane-role="evidence_lane"
            {...targetDataAttributes(
              identity.reference_instance_id,
              "evidence-lane",
              bundle.targetIndex,
            )}
          >
            <div className={styles.laneHeader}>
              <h3>Evidence Lane</h3>
              <span className="mono">required evidence reachable before commit</span>
            </div>
            <div className={styles.infoCard}>
              <h4>Required evidence lanes</h4>
              {renderTokenList(projection.evidence_before_commit.required_evidence_lane_ids)}
            </div>
            <div className={styles.infoCard}>
              <h4>Required evidence regions</h4>
              {renderTokenList(projection.evidence_before_commit.required_evidence_region_ids)}
            </div>
            <p className="muted">
              Route change required: <span className="mono">{String(projection.evidence_before_commit.route_change_required)}</span>{" "}
              · Commit / destructive action required:{" "}
              <span className="mono">
                {String(projection.evidence_before_commit.commit_or_destructive_action_required)}
              </span>
            </p>
          </article>
        </section>

        <section
          className={`${styles.region} ${styles.statusRegion}`}
          data-region-id="status-region"
          data-region-kind="status_region"
        >
          <div className={styles.regionHeader}>
            <div>
              <p className={styles.regionEyebrow}>Status / Trust Lane</p>
              <h2>Epistemic states and trust boundaries stay explicit</h2>
            </div>
            <span className={styles.regionMarker}>No worker prose or event stream truth substitution</span>
          </div>

          <article
            className={styles.lane}
            id="status-lane"
            data-lane-id="status-lane"
            data-lane-role="status_lane"
          >
            <div className={styles.laneHeader}>
              <h3>Epistemic State Rendering</h3>
              <span className="mono">status-lane</span>
            </div>
            <div className={styles.epistemicGrid}>
              {bundle.morphIr.epistemics.knowledge_states.map((state) => (
                <div
                  key={state}
                  className={styles.epistemicCard}
                  data-epistemic-state={state}
                >
                  <span className={styles.epistemicLabel}>{humanize(state)}</span>
                  <span className="muted">{getEpistemicStateDescription(state)}</span>
                </div>
              ))}
            </div>
            <div className={styles.surfaceGrid}>
              {projection.state_surfaces.map((surface) => (
                <div
                  key={surface.surface_id}
                  className={styles.stateSurface}
                  data-surface-id={surface.surface_id}
                  data-surface-kind={surface.surface_kind}
                  {...targetDataAttributes(
                    identity.reference_instance_id,
                    surface.surface_id,
                    bundle.targetIndex,
                  )}
                >
                  <h4>{humanize(surface.surface_id)}</h4>
                  <p className="muted">{humanize(surface.surface_kind)}</p>
                </div>
              ))}
            </div>
          </article>

          <article
            className={styles.lane}
            id="trust-boundary-lane"
            data-lane-id="trust-boundary-lane"
            data-lane-role="trust_boundary_lane"
          >
            <div className={styles.laneHeader}>
              <h3>Trust Boundary Lane</h3>
              <span className="mono">authority and evidence sensitive</span>
            </div>
            <div
              className={styles.boundaryCard}
              data-truth-source="accepted_v36_artifacts_only"
              {...targetDataAttributes(
                identity.reference_instance_id,
                "warning-status-surface",
                bundle.targetIndex,
              )}
            >
              <p>
                Runtime truth is derived from the accepted V36 artifacts only. Event streams or
                worker prose are not rendered here as accepted truth, and any future non-authoritative
                content must remain labeled as non-authoritative.
              </p>
              <dl className={styles.definitionGrid}>
                <div>
                  <dt>Canonical profile</dt>
                  <dd>{bundle.approvedProfileTable.canonical_reference_profile_id}</dd>
                </div>
                <div>
                  <dt>Alternate lawful profile</dt>
                  <dd>{bundle.approvedProfileTable.alternate_lawful_profile_id}</dd>
                </div>
              </dl>
            </div>
            <div className={styles.manifestGrid}>
              <article className={styles.infoCard}>
                <h4>Stable provenance hooks</h4>
                <ul className={styles.manifestList}>
                  {[...projection.stable_provenance_hooks, ...interactionContract.stable_provenance_hooks].map(
                    (hook) => (
                      <li key={hook.hook_id}>
                        <span className="mono">{hook.target_kind}</span> →{" "}
                        <span className="mono">{hook.target_ref}</span>
                      </li>
                    ),
                  )}
                </ul>
              </article>
              <article className={styles.infoCard}>
                <h4>Implementation bindings</h4>
                <ul className={styles.manifestList}>
                  {[
                    ...projection.implementation_observable_bindings,
                    ...interactionContract.implementation_observable_bindings,
                  ].map((binding) => (
                    <li key={binding.binding_id}>
                      <span className="mono">{binding.target_kind}</span> →{" "}
                      <span className="mono">{binding.target_ref}</span>
                    </li>
                  ))}
                </ul>
              </article>
            </div>
          </article>
        </section>
      </main>
    </div>
  );
}
