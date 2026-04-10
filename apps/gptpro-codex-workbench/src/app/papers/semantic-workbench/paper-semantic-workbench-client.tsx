"use client";

import { useState, useTransition, type ChangeEvent } from "react";

import styles from "./page.module.css";
import { SpatialLaneScene } from "./spatial-lane-scene";
import {
  type CommittedSampleArtifact,
  createViewModel,
  PAPER_SEMANTIC_WORKBENCH_ROUTE_ID,
  type PaperSemanticWorkbenchViewConfig,
  type PaperSemanticWorkbenchViewModel,
  type SelectedSurface,
  type VisibleLaneId,
  VISIBLE_LANE_VALUES,
} from "./view-model";

type WorkbenchClientProps = {
  sampleArtifacts: CommittedSampleArtifact[];
  initialViewModel: PaperSemanticWorkbenchViewModel;
};

function formatAuthors(authors: string[]): string {
  return authors.join(", ");
}

function formatSampleLabel(sample: CommittedSampleArtifact): string {
  return `${sample.artifact.source.title} (${sample.artifact.source.artifact_kind})`;
}

function renderIdentityList(values: string[] | null) {
  if (!values || values.length === 0) {
    return <p className={styles.emptyNote}>No identity law fields available.</p>;
  }
  return (
    <ul className={styles.inlineList}>
      {values.map((value) => (
        <li key={value}>
          <span>{value}</span>
        </li>
      ))}
    </ul>
  );
}

function renderSpanReferences(spanIds: string[], spansById: Map<string, { quote: string; span_id: string }>) {
  return (
    <ul className={styles.detailList}>
      {spanIds.map((spanId) => {
        const span = spansById.get(spanId);
        return (
          <li key={spanId}>
            <strong>{spanId}</strong>
            <span>{span?.quote ?? "Missing anchored span"}</span>
          </li>
        );
      })}
    </ul>
  );
}

function renderFailure(viewModel: PaperSemanticWorkbenchViewModel) {
  return (
    <section className={styles.failureBanner}>
      <strong>Fixture stack failed closed</strong>
      <p>
        {viewModel.failure_code ??
          "The committed paper-semantic workbench fixture set could not be trusted as a released V52-A stack."}
      </p>
    </section>
  );
}

export function PaperSemanticWorkbenchClient({
  sampleArtifacts,
  initialViewModel,
}: WorkbenchClientProps) {
  const [isPending, startViewTransition] = useTransition();
  const [viewConfig, setViewConfig] = useState<PaperSemanticWorkbenchViewConfig>({
    schema: "adeu_paper_semantic_workbench_view_config@1",
    route_id: PAPER_SEMANTIC_WORKBENCH_ROUTE_ID,
    selected_sample_artifact_ref: initialViewModel.selected_sample_artifact_ref,
    selected_surface: initialViewModel.selected_surface,
    focus_claim_id: initialViewModel.focus_claim_id,
    visible_lane_ids: [...initialViewModel.visible_lane_ids],
  });

  const viewModel =
    sampleArtifacts.length === 0 && initialViewModel.route_status === "fail_closed_invalid_fixture_stack"
      ? initialViewModel
      : createViewModel(sampleArtifacts, viewConfig);

  const artifact = viewModel.artifact;
  const spansById = new Map(
    artifact?.spans.map((span) => [span.span_id, { quote: span.quote, span_id: span.span_id }]) ??
      [],
  );
  const claimsById = new Map(artifact?.claims.map((claim) => [claim.claim_id, claim]) ?? []);

  function updateConfig(updater: (current: PaperSemanticWorkbenchViewConfig) => PaperSemanticWorkbenchViewConfig) {
    startViewTransition(() => {
      setViewConfig((current) => updater(current));
    });
  }

  function handleSampleChange(event: ChangeEvent<HTMLSelectElement>) {
    const nextRef = event.target.value;
    const nextSample = sampleArtifacts.find((item) => item.ref === nextRef);
    updateConfig((current) => ({
      ...current,
      selected_sample_artifact_ref: nextRef,
      focus_claim_id: nextSample?.artifact.projections[0]?.recommended_focus_claim_id ?? null,
      visible_lane_ids: [...VISIBLE_LANE_VALUES],
    }));
  }

  function handleSurfaceChange(nextSurface: SelectedSurface) {
    updateConfig((current) => ({
      ...current,
      selected_surface: nextSurface,
    }));
  }

  function toggleLane(laneId: VisibleLaneId) {
    updateConfig((current) => {
      const isVisible = current.visible_lane_ids.includes(laneId);
      if (isVisible && current.visible_lane_ids.length === 1) {
        return current;
      }
      return {
        ...current,
        visible_lane_ids: isVisible
          ? current.visible_lane_ids.filter((item) => item !== laneId)
          : [...current.visible_lane_ids, laneId],
      };
    });
  }

  function focusClaim(claimId: string) {
    updateConfig((current) => ({
      ...current,
      focus_claim_id: claimId,
    }));
  }

  const focusedClaim =
    viewModel.focus_claim_id && claimsById.has(viewModel.focus_claim_id)
      ? claimsById.get(viewModel.focus_claim_id) ?? null
      : null;
  const panelNote =
    viewModel.route_status === "ready_clean"
      ? "First render is ready-clean with the default committed abstract artifact selected. All navigation is local to the released sample stack."
      : "The route stayed inside the committed fixture stack only and failed closed before any rendering drift or live widening.";

  return (
    <div
      className={styles.shell}
      data-route-id={PAPER_SEMANTIC_WORKBENCH_ROUTE_ID}
      data-route-status={viewModel.route_status}
      data-selected-surface={viewModel.selected_surface}
    >
      <section className={styles.hero}>
        <div>
          <p className={styles.eyebrow}>V52-D bounded route-local visualization</p>
          <h1>Paper Semantic Workbench</h1>
          <p className={styles.lede}>
            One released paper-semantic artifact in, one bounded local workbench projection out.
            This route consumes committed `V52-A` artifacts only, derives a route-local spatial
            scene from released ordering anchors, and still refuses live-worker and API widening.
          </p>
        </div>
        <span className={styles.statusBadge} data-status={viewModel.route_status}>
          {isPending ? "transitioning" : viewModel.route_status}
        </span>
      </section>

      <section className={styles.controlsPanel}>
        <div className={styles.controlsIntro}>
          <h2>Committed sample registry</h2>
          <p className={styles.panelNote}>{panelNote}</p>
        </div>

        <div className={styles.controlGrid}>
          <label className={styles.field}>
            <span>Sample artifact</span>
            <select value={viewConfig.selected_sample_artifact_ref} onChange={handleSampleChange}>
              {sampleArtifacts.map((sample) => (
                <option key={sample.ref} value={sample.ref}>
                  {formatSampleLabel(sample)}
                </option>
              ))}
            </select>
          </label>

          <div className={styles.field}>
            <span>Surface</span>
            <div className={styles.toggleRow}>
              {(["artifact", "local", "spatial"] as const).map((surface) => (
                <button
                  key={surface}
                  type="button"
                  className={surface === viewModel.selected_surface ? styles.toggleActive : styles.toggleButton}
                  onClick={() => handleSurfaceChange(surface)}
                >
                  {surface}
                </button>
              ))}
            </div>
          </div>

          <div className={styles.field}>
            <span>Visible lanes</span>
            <div className={styles.toggleRow}>
              {VISIBLE_LANE_VALUES.map((laneId) => (
                <button
                  key={laneId}
                  type="button"
                  className={
                    viewModel.visible_lane_ids.includes(laneId)
                      ? styles.toggleActive
                      : styles.toggleButton
                  }
                  onClick={() => toggleLane(laneId)}
                >
                  {laneId}
                </button>
              ))}
            </div>
          </div>
        </div>
      </section>

      {viewModel.route_status === "fail_closed_invalid_fixture_stack" || !artifact ? (
        renderFailure(viewModel)
      ) : (
        <div className={styles.grid}>
          <section className={styles.panel}>
            <h2>Released artifact identity</h2>
            <dl className={styles.detailGrid}>
              <div>
                <dt>selected_sample_artifact_ref</dt>
                <dd>{viewModel.selected_sample_artifact_ref}</dd>
              </div>
              <div>
                <dt>artifact_ref</dt>
                <dd>{viewModel.artifact_ref}</dd>
              </div>
              <div>
                <dt>semantic_hash</dt>
                <dd>{viewModel.semantic_hash}</dd>
              </div>
              <div>
                <dt>view_hash</dt>
                <dd>{viewModel.view_hash}</dd>
              </div>
              <div>
                <dt>selected_surface</dt>
                <dd>{viewModel.selected_surface}</dd>
              </div>
              <div>
                <dt>scene_hash</dt>
                <dd>{viewModel.spatial_scene?.scene_hash ?? "n/a"}</dd>
              </div>
            </dl>
          </section>

          <section className={styles.panel}>
            <h2>Authority posture</h2>
            <dl className={styles.detailGrid}>
              <div>
                <dt>source_authority_posture</dt>
                <dd>{artifact.source_authority_posture}</dd>
              </div>
              <div>
                <dt>interpretation_authority_posture</dt>
                <dd>{artifact.interpretation_authority_posture}</dd>
              </div>
              <div>
                <dt>semantic_identity_mode</dt>
                <dd>{artifact.semantic_identity_mode}</dd>
              </div>
            </dl>
            <div className={styles.subsection}>
              <h3>identity_field_names</h3>
              {renderIdentityList(viewModel.identity_field_names)}
            </div>
            <div className={styles.subsection}>
              <h3>projection_field_names</h3>
              {renderIdentityList(viewModel.projection_field_names)}
            </div>
          </section>

          <section className={styles.panel}>
            <h2>Source metadata</h2>
            <dl className={styles.detailGrid}>
              <div>
                <dt>title</dt>
                <dd>{artifact.source.title}</dd>
              </div>
              <div>
                <dt>authors</dt>
                <dd>{formatAuthors(artifact.source.authors)}</dd>
              </div>
              <div>
                <dt>artifact_kind</dt>
                <dd>{artifact.source.artifact_kind}</dd>
              </div>
              <div>
                <dt>year</dt>
                <dd>{artifact.source.year ?? "n/a"}</dd>
              </div>
              <div>
                <dt>venue</dt>
                <dd>{artifact.source.venue ?? "n/a"}</dd>
              </div>
            </dl>
            <blockquote className={styles.sourceText}>{artifact.source.source_text}</blockquote>
          </section>

          <section className={styles.panel}>
            <h2>Anchored spans</h2>
            <ul className={styles.detailList}>
              {artifact.spans.map((span) => (
                <li key={span.span_id}>
                  <strong>{span.span_id}</strong>
                  <span>
                    {span.quote} ({span.start}-{span.end}, paragraph {span.paragraph_index})
                  </span>
                </li>
              ))}
            </ul>
          </section>

          <section className={styles.panel}>
            <h2>Claims</h2>
            <ul className={styles.claimList}>
              {viewModel.ordered_claim_ids.map((claimId) => {
                const claim = claimsById.get(claimId);
                if (!claim) return null;
                const active = claimId === viewModel.focus_claim_id;
                return (
                  <li key={claimId}>
                    <button
                      type="button"
                      className={active ? styles.claimButtonActive : styles.claimButton}
                      onClick={() => focusClaim(claimId)}
                    >
                      <strong>{claim.claim_id}</strong>
                      <span>{claim.claim_text}</span>
                    </button>
                  </li>
                );
              })}
            </ul>
          </section>

          <section className={styles.panel}>
            <h2>Focused claim</h2>
            {focusedClaim ? (
              <>
                <p className={styles.panelLead}>{focusedClaim.claim_text}</p>
                <dl className={styles.detailGrid}>
                  <div>
                    <dt>status</dt>
                    <dd>{focusedClaim.status}</dd>
                  </div>
                  <div>
                    <dt>confidence</dt>
                    <dd>{focusedClaim.confidence ?? "n/a"}</dd>
                  </div>
                </dl>
                <div className={styles.subsection}>
                  <h3>Anchored support</h3>
                  {renderSpanReferences(focusedClaim.span_ids, spansById)}
                </div>
              </>
            ) : (
              <p className={styles.emptyNote}>No focus claim available.</p>
            )}
          </section>

          <section className={styles.panel}>
            <h2>Visible lane fragments</h2>
            <div className={styles.fragmentGrid}>
              {viewModel.visible_lane_ids.map((laneId) => {
                const fragments = artifact.lane_fragments.filter((fragment) => fragment.lane_id === laneId);
                return (
                  <article key={laneId} className={styles.fragmentColumn}>
                    <header>
                      <strong>{laneId}</strong>
                    </header>
                    {fragments.length === 0 ? (
                      <p className={styles.emptyNote}>No fragments visible.</p>
                    ) : (
                      <ul className={styles.detailList}>
                        {fragments.map((fragment) => (
                          <li key={fragment.fragment_id}>
                            <strong>{fragment.short_label}</strong>
                            <span>{fragment.fragment_text}</span>
                          </li>
                        ))}
                      </ul>
                    )}
                  </article>
                );
              })}
            </div>
          </section>

          <section className={styles.panel}>
            <h2>Inference bridges</h2>
            <ul className={styles.detailList}>
              {artifact.inference_bridges.map((bridge) => (
                <li key={bridge.bridge_id}>
                  <strong>{bridge.bridge_kind}</strong>
                  <span>{bridge.rationale}</span>
                </li>
              ))}
            </ul>
          </section>

          <section className={styles.panel}>
            <h2>Diagnostics</h2>
            {artifact.diagnostics.length === 0 ? (
              <p className={styles.emptyNote}>No diagnostics emitted.</p>
            ) : (
              <ul className={styles.detailList}>
                {artifact.diagnostics.map((diagnostic) => (
                  <li key={diagnostic.diagnostic_id}>
                    <strong>
                      {diagnostic.diagnostic_kind} / {diagnostic.severity}
                    </strong>
                    <span>{diagnostic.summary}</span>
                  </li>
                ))}
              </ul>
            )}
          </section>

          <section className={styles.panel}>
            <h2>Released projections</h2>
            <ul className={styles.detailList}>
              {artifact.projections.map((projection) => (
                <li key={projection.projection_id}>
                  <strong>{projection.surface}</strong>
                  <span>
                    lane_order={projection.lane_order.join(" → ")}; claim_order=
                    {projection.claim_order.join(", ")}
                  </span>
                </li>
              ))}
            </ul>
          </section>

          {viewModel.selected_surface === "spatial" && viewModel.spatial_scene ? (
            <section className={styles.panel}>
              <SpatialLaneScene
                scene={viewModel.spatial_scene}
                focusClaimId={viewModel.focus_claim_id}
                onFocusClaim={focusClaim}
              />
            </section>
          ) : null}
        </div>
      )}
    </div>
  );
}
