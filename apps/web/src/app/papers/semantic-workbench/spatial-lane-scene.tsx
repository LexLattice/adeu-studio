"use client";

import type {
  PaperSemanticSpatialSceneEdge,
  PaperSemanticSpatialSceneModel,
  PaperSemanticSpatialSceneNode,
} from "./view-model";
import styles from "./page.module.css";

type SpatialLaneSceneProps = {
  scene: PaperSemanticSpatialSceneModel;
  focusClaimId: string | null;
  onFocusClaim: (claimId: string) => void;
};

type ViewportPoint = {
  left: number;
  top: number;
};

export function SpatialLaneScene({
  scene,
  focusClaimId,
  onFocusClaim,
}: SpatialLaneSceneProps) {
  const bounds = computeSceneBounds(scene.nodes);
  const positions = new Map<string, ViewportPoint>();
  for (const node of scene.nodes) {
    positions.set(node.node_id, projectNode(node, bounds));
  }

  return (
    <section
      className={styles.scenePanel}
      data-scene-hash={scene.scene_hash}
      data-scene-node-count={scene.nodes.length}
      data-scene-edge-count={scene.edges.length}
    >
      <header className={styles.sceneHeader}>
        <div>
          <p className={styles.sceneEyebrow}>V52-D spatial surface</p>
          <h2>Spatial lane recomposition</h2>
        </div>
        <dl className={styles.sceneMeta}>
          <div>
            <dt>artifact_ref</dt>
            <dd>{scene.artifact_ref}</dd>
          </div>
          <div>
            <dt>scene_hash</dt>
            <dd>{scene.scene_hash}</dd>
          </div>
        </dl>
      </header>

      <div className={styles.sceneViewport}>
        <svg
          className={styles.sceneEdges}
          viewBox="0 0 100 100"
          aria-hidden="true"
          preserveAspectRatio="none"
        >
          {scene.edges.map((edge) => renderEdge(edge, positions))}
        </svg>

        <div className={styles.sceneNodes}>
          {scene.nodes.map((node) => {
            const point = positions.get(node.node_id);
            if (!point) return null;
            const active = node.claim_id === focusClaimId;
            return (
              <button
                key={node.node_id}
                type="button"
                className={active ? styles.sceneNodeActive : styles.sceneNode}
                data-node-kind={node.node_kind}
                data-lane-id={node.lane_id ?? "claim"}
                style={{
                  left: `${point.left}%`,
                  top: `${point.top}%`,
                  transform: `translate(-50%, -50%) translateZ(${node.position.z.toFixed(2)}rem)`,
                }}
                onClick={() => onFocusClaim(node.claim_id)}
              >
                <strong>{node.lane_id ?? "claim"}</strong>
                <span>{node.label}</span>
              </button>
            );
          })}
        </div>
      </div>

      <div className={styles.sceneLegend}>
        <p>Claim nodes occupy the root column; lane fragments stay in deterministic O/E/D/U columns.</p>
        <p>Spatial layout is route-local only and remains subordinate to released artifact ordering anchors.</p>
      </div>
    </section>
  );
}

function renderEdge(
  edge: PaperSemanticSpatialSceneEdge,
  positions: Map<string, ViewportPoint>,
) {
  const from = positions.get(edge.from_node_id);
  const to = positions.get(edge.to_node_id);
  if (!from || !to) return null;
  return (
    <line
      key={edge.edge_id}
      className={edge.edge_kind === "inference_bridge" ? styles.sceneInferenceEdge : styles.sceneClaimEdge}
      x1={from.left}
      y1={from.top}
      x2={to.left}
      y2={to.top}
    />
  );
}

function computeSceneBounds(nodes: readonly PaperSemanticSpatialSceneNode[]) {
  let minX = Number.POSITIVE_INFINITY;
  let maxX = Number.NEGATIVE_INFINITY;
  let minY = Number.POSITIVE_INFINITY;
  let maxY = Number.NEGATIVE_INFINITY;

  for (const node of nodes) {
    minX = Math.min(minX, node.position.x);
    maxX = Math.max(maxX, node.position.x);
    minY = Math.min(minY, node.position.y);
    maxY = Math.max(maxY, node.position.y);
  }

  return {
    minX,
    maxX,
    minY,
    maxY,
  };
}

function projectNode(
  node: PaperSemanticSpatialSceneNode,
  bounds: {
    minX: number;
    maxX: number;
    minY: number;
    maxY: number;
  },
): ViewportPoint {
  const horizontalSpan = Math.max(bounds.maxX - bounds.minX, 1);
  const verticalSpan = Math.max(bounds.maxY - bounds.minY, 1);
  return {
    left: 10 + ((node.position.x - bounds.minX) / horizontalSpan) * 80,
    top: 14 + ((node.position.y - bounds.minY) / verticalSpan) * 72,
  };
}
