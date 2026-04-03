"use client";

import { useMemo, useRef, useState } from "react";
import type { Mesh } from "three";
import { Color, Vector3 } from "three";
import { Canvas, useFrame } from "@react-three/fiber";
import { Float, Line, OrbitControls, PerspectiveCamera, RoundedBox, Stars, Text } from "@react-three/drei";

import {
  DIAGNOSTIC_META,
  type DiagnosticKind,
  type LaneId,
  LANE_META,
  LANE_ORDER,
  type ODEUClaimDecomposition,
  type ODEUInferenceBridge,
  type ODEULaneFragment,
  type PaperSemanticWorkbenchArtifact,
} from "./schema";

type SpatialLaneSceneProps = {
  artifact: PaperSemanticWorkbenchArtifact;
  selectedClaimId: string | null;
  visibleLanes: LaneId[];
  onSelectClaim: (claimId: string) => void;
};

type NodeDescriptor = {
  fragment: ODEULaneFragment;
  claim: ODEUClaimDecomposition;
  position: [number, number, number];
  isSelected: boolean;
  diagnosticKinds: DiagnosticKind[];
};

function bridgeColor(bridge: ODEUInferenceBridge, diagnosticKinds: DiagnosticKind[]): string {
  if (diagnosticKinds.includes("contradiction")) return DIAGNOSTIC_META.contradiction.color;
  if (diagnosticKinds.includes("u_overreach")) return DIAGNOSTIC_META.u_overreach.color;
  if (bridge.kind === "missing_bridge") return DIAGNOSTIC_META.missing_bridge.color;
  if (bridge.kind === "contested_bridge") return DIAGNOSTIC_META.contradiction.color;
  if (bridge.kind === "projection_bridge") return "#d1d5db";
  return "#e2e8f0";
}

function nodeOpacity(fragment: ODEULaneFragment): number {
  if (fragment.status === "missing") return 0.3;
  if (fragment.status === "underdetermined") return 0.52;
  if (fragment.status === "inferred") return 0.76;
  return 0.92;
}

function nodeScale(fragment: ODEULaneFragment, isSelected: boolean): [number, number, number] {
  const base = isSelected ? 1.1 : 1;
  if (fragment.status === "missing") return [1.18 * base, 0.82 * base, 0.7 * base];
  return [1.28 * base, 0.92 * base, 0.74 * base];
}

function laneY(lane: LaneId): number {
  const index = LANE_ORDER.indexOf(lane);
  return 1.8 - index * 1.2;
}

function sortClaimsForScene(claims: ODEUClaimDecomposition[]): ODEUClaimDecomposition[] {
  return [...claims].sort((left, right) => {
    if (left.depth !== right.depth) return left.depth - right.depth;
    return left.claim_id.localeCompare(right.claim_id);
  });
}

function SceneNode({
  descriptor,
  color,
  onSelect,
}: {
  descriptor: NodeDescriptor;
  color: string;
  onSelect: () => void;
}) {
  const meshRef = useRef<Mesh>(null);
  const [hovered, setHovered] = useState(false);
  const emissive = new Color(color).multiplyScalar(descriptor.isSelected ? 0.7 : hovered ? 0.55 : 0.36);

  useFrame((_, delta) => {
    const mesh = meshRef.current;
    if (!mesh) return;
    const targetZ = descriptor.isSelected ? 0.26 : hovered ? 0.18 : 0.12;
    mesh.position.z += (targetZ - mesh.position.z) * Math.min(1, delta * 6);
  });

  return (
    <Float speed={descriptor.isSelected ? 1.2 : 0.6} rotationIntensity={0.05} floatIntensity={0.12}>
      <group position={descriptor.position}>
        <RoundedBox
          ref={meshRef}
          args={nodeScale(descriptor.fragment, descriptor.isSelected)}
          radius={0.08}
          smoothness={6}
          onClick={onSelect}
          onPointerOver={() => setHovered(true)}
          onPointerOut={() => setHovered(false)}
        >
          <meshStandardMaterial
            color={color}
            emissive={emissive}
            emissiveIntensity={descriptor.isSelected ? 1.05 : hovered ? 0.78 : 0.42}
            transparent
            opacity={nodeOpacity(descriptor.fragment)}
            metalness={0.35}
            roughness={0.28}
          />
        </RoundedBox>
        <Text
          position={[0, 0.06, 0.28]}
          color="#e5f4ff"
          anchorX="center"
          anchorY="middle"
          maxWidth={1.45}
          fontSize={0.11}
        >
          {descriptor.fragment.short_label}
        </Text>
        <Text
          position={[0, -0.17, 0.28]}
          color={descriptor.fragment.source_kind === "inferred" ? "#cbd5e1" : "#f8fafc"}
          anchorX="center"
          anchorY="middle"
          maxWidth={1.45}
          fontSize={0.09}
        >
          {descriptor.fragment.source_kind === "inferred" ? "inferred" : "explicit"}
        </Text>
        {descriptor.diagnosticKinds.length > 0 ? (
          <Text
            position={[0, -0.33, 0.28]}
            color={DIAGNOSTIC_META[descriptor.diagnosticKinds[0]].color}
            anchorX="center"
            anchorY="middle"
            maxWidth={1.6}
            fontSize={0.08}
          >
            {DIAGNOSTIC_META[descriptor.diagnosticKinds[0]].title}
          </Text>
        ) : null}
      </group>
    </Float>
  );
}

function SpatialLaneSceneInner({
  artifact,
  selectedClaimId,
  visibleLanes,
  onSelectClaim,
}: SpatialLaneSceneProps) {
  const claimById = useMemo(
    () => Object.fromEntries(artifact.claims.map((claim) => [claim.claim_id, claim])) as Record<string, ODEUClaimDecomposition>,
    [artifact.claims],
  );
  const fragmentById = useMemo(
    () => Object.fromEntries(artifact.lane_fragments.map((fragment) => [fragment.fragment_id, fragment])) as Record<string, ODEULaneFragment>,
    [artifact.lane_fragments],
  );
  const diagnosticsById = useMemo(
    () => Object.fromEntries(artifact.diagnostics.map((diag) => [diag.diagnostic_id, diag])) as Record<string, (typeof artifact.diagnostics)[number]>,
    [artifact.diagnostics],
  );

  const sceneClaims = useMemo(() => {
    const sorted = sortClaimsForScene(artifact.claims).filter((claim) => claim.depth === 1 || claim.parent_claim_id === selectedClaimId);
    const selectedTopLevelId = selectedClaimId && claimById[selectedClaimId]?.parent_claim_id ? claimById[selectedClaimId].parent_claim_id : selectedClaimId;
    return sorted.map((claim) => ({
      claim,
      isSelected: claim.claim_id === selectedClaimId || claim.claim_id === selectedTopLevelId,
    }));
  }, [artifact.claims, claimById, selectedClaimId]);

  const nodes = useMemo(() => {
    const descriptors: NodeDescriptor[] = [];
    const topLevelClaims = sceneClaims.filter((entry) => entry.claim.depth === 1);
    const xForTopLevel = new Map<string, number>();
    topLevelClaims.forEach((entry, index) => {
      const center = (topLevelClaims.length - 1) / 2;
      xForTopLevel.set(entry.claim.claim_id, (index - center) * 2.05);
    });

    sceneClaims.forEach((entry) => {
      entry.claim.lane_fragment_ids.forEach((fragmentId) => {
        const fragment = fragmentById[fragmentId];
        if (!fragment || !visibleLanes.includes(fragment.lane)) return;
        const topLevelId = entry.claim.parent_claim_id ?? entry.claim.claim_id;
        const x = xForTopLevel.get(topLevelId) ?? 0;
        const childOffset = entry.claim.parent_claim_id ? 0.85 : 0;
        const z = entry.claim.parent_claim_id ? -0.95 : 0;
        const laneIndex = LANE_ORDER.indexOf(fragment.lane);
        const xOffset = entry.claim.parent_claim_id ? (laneIndex % 2 === 0 ? -childOffset : childOffset) * 0.45 : 0;
        const position: [number, number, number] = [x + xOffset, laneY(fragment.lane), z];
        const diagnosticKinds = fragment.diagnostic_ids
          .map((id) => diagnosticsById[id]?.kind)
          .filter((value): value is DiagnosticKind => Boolean(value));
        descriptors.push({
          fragment,
          claim: entry.claim,
          position,
          isSelected: entry.claim.claim_id === selectedClaimId || entry.claim.parent_claim_id === selectedClaimId,
          diagnosticKinds,
        });
      });
    });
    return descriptors;
  }, [claimById, diagnosticsById, fragmentById, sceneClaims, selectedClaimId, visibleLanes]);

  const nodePositionByFragmentId = useMemo(() => {
    return new Map(nodes.map((node) => [node.fragment.fragment_id, node.position]));
  }, [nodes]);

  const bridges = useMemo(() => {
    return artifact.inference_bridges.filter((bridge) => {
      const from = fragmentById[bridge.from_fragment_id];
      const to = fragmentById[bridge.to_fragment_id];
      return Boolean(from && to && visibleLanes.includes(from.lane) && visibleLanes.includes(to.lane));
    });
  }, [artifact.inference_bridges, fragmentById, visibleLanes]);

  return (
    <>
      <color attach="background" args={["#040b12"]} />
      <fog attach="fog" args={["#040b12", 8, 20]} />
      <PerspectiveCamera makeDefault position={[0, 0.1, 8.8]} fov={32} />
      <ambientLight intensity={0.55} />
      <pointLight position={[0, 4.5, 6]} intensity={38} color="#dbeafe" />
      <pointLight position={[4, -3, 2]} intensity={22} color="#60a5fa" />
      <Stars radius={42} depth={28} count={1600} factor={3.5} saturation={0.05} fade speed={0.8} />

      {visibleLanes.map((lane) => {
        const meta = LANE_META[lane];
        return (
          <group key={lane} position={[0, laneY(lane), -0.6]}>
            <mesh rotation={[-Math.PI / 2.8, 0, 0]}>
              <planeGeometry args={[9.4, 0.88]} />
              <meshStandardMaterial color={meta.color} transparent opacity={0.08} />
            </mesh>
            <Line
              points={[
                [-4.45, 0, 0],
                [4.45, 0, 0],
              ]}
              color={meta.color}
              lineWidth={1.4}
              transparent
              opacity={0.75}
            />
            <Text position={[-4.2, 0.24, 0.2]} fontSize={0.18} color={meta.color} anchorX="left" anchorY="middle">
              {meta.short} · {meta.title}
            </Text>
          </group>
        );
      })}

      {bridges.map((bridge) => {
        const from = nodePositionByFragmentId.get(bridge.from_fragment_id);
        const to = nodePositionByFragmentId.get(bridge.to_fragment_id);
        if (!from || !to) return null;
        const control = new Vector3(
          (from[0] + to[0]) / 2,
          (from[1] + to[1]) / 2 + 0.26,
          Math.min(from[2], to[2]) - 0.4,
        );
        const points = [new Vector3(...from), control, new Vector3(...to)];
        const diagnosticKinds = bridge.diagnostic_ids
          .map((id) => diagnosticsById[id]?.kind)
          .filter((value): value is DiagnosticKind => Boolean(value));
        const color = bridgeColor(bridge, diagnosticKinds);
        const dashed = bridge.kind === "missing_bridge" || diagnosticKinds.includes("missing_bridge");
        return (
          <Line
            key={bridge.bridge_id}
            points={points}
            color={color}
            transparent
            opacity={bridge.kind === "projection_bridge" ? 0.52 : 0.86}
            dashed={dashed}
            dashScale={dashed ? 12 : 1}
            dashSize={0.16}
            gapSize={0.12}
            lineWidth={1.2}
          />
        );
      })}

      {nodes.map((descriptor) => (
        <SceneNode
          key={descriptor.fragment.fragment_id}
          descriptor={descriptor}
          color={LANE_META[descriptor.fragment.lane].color}
          onSelect={() => onSelectClaim(descriptor.claim.claim_id)}
        />
      ))}

      <OrbitControls
        enablePan={false}
        enableDamping
        dampingFactor={0.08}
        minDistance={5.6}
        maxDistance={13.2}
        minPolarAngle={Math.PI / 3.8}
        maxPolarAngle={Math.PI / 2.15}
      />
    </>
  );
}

export default function SpatialLaneScene(props: SpatialLaneSceneProps) {
  return (
    <Canvas gl={{ antialias: true }} dpr={[1, 1.8]}>
      <SpatialLaneSceneInner {...props} />
    </Canvas>
  );
}
