
"use client";

/**
 * ADEU Studio / Morphic UX proof-of-concept
 *
 * Assumes Tailwind CSS is available and these packages are installed:
 * - framer-motion
 * - three
 * - @react-three/fiber
 * - @react-three/drei
 */

import React, { useEffect, useMemo, useRef, useState } from "react";
import { Canvas, useFrame, useThree } from "@react-three/fiber";
import {
  Html,
  Line,
  MeshDistortMaterial,
  OrbitControls,
  RoundedBox,
  Sparkles,
  Float,
} from "@react-three/drei";
import { AnimatePresence, motion } from "framer-motion";
import * as THREE from "three";

const MODE_CONFIGS = {
  vision: {
    id: "vision",
    label: "A — Vision",
    title: "Vision",
    profile: "mythic-coupling",
    theorem: "Synthetic reason needs abstract electrical engineering.",
    description:
      "A cinematic bounded overview: semantic plasticity, explicit intent, deterministic governance, and artifact projection.",
    camera: [6.6, 2.8, 7.4],
    lookAt: [0, 0.35, 0],
    substrateY: -2.25,
    irY: -0.55,
    coreY: 0.55,
    harnessRadius: 2.05,
    pluginRadius: 4.7,
    axisRadius: 3.25,
    moduleY: 0.75,
    coreScale: 1.05,
    shellScale: 1,
  },
  architecture: {
    id: "architecture",
    label: "B — Architecture",
    title: "Architecture",
    profile: "exploded-stack",
    theorem: "The deterministic / semantic distinction is explicit.",
    description:
      "Exploded systems view of substrate, Semantic IR, SPU, harness, adapters, and flow boundaries.",
    camera: [8.5, 4.1, 9.5],
    lookAt: [0, 0.15, 0],
    substrateY: -2.7,
    irY: -0.95,
    coreY: 0.95,
    harnessRadius: 2.45,
    pluginRadius: 5.4,
    axisRadius: 3.5,
    moduleY: 1.05,
    coreScale: 0.92,
    shellScale: 1.08,
  },
  audit: {
    id: "audit",
    label: "C — Governance / Audit",
    title: "Governance",
    profile: "typed-governance",
    theorem:
      "Required evidence must be visible before an authoritative decision.",
    description:
      "O / E / D / U become first-class structural anchors. Authority posture and evidence gates are made explicit.",
    camera: [6.1, 3.2, 6.1],
    lookAt: [0, 0.55, 0],
    substrateY: -2.05,
    irY: -0.35,
    coreY: 0.55,
    harnessRadius: 2.15,
    pluginRadius: 4.6,
    axisRadius: 3.65,
    moduleY: 0.65,
    coreScale: 0.88,
    shellScale: 1.02,
  },
  domain: {
    id: "domain",
    label: "D — Domain Projection",
    title: "Domain Projection",
    profile: "adapter-projection",
    theorem: "Projection changes the adapter, not the governed machine.",
    description:
      "One meta-ontology, many artifact classes. The outer ring morphs while the core architecture remains invariant.",
    camera: [8.7, 2.7, 9.9],
    lookAt: [0, 0.35, 0],
    substrateY: -2.05,
    irY: -0.42,
    coreY: 0.48,
    harnessRadius: 2.1,
    pluginRadius: 6,
    axisRadius: 3.3,
    moduleY: 0.7,
    coreScale: 0.96,
    shellScale: 1,
  },
};

const AXES = [
  {
    id: "O",
    title: "Ontology",
    short: "typed entities / families",
    accent: "#67e8f9",
    blurb:
      "Typed entities, relations, package boundaries, artifact classes, and boundary objects.",
  },
  {
    id: "E",
    title: "Epistemics",
    short: "evidence / validation / provenance",
    accent: "#c084fc",
    blurb:
      "Deterministic validation, solver evidence, proof lanes, provenance, uncertainty posture, and test surfaces.",
  },
  {
    id: "D",
    title: "Deontics",
    short: "policy / gates / obligations",
    accent: "#fbbf24",
    blurb:
      "Capability policy, permissions, prohibitions, approval gates, and fail-closed behavior.",
  },
  {
    id: "U",
    title: "Utility",
    short: "purpose / stop-gates / delivery",
    accent: "#86efac",
    blurb:
      "Arc-scoped delivery, dashboards, stop-gates, optimization surfaces, and governed improvement.",
  },
];

const DOMAINS = [
  {
    id: "software",
    label: "Codebase / app",
    sceneLabel: "code",
    accent: "#6ee7ff",
    profile: [1.08, 0.48, 0.88, 0.62, 0.34],
    blurb:
      "Semantic IR resolves into specs, tests, modules, and deployable behavior.",
  },
  {
    id: "ui",
    label: "Website / UI",
    sceneLabel: "ui",
    accent: "#93c5fd",
    profile: [0.68, 0.96, 0.92, 0.52, 0.28],
    blurb:
      "Views, states, interactions, evidence surfaces, and guarded commit paths.",
  },
  {
    id: "paper",
    label: "Academic paper",
    sceneLabel: "paper",
    accent: "#c4b5fd",
    profile: [1.12, 1.04, 0.86, 0.7, 0.4],
    blurb:
      "Claims, sources, methods, and structure become typed artifact semantics.",
  },
  {
    id: "law",
    label: "Contract / law",
    sceneLabel: "law",
    accent: "#fcd34d",
    profile: [1.18, 0.82, 1.18, 0.76, 0.28],
    blurb:
      "Definitions, obligations, exceptions, remedies, and authority surfaces are projected through the same core machine.",
  },
  {
    id: "benchmark",
    label: "Contest / puzzle / benchmark",
    sceneLabel: "benchmark",
    accent: "#fb7185",
    profile: [0.66, 1.08, 0.72, 1.02, 0.42],
    blurb:
      "Problem packets, verifiers, score surfaces, and replayable traces share one harnessed semantic architecture.",
  },
  {
    id: "workflow",
    label: "Research workflow",
    sceneLabel: "workflow",
    accent: "#86efac",
    profile: [0.94, 0.56, 1.02, 0.68, 0.54],
    blurb:
      "Hypotheses, evidence capture, tool use, and repeatable traces become a bounded operator loop.",
  },
];

const LAYER_OPTIONS = [
  { id: "substrate", label: "Byte substrate" },
  { id: "ir", label: "Semantic IR" },
  { id: "spu", label: "SPU" },
  { id: "harness", label: "Harness" },
  { id: "plugins", label: "Plugins" },
  { id: "traces", label: "Traces" },
];

const META = {
  theorem: {
    group: "System theorem",
    title: "Governed coupling",
    subtitle: "semantic plasticity + logical discipline",
    accent: "#7dd3fc",
    blurb:
      "The SPU supplies semantic plasticity. The harness supplies logical discipline. Agentic capability emerges from their governed coupling.",
    role:
      "Couples probabilistic semantic power to explicit interfaces, traces, contracts, and deterministic lowering.",
    evidence:
      "Inspect Semantic IR, tests, constraints, provenance, and adapter state before any authoritative move.",
    authority:
      "Projections may express authority; they may not mint authority.",
  },
  substrate: {
    group: "Foundation",
    title: "Byte substrate",
    subtitle: "ultimate transformation field",
    accent: "#38bdf8",
    blurb:
      "Every digital artifact terminates in byte transformations. This lattice is the final execution surface.",
    role:
      "Deterministic machine substrate: storage, transport, serialization, execution, and reproducible state change.",
    evidence:
      "Bytes changed or they did not. Lowering and execution must stay inspectable.",
    authority:
      "Operational truth lives here, but meaning is only legible through typed layers above it.",
  },
  ir: {
    group: "Intermediate layer",
    title: "Semantic IR",
    subtitle: "explicit intent before lowering",
    accent: "#67e8f9",
    blurb:
      "A human/machine-legible layer for intent, contracts, tests, constraints, and acceptance criteria before deterministic lowering.",
    role:
      "Makes artifact semantics inspectable, bindable, and testable before byte-level execution.",
    evidence:
      "Same-context evidence, named constraints, proof lanes, and acceptance surfaces belong here.",
    authority:
      "Advisory until bound to gates, validators, and external authority sources.",
  },
  spu: {
    group: "Semantic core",
    title: "SPU",
    subtitle: "semantic processing unit",
    accent: "#67e8f9",
    blurb:
      "The semi-tamed semantic field: generative, compressive, probabilistic, plastic, and powerful.",
    role:
      "Supplies candidate structure, synthesis, reframing, semantic search, and abstraction pressure.",
    evidence:
      "Uncertainty is real. Outputs are proposals until governed, traced, validated, and typed.",
    authority: "Oracle output is advisory only.",
  },
  harness: {
    group: "Governance shell",
    title: "Harness",
    subtitle: "deterministic constitutional shell",
    accent: "#fbbf24",
    blurb:
      "Routing, constraints, validators, interface exposure, memory/tool binding, recurrence management, and trace governance.",
    role:
      "Grounds the SPU in typed interfaces, policy, orchestration, fail-closed checks, and bounded adapters.",
    evidence:
      "Validators, gates, traces, posture, and explicit state exposure must all be visible here.",
    authority:
      "The deterministic adjudicator is the authoritative control surface.",
  },
};

const IR_CARDS = ["intent", "tests", "constraints", "accept", "proof lane", "trace"];

function cx(...parts) {
  return parts.filter(Boolean).join(" ");
}

function damp3(target, source, lambda, delta) {
  target.x = THREE.MathUtils.damp(target.x, source[0], lambda, delta);
  target.y = THREE.MathUtils.damp(target.y, source[1], lambda, delta);
  target.z = THREE.MathUtils.damp(target.z, source[2], lambda, delta);
}

function stableUnitNoise(seed) {
  const raw = Math.sin(seed * 12.9898) * 43758.5453123;
  return raw - Math.floor(raw);
}

function circlePoints(radius, y = 0, segments = 48) {
  return Array.from({ length: segments + 1 }, (_, index) => {
    const angle = (index / segments) * Math.PI * 2;
    return [Math.cos(angle) * radius, y, Math.sin(angle) * radius];
  });
}

function squarePoints(size, y = 0) {
  return [
    [-size, y, -size],
    [size, y, -size],
    [size, y, size],
    [-size, y, size],
    [-size, y, -size],
  ];
}

function getAxisLayout(cfg) {
  const angles = [-Math.PI / 4, Math.PI / 4, (3 * Math.PI) / 4, (-3 * Math.PI) / 4];
  return AXES.map((axis, index) => {
    const angle = angles[index];
    return {
      ...axis,
      angle,
      position: [
        Math.cos(angle) * cfg.axisRadius,
        cfg.substrateY,
        Math.sin(angle) * cfg.axisRadius,
      ],
    };
  });
}

function getDomainLayout(mode, selectedDomain, cfg) {
  const step = (Math.PI * 2) / DOMAINS.length;
  const selectedIndex = Math.max(
    0,
    DOMAINS.findIndex((domain) => domain.id === selectedDomain),
  );
  const baseAngle = mode === "domain" ? Math.PI * 0.22 - selectedIndex * step : Math.PI * 0.16;

  return DOMAINS.map((domain, index) => {
    const angle = index * step + baseAngle;
    const isSelected = domain.id === selectedDomain;
    const radius =
      cfg.pluginRadius +
      (mode === "architecture" ? 0.25 : 0) +
      (mode === "domain" && isSelected ? -0.9 : 0);
    const y =
      cfg.moduleY +
      (mode === "architecture" ? Math.sin(index * 1.7) * 0.18 : 0) +
      (isSelected ? 0.16 : 0);

    return {
      ...domain,
      angle,
      position: [Math.cos(angle) * radius, y, Math.sin(angle) * radius],
      rotation: [0, -angle + Math.PI / 2, 0],
      scale: isSelected ? (mode === "domain" ? 1.26 : 1.08) : mode === "domain" ? 0.94 : 0.88,
    };
  });
}

function getConceptMeta(id) {
  if (META[id]) return META[id];

  const axis = AXES.find((item) => item.id === id);
  if (axis) {
    return {
      group: "ADEU axis",
      title: `${axis.id} — ${axis.title}`,
      subtitle: axis.short,
      accent: axis.accent,
      blurb: axis.blurb,
      role: axis.blurb,
      evidence:
        axis.id === "E"
          ? "Evidence, proof lanes, deterministic validation, and provenance must stay explicit."
          : axis.id === "D"
            ? "Permissions, prohibitions, and approval gates must be typed and fail closed."
            : axis.id === "O"
              ? "Every artifact and relation needs an explicit type and boundary."
              : "Utility must be declared, bounded, and governed rather than smuggled in post hoc.",
      authority:
        axis.id === "D"
          ? "Deontics governs what may, must, and must not happen."
          : "This axis shapes interpretation and control, but not by itself a final authority source.",
    };
  }

  const domain = DOMAINS.find((item) => item.id === id);
  if (domain) {
    return {
      group: "Domain adapter",
      title: domain.label,
      subtitle: "one meta-ontology, one core machine",
      accent: domain.accent,
      blurb: domain.blurb,
      role:
        "Projects the same governed semantic core into a domain-specific artifact family without changing the underlying machine.",
      evidence:
        "Acceptance criteria, verifier shape, evidence surfaces, and authority posture differ by domain while core governance persists.",
      authority:
        "Adapters expose domain interfaces; they do not override harness policy.",
    };
  }

  return META.theorem;
}

function getFocusTarget(selectedConcept, cfg, domainLayout, axisLayout) {
  const domain = domainLayout.find((item) => item.id === selectedConcept);
  if (domain) return domain.position;

  const axis = axisLayout.find((item) => item.id === selectedConcept);
  if (axis) {
    return [axis.position[0], cfg.coreY + 0.85, axis.position[2]];
  }

  if (selectedConcept === "substrate") return [0, cfg.substrateY + 0.35, 0];
  if (selectedConcept === "ir") return [0, cfg.irY + 0.12, 0];
  if (selectedConcept === "spu") return [0, cfg.coreY + 0.2, 0];
  if (selectedConcept === "harness") return [0, cfg.coreY + 0.35, 0];

  return [0, cfg.coreY + 0.2, 0];
}

export default function ADEUStudioMorphicSurface() {
  const [mode, setMode] = useState("vision");
  const [selectedConcept, setSelectedConcept] = useState("theorem");
  const [hoveredConcept, setHoveredConcept] = useState(null);
  const [domain, setDomain] = useState("software");
  const [lane, setLane] = useState("advisory");
  const [activeAxes, setActiveAxes] = useState(["O", "E", "D", "U"]);
  const [layers, setLayers] = useState({
    substrate: true,
    ir: true,
    spu: true,
    harness: true,
    plugins: true,
    traces: true,
  });

  const selectedMeta = useMemo(() => getConceptMeta(selectedConcept), [selectedConcept]);
  const modeConfig = MODE_CONFIGS[mode];
  const evidenceVisible = layers.traces;
  const focusLabel = getConceptMeta(hoveredConcept || selectedConcept).title;

  const handleModeChange = (nextMode) => {
    setMode(nextMode);
    if (nextMode === "vision") setSelectedConcept("theorem");
    if (nextMode === "architecture") setSelectedConcept("harness");
    if (nextMode === "audit") setSelectedConcept("D");
    if (nextMode === "domain") setSelectedConcept(domain);
  };

  const toggleLayer = (key) => {
    setLayers((current) => ({ ...current, [key]: !current[key] }));
  };

  const toggleAxis = (axisId) => {
    setSelectedConcept(axisId);
    setActiveAxes((current) =>
      current.includes(axisId)
        ? current.filter((item) => item !== axisId)
        : [...current, axisId],
    );
  };

  const selectDomain = (domainId) => {
    setDomain(domainId);
    setSelectedConcept(domainId);
  };

  return (
    <div className="h-screen overflow-hidden bg-[#03060b] text-white">
      <div className="pointer-events-none absolute inset-0 bg-[radial-gradient(circle_at_top,rgba(56,189,248,0.14),transparent_28%),radial-gradient(circle_at_85%_18%,rgba(251,191,36,0.10),transparent_22%),linear-gradient(180deg,#05080d_0%,#020407_100%)]" />
      <div className="pointer-events-none absolute inset-0 opacity-40 [background-image:linear-gradient(rgba(255,255,255,0.04)_1px,transparent_1px),linear-gradient(90deg,rgba(255,255,255,0.04)_1px,transparent_1px)] [background-size:72px_72px] [mask-image:radial-gradient(circle_at_center,black,transparent_88%)]" />

      <div className="grid h-full grid-rows-[minmax(0,1fr)_56px] gap-4 p-4">
        <div className="grid min-h-0 grid-cols-1 gap-4 xl:grid-cols-[280px_minmax(0,1fr)_360px]">
          <motion.aside
            initial={{ opacity: 0, x: -16 }}
            animate={{ opacity: 1, x: 0 }}
            transition={{ duration: 0.45 }}
            className="min-h-0 overflow-y-auto"
          >
            <Panel eyebrow="ADEU Studio" title="Morphic operator surface">
              <p className="text-sm leading-6 text-white/72">
                A bounded workbench for harnessing synthetic reason with explicit meta-ontology,
                evidence posture, and governance.
              </p>
              <div className="mt-4 flex flex-wrap gap-2">
                <SmallTag active accent="#67e8f9">
                  evidence-first
                </SmallTag>
                <SmallTag active accent="#c084fc">
                  explicit state
                </SmallTag>
                <SmallTag active accent="#fbbf24">
                  bounded authority
                </SmallTag>
              </div>
            </Panel>

            <Panel eyebrow="Surface modes" title="Morph profile" className="mt-4">
              <div className="grid gap-2">
                {Object.values(MODE_CONFIGS).map((entry) => {
                  const active = mode === entry.id;
                  return (
                    <motion.button
                      key={entry.id}
                      onClick={() => handleModeChange(entry.id)}
                      whileHover={{ scale: 1.01 }}
                      whileTap={{ scale: 0.99 }}
                      className="relative overflow-hidden rounded-2xl border border-white/12 bg-slate-950/80 p-3 text-left shadow-[inset_0_1px_0_rgba(255,255,255,0.04)] transition-colors hover:border-cyan-300/25 hover:bg-slate-900/85"
                      style={{
                        background: active
                          ? "linear-gradient(180deg, rgba(12, 74, 110, 0.92), rgba(8, 23, 40, 0.96))"
                          : "linear-gradient(180deg, rgba(15, 23, 42, 0.96), rgba(2, 6, 23, 0.9))",
                        borderColor: active ? "rgba(103, 232, 249, 0.34)" : "rgba(255, 255, 255, 0.12)",
                        boxShadow: active
                          ? "inset 0 1px 0 rgba(255,255,255,0.05), 0 0 30px rgba(34, 211, 238, 0.12)"
                          : "inset 0 1px 0 rgba(255,255,255,0.04)",
                      }}
                    >
                      {active ? (
                        <motion.div
                          layoutId="mode-highlight"
                          className="absolute inset-0 rounded-2xl bg-[linear-gradient(135deg,rgba(34,211,238,0.20),rgba(8,47,73,0.76))] shadow-[inset_0_0_0_1px_rgba(103,232,249,0.38),0_0_32px_rgba(34,211,238,0.12)]"
                        />
                      ) : null}
                      <div className="relative">
                        <div className="text-[10px] uppercase tracking-[0.24em] text-slate-300/70">
                          {entry.label}
                        </div>
                        <div className="mt-1 text-sm font-medium text-white">{entry.title}</div>
                        <div className="mt-1 text-xs leading-5 text-slate-200/78">
                          {entry.description}
                        </div>
                      </div>
                    </motion.button>
                  );
                })}
              </div>
            </Panel>

            <Panel eyebrow="Dual-lane posture" title="Operator stance" className="mt-4">
              <div className="grid grid-cols-2 gap-2">
                <LaneButton
                  active={lane === "advisory"}
                  accent="#67e8f9"
                  title="Advisory lane"
                  body="Oracle output. Proposals, scenarios, alternatives."
                  onClick={() => setLane("advisory")}
                />
                <LaneButton
                  active={lane === "authoritative"}
                  accent="#fbbf24"
                  title="Authority surface"
                  body="Expressed and gated. Never minted by UI alone."
                  onClick={() => setLane("authoritative")}
                />
              </div>
              <p className="mt-3 text-xs leading-5 text-white/55">
                Required evidence must be visible before an authoritative decision. The UI may
                express authority states, but it may not mint authority.
              </p>
            </Panel>

            <Panel eyebrow="Explicit exposure" title="Layer controls" className="mt-4">
              <div className="grid grid-cols-2 gap-2">
                {LAYER_OPTIONS.map((layer) => (
                  <ToggleChip
                    key={layer.id}
                    label={layer.label}
                    active={layers[layer.id]}
                    accent={layers[layer.id] ? "#67e8f9" : "#475569"}
                    onClick={() => toggleLayer(layer.id)}
                  />
                ))}
              </div>
            </Panel>

            <Panel eyebrow="ADEU" title="Axes" className="mt-4">
              <div className="grid grid-cols-2 gap-2">
                {AXES.map((axis) => (
                  <ToggleChip
                    key={axis.id}
                    label={`${axis.id} — ${axis.title}`}
                    active={activeAxes.includes(axis.id)}
                    accent={axis.accent}
                    onClick={() => toggleAxis(axis.id)}
                  />
                ))}
              </div>
            </Panel>

            <Panel eyebrow="Projection ring" title="Domain adapters" className="mt-4">
              <div className="grid gap-2">
                {DOMAINS.map((entry) => {
                  const active = domain === entry.id;
                  return (
                    <motion.button
                      key={entry.id}
                      onClick={() => selectDomain(entry.id)}
                      whileHover={{ x: 2 }}
                      className="rounded-2xl border border-white/12 bg-[linear-gradient(180deg,rgba(15,23,42,0.94),rgba(2,6,23,0.86))] px-3 py-3 text-left shadow-[inset_0_1px_0_rgba(255,255,255,0.04)] transition-colors hover:border-white/20 hover:bg-[linear-gradient(180deg,rgba(15,23,42,0.98),rgba(3,7,18,0.94))]"
                      style={
                        active
                          ? {
                              background:
                                "linear-gradient(180deg, rgba(15, 23, 42, 0.98), rgba(2, 6, 23, 0.94))",
                              borderColor: `${entry.accent}55`,
                              boxShadow: `inset 0 1px 0 rgba(255,255,255,0.04), 0 0 0 1px ${entry.accent}22, 0 0 24px ${entry.accent}18`,
                            }
                          : {
                              background:
                                "linear-gradient(180deg, rgba(15, 23, 42, 0.94), rgba(2, 6, 23, 0.86))",
                              borderColor: "rgba(255,255,255,0.12)",
                              boxShadow: "inset 0 1px 0 rgba(255,255,255,0.04)",
                            }
                      }
                    >
                      <div className="flex items-start justify-between gap-3">
                        <div>
                          <div className="text-sm font-medium text-white">{entry.label}</div>
                          <div className="mt-1 text-xs leading-5 text-slate-200/78">
                            {entry.blurb}
                          </div>
                        </div>
                        <div
                          className="mt-1 h-2.5 w-2.5 rounded-full"
                          style={{ backgroundColor: entry.accent }}
                        />
                      </div>
                    </motion.button>
                  );
                })}
              </div>
            </Panel>
          </motion.aside>

          <motion.main
            initial={{ opacity: 0, y: 12 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ duration: 0.5 }}
            className="relative min-h-0 overflow-hidden rounded-[30px] border border-white/10 bg-white/[0.03] shadow-[0_18px_80px_rgba(0,0,0,0.4)]"
          >
            <div className="absolute inset-0 bg-[radial-gradient(circle_at_top,rgba(56,189,248,0.12),transparent_30%),radial-gradient(circle_at_78%_14%,rgba(251,191,36,0.08),transparent_20%),linear-gradient(180deg,rgba(255,255,255,0.03),rgba(255,255,255,0.01))]" />
            <div className="absolute inset-0 opacity-50 [background-image:linear-gradient(rgba(255,255,255,0.03)_1px,transparent_1px),linear-gradient(90deg,rgba(255,255,255,0.03)_1px,transparent_1px)] [background-size:64px_64px] [mask-image:radial-gradient(circle_at_center,black,transparent_85%)]" />

            <ADEUScene
              mode={mode}
              domain={domain}
              lane={lane}
              layers={layers}
              activeAxes={activeAxes}
              selectedConcept={selectedConcept}
              hoveredConcept={hoveredConcept}
              onSelect={setSelectedConcept}
              onHover={setHoveredConcept}
            />

            <div className="pointer-events-none absolute inset-0 z-10">
              <AnimatePresence mode="wait">
                <motion.div
                  key={mode}
                  initial={{ opacity: 0, y: -10 }}
                  animate={{ opacity: 1, y: 0 }}
                  exit={{ opacity: 0, y: -10 }}
                  transition={{ duration: 0.24 }}
                  className="absolute left-4 top-4 max-w-[420px] rounded-3xl border border-white/10 bg-slate-950/70 p-4 backdrop-blur-xl shadow-[0_18px_40px_rgba(0,0,0,0.32)]"
                >
                  <div className="text-[10px] uppercase tracking-[0.26em] text-cyan-200/70">
                    {modeConfig.label}
                  </div>
                  <div className="mt-2 text-sm font-semibold text-white/92">{modeConfig.theorem}</div>
                  <div className="mt-2 text-xs leading-5 text-white/58">{modeConfig.description}</div>
                  <div className="mt-3 flex flex-wrap gap-2 text-[11px] font-medium text-white/70">
                    <span className="rounded-full border border-white/10 bg-white/[0.04] px-2 py-1">
                      SPU → Semantic IR → byte substrate
                    </span>
                    <span className="rounded-full border border-white/10 bg-white/[0.04] px-2 py-1">
                      harness governs relations
                    </span>
                  </div>
                </motion.div>
              </AnimatePresence>

              <div className="absolute right-4 top-4 flex max-w-[520px] flex-wrap justify-end gap-2">
                <OverlayChip label="focus" value={focusLabel} />
                <OverlayChip
                  label="evidence"
                  value={evidenceVisible ? "visible" : "hidden"}
                  accent={evidenceVisible ? "#67e8f9" : "#64748b"}
                />
                <OverlayChip
                  label="authority"
                  value={lane === "advisory" ? "advisory only" : "expressed / gated"}
                  accent={lane === "advisory" ? "#67e8f9" : "#fbbf24"}
                />
                <OverlayChip label="adapter" value={getConceptMeta(domain).title} />
              </div>

              <div className="absolute bottom-4 left-4 rounded-2xl border border-white/10 bg-slate-950/60 px-3 py-2 text-[11px] tracking-[0.18em] text-white/55 backdrop-blur-xl">
                CLICK NODES · ORBIT · ZOOM · INSPECT STATE
              </div>
            </div>
          </motion.main>

          <motion.aside
            initial={{ opacity: 0, x: 16 }}
            animate={{ opacity: 1, x: 0 }}
            transition={{ duration: 0.45 }}
            className="min-h-0 overflow-y-auto"
          >
            <AnimatePresence mode="wait">
              <motion.div
                key={`${mode}-${selectedConcept}-${lane}-${domain}`}
                initial={{ opacity: 0, y: 10 }}
                animate={{ opacity: 1, y: 0 }}
                exit={{ opacity: 0, y: -10 }}
                transition={{ duration: 0.22 }}
              >
                <Panel
                  eyebrow={selectedMeta.group}
                  title={selectedMeta.title}
                  accent={selectedMeta.accent}
                >
                  <div className="text-sm leading-6 text-white/74">{selectedMeta.subtitle}</div>
                  <p className="mt-3 text-sm leading-6 text-white/66">{selectedMeta.blurb}</p>

                  <div className="mt-5 space-y-3">
                    <StateRow label="Role" value={selectedMeta.role} />
                    <StateRow label="Evidence" value={selectedMeta.evidence} />
                    <StateRow
                      label="Authority"
                      value={selectedMeta.authority}
                      accent={selectedMeta.accent}
                    />
                  </div>
                </Panel>
              </motion.div>
            </AnimatePresence>

            <Panel eyebrow={modeConfig.profile} title="Surface theorem" className="mt-4">
              <div className="rounded-2xl border border-white/10 bg-white/[0.03] p-3">
                <div className="text-sm font-medium text-white/90">{modeConfig.theorem}</div>
                <div className="mt-2 text-xs leading-5 text-white/58">{modeConfig.description}</div>
              </div>

              <div className="mt-4 grid grid-cols-2 gap-2">
                <MiniMetric label="morph" value={modeConfig.profile} />
                <MiniMetric label="adapter" value={getConceptMeta(domain).title} />
                <MiniMetric
                  label="lane"
                  value={lane === "advisory" ? "advisory only" : "gated surface"}
                />
                <MiniMetric label="evidence" value={evidenceVisible ? "same-context" : "hidden"} />
              </div>
            </Panel>

            <Panel eyebrow="Authority posture" title="Advisory vs authoritative" className="mt-4">
              <div className="grid grid-cols-2 gap-2">
                <div className="rounded-2xl border border-cyan-300/15 bg-cyan-400/[0.06] p-3">
                  <div className="text-[10px] uppercase tracking-[0.24em] text-cyan-200/70">
                    Advisory lane
                  </div>
                  <div className="mt-2 text-xs leading-5 text-white/60">
                    Scenarioing, synthesis, candidate structure, semantic exploration.
                  </div>
                </div>
                <div className="rounded-2xl border border-amber-300/15 bg-amber-400/[0.06] p-3">
                  <div className="text-[10px] uppercase tracking-[0.24em] text-amber-200/70">
                    Authority surface
                  </div>
                  <div className="mt-2 text-xs leading-5 text-white/60">
                    Expressed through explicit gates, validators, source surfaces, and external
                    authority.
                  </div>
                </div>
              </div>

              <div className="mt-4 rounded-2xl border border-white/10 bg-white/[0.03] p-3">
                <div className="text-[10px] uppercase tracking-[0.24em] text-white/45">
                  Explicit state exposure
                </div>
                <div className="mt-3 flex flex-wrap gap-2 text-[11px] font-mono text-white/70">
                  <CodePill>{`mode=${mode}`}</CodePill>
                  <CodePill>{`focus=${selectedConcept}`}</CodePill>
                  <CodePill>{`domain=${domain}`}</CodePill>
                  <CodePill>{`lane=${lane}`}</CodePill>
                  <CodePill>{`axes=${activeAxes.join("") || "none"}`}</CodePill>
                  <CodePill>{`traces=${layers.traces ? "on" : "off"}`}</CodePill>
                </div>
              </div>
            </Panel>
          </motion.aside>
        </div>

        <footer className="relative overflow-hidden rounded-2xl border border-white/10 bg-white/[0.03] px-4 backdrop-blur-xl">
          <div className="absolute inset-0 bg-[linear-gradient(90deg,rgba(56,189,248,0.06),transparent_22%,transparent_78%,rgba(251,191,36,0.05))]" />
          <div className="relative flex h-full items-center justify-between gap-4 text-[11px]">
            <div className="flex flex-wrap items-center gap-3 uppercase tracking-[0.24em] text-white/45">
              <span>ADEU Studio</span>
              <span className="text-cyan-200/70">morphic operator workbench</span>
              <span>profile: {modeConfig.profile}</span>
            </div>

            <div className="flex flex-wrap items-center gap-2 font-mono text-white/70">
              <StatusChip label="mode" value={modeConfig.title} />
              <StatusChip label="focus" value={focusLabel} />
              <StatusChip label="adapter" value={getConceptMeta(domain).title} />
              <StatusChip
                label="authority"
                value={lane === "advisory" ? "advisory" : "expressed / gated"}
                accent={lane === "advisory" ? "#67e8f9" : "#fbbf24"}
              />
              <StatusChip
                label="evidence"
                value={evidenceVisible ? "visible" : "hidden"}
                accent={evidenceVisible ? "#67e8f9" : "#64748b"}
              />
            </div>
          </div>
        </footer>
      </div>
    </div>
  );
}

function Panel({ eyebrow, title, accent, className, children }) {
  return (
    <section
      className={cx(
        "rounded-[26px] border border-white/10 bg-white/[0.04] p-4 backdrop-blur-xl shadow-[0_12px_45px_rgba(0,0,0,0.28)]",
        className,
      )}
      style={
        accent
          ? {
              boxShadow: `0 12px 45px rgba(0,0,0,0.28), inset 0 1px 0 rgba(255,255,255,0.04), 0 0 26px ${accent}12`,
            }
          : undefined
      }
    >
      {eyebrow ? (
        <div className="text-[10px] uppercase tracking-[0.26em] text-white/42">{eyebrow}</div>
      ) : null}
      {title ? <div className="mt-2 text-lg font-semibold text-white/92">{title}</div> : null}
      <div className={title ? "mt-3" : ""}>{children}</div>
    </section>
  );
}

function SmallTag({ children, active, accent = "#67e8f9" }) {
  return (
    <div
      className="rounded-full border px-2.5 py-1 text-[11px] font-medium text-white/72"
      style={
        active
          ? {
              borderColor: `${accent}66`,
              boxShadow: `0 0 18px ${accent}20`,
            }
          : { borderColor: "rgba(255,255,255,0.10)" }
      }
    >
      {children}
    </div>
  );
}

function OverlayChip({ label, value, accent = "#67e8f9" }) {
  return (
    <div
      className="rounded-full border bg-slate-950/70 px-3 py-1.5 text-[11px] font-medium text-white/76 backdrop-blur-xl"
      style={{ borderColor: `${accent}30`, boxShadow: `0 0 18px ${accent}16` }}
    >
      <span className="mr-2 uppercase tracking-[0.2em] text-white/42">{label}</span>
      <span>{value}</span>
    </div>
  );
}

function LaneButton({ active, accent, title, body, onClick }) {
  return (
    <motion.button
      whileHover={{ scale: 1.01 }}
      whileTap={{ scale: 0.99 }}
      onClick={onClick}
      className="rounded-2xl border border-white/12 bg-[linear-gradient(180deg,rgba(15,23,42,0.96),rgba(2,6,23,0.86))] p-3 text-left shadow-[inset_0_1px_0_rgba(255,255,255,0.04)] transition-colors hover:border-white/20"
      style={
        active
          ? {
              background: `linear-gradient(180deg, ${accent}22, rgba(2, 6, 23, 0.92))`,
              borderColor: `${accent}55`,
              boxShadow: `inset 0 1px 0 rgba(255,255,255,0.04), 0 0 0 1px ${accent}22, 0 0 22px ${accent}18`,
            }
          : {
              background: "linear-gradient(180deg, rgba(15, 23, 42, 0.96), rgba(2, 6, 23, 0.86))",
              borderColor: "rgba(255,255,255,0.12)",
              boxShadow: "inset 0 1px 0 rgba(255,255,255,0.04)",
            }
      }
    >
      <div className="text-[10px] uppercase tracking-[0.24em] text-slate-300/70">{title}</div>
      <div className="mt-2 text-xs leading-5 text-slate-200/80">{body}</div>
    </motion.button>
  );
}

function ToggleChip({ label, active, accent, onClick }) {
  return (
    <motion.button
      whileHover={{ y: -1 }}
      whileTap={{ scale: 0.98 }}
      onClick={onClick}
      className="rounded-2xl border px-3 py-2 text-left text-xs font-medium transition-colors"
      style={
        active
          ? {
              borderColor: `${accent}66`,
              background: `${accent}10`,
              boxShadow: `0 0 18px ${accent}18`,
            }
          : {
              borderColor: "rgba(255,255,255,0.10)",
              background: "rgba(255,255,255,0.03)",
            }
      }
    >
      <span className="text-white/72">{label}</span>
    </motion.button>
  );
}

function StateRow({ label, value, accent }) {
  return (
    <div
      className="rounded-2xl border border-white/10 bg-white/[0.03] p-3"
      style={accent ? { boxShadow: `0 0 20px ${accent}10` } : undefined}
    >
      <div className="text-[10px] uppercase tracking-[0.24em] text-white/42">{label}</div>
      <div className="mt-2 text-sm leading-6 text-white/70">{value}</div>
    </div>
  );
}

function MiniMetric({ label, value }) {
  return (
    <div className="rounded-2xl border border-white/10 bg-white/[0.03] p-3">
      <div className="text-[10px] uppercase tracking-[0.24em] text-white/42">{label}</div>
      <div className="mt-2 text-sm text-white/80">{value}</div>
    </div>
  );
}

function CodePill({ children }) {
  return (
    <div className="rounded-full border border-white/10 bg-black/20 px-2.5 py-1">{children}</div>
  );
}

function StatusChip({ label, value, accent = "#67e8f9" }) {
  return (
    <div
      className="rounded-full border bg-black/20 px-3 py-1"
      style={{ borderColor: `${accent}26` }}
    >
      <span className="mr-2 uppercase tracking-[0.18em] text-white/40">{label}</span>
      <span>{value}</span>
    </div>
  );
}

function ADEUScene({
  mode,
  domain,
  lane,
  layers,
  activeAxes,
  selectedConcept,
  hoveredConcept,
  onSelect,
  onHover,
}) {
  const cfg = MODE_CONFIGS[mode];
  const domainLayout = useMemo(() => getDomainLayout(mode, domain, cfg), [mode, domain, cfg]);
  const axisLayout = useMemo(() => getAxisLayout(cfg), [cfg]);
  const focusTarget = useMemo(
    () => getFocusTarget(selectedConcept, cfg, domainLayout, axisLayout),
    [selectedConcept, cfg, domainLayout, axisLayout],
  );

  return (
    <Canvas
      dpr={[1, 1.75]}
      camera={{ position: cfg.camera, fov: 42 }}
      gl={{ antialias: true, alpha: true }}
      onPointerMissed={() => onSelect("theorem")}
      className="h-full w-full"
    >
      <color attach="background" args={["#02050a"]} />
      <fog attach="fog" args={["#02050a", 8, 18]} />
      <ambientLight intensity={0.8} />
      <hemisphereLight intensity={0.55} groundColor="#060b10" />
      <directionalLight position={[0, 5, 5]} intensity={1.6} color="#ffffff" />
      <pointLight position={[4.5, 4.2, 3.2]} intensity={85} distance={18} color="#6ee7ff" />
      <pointLight position={[-4.5, 1.4, 4.5]} intensity={48} distance={16} color="#ffc96d" />
      <pointLight position={[0, -2.8, 0]} intensity={25} distance={10} color="#2a88ff" />

      {layers.substrate ? (
        <ByteSubstrate
          cfg={cfg}
          mode={mode}
          emphasis={selectedConcept === "substrate" || hoveredConcept === "substrate"}
          onSelect={onSelect}
          onHover={onHover}
        />
      ) : null}

      {layers.ir ? (
        <SemanticIR
          cfg={cfg}
          mode={mode}
          emphasis={selectedConcept === "ir" || hoveredConcept === "ir"}
          onSelect={onSelect}
          onHover={onHover}
        />
      ) : null}

      {layers.spu ? (
        <SPUCore
          cfg={cfg}
          mode={mode}
          emphasis={selectedConcept === "spu" || hoveredConcept === "spu"}
          onSelect={onSelect}
          onHover={onHover}
        />
      ) : null}

      {layers.harness ? (
        <HarnessShell
          cfg={cfg}
          mode={mode}
          lane={lane}
          emphasis={selectedConcept === "harness" || hoveredConcept === "harness"}
          onSelect={onSelect}
          onHover={onHover}
        />
      ) : null}

      <ADEUAnchors
        cfg={cfg}
        mode={mode}
        axisLayout={axisLayout}
        activeAxes={activeAxes}
        selectedConcept={selectedConcept}
        hoveredConcept={hoveredConcept}
        onSelect={onSelect}
        onHover={onHover}
      />

      {layers.plugins ? (
        <DomainModules
          mode={mode}
          cfg={cfg}
          domainLayout={domainLayout}
          selectedConcept={selectedConcept}
          hoveredConcept={hoveredConcept}
          onSelect={onSelect}
          onHover={onHover}
        />
      ) : null}

      {layers.traces ? (
        <FlowLines
          cfg={cfg}
          mode={mode}
          lane={lane}
          domain={domain}
          activeAxes={activeAxes}
          domainLayout={domainLayout}
          axisLayout={axisLayout}
        />
      ) : null}

      <GroundGlow cfg={cfg} />

      <CameraRig mode={mode} cfg={cfg} focusTarget={focusTarget} />
    </Canvas>
  );
}

function GroundGlow({ cfg }) {
  const mesh = useRef();

  useFrame((state, delta) => {
    if (!mesh.current) return;
    mesh.current.rotation.z += delta * 0.05;
    const scale = 1 + Math.sin(state.clock.elapsedTime * 0.35) * 0.02;
    mesh.current.scale.setScalar(scale);
  });

  return (
    <mesh ref={mesh} rotation={[-Math.PI / 2, 0, 0]} position={[0, cfg.substrateY - 0.35, 0]}>
      <ringGeometry args={[3.8, 7.6, 80]} />
      <meshBasicMaterial color="#0a1e2f" transparent opacity={0.35} />
    </mesh>
  );
}

function CameraRig({ mode, cfg, focusTarget }) {
  const controls = useRef();
  const sceneCamera = useThree((state) => state.camera);
  const cameraRef = useRef(null);

  useEffect(() => {
    cameraRef.current = sceneCamera;
  }, [sceneCamera]);

  useFrame((_, delta) => {
    const camera = cameraRef.current;
    if (!camera) return;

    const targetPos = new THREE.Vector3(...cfg.camera);
    camera.position.x = THREE.MathUtils.damp(camera.position.x, targetPos.x, 2.25, delta);
    camera.position.y = THREE.MathUtils.damp(camera.position.y, targetPos.y, 2.25, delta);
    camera.position.z = THREE.MathUtils.damp(camera.position.z, targetPos.z, 2.25, delta);

    if (controls.current) {
      controls.current.target.x = THREE.MathUtils.damp(
        controls.current.target.x,
        focusTarget[0],
        3.5,
        delta,
      );
      controls.current.target.y = THREE.MathUtils.damp(
        controls.current.target.y,
        focusTarget[1],
        3.5,
        delta,
      );
      controls.current.target.z = THREE.MathUtils.damp(
        controls.current.target.z,
        focusTarget[2],
        3.5,
        delta,
      );
      controls.current.update();
    }
  });

  return (
    <OrbitControls
      ref={controls}
      enablePan={false}
      enableDamping
      dampingFactor={0.08}
      minDistance={5.2}
      maxDistance={15}
      minPolarAngle={0.55}
      maxPolarAngle={1.42}
      minAzimuthAngle={-Math.PI / 2}
      maxAzimuthAngle={Math.PI / 2}
    />
  );
}

// Deep deterministic layer: every artifact ultimately lands on a byte-level
// transformation field. The instanced voxel lattice keeps that foundation visible.
function ByteSubstrate({ cfg, mode, emphasis, onSelect, onHover }) {
  const group = useRef();
  const instanced = useRef();
  const dummy = useMemo(() => new THREE.Object3D(), []);
  const cells = useMemo(() => {
    const output = [];
    for (let x = -8; x <= 8; x += 1) {
      for (let z = -8; z <= 8; z += 1) {
        const seed = (x + 9) * 100 + (z + 9);
        output.push({
          x: x * 0.34,
          z: z * 0.34,
          phase: stableUnitNoise(seed) * Math.PI * 2,
          scale: 0.6 + stableUnitNoise(seed + 17) * 0.7,
        });
      }
    }
    return output;
  }, []);

  useFrame((state, delta) => {
    if (!group.current || !instanced.current) return;

    damp3(group.current.position, [0, cfg.substrateY, 0], 4, delta);
    damp3(group.current.rotation, [0, mode === "vision" ? 0.1 : 0, 0], 4, delta);

    const time = state.clock.elapsedTime;
    cells.forEach((cell, index) => {
      const height =
        0.16 +
        (Math.sin(time * 1.7 + cell.phase) * 0.5 + 0.5) * 0.32 * cell.scale +
        (emphasis ? 0.08 : 0);
      dummy.position.set(cell.x, height / 2 - 0.02, cell.z);
      dummy.scale.set(1, height, 1);
      dummy.updateMatrix();
      instanced.current.setMatrixAt(index, dummy.matrix);
    });
    instanced.current.instanceMatrix.needsUpdate = true;
  });

  return (
    <group
      ref={group}
      onClick={(event) => {
        event.stopPropagation();
        onSelect("substrate");
      }}
      onPointerEnter={() => onHover("substrate")}
      onPointerLeave={() => onHover(null)}
    >
      <mesh rotation={[-Math.PI / 2, 0, 0]} position={[0, -0.06, 0]}>
        <circleGeometry args={[3.65, 56]} />
        <meshBasicMaterial color="#07111c" transparent opacity={0.55} />
      </mesh>

      <instancedMesh ref={instanced} args={[null, null, cells.length]}>
        <boxGeometry args={[0.075, 1, 0.075]} />
        <meshPhysicalMaterial
          color={emphasis ? "#7fefff" : "#194760"}
          emissive={emphasis ? "#2be8ff" : "#0d3347"}
          emissiveIntensity={emphasis ? 2.2 : 0.7}
          metalness={0.55}
          roughness={0.18}
          clearcoat={1}
        />
      </instancedMesh>

      <Line
        points={squarePoints(3.02, 0.02)}
        color={emphasis ? "#7fefff" : "#2a5c79"}
        lineWidth={1.2}
        transparent
        opacity={0.88}
      />
      <Line
        points={circlePoints(3.3, 0.01, 64)}
        color={emphasis ? "#68e8ff" : "#15384e"}
        lineWidth={0.85}
        transparent
        opacity={0.48}
      />

      <NodeLabel
        position={[0, 0.44, 0]}
        title="Byte substrate"
        subtitle="ultimate transformation field"
        accent="#38bdf8"
        visible={emphasis || mode === "architecture" || mode === "vision"}
      />
    </group>
  );
}

// Human/machine-legible intent layer. This sits between semantic generation
// and deterministic lowering so contracts, tests, and constraints stay explicit.
function SemanticIR({ cfg, mode, emphasis, onSelect, onHover }) {
  const group = useRef();

  useFrame((state, delta) => {
    if (!group.current) return;
    damp3(group.current.position, [0, cfg.irY, 0], 4, delta);
    damp3(group.current.rotation, [0, -state.clock.elapsedTime * 0.05, 0], 2, delta);
  });

  return (
    <group
      ref={group}
      onClick={(event) => {
        event.stopPropagation();
        onSelect("ir");
      }}
      onPointerEnter={() => onHover("ir")}
      onPointerLeave={() => onHover(null)}
    >
      <mesh rotation={[-Math.PI / 2, 0, 0]}>
        <ringGeometry args={[1.3, 2.25, 80]} />
        <meshBasicMaterial
          color={emphasis ? "#79f0ff" : "#123549"}
          transparent
          opacity={emphasis ? 0.5 : 0.28}
        />
      </mesh>

      <Line
        points={circlePoints(1.72, 0.02, 64)}
        color={emphasis ? "#83f1ff" : "#3d6d84"}
        lineWidth={1.15}
        transparent
        opacity={0.9}
      />
      <Line
        points={circlePoints(2.1, 0.015, 64)}
        color={emphasis ? "#73deff" : "#22475a"}
        lineWidth={0.7}
        transparent
        opacity={0.55}
      />

      {IR_CARDS.map((label, index) => {
        const angle = (index / IR_CARDS.length) * Math.PI * 2 + Math.PI / 7;
        const x = Math.cos(angle) * 1.72;
        const z = Math.sin(angle) * 1.72;
        const y = 0.08 + Math.sin(index * 2.1) * 0.03;

        return (
          <Float
            key={label}
            speed={1 + index * 0.12}
            floatIntensity={mode === "vision" ? 0.28 : 0.14}
            rotationIntensity={0.05}
          >
            <group position={[x, y, z]} rotation={[0, -angle + Math.PI / 2, 0]}>
              <RoundedBox args={[0.62, 0.14, 0.24]} radius={0.04} smoothness={4}>
                <meshPhysicalMaterial
                  color="#16354b"
                  emissive={emphasis ? "#1b819f" : "#0d3142"}
                  emissiveIntensity={emphasis ? 1.6 : 0.7}
                  metalness={0.7}
                  roughness={0.22}
                  clearcoat={1}
                  transparent
                  opacity={0.94}
                />
              </RoundedBox>

              {mode !== "vision" || emphasis ? (
                <Html center transform distanceFactor={10} position={[0, 0.16, 0]}>
                  <div className="rounded-full border border-cyan-300/20 bg-slate-950/70 px-2 py-1 text-[9px] uppercase tracking-[0.16em] text-white/70 backdrop-blur-md">
                    {label}
                  </div>
                </Html>
              ) : null}
            </group>
          </Float>
        );
      })}

      <NodeLabel
        position={[0, 0.36, 0]}
        title="Semantic IR"
        subtitle="explicit intent before lowering"
        accent="#67e8f9"
        visible={emphasis || mode !== "vision"}
      />
    </group>
  );
}

// The SPU is intentionally not a generic "AI brain". It is a semi-fluid
// semantic core: high-dimensional, probabilistic, generative, and only half tamed.
function SPUCore({ cfg, mode, emphasis, onSelect, onHover }) {
  const group = useRef();

  useFrame((state, delta) => {
    if (!group.current) return;
    const time = state.clock.elapsedTime;
    damp3(
      group.current.position,
      [0, cfg.coreY + Math.sin(time * 0.8) * 0.04, 0],
      4,
      delta,
    );
    damp3(
      group.current.scale,
      [
        cfg.coreScale + (emphasis ? 0.04 : 0),
        cfg.coreScale + (emphasis ? 0.04 : 0),
        cfg.coreScale + (emphasis ? 0.04 : 0),
      ],
      4,
      delta,
    );
    group.current.rotation.y += delta * (mode === "vision" ? 0.16 : 0.12);
  });

  return (
    <group
      ref={group}
      onClick={(event) => {
        event.stopPropagation();
        onSelect("spu");
      }}
      onPointerEnter={() => onHover("spu")}
      onPointerLeave={() => onHover(null)}
    >
      <mesh>
        <sphereGeometry args={[1.08, 64, 64]} />
        <MeshDistortMaterial
          color="#8af4ff"
          emissive="#28ddff"
          emissiveIntensity={emphasis ? 2.8 : 1.8}
          metalness={0.24}
          roughness={0.1}
          distort={mode === "vision" ? 0.42 : 0.3}
          speed={2.1}
          transparent
          opacity={0.94}
        />
      </mesh>

      <mesh scale={0.58}>
        <icosahedronGeometry args={[1, 2]} />
        <meshBasicMaterial color="#e6fcff" wireframe transparent opacity={0.22} />
      </mesh>

      <mesh scale={1.38} rotation={[Math.PI / 4, 0, 0]}>
        <icosahedronGeometry args={[1, 1]} />
        <meshBasicMaterial
          color={emphasis ? "#79efff" : "#2b5a73"}
          wireframe
          transparent
          opacity={0.16}
        />
      </mesh>

      <mesh rotation={[Math.PI / 2, 0, 0]} scale={1.52}>
        <torusGeometry args={[1.02, 0.02, 16, 100]} />
        <meshBasicMaterial
          color={emphasis ? "#92f8ff" : "#2c6681"}
          transparent
          opacity={0.62}
        />
      </mesh>

      <Sparkles
        count={100}
        scale={3}
        size={2.4}
        speed={0.45}
        opacity={0.58}
        color={emphasis ? "#d5fbff" : "#77dff7"}
      />

      <pointLight intensity={emphasis ? 18 : 12} distance={6.5} color="#5ee7ff" />

      <NodeLabel
        position={[0, 1.7, 0]}
        title="SPU"
        subtitle="semantic processing unit"
        accent="#67e8f9"
        visible
      />
    </group>
  );
}

// The harness is the deterministic constitutional shell around the SPU:
// routing, gates, validation, recurrence management, and bounded interfaces.
function HarnessShell({ cfg, mode, lane, emphasis, onSelect, onHover }) {
  const group = useRef();
  const ringY = mode === "architecture" ? 0.78 : 0.62;
  const r = cfg.harnessRadius;
  const nodePositions = [
    [r, 0, 0],
    [0, 0, r],
    [-r, 0, 0],
    [0, 0, -r],
  ];

  useFrame((_, delta) => {
    if (!group.current) return;
    damp3(group.current.position, [0, cfg.coreY, 0], 4, delta);
    damp3(
      group.current.scale,
      [
        cfg.shellScale + (emphasis ? 0.03 : 0),
        cfg.shellScale + (emphasis ? 0.03 : 0),
        cfg.shellScale + (emphasis ? 0.03 : 0),
      ],
      4,
      delta,
    );
    group.current.rotation.y += delta * 0.08;
  });

  return (
    <group
      ref={group}
      onClick={(event) => {
        event.stopPropagation();
        onSelect("harness");
      }}
      onPointerEnter={() => onHover("harness")}
      onPointerLeave={() => onHover(null)}
    >
      <Line
        points={[...nodePositions, nodePositions[0]]}
        color={emphasis ? "#ffd27a" : "#6a5a38"}
        lineWidth={1.2}
        transparent
        opacity={0.86}
      />
      <Line
        points={circlePoints(r * 0.92, ringY, 64)}
        color={lane === "authoritative" || emphasis ? "#ffd37b" : "#6a5c3a"}
        lineWidth={1.05}
        transparent
        opacity={0.82}
      />
      <Line
        points={circlePoints(r * 0.92, -ringY, 64)}
        color={lane === "authoritative" || emphasis ? "#ffd37b" : "#6a5c3a"}
        lineWidth={1.05}
        transparent
        opacity={0.62}
      />
      <Line
        points={circlePoints(1.16, 0, 64)}
        color={emphasis ? "#7be9ff" : "#214a63"}
        lineWidth={0.85}
        transparent
        opacity={0.72}
      />

      {nodePositions.map((position, index) => (
        <group key={index}>
          <Line
            points={[
              [position[0], -ringY, position[2]],
              [position[0], ringY, position[2]],
            ]}
            color="#6e7480"
            lineWidth={0.75}
            transparent
            opacity={0.6}
          />
          <Line
            points={[
              [0, 0, 0],
              [position[0] * 0.72, 0, position[2] * 0.72],
            ]}
            color="#65ddff"
            lineWidth={0.8}
            transparent
            opacity={0.5}
          />
          <SwitchNode position={position} active={lane === "authoritative" || emphasis} />
        </group>
      ))}

      {Array.from({ length: 8 }).map((_, index) => {
        const angle = (index / 8) * Math.PI * 2 + Math.PI / 8;
        const x = Math.cos(angle) * r * 0.92;
        const z = Math.sin(angle) * r * 0.92;
        return (
          <mesh key={index} position={[x, ringY, z]}>
            <sphereGeometry args={[0.065, 16, 16]} />
            <meshBasicMaterial
              color={lane === "authoritative" ? "#ffd887" : "#6a6f77"}
              transparent
              opacity={0.85}
            />
          </mesh>
        );
      })}

      <NodeLabel
        position={[0, ringY + 0.88, 0]}
        title="Harness"
        subtitle="deterministic constitutional shell"
        accent="#fbbf24"
        visible={emphasis || mode !== "vision"}
      />
    </group>
  );
}

function SwitchNode({ position, active }) {
  const group = useRef();

  useFrame((_, delta) => {
    if (!group.current) return;
    group.current.rotation.y += delta * 0.4;
  });

  return (
    <group ref={group} position={position}>
      <RoundedBox args={[0.24, 0.24, 0.24]} radius={0.04} smoothness={4}>
        <meshPhysicalMaterial
          color={active ? "#ffd271" : "#4b4d50"}
          emissive={active ? "#ffbb3e" : "#1c1d20"}
          emissiveIntensity={active ? 1.4 : 0.3}
          metalness={1}
          roughness={0.18}
          clearcoat={1}
        />
      </RoundedBox>
      <mesh scale={1.45}>
        <boxGeometry args={[0.2, 0.2, 0.2]} />
        <meshBasicMaterial color={active ? "#ffe4a9" : "#52565d"} wireframe transparent opacity={0.4} />
      </mesh>
    </group>
  );
}

// O / E / D / U are not decorative badges. They are structural towers that
// intersect the IR and governance shell so typing remains inspectable in-scene.
function ADEUAnchors({
  cfg,
  mode,
  axisLayout,
  activeAxes,
  selectedConcept,
  hoveredConcept,
  onSelect,
  onHover,
}) {
  const topPoints = axisLayout.map((axis) => [
    axis.position[0],
    cfg.coreY + 1.35,
    axis.position[2],
  ]);

  return (
    <group>
      {mode === "audit" ? (
        <Line
          points={[...topPoints, topPoints[0]]}
          color="#a6b5c8"
          lineWidth={0.8}
          transparent
          opacity={0.35}
        />
      ) : null}

      {axisLayout.map((axis) => (
        <AxisTower
          key={axis.id}
          axis={axis}
          cfg={cfg}
          mode={mode}
          active={activeAxes.includes(axis.id)}
          emphasis={selectedConcept === axis.id || hoveredConcept === axis.id}
          onSelect={onSelect}
          onHover={onHover}
        />
      ))}
    </group>
  );
}

function AxisTower({ axis, cfg, mode, active, emphasis, onSelect, onHover }) {
  const group = useRef();
  const localIrY = cfg.irY - cfg.substrateY;
  const localHarnessY = cfg.coreY + 0.28 - cfg.substrateY;
  const topY = cfg.coreY + 1.38 - cfg.substrateY;

  useFrame((state, delta) => {
    if (!group.current) return;
    const pulse = active ? 0.05 + Math.sin(state.clock.elapsedTime * 1.7 + axis.angle) * 0.02 : 0;
    damp3(
      group.current.position,
      [
        axis.position[0],
        axis.position[1],
        axis.position[2],
      ],
      4,
      delta,
    );
    damp3(
      group.current.scale,
      [
        1 + pulse + (emphasis ? 0.04 : 0),
        1 + pulse + (emphasis ? 0.04 : 0),
        1 + pulse + (emphasis ? 0.04 : 0),
      ],
      4,
      delta,
    );
  });

  return (
    <group
      ref={group}
      onClick={(event) => {
        event.stopPropagation();
        onSelect(axis.id);
      }}
      onPointerEnter={() => onHover(axis.id)}
      onPointerLeave={() => onHover(null)}
    >
      <mesh position={[0, topY / 2, 0]}>
        <cylinderGeometry args={[0.05, 0.05, topY, 12]} />
        <meshBasicMaterial
          color={active ? axis.accent : "#30404f"}
          transparent
          opacity={active ? 0.75 : 0.26}
        />
      </mesh>

      <mesh position={[0, localIrY, 0]}>
        <sphereGeometry args={[0.11, 20, 20]} />
        <meshBasicMaterial
          color={active ? axis.accent : "#44525c"}
          transparent
          opacity={active ? 0.9 : 0.42}
        />
      </mesh>

      <mesh position={[0, localHarnessY, 0]}>
        <sphereGeometry args={[0.15, 20, 20]} />
        <meshBasicMaterial
          color={active ? axis.accent : "#52616d"}
          transparent
          opacity={active ? 0.95 : 0.35}
        />
      </mesh>

      <Line
        points={[
          [0, localIrY, 0],
          [-axis.position[0], cfg.irY - cfg.substrateY, -axis.position[2]],
        ]}
        color={active ? axis.accent : "#43515e"}
        lineWidth={0.7}
        transparent
        opacity={active ? 0.6 : 0.22}
      />
      <Line
        points={[
          [0, localHarnessY, 0],
          [-axis.position[0], cfg.coreY + 0.28 - cfg.substrateY, -axis.position[2]],
        ]}
        color={active ? axis.accent : "#43515e"}
        lineWidth={0.85}
        transparent
        opacity={active ? 0.72 : 0.26}
      />

      <NodeLabel
        position={[0, topY + 0.28, 0]}
        title={`${axis.id} — ${axis.title}`}
        subtitle={axis.short}
        accent={axis.accent}
        visible={mode === "audit" || emphasis || active}
      />
    </group>
  );
}

// Domain adapters project the same meta-ontology into different artifact classes.
// The outer ring reconfigures, but the governed core stays invariant.
function DomainModules({
  mode,
  cfg,
  domainLayout,
  selectedConcept,
  hoveredConcept,
  onSelect,
  onHover,
}) {
  return (
    <group>
      {domainLayout.map((item) => (
        <DomainModule
          key={item.id}
          item={item}
          mode={mode}
          selected={selectedConcept === item.id}
          hovered={hoveredConcept === item.id}
          onSelect={onSelect}
          onHover={onHover}
        />
      ))}
    </group>
  );
}

function DomainModule({ item, mode, selected, hovered, onSelect, onHover }) {
  const group = useRef();
  const seed = useMemo(() => stableUnitNoise(item.position[0] + item.position[2]) * 10, [item.position]);

  useFrame((state, delta) => {
    if (!group.current) return;
    const bob = Math.sin(state.clock.elapsedTime * 0.9 + seed) * 0.06;
    damp3(
      group.current.position,
      [item.position[0], item.position[1] + bob, item.position[2]],
      4,
      delta,
    );
    damp3(
      group.current.scale,
      [
        item.scale + (selected ? 0.06 : hovered ? 0.03 : 0),
        item.scale + (selected ? 0.06 : hovered ? 0.03 : 0),
        item.scale + (selected ? 0.06 : hovered ? 0.03 : 0),
      ],
      4,
      delta,
    );
    damp3(group.current.rotation, item.rotation, 4, delta);
  });

  return (
    <group
      ref={group}
      onClick={(event) => {
        event.stopPropagation();
        onSelect(item.id);
      }}
      onPointerEnter={() => onHover(item.id)}
      onPointerLeave={() => onHover(null)}
    >
      <RoundedBox args={[1.08, 0.18, 0.72]} radius={0.06} smoothness={4} position={[0, 0, 0]}>
        <meshPhysicalMaterial
          color="#0e1721"
          emissive={selected ? item.accent : "#111827"}
          emissiveIntensity={selected ? 0.3 : 0.08}
          metalness={0.92}
          roughness={0.18}
          clearcoat={1}
        />
      </RoundedBox>

      {item.profile.map((height, index) => (
        <RoundedBox
          key={index}
          args={[0.12, height, 0.12]}
          radius={0.03}
          smoothness={4}
          position={[-0.32 + index * 0.16, height / 2 + 0.12, 0]}
        >
          <meshPhysicalMaterial
            color={item.accent}
            emissive={item.accent}
            emissiveIntensity={selected || mode === "domain" ? 1.1 : 0.55}
            metalness={0.9}
            roughness={0.18}
            clearcoat={1}
          />
        </RoundedBox>
      ))}

      <mesh position={[0, 0.98, 0]}>
        <torusGeometry args={[0.42, 0.014, 16, 72]} />
        <meshBasicMaterial
          color={item.accent}
          transparent
          opacity={selected || mode === "domain" ? 0.8 : 0.34}
        />
      </mesh>

      <NodeLabel
        position={[0, 1.25, 0]}
        title={item.label}
        subtitle={`adapter · ${item.sceneLabel}`}
        accent={item.accent}
        visible={selected || hovered || mode === "domain"}
      />
    </group>
  );
}

// Flow geometry makes the theorem visible:
// SPU = semantic plasticity
// Harness = logical discipline
// Coupling = governed agentic capability
function FlowLines({ cfg, mode, lane, domain, activeAxes, domainLayout, axisLayout }) {
  const selectedDomain = domainLayout.find((item) => item.id === domain) || domainLayout[0];
  const ringY = cfg.coreY + (mode === "architecture" ? 0.78 : 0.62);
  const nodeRadius = cfg.harnessRadius;

  const switchPoints = [
    [nodeRadius, cfg.coreY, 0],
    [0, cfg.coreY, nodeRadius],
    [-nodeRadius, cfg.coreY, 0],
    [0, cfg.coreY, -nodeRadius],
  ];

  return (
    <group>
      {/* Semantic plasticity lane: advisory traffic resolves toward the SPU. */}
      <Line
        points={[
          [-3.15, cfg.coreY + 1.75, 0.15],
          [-1.75, cfg.coreY + 0.82, 0.08],
          [0, cfg.coreY, 0],
        ]}
        color="#70e7ff"
        lineWidth={1.2}
        transparent
        opacity={lane === "advisory" ? 0.92 : 0.34}
      />

      {/* Authority surface: a separate, gated line terminates at harness switchgear. */}
      <Line
        points={[
          [3.15, cfg.coreY + 1.75, 0.15],
          [1.82, cfg.coreY + 0.95, 0.1],
          [cfg.harnessRadius, cfg.coreY, 0],
        ]}
        color="#ffd074"
        lineWidth={1.2}
        transparent
        opacity={lane === "authoritative" ? 0.92 : 0.34}
      />

      {switchPoints.map((point, index) => (
        <Line
          key={`semantic-${index}`}
          points={[
            [0, cfg.coreY, 0],
            [point[0] * 0.5, cfg.coreY + 0.1, point[2] * 0.5],
            [point[0], cfg.coreY, point[2]],
          ]}
          color="#65e3ff"
          lineWidth={1}
          transparent
          opacity={mode === "vision" ? 0.55 : 0.76}
        />
      ))}

      {switchPoints.map((point, index) => (
        <Line
          key={`lower-${index}`}
          points={[
            [point[0], cfg.coreY, point[2]],
            [point[0] * 0.82, cfg.irY + 0.2, point[2] * 0.82],
            [point[0] * 0.95, cfg.irY, point[2] * 0.95],
          ]}
          color="#ffc96d"
          lineWidth={0.9}
          transparent
          opacity={0.62}
        />
      ))}

      {Array.from({ length: 10 }).map((_, index) => {
        const angle = (index / 10) * Math.PI * 2;
        const x = Math.cos(angle) * 1.55;
        const z = Math.sin(angle) * 1.55;
        return (
          <Line
            key={`to-substrate-${index}`}
            points={[
              [x, cfg.irY, z],
              [x * 1.15, cfg.substrateY + 0.26, z * 1.15],
              [x * 1.48, cfg.substrateY + 0.02, z * 1.48],
            ]}
            color="#ffbf64"
            lineWidth={0.72}
            transparent
            opacity={0.45}
          />
        );
      })}

      {domainLayout.map((item) => {
        const bright = item.id === domain || mode === "domain";
        return (
          <Line
            key={`module-${item.id}`}
            points={[
              item.position,
              [item.position[0] * 0.72, cfg.coreY + 0.9, item.position[2] * 0.72],
              [item.position[0] * 0.44, cfg.coreY + 0.24, item.position[2] * 0.44],
            ]}
            color={bright ? item.accent : "#334c5d"}
            lineWidth={bright ? 1.06 : 0.74}
            transparent
            opacity={bright ? 0.92 : 0.3}
          />
        );
      })}

      {mode === "audit"
        ? activeAxes.map((axisId) => {
            const axis = axisLayout.find((item) => item.id === axisId);
            if (!axis) return null;
            return (
              <Line
                key={`audit-${axisId}`}
                points={[
                  selectedDomain.position,
                  [axis.position[0], cfg.coreY + 1.05, axis.position[2]],
                  [axis.position[0], ringY, axis.position[2]],
                  [0, cfg.coreY, 0],
                ]}
                color={axis.accent}
                lineWidth={1.05}
                transparent
                opacity={0.74}
              />
            );
          })
        : null}
    </group>
  );
}

function NodeLabel({ position, title, subtitle, accent = "#67e8f9", visible }) {
  if (!visible) return null;

  return (
    <Html center transform position={position} distanceFactor={8.6}>
      <div
        className="pointer-events-none min-w-[140px] rounded-2xl border bg-slate-950/70 px-3 py-2 text-center backdrop-blur-xl"
        style={{
          borderColor: `${accent}2e`,
          boxShadow: `0 0 28px ${accent}12`,
        }}
      >
        <div className="text-[10px] uppercase tracking-[0.2em]" style={{ color: accent }}>
          {title}
        </div>
        <div className="mt-1 text-[11px] text-white/70">{subtitle}</div>
      </div>
    </Html>
  );
}
