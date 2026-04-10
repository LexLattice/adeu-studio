"use client";

import dynamic from "next/dynamic";

const ADEUStudioMorphicSurface = dynamic(
  () => import("../../../prototypes/adeu-studio-morphic-surface.jsx"),
  {
    ssr: false,
    loading: () => (
      <main className="min-h-screen bg-[#06131b] text-[#dffcff]">
        <div className="flex min-h-screen items-center justify-center px-6">
          <div className="max-w-xl space-y-4 text-center">
            <p className="text-xs uppercase tracking-[0.35em] text-cyan-300/70">
              ADEU Studio
            </p>
            <h1 className="text-3xl font-semibold text-white">
              Loading morphic surface
            </h1>
            <p className="text-sm leading-6 text-cyan-50/75">
              Initializing the bounded operator workbench, semantic lattice, and
              governed scene overlays.
            </p>
          </div>
        </div>
      </main>
    ),
  },
);

export default function MorphicStudioPage() {
  return <ADEUStudioMorphicSurface />;
}
