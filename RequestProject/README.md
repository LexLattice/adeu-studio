# RequestProject

Temporary Lean 4.28 / Mathlib 4.28 workspace for the ASIR formal sidecar.

Purpose:

- hold the isolated Lean toolchain compatible with Aristotle;
- provide a bounded place for materializing the ASIR proof-mirror kernels later;
- stay separate from the existing `packages/adeu_lean` lane until an explicit lock says
  otherwise.

Current state:

- the authoritative formal notes live under `docs/formal/asir/`;
- this workspace is scaffolded and buildable, but the ASIR kernel `.lean` files are
  still planned rather than fully materialized here.

Planned source paths:

- `RequestProject/ASIRKernel.lean`
- `RequestProject/ASIRKernelHybrid.lean`
- `RequestProject/ASIRKernelGating.lean`
