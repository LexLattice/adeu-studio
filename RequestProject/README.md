# RequestProject

Temporary Lean 4.28 / Mathlib 4.28 workspace for the ASIR formal sidecar.

Purpose:

- hold the isolated Lean toolchain compatible with Aristotle;
- provide a bounded place for materializing and replaying the ASIR proof-mirror
  kernels;
- stay separate from the existing `packages/adeu_lean` lane until an explicit lock says
  otherwise.

Current state:

- the authoritative formal notes live under `docs/formal/asir/`;
- this workspace is scaffolded and buildable, but the ASIR kernel `.lean` files are not
  yet committed here;
- Aristotle has now produced an off-repo canonical-pack proposal that is suitable for a
  later maintainer-side import and replay pass;
- until that import happens, this workspace remains a reserved Lean sidecar shell rather
  than the authoritative home of the ASIR proofs.

Planned canonical source paths:

- `RequestProject/ASIRKernel.lean`
- `RequestProject/ASIRKernelHybrid.lean`
- `RequestProject/ASIRKernelGating.lean`
- `RequestProject/ASIRKernelCheckpointArtifacts.lean`
- `RequestProject/ASIRKernelTargetedPipeline.lean`

Planned import surface:

- `RequestProject.lean` should expose only the canonical pack above by default;
- the older blanket pipeline should not remain in the default import surface once the
  formal lane is imported.

Legacy posture:

- if the older blanket pipeline is retained for historical comparison, it should move
  under a clearer legacy namespace rather than live beside the canonical pack as a
  peer module;
- compatibility shims are acceptable during transition, but the canonical pack should
  remain the only default proof surface.
