# Assessment of DRAFT_NEXT_ARC_OPTIONS_v4_SYNTHESIS.md

This report provides an assessment of the consolidated `docs/DRAFT_NEXT_ARC_OPTIONS_v4_SYNTHESIS.md` draft against the current repository state, highlighting extra edges, enhancements, and expansions across the synthesized paths.

## 1. Repository State Context

The synthesis natively acknowledges that `vNext+16` (formal integrity) is complete and stops short of modifying frozen `vNext+14` provider parity layers. The document accurately reflects the operational reality: the underlying systems are stable, deterministic, and highly audited, meaning the repository is ripe for either user-facing productization (`S3`) or deepening the logical rigor (`S1`, `S4`, `S6`).

## 2. Edges and Gaps Identified

### Cycle-Policy Expansion Edge (S1)
- **Edge**: Path S1 suggests extending D2's cycle policy scope beyond the `E` layer to include `D` layer dependency cycles. However, `D` layer cycles are rarely simple `depends_on` relationships; they often involve complex modal resolutions like `excepts` boundaries (e.g., Policy A excepts Policy B, Policy B excepts Policy A). Treating these as standard "dependency cycles" might falsely flag valid, structurally bounded conflict-resolution rules.
- **Remediation**: The definition of cycle detection in the `D` layer must be rigidly decoupled from the `E` layer algorithm. An explicit check for "exception loops" versus "dependency loops" must be defined.

### Lossy Coherence Mapping (S4)
- **Edge**: S4 proposes a Cross-IR Coherence Bridge (Concept IR ↔ Core-IR). Concept IR carries concepts like tournaments, generation candidates, and scoring distributions (`concepts.tournament.live_generation`), which do not have native 1:1 representational equivalents in the strict, flattened `O/E/D/U` layers of `adeu_core_ir@0.1`.
- **Remediation**: Establish a "bridge projection" contract that explicitly dictates how unmappable Concept IR artifacts are safely dropped or rolled up into `E`-layer `Evidence` nodes in the Core-IR pipeline without causing validation failures.

### Tooling Consolidation Determinism Risks (S5)
- **Edge**: Path S5 proposes extracting shared manifest/artifact validations and evaluating schema-family consolidation. Because the stop-gate metrics explicitly lock hash formulations down to specific keys and schema versions (e.g., `stop_gate_metrics@1`), consolidating schemas directly threatens the historical deterministic parity of v14/v15/v16 fixtures.
- **Remediation**: S5 must explicitly mandate that *refactored tooling must reproduce the exact `sha256` artifact hashes* of prior v14-v16 fixtures to prove the refactor is safe. A "migration determinism" test suite should be the first deliverable of S5.

## 3. Recommended Enhancements

### Deterministic UI Projections (S3a)
- **Enhancement**: Path S3a proposes a read-only surface and deterministic render-payload builders. To maintain the project's strict determinism ethos, the layout coordinates/groupings for the UI should themselves be a versioned artifact (`adeu_lane_layout@0.1`), mapping O/E/D/U nodes deterministically into visual bounding contexts.
- **Value**: Prevents front-end code from introducing arbitrary, non-deterministic sorting or grouping logic that obscures the fidelity of the backend core-IR payloads.

### Evidence Linkage in Normative Advice (S6)
- **Enhancement**: S6 proposes non-authoritative gating advice. The advice artifact (`adeu_gating_advice@0.1`) should structurally mandate `justification_refs`: an array of explicit core-IR node IDs (`D`-node laws or `E`-node evidence) that triggered the advice.
- **Value**: Ensure the advice layer isn't a black box, maintaining the explicitly interconnected nature of the trust lanes and guaranteeing explainability all the way down to the base IR.

## 4. Possible Expansions

### Soft Constraint / Goal Mapping (S8)
- **Expansion**: For the future solver semantics v4 expansion, soft constraints and stochastic optimizations should be strictly partitioned into the `U` layer (Metrics, Preferences, Goals) of `adeu_core_ir`. 
- **Value**: This protects the `D` layer (Norms, Policies, Constraints) from probabilistic blurring, retaining hard deontic logic while cleanly integrating utility-based optimization into the existing IR lanes.

### Proposer Abuse / Quota Manifest (S3b)
- **Expansion**: Before activating `S3b` (Core-IR Proposer Activation), a deterministic quota and abuse-protection schema (e.g., `adeu_provider_quota@0.1`) should be introduced.
- **Value**: Generating full O/E/D/U tree projections via LLM endpoints can be highly token-intensive. A structural budget tracker prevents runaway synthesis loops from exhausting underlying provider allocations in production scenarios.
