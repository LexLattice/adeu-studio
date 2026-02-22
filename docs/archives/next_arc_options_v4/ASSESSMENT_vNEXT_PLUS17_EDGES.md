# Assessment of LOCKED_CONTINUATION_vNEXT_PLUS17.md

This report provides a thorough assessment of the drafted `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md` against the existing repository state, focusing on edges, enhancements, and possible expansions for the Path S1 (Integrity Diagnostics Expansion) thin slice.

## 1. Repository State Context

The repository recently locked and implemented `vNext+16`, establishing the baseline for deterministic dangling references, cycle policies, and deontic conflicts. The `vNext+17` draft correctly identifies that it must strictly build on this foundation without mutating `adeu_core_ir@0.1` validation or `vNext+14` provider parity. The draft focuses on Path S1 (E1-E4), extending the integrity diagnostics to be deeper but strictly non-authoritative.

## 2. Edges and Gaps Identified

### Cycle Taxonomy Ambiguity (E2)
- **Edge**: The draft defines `dependency_loop` and `exception_loop` for `D`-layer cycles, mapped based on the presence of an `excepts` edge. However, if a cycle contains *only* `excepts` edges (e.g., A excepts B, B excepts A), it is fundamentally different in normative resolution than a cycle containing a mix of `depends_on` and `excepts`. Both are currently grouped into `exception_loop`.
- **Remediation**: The taxonomy should ideally distinguish `pure_exception_loop` from `mixed_normative_loop` to provide a clearer deterministic signal for downstream policy resolution.

### Deontic Tension Mapping (E3)
- **Edge**: The draft accurately defers the `{obligatory, permitted}` modality pair, locking in only `{forbidden, permitted}` as `deontic_tension`. While safe, this creates an asymmetric handling of the `permitted` modality that might complicate future unified normative resolution engines.
- **Remediation**: Explicitly document *why* `{obligatory, permitted}` is deferred (e.g., because "permitted" often acts as an exception to "forbidden" but is redundant or non-conflicting with "obligatory"). Recording the rationale in the lock prevents future regressions in the deductive logic.

### Diagnostic Volume Cap Risk (E1/E2/E3)
- **Edge**: The draft hardcodes an emission cap of `1000` issues/cycles/conflicts per fixture, failing closed with `URM_ADEU_INTEGRITY_FIXTURE_INVALID` if exceeded. While necessary for determinism, large provider-generated graphs might legitimately exceed this count with structurally valid but noisy data, rendering the entire fixture "invalid" rather than just "noisy_but_valid".
- **Remediation**: Ensure the `1000` cap is strictly enforced on *canonicalized/deduplicated* outputs, not intermediate candidate generation, to avoid premature rejection of large graphs.

## 3. Recommended Enhancements

### Cross-Diagnostic References
- **Enhancement**: When `E1` (Reference Integrity) identifies a `duplicate_edge_identity`, that duplicate edge might participate in an `E2` (Cycle Policy) loop. Currently, these diagnostic artifacts are isolated. 
- **Value**: Adding an optional (but deterministic) linkage or standardized trace ID across `E1`, `E2`, and `E3` would allow downstream explainability tools to understand when a structural flaw (duplicate edge) is the root cause of a semantic flaw (cycle or conflict).

### Manifest Hash Anchoring (E4)
- **Enhancement**: The draft hashes the `vnext_plus17_manifest.json` as part of the transfer report. To ensure absolute CI resilience, the report should ideally hash the *run payloads themselves* (the actual fixture contents) rather than just the manifest index.
- **Value**: Prevents a scenario where a developer mutates a fixture payload on disk without updating the manifest index, which could silently pass the manifest hash check but alter the deterministic diagnostic output logic.

## 4. Possible Expansions

### Validation-Bypass Fixture Harness
- **Expansion**: The draft explicitly requires deterministic "validator-bypass malformed-payload cases" to test extended diagnostics without failing standard `adeu_core_ir` checks. Creating a dedicated, versioned `adeu_bypass_runner@0.1` utility specifically for loading these diagnostic fixtures would cleanly separate this logic from standard runtime projection pipelines.
- **Value**: Prevents the test harness logic needed for `vNext+17` from leaking into or inadvertently weakening the production strict-validation loaders.

### Provider Quota Integration
- **Expansion**: Even though `vNext+17` generates diagnostics from persisted artifacts (no live live provider calls), future S3b arcs will. Designing the schema layouts for E1/E2/E3 to optionally receive a `generation_cost_ref` now would save a forced schema migration later when live proposers are re-enabled.
