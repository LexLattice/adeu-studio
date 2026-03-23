# 3. The Architecture Compiler: Resolving the "Missing IR" Paradox

**Status:** Proposed Architecture Draft
**Module:** `adeu_architecture_ir`
**Scope:** High-level architecture, hybrid pipeline specification, and ADEU-native IR pseudo-code

## 3.1. The Solution and Module Identity

Standard agents fail at complex product architecture because they attempt to compile ambiguous, high-compression human intent (e.g., "build a secure approval flow") directly into a low-level target ontology (React components, SQL schemas, API routers). This skips the foundational compilation step: **lowering semantics into a strict Intermediate Representation (IR)**. 

To solve this, we introduce `adeu_architecture_ir`, a new module that sits strictly between the agent's semantic parsing of the human brief and the final generation of target artifacts, bridging the open ontology of intent with the hermetic space of execution. 

The core invariant of this module:
> **No implementation code is generated without a valid, deterministically checked Semantic Architecture IR.**

This IR forces the resident agent to explicitly decode and instantiate the hidden world—trust boundaries, state models, data lifecycles, invariant properties, and access policies—before writing a single line of React or Python. 

## 3.2. O/E/D/U Abstraction of the Architecture IR

Every architecture proposed by the LLM must formally map onto the four ADEU axes:

- **Ontology (O):** The basic objects in the IR are not "buttons," "functions," or "tables." They are `DomainEntity`, `StateTransition`, `TrustBoundary`, `Actor`, and `Invariant`. This resolves semantic compression by forcing out the actual moving parts.
- **Epistemics (E):** The IR is evaluated deterministically. The `adeu_kernel` and its Z3 solver backend check if the declared `StateTransition`s preserve the declared `Invariant`s. Unreachable states or uncovered failure modes are surfaced and flagged as `deterministic_fail`. The architecture is proven coherent before implementation is mapped.
- **Deontics (D):** Operations crossing a `TrustBoundary` are evaluated against the repository's deterministic `capability_lattice`. Unapproved permission escalations or capability mismatches trigger a fail-closed rejection.
- **Utility (U):** The structured IR prevents "fake safety" and inflated code generation. The output serves as an unambiguous, testable target plan, executed as an `adeu_agent_harness` taskpack, yielding bounded orchestration rather than blind prompt-looping.

## 3.3. The Hybrid Compilation Pipeline

Leveraging the hybrid execution architecture established in recent arcs (such as `vNext+15` / `V39` / `synthetic_pressure_mismatch_drift`), we avoid placing naked trust in the LLM's raw output. The system operates as a hybrid compiler where the deterministic kernel controls the gating:

### Phase 1: Semantic Lowering (Resident Agent)
The LLM agent ingests the human problem brief and compiles it **only** down to the `ArchitectureIntentIR`. It acts strictly as a semantic translator, transforming open ontology into the confined formal ontology.

### Phase 2: Deterministic Verification (Kernel & Z3)
The `adeu_kernel` takes the JSON-serialized Architecture IR and formally verifies structural coherence:
- Are all `DomainEntity` states reachable?
- Are failure states explicitly modeled (preventing state-model drift and silent failures)?
- Does the topology respect `TrustBoundary` isolation given the `capability_lattice`?

If validation yields a `deterministic_fail`, the pipeline does not brute-force retry. Following the hybrid orchestration pattern, it dispatches an `architecture_oracle_request@1` back to the resident agent for targeted interpretation and local resolution adjudication.

### Phase 3: Bounded Projection (Target Generation)
Only upon a `deterministic_pass` from Phase 2 does the system allow the semantic compiler pipeline to project the verified IR into local repository target artifacts (React trees, schemas, API routes). The target compilation uses the proven IR as the rigid constraint template, preventing architectural hallucination. 

## 3.4. ADEU-Native Pseudo-Code: Instantiating the Semantic IR

The following is an explicit specification of the IR using ADEU-native typed primitives. This represents the high-level formal contract that the LLM must reliably populate and the deterministic kernel will ruthlessly evaluate.

```python
# module: adeu_architecture_ir/models.py
# pseudo-code specification

from pydantic import BaseModel, Field
from typing import List, Optional, Literal

class Actor(BaseModel):
    id: str = Field(..., description="Canonical ID of the system actor (e.g., 'user_authenticated', 'system_cron')")
    capabilities: List[str] = Field(..., description="Lattice capabilities possessed by this actor. Must exist in urm.capability.lattice")

class TrustBoundary(BaseModel):
    id: str = Field(..., description="Boundary identifier (e.g., 'client_to_api', 'api_to_db')")
    ingress_policy: str = Field(..., description="Required capability for ingress passage")
    egress_policy: str = Field(..., description="Required data state or proof certificate before egress")

class StateNode(BaseModel):
    id: str = Field(..., description="Explicit state enumeration")
    is_terminal: bool

class StateTransition(BaseModel):
    source_state: str
    target_state: str
    triggering_actor: str
    boundary_crossed: Optional[str] = None
    required_invariants: List[str] = Field(..., description="Deterministically provable conditions for transition (e.g., 'is_authorized', 'payload_valid')")

class DomainEntity(BaseModel):
    id: str
    states: List[StateNode]
    transitions: List[StateTransition]
    failure_model: str = Field(..., description="Explicit declaration of how this entity fails. Cannot be omitted or 'none'. Forces agent out of silent-success posture.")

class ArchitectureIntentIR(BaseModel):
    """
    The strict intermediate representation of the intended architecture.
    This must compile cleanly through adeu_kernel before any target code is created.
    """
    schema_version: Literal["architecture_ir.v1"] = "architecture_ir.v1"
    intent_hash: str = Field(..., description="SHA-256 hash of the original human brief, establishing an immutable provenance link.")
    actors: List[Actor]
    boundaries: List[TrustBoundary]
    entities: List[DomainEntity]
```

## 3.5. Artifact Traceability and Output

Execution of this pipeline produces immutable, schema-versioned deterministic artifacts to the `/artifacts/` directory, extending the existing semantic governance pipeline:

1. `architecture_proposal.v1.json` - The raw typed IR proposed by the agent during Phase 1.
2. `architecture_validator_evidence.v1.json` - The Z3 solver output and kernel execution trace proving that the proposed IR has no cycle violations, unreachable states, or unapproved boundary crossings. 
3. `architecture_projection_manifest.v1.json` - The deterministic map tracking how IR entities physically translate to generated files, avoiding ghost structures and semantic pressure failures.

By gating physical implementation code behind `ArchitectureIntentIR`, we constrain the boundless space of software engineering to a strict, hybrid-verified pipeline. The AI model's fluency is harnessed entirely for semantic alignment within the hermetic sandbox; the ODEU systems guarantee the resulting structural integrity.

---

## Codex Commentary (2026-03-23)

Relative to [ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md](/home/rose/work/LexLattice/odeu/docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md), this draft is conceptually aligned but much thinner. It has a few clean ideas worth keeping in mind, but it is not yet specific enough to serve as the main architecture baseline by itself.

### What This Draft Does Well

- It states the core invariant very cleanly:
  - no implementation code without a valid, deterministically checked architecture IR.
- It picks the right module identity:
  - `adeu_architecture_ir`
- It emphasizes a few architecture concerns that deserve to remain explicit in the final design:
  - trust boundaries
  - state models
  - data lifecycles
  - access policies
  - explicit failure modeling
- The `failure_model` field on `DomainEntity` is a useful forcing function. That is worth preserving in some form because it prevents silent-success architecture.
- The `architecture_projection_manifest.v1.json` idea is good. A deterministic projection manifest is a valuable bridge artifact between semantic IR and generated surfaces.

### What I Would Not Borrow As-Is

- The draft is too compressed to be ADEU-closeout-grade:
  - it does not specify authority-boundary policy;
  - it does not define a real artifact family;
  - it does not define checkpoint law, replay identity, or conformance semantics at the needed depth.
- The hybrid precedent citation is loose. In repo-native terms, the tighter precedent is the bounded `V39-E` lane finalized in `vNext+76`, not the broader historical shorthand used here.
- The pseudo-code is closer to a Python sketch than an ADEU-native semantic language.
- The object model is underpowered for the architecture problem:
  - `Actor`
  - `TrustBoundary`
  - `StateNode`
  - `StateTransition`
  - `DomainEntity`
  are useful, but they omit key architecture-native objects such as:
  - surfaces
  - capabilities as first-class architecture objects
  - decisions
  - evidence requirements
  - gates
  - utility ordering
  - ambiguity records
- The draft leans heavily on a single kernel/Z3 verification picture. Some architecture checks should indeed be formalized, but a lot of the real value will come from staged deterministic validators plus bounded hybrid checkpoints rather than one solver-shaped pass.

### What Seems Worth Borrowing Into Our Architecture

- Keep the invariant wording:
  - no code generation without valid architecture IR
- Preserve explicit failure modeling as a required architecture concern.
- Preserve the idea of a deterministic projection manifest as a first-class emitted artifact.
- Keep the simple, direct module framing:
  - architecture IR exists between semantic parsing and implementation projection.

### Net Assessment

This draft is useful as a concise thesis statement and as a reminder to keep state, trust, and failure modeling central. It is not the document I would use as the main structural template, but I would consider borrowing:

- the headline invariant;
- the explicit `failure_model` emphasis;
- the projection-manifest concept.
