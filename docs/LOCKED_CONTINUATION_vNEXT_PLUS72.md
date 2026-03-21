# Locked Continuation vNext+72

Status: `V39-A` implementation contract.

## V72 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v39a_external_contribution_alignment_contract@1",
  "target_arc": "vNext+72",
  "target_path": "V39-A",
  "target_scope": "external_contribution_retrospective_alignment",
  "reference_contribution_kind": "external_single_pr",
  "reference_fixture_id": "pr293_poetry_utility"
}
```

## Slice

- Arc label: `vNext+72`
- Family label: `V39-A`
- Scope label: retrospective alignment baseline for imported external
  contributions

## Objective

Introduce a bounded repo-native way to retrospectively evaluate an imported
single-PR contribution against the repo's current ADEU structural law without
pretending the contribution originated inside the full native arc workflow.

The first accepted reference target is a committed local subject bundle derived
from the poetry-utility contribution associated with PR `#293`, evaluated as an
imported external lane and normalized into explicit alignment artifacts.

## Required Deliverables

1. New typed ADEU core artifacts:
   - `external_contribution_alignment_packet@1`
   - `module_conformance_report@1`
   - packet/report fields that make the bounded subject explicit, including:
     - `subject_kind`
     - `evaluation_lane`
     - `reference_fixture_id`
     - `claimed_scope`
     - `observed_reachable_surfaces`
     - `accepted_shipped_scope`
     - `precedent_status`
2. Deterministic builders or validators that:
   - classify the contribution lane and structural impact class;
   - record and preserve the three-layer scope model:
     - `claimed_scope`,
     - `observed_reachable_surfaces`,
     - `accepted_shipped_scope`;
   - separate code-alignment judgment from meta-sequence judgment;
   - record required maintainer follow-ups and precedent status;
   - default precedent status to `non_precedent` unless a maintainer explicitly
     grants precedent-bearing status with a reason field;
   - pin the exact policy source paths, content hashes, and evaluator/tool
     version used to derive the report;
   - derive the conformance report from explicit packet inputs plus current
     repo policy sources rather than from free-form retrospective prose.
3. One committed reference bundle for the imported poetry contribution:
   - localized subject snapshot capturing:
     - imported diff,
     - materialized metadata,
     - claimed-scope text,
     - other admissible local evidence;
   - alignment packet fixture
   - conformance report fixture
   - evidence fixture binding the report to the consumed input packet and repo
     policy sources
4. Repo-local operator guidance for:
   - imported external single-PR intake,
   - retrospective alignment,
   - maintainer normalization boundaries.
5. Python tests covering:
   - packet/model validation,
   - deterministic conformance derivation,
   - truthful scope separation,
   - fail-closed handling for missing required alignment inputs.

## Hard Constraints

- No artifact in this slice may claim that the imported contribution satisfied a
  pre-doc or pre-lock sequence it did not actually satisfy.
- Code alignment and meta-sequence alignment must remain separate reported
  dimensions; one may not silently substitute for the other.
- No canonical conformance artifact may be derived from live GitHub network
  queries at evaluation time; canonical evaluation must consume committed or
  explicitly materialized local inputs, and the canonical subject is the
  localized subject bundle rather than the live PR object.
- Canonical evaluation evidence must record:
  - exact policy source paths,
  - exact policy content hashes,
  - evaluator or tool version.
- The reference contribution must be explicit about whether it is:
  - internal-only utility work, or
  - externally reachable product surface work.
- The scope model must preserve:
  - `claimed_scope`,
  - `observed_reachable_surfaces`,
  - `accepted_shipped_scope`,
  and may not collapse observation into judgment.
- Claimed shipped scope must fail closed when contradicted by actual reachable
  repo surfaces.
- The first family may check structural conformance, but it may not auto-accept
  architectural meaning, user value, or merge worthiness as if those were
  fully machine-resolved.
- The first family must stay bounded to one imported reference contribution and
  may not widen into a generalized all-modules scoring engine.
- Imported work must not become process precedent solely by existing in repo
  history; precedent status must default to `non_precedent` unless a maintainer
  explicitly grants precedent-bearing status with a reason.

## PR Shape

- Single integrated PR.

Rationale:

- the packet schema, conformance report, deterministic derivation, reference
  bundle, and tests are tightly coupled and should land together to avoid
  temporary policy drift.
