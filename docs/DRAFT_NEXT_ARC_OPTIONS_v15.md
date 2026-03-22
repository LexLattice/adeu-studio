# Draft Next Arc Options v15

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v14.md`, updated after
`vNext+74` closeout.

This draft keeps `V39` as the active module-conformance family and moves from released
observation/report substrate into released policy projection and fix-plan semantics.

`V39-A` is closed on `main` as the retrospective external-contribution alignment
baseline.

`V39-B` is closed on `main` as the synthetic pressure-mismatch registry baseline.

`V39-C` is now also closed on `main` as the synthetic pressure-mismatch observation
and conformance baseline.

The next question is how to turn released conformance findings into agent-facing
guidance and bounded fix-plan artifacts without widening prematurely into repo
mutation, repo-wide scanning, or hybrid oracle execution.

## Baseline

- `V39-A` established a typed retrospective-alignment lane for imported single-PR
  contributions through:
  - canonical `external_contribution_alignment_packet@1`;
  - canonical `module_conformance_report@1`;
  - canonical `v39a_external_contribution_alignment_evidence@1`.
- `V39-B` established a typed registry substrate for pressure-mismatch drift through:
  - canonical `synthetic_pressure_mismatch_rule_registry@1`;
  - authoritative and mirrored schema exports;
  - one committed v73 reference fixture spanning all five drift families;
  - bounded vocabularies, structured `counterexample_policy`, anti-authorship
    governance, anti-score posture, and `safe_autofix` constraints.
- `V39-C` established a typed observed-finding lane through:
  - canonical `synthetic_pressure_mismatch_observation_packet@1`;
  - canonical `synthetic_pressure_mismatch_conformance_report@1`;
  - deterministic-local detector execution only;
  - committed positive, no-finding, and rejected unsupported-execution fixtures;
  - fail-closed handling for unsupported subject kinds and non-aggregated finding refs.
- The repo now already has:
  - deterministic local gates through `make check`;
  - deterministic arc scaffold and closeout linting;
  - one bounded imported-work conformance lane;
  - one bounded structural-drift registry lane;
  - one bounded structural-drift observation/report lane.

## Gap

The missing layer is no longer rule law or observed findings alone.

The missing layer is a bounded, typed way to project released pressure-mismatch
findings into:

- forward coding agent guidance;
- post-code optimizer guidance;
- bounded fix-plan artifacts for later human or deterministic consumption.

Today the repo still lacks a canonical way to:

- consume released `synthetic_pressure_mismatch_conformance_report@1` outputs and emit
  a canonical `synthetic_pressure_mismatch_fix_plan@1`;
- keep forward-agent prevention guidance separate from post-optimizer corrective
  guidance;
- derive bounded safe-autofix planning only from findings that are already released as
  `safe_autofix_candidates`;
- preserve the distinction between:
  - findings,
  - plans,
  - actual repo mutation;
- emit valid no-op/no-finding fix plans rather than forcing fake action into the lane.

## Recommended Family

- Family name: `V39`
- Family theme: module conformance and structural drift governance
- Closed paths:
  - `V39-A`
  - `V39-B`
  - `V39-C`
- Recommended next path: `V39-D`
- Default path selection:
  select `V39-D` as the next default candidate

## Closed Earlier Paths

### `V39-A`

Solved:

- imported single-PR lane classification;
- code-alignment vs meta-sequence separation;
- truthful three-layer scope recording;
- pinned policy provenance for deterministic replay;
- default-negative precedent semantics.

### `V39-B`

Solved:

- canonical pressure-mismatch drift registry law;
- bounded vocabularies for signal, evidence, action, route, and utility fields;
- structured `counterexample_policy`;
- schema-level and model-level `safe_autofix` constraints;
- anti-authorship and anti-score boundaries for the released registry family.

### `V39-C`

Solved:

- canonical observation packet and conformance report substrate;
- deterministic-local detector execution only;
- single-subject packet scope;
- count-based and list-based conformance aggregation;
- no-finding and unsupported-execution replay;
- fail-closed support for unsupported subject kinds and out-of-set finding refs.

## Recommended Next Path (`V39-D`)

Implement a bounded policy-projection and fix-plan lane that consumes the released
`synthetic_pressure_mismatch_conformance_report@1` and emits a canonical
`synthetic_pressure_mismatch_fix_plan@1`.

`V39-D` should introduce:

- canonical `synthetic_pressure_mismatch_fix_plan@1`;
- explicit source binding back to:
  - the released `synthetic_pressure_mismatch_conformance_report@1`,
  - the released `synthetic_pressure_mismatch_observation_packet@1` packet set,
  - the released `synthetic_pressure_mismatch_rule_registry@1`;
- separate forward-agent and post-optimizer policy projection surfaces;
- bounded plan items derived from released findings rather than free-form advice;
- exact source-finding binding for every projected item through a stable
  `source_finding_id` or equivalent exact source item identity;
- bounded item typing through:
  - `plan_posture`,
  - `projection_kind`,
  - `projected_next_step_text`;
- safe-autofix planning only for findings already carried by released
  `safe_autofix_candidates`;
- valid no-op / no-finding fix-plan replay for empty conformance outputs and for
  findings-present-but-non-plannable outputs;
- explicit plan-level anti-mutation and anti-score law.

## Why This Path

- It is the natural consumer of the released `V39-C` conformance substrate rather than
  a family jump.
- It externalizes the role split that the registry already hints at through
  `forward_agent_policy` and `post_optimizer_policy`.
- It creates a typed planning surface without prematurely authorizing diffs, file
  edits, or hybrid checkpoint execution.
- It keeps projection as consumption of released policy rather than silently creating
  a second policy-authoring lane.
- It preserves the repo’s discipline:
  first release the law, then release the findings, then release the bounded plan
  surface, and only later consider hybrid adjudication.

## First-Slice Boundary (`V39-D`)

`V39-D` should stay bounded to:

- policy projection and fix-plan semantics only;
- released `V39-B` and `V39-C` artifacts as its sole canonical inputs;
- separate forward-agent and post-optimizer outputs inside the plan;
- bounded safe-autofix planning only for the narrow deterministic-local subset already
  emitted by `V39-C`;
- plan outputs that remain inspectable and non-scalar by construction;
- committed local fixtures for reference conformance inputs and derived fix plans.

It should not attempt:

- patch generation or file mutation;
- direct autofix execution;
- repo-wide scanning;
- semantic-ambiguous or meta-governance detector expansion;
- oracle requests, oracle resolutions, or checkpoint traces;
- hidden priority scores or merge-worthiness outputs;
- generic “rewrite code to look less AI-generated” behavior.

## Follow-On Path Inside `V39`

### `V39-E`

Hybrid execution lane:

- canonical `synthetic_pressure_mismatch_oracle_request@1`;
- canonical `synthetic_pressure_mismatch_oracle_resolution@1`;
- canonical `synthetic_pressure_mismatch_checkpoint_trace@1`;
- explicit checkpoint classifier;
- deterministic adjudicator with replay, cache, and version pinning;
- bounded human-escalation lane for unstable or contradictory oracle outputs.

This lane remains intentionally later and higher-risk than `V39-D`.

## Governing References

The higher-order concept note for this family remains:

- `docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md`

The released substrate that `V39-D` must consume rather than redefine is:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md`
