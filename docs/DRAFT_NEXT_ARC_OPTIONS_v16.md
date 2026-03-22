# Draft Next Arc Options v16

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v15.md`, updated after
`vNext+75` closeout.

This draft keeps `V39` as the active module-conformance family and moves from
released advisory fix-plan projection into the later-risk hybrid checkpoint and
oracle-adjudication lane.

`V39-A` is closed on `main` as the retrospective external-contribution alignment
baseline.

`V39-B` is closed on `main` as the synthetic pressure-mismatch registry baseline.

`V39-C` is closed on `main` as the synthetic pressure-mismatch observation and
conformance baseline.

`V39-D` is now also closed on `main` as the synthetic pressure-mismatch fix-plan and
policy-projection baseline.

The next question is how to add typed mixed-confidence adjudication without confusing
deterministic authority, oracle advice, and human escalation.

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
- `V39-D` established a typed advisory planning lane through:
  - canonical `synthetic_pressure_mismatch_fix_plan@1`;
  - exact source-finding binding back to released `V39-C` findings;
  - structurally separate forward-agent and post-optimizer projections;
  - candidate-only `safe_autofix` planning;
  - valid no-op replay and strict anti-mutation / anti-score posture.
- The repo now already has:
  - deterministic local gates through `make check`;
  - deterministic arc scaffold and closeout linting;
  - released registry, observation/report, and advisory fix-plan substrates;
  - one bounded imported-work conformance lane;
  - one bounded structural-drift family with explicit later-room for hybrid
    adjudication.

## Gap

The missing layer is no longer rule law, observed findings, or advisory plans alone.

The missing layer is a bounded hybrid execution substrate in which:

- a deterministic harness classifies each checkpoint first;
- only typed `oracle_needed` checkpoints invoke the resident coding agent;
- `human_needed` remains explicit rather than being laundered into fake certainty;
- oracle advice is replayable, pinned, and advisory-only;
- deterministic adjudication remains the authority over the final checkpoint trace.

Today the repo still lacks a canonical way to:

- emit a canonical `synthetic_pressure_mismatch_checkpoint_trace@1`;
- materialize canonical `synthetic_pressure_mismatch_oracle_request@1` and
  `synthetic_pressure_mismatch_oracle_resolution@1` artifacts;
- distinguish the four checkpoint classes:
  - `deterministic_pass`,
  - `deterministic_fail`,
  - `oracle_needed`,
  - `human_needed`;
- pin replay identity across:
  - source artifact identity,
  - policy source hashes,
  - model id,
  - model version,
  - reasoning effort;
- keep current released `V39-C` / `V39-D` deterministic-only coverage honest while
  still exercising oracle-assisted and human-only branches through explicit local
  hybrid fixtures rather than overclaiming current detector coverage.

## Recommended Family

- Family name: `V39`
- Family theme: module conformance and structural drift governance
- Closed paths:
  - `V39-A`
  - `V39-B`
  - `V39-C`
  - `V39-D`
- Recommended next path: `V39-E`
- Default path selection:
  select `V39-E` as the next default candidate

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

### `V39-D`

Solved:

- canonical advisory fix-plan substrate;
- exact source-finding binding back to released conformance findings;
- role-separated forward-agent and post-optimizer projection;
- candidate-only `safe_autofix` planning;
- valid no-op fix-plan replay;
- anti-mutation and anti-score plan boundaries.

## Recommended Next Path (`V39-E`)

Implement a bounded hybrid checkpoint and oracle-adjudication lane that consumes the
released `V39-B`, `V39-C`, and `V39-D` substrates where applicable, while keeping the
deterministic harness as authority over final checkpoint disposition.

`V39-E` should introduce:

- canonical `synthetic_pressure_mismatch_oracle_request@1`;
- canonical `synthetic_pressure_mismatch_oracle_resolution@1`;
- canonical `synthetic_pressure_mismatch_checkpoint_trace@1`;
- explicit checkpoint classifier with exactly:
  - `deterministic_pass`,
  - `deterministic_fail`,
  - `oracle_needed`,
  - `human_needed`;
- deterministic adjudicator ownership over final trace materialization;
- replay identity pinned across source bindings, policy sources, model id, model
  version, and reasoning effort;
- bounded cache semantics keyed to exact request identity;
- bounded human-escalation semantics and fail-closed handling for contradictory or
  unstable oracle output;
- explicit local hybrid fixtures for oracle-assisted and human-only branches where
  current released `V39-C` / `V39-D` fixtures remain intentionally deterministic-only.
- frozen final adjudication vocabulary plus exact
  `checkpoint_class -> final_adjudication` transition law;
- exact starter `source_kind` vocabulary and request-emission boundaries.

## Why This Path

- It is the next natural consumer of the released `V39-D` plan surface rather than a
  family jump.
- It makes the mixed-confidence architecture explicit instead of leaving
  deterministic-vs-oracle behavior implicit in prose.
- It preserves the repo’s discipline:
  first release the law, then the findings, then the advisory plan, then the hybrid
  adjudication surface.
- It lets the repo exercise oracle-assisted and human-only branches without lying
  about current released observation coverage.
- It keeps hybrid adjudication typed and replayable before any later conversation
  about repo mutation or broader execution surfaces.

## First-Slice Boundary (`V39-E`)

`V39-E` should stay bounded to:

- checkpoint classification, oracle request/resolution artifacts, and checkpoint trace
  semantics only;
- deterministic adjudication as the only authority over final checkpoint disposition;
- released `V39-B`, `V39-C`, and `V39-D` artifacts as canonical upstream references
  when checkpoints derive from already-released findings or projected plan items;
- either released conformance findings or released fix-plan projections as valid
  upstream checkpoint sources, depending on source surface;
- committed local hybrid fixtures for oracle-assisted and human-only branches where
  no released deterministic observation/report path exists yet;
- single-round oracle assistance at most once per checkpoint in the first baseline;
- replayable and cacheable request identity only when source, policy, and model
  identity match exactly;
- explicit fail-closed conversion of contradictory or unstable oracle outputs into
  `human_needed`.

It should not attempt:

- patch generation or file mutation;
- direct autofix execution;
- generic resident-agent orchestration beyond typed checkpoint requests;
- live-network canonicalization of evaluation evidence;
- repo-wide scanning;
- silent widening of `V39-C` detector coverage;
- workflow-blocking policy automation;
- hidden priority scores, merge-worthiness outputs, or authorship classification.

## Governing References

The higher-order concept note for this family remains:

- `docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md`

The released substrate that `V39-E` must consume rather than redefine is:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS75.md`
