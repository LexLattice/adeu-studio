# Draft Next Arc Options v14

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v13.md`, updated after
`vNext+73` closeout.

This draft keeps `V39` as the active module-conformance family and moves from released
rule law into released observation/report substrate.

`V39-A` is closed on `main` as the retrospective external-contribution alignment
baseline.

`V39-B` is now also closed on `main` as the synthetic pressure-mismatch registry
baseline.

The next question is how to bind the released rule registry to concrete local subjects
without jumping prematurely into fix plans, broad heuristic CI law, or hybrid oracle
execution.

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
  - first-slice hard law for bounded vocabularies, structured
    `counterexample_policy`, anti-authorship governance, anti-score posture, and
    `safe_autofix` constraints.
- The repo now already has:
  - deterministic local gates through `make check`;
  - deterministic arc scaffold and closeout linting;
  - one bounded imported-work conformance lane;
  - one bounded structural-drift rule registry lane.

## Gap

The missing layer is no longer rule law alone.

The missing layer is a bounded, typed way to bind released pressure-mismatch rules to
concrete local subjects and emit released conformance outputs without widening into
fix plans or oracle execution.

Today the repo still lacks a canonical way to:

- materialize concrete `synthetic_pressure_mismatch_observation_packet@1` artifacts
  from local subject inputs and the released rule registry;
- emit a canonical `synthetic_pressure_mismatch_conformance_report@1` from observed
  findings;
- distinguish registry law from observed findings without collapsing them together;
- execute only the deterministic-local subset of registry rules in a released,
  fail-closed detector lane;
- seed that observation/report lane with committed local subject fixtures rather than
  live repo-wide scanning or network-dependent state.

## Recommended Family

- Family name: `V39`
- Family theme: module conformance and structural drift governance
- Closed paths:
  - `V39-A`
  - `V39-B`
- Recommended next path: `V39-C`
- Default path selection:
  select `V39-C` as the next default candidate

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
- non-empty subject/utility/rule arrays;
- schema-level and model-level `safe_autofix` constraints;
- anti-authorship and anti-score boundaries for the released registry family.

## Recommended Next Path (`V39-C`)

Implement a bounded observation and reporting lane that consumes the released
`synthetic_pressure_mismatch_rule_registry@1` and emits concrete conformance artifacts
for committed local subjects.

`V39-C` should introduce:

- canonical `synthetic_pressure_mismatch_observation_packet@1`;
- canonical `synthetic_pressure_mismatch_conformance_report@1`;
- single-subject observation packets with explicit registry-linked finding carry-through;
- deterministic detector execution for the deterministic-local subset only;
- one or more committed local subject fixtures and corresponding accepted packet/report
  fixtures;
- explicit no-finding replay and rejected unsupported-execution cases in the fixture
  baseline;
- explicit binding from observation outputs back to the released registry rule ids;
- released report aggregation without hidden scalar scoring.

## Why This Path

- It is the natural consumer of the released `V39-B` registry rather than a parallel
  family jump.
- It keeps the conformance family grounded in typed observed outputs instead of
  planning-only abstractions.
- It preserves the repo’s current discipline:
  first release the law, then release the bounded observation surface, then consider
  policy projection and hybrid execution later.
- It avoids premature widening into fix plans or oracle lanes before observed findings
  exist as released substrate.

## First-Slice Boundary (`V39-C`)

`V39-C` should stay bounded to:

- observation packet and conformance report only;
- deterministic-local detector execution only;
- committed local subject fixtures only;
- one bounded repo-native observation lane rather than repo-wide scanning;
- explicit linkage to released `V39-B` rule ids and schema exports;
- report aggregation that is inspectable and non-scalar by construction.

It should not attempt:

- fix-plan artifact rollout;
- automatic repo mutation or autofix execution;
- semantic-ambiguous or meta-governance detector execution;
- oracle requests, oracle resolutions, or checkpoint traces;
- generic “scan the whole repo for AI code” behavior;
- hidden scoring or merge-worthiness outputs.

## Follow-On Paths Inside `V39`

### `V39-D`

Agent-policy projection lane:

- canonical `synthetic_pressure_mismatch_fix_plan@1`;
- forward coding agent policy projection;
- post-code optimizer policy projection;
- bounded safe-autofix planning only for the narrow deterministic-local subset.

### `V39-E`

Hybrid execution lane:

- canonical `synthetic_pressure_mismatch_oracle_request@1`;
- canonical `synthetic_pressure_mismatch_oracle_resolution@1`;
- canonical `synthetic_pressure_mismatch_checkpoint_trace@1`;
- explicit checkpoint classifier;
- deterministic adjudicator with replay, cache, and version pinning;
- bounded human-escalation lane for unstable or contradictory oracle outputs.

This lane remains intentionally later and higher-risk than `V39-C` and `V39-D`.

## Governing References

The higher-order concept note for this family remains:

- `docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md`

The released substrate that `V39-C` must consume rather than redefine is:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md`
