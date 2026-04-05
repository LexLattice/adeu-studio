# Draft Next Arc Options v27

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`, updated after the
structural-reasoning assessment seed was clarified as a separate but connected family
direction.

This draft does not automatically supersede the contest-participation planning branch in
`docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`.

Instead, it records a second connected candidate family:

how should ADEU Studio assess model structural reasoning fidelity before widening into
SRM-style governors, downstream contest optimization, or reasoning-runtime selection?

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

Interpretive doctrine for this planning surface:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`, `deferred`, and
  `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and absence-of-authorization
  statements for this planning draft, not lock-equivalent permanent prohibitions by
  themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A` through `V41-F` are closed on `main`.
- `vNext+98` is the current baseline implementation state.
- `V42-A` through `V42-G4` are closed on `main`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v25.md` is the authoritative planning record for the
  state where post-`V42` next-family selection remained unselected.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md` records one connected candidate family:
  - `V43`
  - ADEU external governed contest participation substrate
  - contest-world compilation before tactical participation
- `docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md` now records a second
  connected planning seed:
  - structural reasoning assessment before SRM release or downstream optimization.

## Gap

The repo still lacks a released way to:

- assess whether a candidate model can faithfully execute an explicit abstract reasoning
  template rather than merely land on correct answers intermittently;
- distinguish knowledge deficit from procedural-discipline deficit using small,
  inspectable paired probes;
- normalize structural reasoning failures into reusable taxonomy rather than vague
  "model got confused" narratives;
- generate typed model-structural suitability profiles before widening into:
  - SRM-like reasoning governors;
  - contest/runtime model selection;
  - verifier/search designs that assume a stable procedural core.

The missing layer is therefore not a new contest host adapter or a new task benchmark.

The missing layer is a structural reasoning assessment substrate.

## Relationship To `V43`

`V43` and this new candidate family are connected but non-identical.

`V43` asks:

- what kind of external contest world is this?
- what is lawful?
- what is measured?
- where could reasoning AI help?

This new family asks:

- is a candidate model structurally suitable to inhabit an explicit inferential
  skeleton under ADEU discipline?

So this family may constrain:

- model selection for later contest or runtime lanes;
- whether verifier/search layers are justified;
- whether a future SRM-style governor architecture is warranted;
- how strongly downstream performance claims should be trusted.

But it may not mint:

- contest law;
- host-adapter semantics;
- contest archetype doctrine;
- general leverage doctrine for external contests.

Planning relationship:

- `V43` remains a valid connected candidate family from `v26`;
- this draft introduces a separate connected candidate family rather than replacing it;
- whether `V44` should precede `V43`, run as a parallel planning branch, or constrain a
  later `V43` implementation remains planning-bound and not yet locked.

## Recommended Family

- Family name: `V44`
- Family theme: ADEU structural reasoning assessment substrate
- Released earlier shaping inputs:
  - `V41-A` through `V41-F`
  - `V42-A` through `V42-G4`
- Connected candidate family not reopened or superseded here:
  - `V43`
- Recommended architecture reference:
  - `docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md`
- Recommended decomposition reference:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS133.md`
- Recommended next path for this branch:
  - `V44-D`
- Recommended next concrete arc for this branch if selected:
  - `vNext+134`
- Default path selection for this branch:
  - select `V44-D` as the next default candidate
  - keep that starter bounded to probe-library widening across template classes only,
    still prior to profile aggregation, benchmark scoring, or recursive-depth release

This family/path recommendation is branch-local to the `v27` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected `V43`
branch from `v26` remains in parallel planning scope.

## Closed Earlier Families (`V41` And `V42`)

`V41` should now be read as a released practical-analysis substrate that already proved
some explicit inferential-lane discipline in prompt-facing form.

`V42` should now be read as a released contest-domain specialization that proved ADEU
can run a bounded local-first reasoning/evidence control plane over one external
challenge family.

Neither `V41` nor `V42` released a general structural reasoning assessment family.

`V44` is the planning move that generalizes the structural thread without reopening the
released contest or practical-analysis contracts.

## Recommended Next Family (`V44`)

`V44` should release a bounded assessment doctrine around:

- explicit abstract reasoning templates as assessable objects;
- small, inspectable structural probes;
- per-run structural traces;
- explicit hierarchical-action assessment posture when a probe carries parent/child task
  structure rather than remaining flat;
- normalized structural failure taxonomy;
- model structural suitability profiling;
- explicit distinction between:
  - knowledge deficit,
  - procedural-discipline deficit,
  - blocked posture,
  - invalid early closure;
- explicit distinction between:
  - horizontal action continuity / plan-spine fidelity,
  - vertical semantic decomposition / active-step compilation fidelity,
  - reintegration fidelity after local descent.

The family should treat future SRM-like architectures as:

- downstream consumers of the assessment family;
- not the first release inside this family.

The family should treat contest-participation work such as `V43` as:

- one connected downstream consumer of model-structural assessment;
- not something that this family is allowed to redefine.

## Suggested `V44` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V44-A` | template probe + structural trace substrate | candidate `adeu_reasoning_template_probe@1` and candidate `adeu_structural_reasoning_trace@1` | closed_on_main |
| `V44-B` | normalized failure taxonomy only | candidate `adeu_structural_failure_taxonomy@1` with blocked preserved as non-failure and no profile promotion posture | closed_on_main |
| `V44-C` | paired-condition differential diagnosis | knowledge-vs-procedure assay posture over bounded probe suites, still prior to any released profile aggregation | closed_on_main |
| `V44-D` | probe-library widening across template classes | expanded bounded probe library over decomposition, branching, repair, and invariance classes | planned |
| `V44-E` | recursive-depth / structural-extension assessment seam | bounded recursive-closure assessment surfaces, still prior to SRM release | planned_later |

These output names are planning-level candidate names, not lock-level schema authority.

## Completed Next Path (`V44-A`)

The bounded probe-definition and structural-trace lane is now closed on `main`.

`V44-A` should introduce:

- one canonical bounded probe artifact candidate:
  - explicit template identity and class;
  - explicit lane structure;
  - explicit top-level action spine and active-step posture when the probe is
    hierarchically staged;
  - explicit completion versus invalid-closure posture;
  - explicit blocked posture when information is intentionally withheld;
  - optional paired-condition compatibility fields for later `V44-C` use, including:
    - supplied-knowledge condition;
    - withheld-knowledge condition;
    - injected-knowledge continuation point;
- one canonical bounded structural trace artifact candidate:
  - per-step or per-lane reasoning evidence;
  - explicit trace of preserved versus broken structure;
  - explicit return-to-parent or return-to-plan evidence when local descent occurs;
  - local-repair entrypoint posture when repair is part of the probe;
- one small initial probe set rich enough to expose:
  - lane collapse;
  - branch collapse;
  - plan-spine drift;
  - active-step decomposition failure;
  - reintegration failure after local descent;
  - unsupported certainty;
  - invalid early closure;
  - non-local repair drift;
- deterministic local fixtures for one or more initial template classes;
- no widening yet into taxonomy aggregation, scoring doctrine, SRM architecture, or
  downstream runtime selection claims.

`V44-A` is evidence-first and non-promotional:

- it may emit traces and bounded diagnostics;
- it may not yet emit model-suitability promotion for contest selection, SRM governance
  selection, or downstream optimizer preference.

## Why This Path

- It is the narrowest safe consumer of the structural-assessment seed.
- It operationalizes the abstract template concept rather than leaving it rhetorical.
- It creates the raw evidence layer needed before taxonomy and profile aggregation.
- It makes knowledge-vs-procedure discrimination testable rather than merely asserted.
- It prevents the family from collapsing immediately into speculative SRM architecture
  or opaque "reasoning benchmark" claims.

## Completed First-Slice Boundary (`V44-A`)

`V44-A` stayed bounded to:

- explicit template-probe definition only;
- explicit structural trace emission only;
- one small initial probe library only;
- one tiny hierarchical probe chain when it materially sharpens failure diagnosis;
- deterministic local fixtures only;
- explicit blocked versus invalid-closure posture only;
- small inspectable probe environments only.

It did not attempt:

- broad cross-model leaderboarding;
- generic single-number "reasoning IQ" claims;
- failure-taxonomy aggregation beyond what the first traces can support;
- model-suitability promotion into contest or SRM lanes;
- model-suitability promotion for downstream optimizer preference;
- SRM architecture release;
- distillation or fine-tuning prescriptions;
- autonomous contest/runtime orchestration;
- broad recursive self-extension claims.

## Follow-On Paths Inside `V44`

### `V44-B`

Normalized taxonomy lane:

- candidate `adeu_structural_failure_taxonomy@1`;
- consume only released `V44-A` probe/trace contracts and deterministic `v44a`
  fixtures;
- preserve explicit blocked-versus-invalid posture while normalizing only structural
  failure families;
- explicit non-equivalence between task score and structural reasoning fidelity;
- explicit rejection of one-number overclaim posture.

This path is now closed on `main`.

### `V44-C`

Differential diagnosis lane:

- paired supplied-knowledge versus withheld-knowledge probe conditions;
- injected-knowledge continuation posture;
- clearer empirical separation between:
  - knowledge deficit,
  - procedural-discipline deficit.

The first `V44-C` starter should stop at pair-level differential diagnosis only.

Any later explicitly pre-differential profile lane must consume the released
`V44-C` differential surface rather than being silently embedded in the starter slice.

This path is now closed on `main`.

### `V44-D`

Probe-library widening lane:

- broader coverage across template classes;
- controlled surface-variation and local-repair suites;
- richer termination and closure diagnostics without widening yet into SRM architecture.

## Completed Second-Slice Boundary (`V44-B`)

`V44-B` stayed bounded to:

- one normalized structural-failure taxonomy contract only;
- one deterministic taxonomy helper only;
- released `V44-A` probe/trace consumption only;
- explicit blocked-versus-invalid posture preservation only;
- explicit hierarchy-aware starter normalization only;
- deterministic local fixtures and mapping-matrix evidence only.

It did not attempt:

- paired-condition diagnosis;
- supplied-versus-withheld condition comparison;
- injected-knowledge continuation doctrine;
- model-profile aggregation or model ranking;
- benchmark scoring or benchmark-family projection;
- any one-number structural-fidelity score.

## Completed Third-Slice Boundary (`V44-C`)

`V44-C` stayed bounded to:

- one paired-condition differential contract only;
- one deterministic pair helper only;
- released `V44-A` probe/trace consumption only;
- released `V44-B` taxonomy consumption only;
- starter supplied-versus-withheld pair law only;
- optional injected-knowledge support posture only;
- trace-qualified supporting event refs only;
- deterministic local fixtures and mapping-matrix evidence only.

It did not attempt:

- model-profile aggregation or model ranking;
- one-number structural-fidelity summaries;
- benchmark scoring or benchmark-family projection;
- recursive-depth or probe-library widening;
- any silent three-condition override doctrine.

### `V44-E`

Deferred recursive-depth and structural-extension lane:

- bounded recursive template-depth assessment;
- explicit valid-closure versus invalid-early-closure posture;
- still assessment-first and still prior to any released SRM governor family.

## Candidate Package Ownership

The first planning pass should assume one primary family package:

- `packages/adeu_reasoning_assessment`

The first slice should assume:

- `packages/adeu_reasoning_assessment` is the only active implementation package for
  `V44-A`.

Later architecture work may widen package ownership if the family eventually reaches
governor or downstream-consumer surfaces.

## Governing References

The higher-order concept notes for this family direction are:

- `docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md`
- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`

Connected but non-authorizing context docs are:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`
- `docs/DRAFT_CONTEST_PARTICIPATION_MODULE_SPEC_v0.md`

The released earlier shaping surfaces that `V44` should learn from rather than reopen
are:

- released `V41-A` through `V41-F`
- released `V42-A` through `V42-G4`

## Planning Boundary

- no reopening of released `V41` or released `V42-A`..`V42-G4` contracts is authorized
  by this planning draft;
- no automatic supersession of the `V43` contest-participation planning branch is
  authorized by this planning draft;
- no lock-level schema authority is created by the candidate artifact names above;
- no SRM architecture release is authorized by this planning draft;
- no contest-law or host-adapter doctrine is authorized by this planning draft;
- no broad model ranking or generic reasoning-IQ claim is authorized by this planning
  draft;
- no distillation, fine-tuning, or downstream runtime-selection doctrine is authorized
  without later decomposition and lock-level gating;
- no recursive self-extension claim is authorized beyond bounded assessment posture.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v26.md",
  "baseline_arc": "vNext+98",
  "closed_prior_families": [
    "V41",
    "V42"
  ],
  "connected_candidate_families_in_scope": [
    "V43",
    "V44"
  ],
  "branch_candidate_family": "V44",
  "branch_candidate_status": "selected_for_v27_planning_surface_not_repo_wide_family_selection",
  "connected_family_not_reopened_here": "V43",
  "closed_current_family_paths": [
    "V44-A",
    "V44-B",
    "V44-C"
  ],
  "planned_current_family_paths": [
    "V44-D",
    "V44-E"
  ],
  "default_next_arc_candidate_for_this_branch": "V44-D",
  "default_next_concrete_arc_candidate_for_this_branch": "vNext+134",
  "family_architecture_doc": "docs/DRAFT_STRUCTURAL_REASONING_ASSESSMENT_SPEC_v0.md",
  "family_decomposition_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS133.md",
  "planned_family_packages": [
    "packages/adeu_reasoning_assessment"
  ],
  "first_slice_active_packages": [
    "packages/adeu_reasoning_assessment"
  ],
  "family_theme": "structural_reasoning_assessment_before_srm_release",
  "branch_local_planning_selection_only": true,
  "v44_constrains_but_does_not_mint_contest_or_host_doctrine": true,
  "assessment_before_srm_architecture_required": true,
  "template_probe_and_trace_first_required": true,
  "v44a_probe_shape_future_compatible_with_v44c_required": true,
  "v44a_evidence_first_non_promotional_required": true,
  "knowledge_vs_procedural_differential_required": true,
  "small_inspectable_probe_design_required": true,
  "blocked_vs_invalid_closure_separation_required": true,
  "task_score_and_structural_fidelity_non_equivalent_required": true,
  "horizontal_plan_spine_fidelity_required": true,
  "vertical_active_step_compilation_fidelity_required": true,
  "reintegration_fidelity_required": true,
  "flat_arbitrary_instruction_following_rejected_when_hierarchy_matters": true,
  "connected_v46_benchmark_projection_consumer_expected": true,
  "failure_taxonomy_lane_planned": true,
  "profile_lane_deferred_until_post_differential_or_explicitly_pre_differential": true,
  "differential_diagnosis_lane_planned": true,
  "recursive_depth_assessment_seam_planned_later": true,
  "srm_release_initially_deferred": true,
  "distillation_or_finetuning_doctrine_initially_deferred": true,
  "broad_model_ranking_initially_deferred": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md",
  "next_family_decomposition_required_before_lock": true
}
```
