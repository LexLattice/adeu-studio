# Draft Next Arc Options v11 (Post vNext+66, Post V37-A Closure)

This document defines the post-`vNext+65` planning baseline after the first
ADEU-governed UX family closed on `main`, using the recursive-compilation note as the
methodological bridge into the next family.

Status: active planning draft (`V34`, `V35`, `V36-A` through `V36-E`, and `V37-A`
closed; `V37-B` proposed as next default candidate, no later `V37` path yet locked).

Goal:

- carry forward the completed `V34` trust/distribution line without reopening it;
- carry forward the completed `V35-A` through `V35-E` orchestration/delegation/
  visibility/topology/enforcement line without widening it implicitly;
- carry forward the completed `V36-A` through `V36-E` typed UX-governance /
  compiler-export line without widening it implicitly;
- turn the higher-order recursive-compilation note into an actual implementation roadmap
  rather than leaving it as commentary above the repo;
- use the repo's now-released harness, artifact, runtime, and evidence surfaces to build
  one bounded runnable meta-testing loop rather than another prose-only control layer;
- make explicit intent a first-class authoritative input to the loop:
  the loop should assess outputs against an accepted intent packet rather than against
  unbound retrospective prose;
- shift the repo's assessment posture from retrospective-only slice commentary toward
  intent-first typed evaluation of the development process itself;
- make "module" mean both:
  reasoning-side modules active in the meta-loop and hard checkpoint modules already
  provided by repo scripts, validators, evidence lanes, and emitted artifacts;
- link those two sides explicitly so soft reasoning can guide, predict, compare, and
  synthesize, while hard checkpoints remain authoritative for validation truth;
- make the soft/hard distinction machine-checkable:
  reasoning modules may express expected success, drift hypotheses, or repair candidates,
  but may not mint pass/fail, completion, or governance by prose alone;
- turn future planning from vague "build feature X next" into bounded drift-reduction
  over an explicit reference loop;
- start on native repo terrain with one bounded `arc_bundle_recursive_compilation_loop`
  rather than a generic benchmark platform or generalized autonomous orchestrator.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, release scope, or autonomous repo mutation by itself.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/LOCKED_URM_CODEX_INTEGRATION_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS66.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS66.md`
- `docs/ASSESSMENT_vNEXT_PLUS66_EDGES.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

## Baseline Agreement (Current Ground Truth)

- Baseline implementation is `vNext+66` (`V37-A`) on `main`.
- `V34-A` through `V34-G`, `V35-A` through `V35-E`, and `V36-A` through `V36-E` are
  closed.
- `V37-A` is now also closed:
  canonical `meta_testing_intent_packet@1`, canonical `meta_module_catalog@1`, one
  accepted bound reference-instance pair for the first bounded
  `arc_bundle_recursive_compilation_loop`, and canonical
  `v37a_meta_intent_module_catalog_evidence@1` now exist on `main`.
- `stop_gate_metrics@1` remains the active stop-gate schema family.
- Stop-gate metric-key cardinality baseline remains `80` (derived from `metrics` object
  keys only).
- Determinism/replayability, canonical JSON hashing, and fail-closed posture remain
  mandatory.
- The execution constitution is no longer hypothetical:
  `V35-A` through `V35-E` already froze canonical orchestration state, delegated worker
  handoffs, transcript/progress visibility, topology duty maps, and bounded runtime
  enforcement.
- The first bounded typed UX-governance stack is no longer hypothetical:
  `V36-A` through `V36-E` already froze canonical UX substrate, projection/interaction
  law, one bounded rendered reference surface, diagnostics/conformance, and bounded
  compiler export.
- The repo now has enough hard harness to support a bounded meta-testing family on native
  terrain:
  deterministic docs-first slice workflow, closeout bundles, evidence materializers,
  committed artifact trees, route/runtime fixtures, and dedicated arc start/closeout
  validation commands already exist.
- The repo already contains both soft and hard control surfaces relevant to a future
  meta-loop:
  - soft side:
    the reasoning agent drafts locks, assesses feedback, proposes next slices, and
    performs higher-order synthesis;
  - hard side:
    scripts and validators such as arc-bundle linting, closeout consistency linting,
    semantic closeout linting, stop-gate metrics/report generation, quality dashboard
    generation, and committed event-stream validation already exist as executable
    checkpoints.
- The hard checkpoint side of the first-family loop is therefore mostly non-greenfield:
  the executor surfaces already exist in repo code and are already exercised by the test
  suite, even though the surrounding meta-loop family is new.
- The recursive-compilation note is now explicit:
  the model inside this repo is already functioning as builder, soft simulator, drift
  detector, and temporary executable substrate for reasoning paths not yet fully compiled
  into hard components.
- The first recursive-compilation substrate is no longer hypothetical:
  explicit intent, module ontology, executor binding, parameter-safety, dispatch
  provenance, and hard-checkpoint truth-boundary preservation are now frozen in released
  `V37-A` artifacts on native repo terrain.
- The empirical legibility claim is now part of repo methodology:
  drift classes, compilation boundaries, and stabilization of soft critique into recurring
  controls are observable in the build loop rather than merely theorized.
- The maturation-law distinction is now explicit:
  prompts currently still carry some structural discipline, but the next durable move is
  to compile more of that discipline into substrate rather than into repeated prose.
- The higher-order distinction between:
  - `operational_influence`
  - `accepted_compilation`
  is now explicit and should shape the next family.
- The first bounded reference loop already has a natural native anchor in current repo
  terrain:
  a `v65`-style arc closeout flow can already be executed through the dedicated closeout
  lane and the existing stop-gate / quality-dashboard / instruction-policy /
  consistency-lint surfaces.
- The closeout hardening bundle exists as a separate operational proposal only:
  - `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- The Copilot/Codex CLI approval-flag drift remains a separate future-cleanup item and is
  not implicitly folded into this new family.

## Planning Boundary (For This Family)

- No implicit reopening of the closed `V35` execution-constitution surfaces is
  authorized.
- No implicit reopening of the closed `V36` UX-governance / compiler-export surfaces is
  authorized.
- No model-only self-grading is authorized as authoritative validation.
- No hidden prompt-only sequence is authorized as the operative source of loop structure:
  intended module order, prerequisites, bindings, and branch conditions must be explicit.
- No reasoning prose, worker prose, or event-stream prose may substitute for accepted
  artifact/script outputs when the loop reaches a validation checkpoint.
- No autonomous repo mutation, autonomous policy promotion, or autonomous lock/schema
  update is authorized in the first family.
- No generic "self-improving benchmark platform" or generalized agentic operating system
  is recommended as primary scope.
- No silent collapse of:
  - explicit intent,
  - observed checkpoint result,
  - and post-hoc synthesis
  is permitted.
- No path in this family may treat operational influence as equivalent to accepted
  compilation:
  affecting the builder live is not the same as becoming accepted repo governance.
- No checkpoint module may be invoked without an explicit input/output contract and named
  place in the loop sequence.
- No checkpoint executor binding may interpolate unvalidated soft-step output directly
  into shell text:
  first-family executor bindings should be treated as typed command surfaces with strict
  parameter validation rather than free-form shell templates.
- No reasoning module may claim pass/fail, completion, or control-update authority unless
  that claim is explicitly bound to a downstream hard checkpoint or later accepted control
  process.
- No event stream, notebook-style transcript, or free-form reflection may be treated as a
  canonical truth source by itself.
- No broad rollout across unrelated repo workflows is recommended in the first family;
  the first reference terrain should stay narrow and ADEU-native:
  one bounded `arc_bundle_recursive_compilation_loop`.
- The closeout hardening bundle remains a separate operational track and is not implicitly
  folded into any post-`V36` family unless explicitly locked later.

## Naming Convention (New Family)

- `V37-*` identifiers are reserved for the first recursive-compilation / meta-testing
  family and are not reused elsewhere.
- `B37-*` identifiers are reserved for explicit multi-path bundles if later needed.
- `V36-*` and `V35-*` remain historical/closed and are not reused.

## Family Scale Note

- `V37` defines `5` paths (`V37-A` through `V37-E`) with a default sequential planning
  span now continuing from `vNext+67` through `vNext+70`.
- This sequence is planning intent only; each arc still requires explicit lock/assessment/
  decision docs before implementation authority is granted.

## Vision Contract (Planning-Level)

- Authoritative sources:
  - accepted governance docs and accepted evidence artifacts;
  - the explicit intent packet and accepted module catalog for the bounded reference loop;
  - accepted sequence/trace artifacts for the bounded reference loop;
  - accepted hard checkpoint module outputs and their bound artifact hashes/paths;
  - already-accepted execution-state/visibility/topology/enforcement artifacts from the
    closed `V35` line when the loop needs authoritative runtime context;
  - already-accepted UX-governance / rendered-surface / conformance artifacts from the
    closed `V36` line when the loop needs authoritative UI or conformance context.
- Non-authoritative sources:
  - free-form reasoning prose by itself;
  - hidden prompt choreography not externalized into the module sequence contract;
  - worker prose or event streams by themselves;
  - retrospective narrative summaries not bound to explicit intent and hard checkpoint
    outputs;
  - self-declared pass/fail claims not backed by checkpoint results;
  - advisory control ideas not yet accepted through normal repo process.
- Operational rule:
  - the next family should make recursive compilation runnable without confusing soft
    probe with hard release;
  - reasoning modules may interpret intent, decompose work, predict drift, compare actual
    vs intended flow, and synthesize candidate hardenings;
  - hard checkpoint modules remain authoritative for observed validation results;
  - typed conformance should be derived from explicit intent plus observed checkpoint
    outputs through accepted diagnostics, not from vibes or self-grading;
  - recurring critique becomes accepted governance only when it crosses the compilation
    boundary into accepted repo controls:
    lock text, schema fields, validators, evidence requirements, runtime guards, or
    workflow gates.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "recursive_compilation_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v10.md",
  "methodology_note": "docs/DRAFT_RECURSIVE_COMPILATION_v0.md",
  "closed_path_families": [
    "V34",
    "V35",
    "V36"
  ],
  "closed_paths": [
    "V34-A",
    "V34-B",
    "V34-C",
    "V34-D",
    "V34-E",
    "V34-F",
    "V34-G",
    "V35-A",
    "V35-B",
    "V35-C",
    "V35-D",
    "V35-E",
    "V36-A",
    "V36-B",
    "V36-C",
    "V36-D",
    "V36-E",
    "V37-A"
  ],
  "next_path_family": "V37",
  "v37_path_count": 5,
  "v37_default_arc_span": {
    "from": "vNext+67",
    "to": "vNext+70"
  },
  "default_next_arc_candidate": "V37-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality_baseline": 80,
  "no_implicit_metric_key_expansion": true,
  "artifact_authority_model": "explicit_intent_plus_hard_checkpoint_outputs",
  "soft_reasoning_authority_model": "advisory_unless_checkpoint_bound",
  "bounded_reference_loop_family": "arc_bundle_recursive_compilation_loop",
  "first_reference_loop_anchor": {
    "shape": "arc_closeout_bundle_instance",
    "reference_arc": 65,
    "reference_phase": "closeout"
  },
  "explicit_intent_packet_required": true,
  "explicit_module_catalog_required": true,
  "explicit_sequence_contract_required": true,
  "explicit_run_trace_required": true,
  "reference_loop_binding_tuple": [
    "reference_loop_family",
    "reference_instance_id",
    "intent_packet_id"
  ],
  "module_classes": [
    "reasoning_module",
    "checkpoint_module",
    "evidence_gate_module",
    "operator_gate_module"
  ],
  "checkpoint_module_executor_binding_required": true,
  "reasoning_dispatch_provenance_required": true,
  "hard_checkpoint_module_capabilities_required": [
    "bundle_lint",
    "artifact_consistency_lint",
    "semantic_closeout_lint",
    "stop_gate_metrics_build",
    "quality_dashboard_build",
    "committed_event_stream_validation",
    "instruction_policy_validation"
  ],
  "required_drift_taxonomy": [
    "ontology_drift",
    "epistemic_drift",
    "deontic_drift",
    "utility_drift"
  ],
  "repeated_drift_window_rule": {
    "minimum_runs": 2,
    "same_reference_loop_instance_required": true,
    "same_intent_packet_required": true,
    "window_scope": "accepted_run_trace_set_only"
  },
  "operational_influence_threshold_explicit": true,
  "accepted_compilation_threshold_explicit": true,
  "prompt_substrate_maturation_law_acknowledged": true,
  "no_hidden_prompt_only_sequence_authority": true,
  "no_event_stream_or_worker_prose_truth_substitution": true,
  "no_repo_self_mutation_without_explicit_future_lock": true,
  "control_update_export_mode": "advisory_candidates_only",
  "control_target_priority_order": [
    "validator_rule",
    "runtime_guard",
    "evidence_requirement",
    "schema_field",
    "lock_text",
    "module_catalog_field",
    "sequence_contract_field",
    "prompt_dispatch_convention"
  ],
  "closeout_hardening_bundle_status": "separate_operational_proposal_only"
}
```

## Path V37-A: Meta Intent Packet and Module Ontology Baseline

Lock class: `L1`

Goal:

- make the bounded meta-testing loop legible as typed intent plus typed module ontology
  rather than as prompt choreography or operator folklore.

Scope:

- define canonical `meta_testing_intent_packet@1` for one bounded
  `arc_bundle_recursive_compilation_loop`;
- define canonical `meta_module_catalog@1` for the same bounded loop;
- require `meta_testing_intent_packet@1` to carry at least:
  - explicit objective;
  - success condition;
  - failure condition;
  - authoritative input set;
  - required hard checkpoints;
  - required evidence outputs;
  - allowed reasoning latitude;
  - refusal/escalation conditions;
  - ADEU priority ordering for ontology/epistemics/deontics/utility significance;
- require `meta_module_catalog@1` to carry at least:
  - stable module id;
  - module class;
  - input contract;
  - output contract;
  - authority status;
  - executor binding ref for checkpoint/evidence-gate/operator-gate modules:
    exact repo command, script, or tool surface that instantiates the module;
  - executor parameter policy for checkpoint/evidence-gate/operator-gate modules:
    typed parameter slots, validation rule, and prohibition on unchecked shell
    interpolation for soft-originated inputs;
  - dispatch provenance ref for reasoning modules:
    prompt surface, template/version ref, or dispatch convention id;
  - predecessor/successor constraints;
  - expected evidence refs;
  - whether the module is soft reasoning or hard checkpoint in role;
- freeze the first-family module classes:
  - `reasoning_module`
  - `checkpoint_module`
  - `evidence_gate_module`
  - `operator_gate_module`
- freeze the first-family binding tuple:
  - `reference_loop_family`
  - `reference_instance_id`
  - `intent_packet_id`
- freeze the first-family drift taxonomy for later diagnostics:
  - `ontology_drift`
  - `epistemic_drift`
  - `deontic_drift`
  - `utility_drift`
- require the first bounded loop family to be ADEU-native and immediately runnable on
  current repo terrain:
  `arc_bundle_recursive_compilation_loop`;
- require one accepted bound reference-instance pair for the first-family intent packet
  and module catalog, not just schema prose.

Locks:

- no runnable loop release is authorized by this path by default;
- no implicit module may exist outside the accepted catalog;
- no module may claim authority status not explicit in the catalog;
- no checkpoint capability may be treated as present unless named in the catalog;
- no module sequence may be treated as authoritative before `V37-B`;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- canonical `meta_testing_intent_packet@1` schema and `meta_module_catalog@1` schema
  exist;
- module classes, binding tuple, authority categories, and ADEU drift taxonomy required
  for the bounded reference loop are frozen;
- one accepted `arc_bundle_recursive_compilation_loop` reference instance exists for both
  schemas and can be serialized canonically and hashed deterministically;
- the accepted reference-instance pair is sufficient to describe one bounded reference
  loop deterministically, including:
  explicit objective,
  authoritative inputs,
  required checkpoints,
  exact checkpoint executor bindings,
  reasoning dispatch provenance,
  allowed reasoning latitude,
  and hard/soft module distinction.

## Path V37-B: Sequence Contract and Run Trace Baseline

Lock class: `L1`

Goal:

- make the bounded meta-loop executable as explicit sequence law rather than as tacit
  operator memory or hidden prompt order.

Scope:

- define canonical `meta_loop_sequence_contract@1` for the first bounded reference loop;
- define canonical `meta_loop_run_trace@1` for the same loop;
- require `meta_loop_sequence_contract@1` to freeze at least:
  - stable step ids;
  - referenced module id per step;
  - ordered phase boundaries;
  - required inputs and expected outputs;
  - checkpoint bindings;
  - branch conditions;
  - failure edges;
  - operator-gate surfaces;
  - dispatch provenance binding for each reasoning step:
    prompt surface ref,
    template/version ref,
    or dispatch convention id;
  - compilation-boundary markers where a live critique may later become candidate control
    input;
- require `meta_loop_run_trace@1` to carry at least:
  - `trace_mode`;
  - planned step id;
  - actual module executed;
  - consumed inputs;
  - emitted outputs;
  - observed checkpoint result refs;
  - skipped/failed/retried status;
  - whether operational influence occurred at that step;
  - whether anything crossed into accepted compilation at that step;
- freeze the first-family `V37-B` trace-law posture explicitly:
  - in `v67`, the accepted `meta_loop_run_trace@1` is a reference trace artifact, not
    proof of executed end-to-end loop behavior;
  - `trace_mode` should therefore be frozen to `reference_not_executed` in the first
    bounded pair;
  - `observed_checkpoint_result_refs` should remain empty unless bound to separately
    accepted pre-existing artifact refs outside the loop itself;
  - `accepted_compilation_occurred` should remain `false` for all steps in the first
    bounded pair unless explicitly bound to already accepted repo controls outside the
    loop itself;
- freeze retry representation explicitly in the first family:
  documented retry behavior should be represented via explicit retry-edge fields or
  explicit retry-policy references rather than inferred from generic failure edges;
- freeze step-binding nullability explicitly in the first family:
  `checkpoint_binding_id`, `branch_condition_id`, `operator_gate_id`, and
  `dispatch_provenance_ref` should remain present with explicit nulls when not
  applicable rather than disappearing by omission;
- make the two thresholds explicit in the sequence/trace layer:
  - `operational_influence`
  - `accepted_compilation`
- require any reasoning step that asserts sufficiency, pass/fail expectation, closure, or
  drift classification to bind to an explicit downstream checkpoint module, evidence gate,
  or operator gate;
- require any checkpoint/evidence-gate/operator-gate step to bind to the exact executor
  ref named in the accepted module catalog rather than to a generic capability label;
- require stable cross-artifact binding back to the accepted `V37-A` reference-instance
  pair through the frozen binding tuple.

Locks:

- no executable reference loop is authorized in this path by default;
- no step ordering may remain prompt-only or undocumented;
- no hidden branch logic is valid if it affects later checkpoints or conformance;
- no reasoning step may be treated as a terminal validator unless explicitly bound to a
  hard checkpoint or accepted future control process.

Acceptance:

- canonical `meta_loop_sequence_contract@1` schema and `meta_loop_run_trace@1` schema
  exist;
- one accepted bound sequence/trace reference pair exists for the same first-family
  intent packet and module catalog;
- the accepted reference pair makes the first bounded loop reproducible enough to drive
  one deterministic reference-law description of a later end-to-end run, including:
  step order,
  prerequisites,
  reasoning dispatch provenance,
  checkpoint bindings,
  exact checkpoint executor bindings,
  operator gates,
  explicit retry representation,
  explicit null-binding representation,
  and the distinction between operational influence and accepted compilation.

## Path V37-C: Arc-Bundle Recursive Compilation Reference Loop

Lock class: `L0`

Goal:

- implement one bounded executable reference meta-loop that actually triggers reasoning
  modules and hard checkpoint modules in intended sequence and assesses outputs against
  explicit intent.

Scope:

- implement one bounded `arc_bundle_recursive_compilation_loop` over the accepted
  `V37-A` and `V37-B` substrate;
- anchor the first reference implementation to one concrete existing native terrain:
  a `v65`-style closeout bundle instance rather than an abstract family-only loop;
- execute both:
  - reasoning modules active in the meta-loop;
  - hard checkpoint modules already present in repo scripts/validators/artifacts;
- require the hard side of the first-family loop to cover actual repo-native capabilities
  from the current harness, such as:
  - bundle lint;
  - closeout consistency lint;
  - semantic closeout lint;
  - stop-gate metrics/report generation;
  - quality dashboard generation;
  - committed event-stream validation;
  - instruction-policy validation;
- require the first-family loop to bind those capabilities to exact repo executors, for
  example:
  - `make arc-closeout-check ARC=<n>`;
  - `apps/api/scripts/build_quality_dashboard.py`;
  - `apps/api/scripts/build_stop_gate_metrics.py`;
  - `apps/api/scripts/generate_instruction_policy_views.py --check`;
  - `events validate`;
- treat those as composed checkpoint-module executor bindings under one accepted
  sequence contract, not as one monolithic executor surface:
  `make arc-closeout-check ARC=<n>` is one checkpoint binding in the loop,
  while quality-dashboard build, stop-gate build, instruction-policy validation, and
  committed event-stream validation remain distinct checkpoint bindings;
- require the later first lock to freeze the chosen authoritative stop-gate executor
  deliberately rather than leaving adjacent repo surfaces interchangeable under the
  capability label alone;
- require any parameter flowing from a reasoning step into a checkpoint executor binding
  to pass typed validation before invocation:
  first-family bindings should be modeled as validated argument vectors, not as raw shell
  fragments;
- normalize observed hard checkpoint outputs into canonical
  `meta_loop_checkpoint_result_manifest@1`;
- require the reference execution to emit one accepted deterministic run trace bound to:
  - explicit intent;
  - accepted module catalog;
  - accepted sequence contract;
  - accepted hard checkpoint outputs;
- require the loop to keep reasoning and checkpoint roles distinct:
  reasoning modules may predict, compare, classify, or synthesize;
  hard checkpoint modules remain authoritative for observed validation truth;
- keep the first reference loop ADEU-native and bounded:
  arc-bundle evaluation and closeout/governance flow over one concrete accepted
  closeout-shaped instance,
  not generalized repo autonomy.

Locks:

- no generalized daemon/orchestrator is authorized by this path;
- no autonomous repo mutation, branch management, PR submission, or policy promotion is
  authorized;
- no checkpoint result may be inferred from model prose when the actual hard checkpoint
  was not run;
- no loop step may exist only inside prompt text without explicit trace representation;
- no rollout across unrelated repo workflows is authorized by this path by default.

Acceptance:

- one bounded reference loop can be executed end-to-end against an explicit intent packet;
- the first accepted reference execution is anchored to one concrete existing arc-bundle
  instance rather than to a family abstraction only;
- both reasoning-module outputs and hard checkpoint outputs are captured under the shared
  binding tuple;
- observed pass/fail- or gate-relevant truth in the run is derived from hard checkpoint
  outputs and accepted artifact refs rather than from unbound reasoning prose;
- the reference loop emits enough deterministic structured output for later typed drift
  diagnostics and conformance.

## Path V37-D: Drift Diagnostics and Conformance Baseline

Lock class: `L1`

Goal:

- make recursive-compilation drift deterministic, typed, and assessable against explicit
  intent rather than leaving it as narrative critique.

Scope:

- define canonical `meta_loop_drift_diagnostics@1`;
- define canonical `meta_loop_conformance_report@1`;
- require each diagnostic finding to carry at least:
  - stable `finding_id`;
  - stable `rule_id` or violation family;
  - severity;
  - ADEU drift class;
  - bound module refs;
  - bound intent clause refs;
  - bound sequence/trace refs;
  - supporting evidence refs;
  - conformance impact;
- require `meta_loop_conformance_report@1` to carry at least:
  - overall judgment;
  - supporting finding ids;
  - severity counts;
  - failed/warning rule families;
  - shared binding tuple;
  - derivation metadata proving it was computed from accepted diagnostics and frozen hard
    inputs rather than from export-local heuristics;
- freeze the first-family conformance aggregation rule:
  - any `error` => `fail`;
  - no `error`, at least one `warning` => `needs_review`;
  - only `advisory` findings or no findings => `pass`;
- require exact cross-layer binding equality for:
  - `reference_loop_family`
  - `reference_instance_id`
  - `intent_packet_id`
  across the accepted `V37-A`, `V37-B`, and `V37-C` artifacts and the new `V37-D`
  diagnostics/conformance artifacts;
- make hard-result truth substitution fail closed:
  worker prose, event streams, and free-form reflections may appear only as provenance or
  context, not as authoritative grounds for pass/fail by themselves;
- freeze seeded first-family violation families, including at least:
  - `sequence_gap_detectable`
  - `intent_clause_unassessed_detectable`
  - `unbound_reasoning_claim_detectable`
  - `checkpoint_bypass_detectable`
  - `missing_artifact_evidence_detectable`
  - `prompt_substrate_mismatch_detectable`
    only where reasoning-dispatch provenance and actual executor bindings are both
    available in the accepted run trace;
  - `repeated_uncompiled_drift_detectable`
    only over at least two accepted runs of the same reference loop instance under the
    same accepted intent packet within one frozen evaluation window;
  - `operational_influence_accepted_compilation_collapse_detectable`

Locks:

- no runtime auto-repair or automatic repo update is authorized by this path;
- no new local heuristic truth sources may be introduced outside:
  explicit intent,
  accepted module/sequence artifacts,
  accepted hard checkpoint outputs,
  and accepted evidence refs;
- no diagnostics/conformance lane may redefine the frozen ADEU drift taxonomy or the
  meaning of operational influence vs accepted compilation.

Acceptance:

- canonical `meta_loop_drift_diagnostics@1` and `meta_loop_conformance_report@1` exist;
- one accepted deterministic diagnostics artifact and one accepted deterministic
  conformance report exist for the bounded reference loop;
- conformance is deterministically derived from diagnostics according to the frozen
  aggregation rule rather than by export-local judgment;
- the accepted artifacts are sufficient to classify drift against explicit intent, bind
  it to actual module/checkpoint outputs, and fail closed on truth substitution or
  checkpoint bypass.

## Path V37-E: Advisory Control-Update Export and Drift-Reduction Candidates

Lock class: `L1`

Goal:

- convert recurring typed drift into bounded advisory control-update candidates without
  collapsing into autonomous self-modification.

Scope:

- define canonical `meta_control_update_candidate@1`;
- define canonical `meta_control_update_manifest@1`;
- require candidates to be derived only from:
  - accepted explicit intent;
  - accepted sequence/trace artifacts;
  - accepted hard checkpoint outputs;
  - accepted drift diagnostics;
  - accepted conformance reports;
- require `meta_control_update_candidate@1` to carry at least:
  - stable candidate id;
  - target control class;
  - target path or surface id;
  - bound drift finding ids;
  - supporting evidence refs;
  - expected drift-reduction claim;
  - risk notes;
  - application friction mode:
    whether the candidate is review-only, adjudication-required, or otherwise blocked from
    direct blind application;
  - advisory-only status;
- require `meta_control_update_manifest@1` to carry at least:
  - shared binding tuple;
  - emitted candidate ids;
  - candidate class counts;
  - derivation refs/hashes;
  - target-class priority order actually used for export ranking;
  - explicit statement that emission is not acceptance;
- limit allowed first-family target control classes to bounded repo-native surfaces such
  as:
  - lock text;
  - schema field;
  - linter/validator rule;
  - evidence requirement;
  - runtime guard;
  - prompt dispatch convention;
  - module-catalog / sequence-contract field;
- require the first-family export lane to rank hard control classes ahead of prompt-local
  repair surfaces:
  validator rule,
  runtime guard,
  evidence requirement,
  and schema field should outrank prompt dispatch convention when multiple repair targets
  are supported by the same drift finding;
- require all emitted candidates to remain advisory:
  existence of a candidate is not policy, not acceptance, and not a repo mutation;
- require first-family advisory exports to avoid blind copy-paste bypass by default:
  raw ready-to-apply patch files and raw executable shell blocks should not be the
  default emitted form when they would let operator fatigue bypass normal adjudication;
- make the family-level capstone explicit:
  recurring critique may now be exported as candidate control input,
  but it crosses the compilation boundary only if a later normal repo process accepts and
  hardens it.

Locks:

- no automatic repo mutation, automatic lock update, automatic schema generation,
  automatic validator rollout, or automatic prompt rewrite is authorized;
- no candidate export may claim governance effect merely because it is evidence-backed;
- no candidate export may circumvent advisory-only status by defaulting to directly
  executable patch/shell payloads without a tracked adjudication step;
- no generalized self-improvement engine or open-ended patch generator is authorized in
  the first family.

Acceptance:

- canonical `meta_control_update_candidate@1` and `meta_control_update_manifest@1`
  exist;
- one accepted advisory export lane exists for the bounded reference loop;
- emitted candidates are deterministically bound to accepted diagnostics/conformance and
  to named target control surfaces;
- export ranking preserves the hard-control-first target priority order rather than
  defaulting to prompt-local fixes when harder substrate fixes are available;
- emitted advisory candidates preserve typed friction between recommendation and
  application rather than collapsing into blind copy-paste mutation surfaces;
- the export lane is sufficient to make recurring high-governance drift legible as a
  candidate future hardening path without treating candidate emission as accepted
  compilation.

## Separate Operational Track (Non-V37)

The higher-order methodology note and the closeout hardening bundle remain separately
named and intentionally orthogonal:

- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`

They should not be treated as implicit `V37` scope unless later formalized under their
own lock bundle. The current recommendation remains:

1. keep the recursive-compilation note above arcs as methodology rather than path
   authority
2. keep `O1` / `O2` / `O3` closeout hardening separate from the first recursive-
   compilation family
3. preserve future-cleanup items as separate operational work rather than silently
   mixing them into `V37`

## Recommended Default Order

1. `V37-A`
   - freeze explicit intent and module ontology first:
     without this, the meta-loop collapses into prose choreography.
2. `V37-B`
   - freeze explicit sequence/trace law before any runnable loop work.
3. `V37-C`
   - implement one bounded executable reference loop on native repo terrain.
4. `V37-D`
   - make drift typed, deterministic, and conformance-bearing once the reference loop
     exists.
5. `V37-E`
   - only then export recurring drift as bounded advisory control-update candidates.

## Non-Goals (Current Family)

This planning draft does not recommend:

- a generalized autonomous software-improvement engine;
- prompt-only self-testing without explicit module sequencing and hard checkpoint
  authority;
- reopening closed `V35` or `V36` families under a meta-testing label;
- model prose, worker prose, or event streams as substitutes for checkpoint truth;
- automatic repo mutation, automatic policy adoption, or automatic validator rollout;
- a repo-wide benchmark platform as the first deliverable;
- hidden prompt choreography as the operative source of sequence law;
- collapsing operational influence into accepted compilation;
- generic "recursive self-reference" without typed ADEU distinctions and accepted repo
  evidence.

## Recommendation

- treat `V37-A` as closed and use it as the frozen substrate for the next recursive-
  compilation slice rather than widening it in place;
- select `V37-B` as the next default candidate:
  explicit sequence contract plus run trace is the minimum executable law required
  before a runnable reference loop can be governed cleanly;
- keep the first implementation terrain narrow and repo-native:
  one bounded `arc_bundle_recursive_compilation_loop`, not a generalized autonomy stack;
- preserve the recursive-compilation note's central distinction:
  live critique may exert operational influence before it becomes accepted compilation,
  and the next family should make that distinction explicit rather than blur it;
- keep the hard/soft split crisp:
  reasoning modules may guide, predict, compare, and synthesize,
  but hard checkpoint modules and accepted artifacts remain authoritative for validation
  truth;
- preserve the separate operational cleanup track (`O1` / `O2` / `O3`) and the
  higher-order methodology note as distinct follow-ons rather than silently mixing them
  into the first `V37` family.
