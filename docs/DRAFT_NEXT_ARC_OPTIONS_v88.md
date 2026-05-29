# Draft Next Arc Options v88

Status: planning draft after `OTB-0` family closeout and the ProgramBench
`revive` v47 reconstruction-to-100 run.

Authority layer: planning.

This draft records the next candidate family after deterministic phase
transition legality became reviewable. It does not authorize semantic
adjudication, ontology generation, probe generation, probe execution, command
execution, code edits, worker dispatch, implementation authority, product
authority, graph-memory authority, recursive policy amendment, PR creation,
commit, merge, release, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

This selector treats `HOB-0` and `OTB-0` as the immediate upstream families:

```text
HOB = deterministic obligation inheritance inside ontology trees.
OTB = deterministic transition legality between meta-program phases.
```

The next pressure is different:

```text
previously green behavior exists
  -> iterative patch touches a shared owner surface
  -> green behavior may silently drift
  -> the orchestrator must rediscover the regression by memory, broad tests, or
     official eval
```

## Current Frontier

The ProgramBench `revive` run exposed a repeatable regression-preservation
failure:

```text
patch adds new behavior
  -> local tail probes pass
  -> older locked surfaces are not always replayed immediately
  -> a shared implementation owner changes package/file routing, formatter
     grammar, config discovery, or diagnostics
  -> previous green rows can regress without a deterministic no-regression
     certificate
```

The final `revive` patch reached full green only after rerunning focused public
tests and locked probes. That process was effective but manual. The next family
should turn the pattern into a reusable artifact:

```text
locked behavioral replay manifest
  + canonical observation hashes
  + impact-cone sentinel selection
  + replay/diff reports
  + no-regression certificates
```

The `revive` review sharpened the trigger:

```text
shared-owner patch
  -> formatter, config, file routing, package context, directive scope, or
     generic rule fallback may affect already-green siblings
  -> replay lock must import protected sibling sentinels before the patch can
     be promoted as a new baseline
```

Primary support inputs:

- `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md`
- `docs/ARCHITECTURE_ADEU_ODEU_TRANSITION_BROKER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0_FAMILY_CLOSEOUT_v0.md`
- `docs/support/programbench_revive_v47_causal_story_to_100.md`
- `artifacts/manual_runs/programbench_revive_v47_otb_hob_phase0_20260528T010131+0300/phase_outputs/p64_tail_batch_closeout.md`

## Next Planning Question

Should the next family make no-regression claims deterministic by replaying
locked behavioral manifests and comparing canonical observation hashes, without
turning the tool into a semantic judge, probe author, command planner, code
patcher, or product authority?

Recommended candidate:

```text
BRL-0:
  Behavioral Replay Lock
```

Alternate descriptive names:

```text
Locked Regression Manifest
Behavioral No-Regression Certificate
```

The family label should remain `BRL-0` for compact slice naming.

## Family Thesis

`BRL-0` should implement the deterministic replay institution that protects
previously green behavior after iterative changes.

The controlling distinction:

```text
source hash:
  same artifact bytes

behavioral replay hash:
  same observed behavior over a named manifest, under explicit
  canonicalization rules
```

Controlling invariant:

```text
No-regression means no observed regression relative to a locked manifest,
under named canonicalization rules, over named protected surfaces.

It is not a universal product-truth claim.
```

Owner-surface invariant:

```text
A patch touching a shared owner is illegal as a promoted baseline unless it
proves preservation of previous green sibling surfaces through a locked replay
manifest or records the uncovered sibling risk as a blocker.
```

## Recommended Next Pressure

- family / practical arc: `BRL-0`
- proposed name:
  - `BRL-0: Behavioral Replay Lock`
- recommended first slice:
  - `BRL-0-A`
- recommended package ownership:
  - `packages/adeu_behavioral_replay_lock`
  - schema mirrors under `spec/`
- adjacent future integration:
  - HOB leaves can reference protected sentinel probes;
  - OTB transitions can require replay-lock certificates before local parity,
    packaged preflight, official-like eval, or official eval;
  - ProgramBench reconstruction can use replay manifests for iterative repair;
  - no integration is selected by this planning draft.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `BRL-0-A` | Manifest, canonicalization profile, observation hash schema, and manifest validation |
| `BRL-0-B` | Replay runner, canonical observation capture, per-probe diff, and suite-root hash report |
| `BRL-0-C` | Impact-cone sentinel selection, no-regression certificates, HOB/OTB handoff, and stale-lock invalidation |

## Selected Surfaces For Starter Drafting

`BRL-0-A` should be the first active slice. Candidate starter surfaces:

- `repo_behavioral_replay_manifest@1`
- `repo_behavioral_probe_contract@1`
- `repo_behavioral_canonicalization_profile@1`
- `repo_behavioral_observation_hash@1`
- `repo_behavioral_replay_manifest_validation_report@1`
- `repo_behavioral_replay_lock_non_authority_guardrail@1`

`BRL-0-A` boundary clarification:

```text
BRL-0-A validates replay manifests and defines canonical hash inputs.
It does not execute probes, compare candidate behavior, select impact-cone
sentinels, or emit no-regression certificates.
```

The selector recommendation is to select `BRL-0-A` as the next default candidate.

`BRL-0-B` later surfaces:

- `repo_behavioral_replay_execution_report@1`
- `repo_behavioral_observation_record@1`
- `repo_behavioral_regression_diff@1`
- `repo_behavioral_suite_root_hash_report@1`

`BRL-0-C` later surfaces:

- `repo_behavioral_impact_cone_selection_report@1`
- `repo_behavioral_no_regression_certificate@1`
- `repo_behavioral_lock_staleness_report@1`
- `repo_behavioral_replay_integration_handoff@1`

## Continuation After `BRL-0-A`

After `BRL-0-A` is released and closed on `main`, continue the selected
`BRL-0` family by drafting the next slice lock/decision/assessment sequence and
select `BRL-0-B` as the next default candidate.

## Continuation After `BRL-0-B`

After `BRL-0-B` is released and closed on `main`, continue the selected
`BRL-0` family by drafting the next slice lock/decision/assessment sequence and
select `BRL-0-C` as the next default candidate.

## Non-Authority Boundary

`BRL-0` may:

- validate replay manifest shape;
- validate probe contracts and canonicalization profiles;
- define canonical observation hash material;
- replay already-specified probes in later slices;
- compare observed exit/stdout/stderr/file/process surfaces in later slices;
- emit structured diffs and suite-root hashes;
- emit bounded no-regression certificates in later slices;
- report stale manifests when protected surface, probe contract, fixture hash,
  canonicalization profile, or target artifact identity changes.

`BRL-0` may not:

- decide which semantic obligations are required;
- decide whether a HOB node applies;
- decide phase-transition legality;
- generate probes from freeform prose;
- inspect product source to decide meaning;
- patch code;
- dispatch workers;
- grant product truth;
- treat official benchmark failures as clean first-pass evidence;
- claim universal no-regression outside the locked manifest scope;
- select future families.

## Candidate First-Slice Acceptance Tests

`BRL-0-A` should prove at least:

1. A valid replay manifest validates and produces a stable manifest hash.
2. Shuffled probe rows produce the same canonical manifest hash.
3. Missing required observation surface declarations fail closed.
4. Unknown canonicalization vocabulary fails closed.
5. A probe that claims file-tree protection without before/after fixture hash
   fields fails closed.
6. A manifest with duplicate `probe_id` rows fails closed.
7. A manifest whose suite-root hash does not match child probe hashes fails
   closed.
8. Non-authority guardrails are exported and forbid semantic, product, and
   implementation claims.
9. A manifest can record owner-surface groups and protected sibling sentinels
   without granting semantic or product authority.
10. Expected observation hashes require provenance and visibility posture.
11. Hashes are domain-separated by schema/object kind/version.
12. Raw, canonicalized, protected, and ignored surfaces are distinct.
13. Mutating probes require explicit fixture/write policy.
14. Secret-like environment material requires safe rendering/storage policy.
15. Draft/stale manifests cannot support promotion claims.

## Recommended Starter Bundle

If selected, the next internal lane should prepare:

- `LOCKED_CONTINUATION_vNEXT_PLUS<n>.md` for `BRL-0-A`;
- `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS<n>.md`;
- `ASSESSMENT_vNEXT_PLUS<n>_EDGES.md`;
- implementation PR for `packages/adeu_behavioral_replay_lock`;
- closeout evidence with schema export, fixture replay, and docs alignment.
