# Draft Stop-Gate Decision vNext+111

Status: proposed gate for `V47-F`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS111.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `anm_benchmark_policy_consumer_binding_profile@1` ships with
  authoritative/mirror schema parity;
- the released benchmark-world vocabularies stay exact and bounded to:
  - `released_v42_local_eval_artifact_world`
  - `released_v42_scorecard_artifact_world`
  - `released_v42_behavior_evidence_artifact_world`;
- every accepted benchmark consumer row binds exactly one explicit released `D-IR`
  clause source;
- result-set and ledger refs remain support-only and fail closed on contradiction;
- any supporting result/ledger refs cohere to the same benchmark target, declared
  snapshot, and bound policy-source lineage where that lineage is represented;
- benchmark refs resolve fail closed against the declared snapshot and source scope;
- benchmark consumer rows respect released `V42-D`, `V42-E`, and `V42-G4` authority
  doctrine where relevant;
- benchmark consumer rows also respect released `V47-C`, `V47-D`, and `V47-E`
  profiles where relevant;
- any required released `V42-*` or `V47-*` doctrine joins fail closed when dangling,
  stale, or unresolved against the declared snapshot/source scope;
- the shipped constrain-action vocabulary remains exact and shared across row action
  fields;
- benchmark action buckets are pairwise disjoint and stay consistent with
  `current_benchmark_consumer_authority_relation`;
- committed accepted/reject fixtures replay deterministically for local-eval,
  scorecard, and behavior-evidence benchmark consumers;
- the slice remains non-executive and does not mint official scorecard, leaderboard,
  submission, tournament, execution, approval, waiver, or deferral authority;
- `V46` benchmark-family release remains deferred rather than being smuggled into this
  slice.

## Do Not Accept If

- benchmark consumer posture widens into generic benchmark-family doctrine instead of
  binding only released benchmark artifact worlds on `main`;
- any benchmark row can be valid without one explicit released `D-IR` clause source;
- local eval is overread as official scorecard or leaderboard authority;
- scorecard source-kind or authority posture is ignored, collapsed, or silently
  upgraded;
- behavior-evidence narrative or claim posture is treated as execution, approval,
  submission, or tournament authority;
- support surfaces attach to unrelated targets, unrelated snapshot/scope baselines, or
  unrelated policy-source lineage while still appearing structurally valid;
- world/ref-kind invariants are loose enough to admit contradictory benchmark rows;
- benchmark binding bypasses released `V42-D`, `V42-E`, `V42-G4`, `V47-C`, `V47-D`, or
  `V47-E` profile doctrine where those surfaces are relevant;
- relevant released `V42-*` or `V47-*` doctrine joins can be left dangling or stale
  without fail-closed rejection;
- action fields invent a second benchmark-action language outside the frozen enum;
- the same action can appear in more than one action bucket or the action buckets drift
  from `current_benchmark_consumer_authority_relation`;
- the implementation silently widens into repo-wide markdown migration or
  source-level `DEFERRED`.

## Local Gate

- run `make arc-start-check ARC=111`
