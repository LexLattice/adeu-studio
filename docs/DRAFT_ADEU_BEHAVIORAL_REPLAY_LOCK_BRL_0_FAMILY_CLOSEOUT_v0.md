# Draft ADEU Behavioral Replay Lock BRL-0 Family Closeout v0

Status: family closeout record after `vNext+280` / `BRL-0-C` merged on `main`.

Authority layer: closeout evidence on `main`.

This note closes `BRL-0` as the Behavioral Replay Lock family. It records the
selected A/B/C deterministic replay-lock surfaces and their authority boundary.
It does not authorize semantic adjudication, domain ontology generation, HOB
obligation closure, OTB transition legality, probe generation outside released
manifests, freeform command planning, worker dispatch, source patching, product
behavior claims, official-eval submission, ProgramBench integration,
future-family selection, release authority, or recursive policy amendment.

## Family-State Marker

```json
{
  "schema": "brl_0_family_closeout_state@1",
  "family": "BRL-0",
  "phase": "family_closed_on_main",
  "closed_by_arc": "vNext+280",
  "closed_by_merge_commit": "c5dfc63541ad910401950bb620e54ed8d988ccfe",
  "authoritative_scope": "behavioral_replay_lock_selected_a_b_c_surfaces_only",
  "future_family_authority": "none"
}
```

## Closed Slice Ladder

| Slice | Global arc | Closed surface | Closeout evidence |
| --- | --- | --- | --- |
| `BRL-0-A` | `vNext+278` | replay manifest, probe contract, canonicalization profile, expected observation hash, manifest validation report, and replay lock non-authority guardrail | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS278.md`; `artifacts/agent_harness/v278/evidence_inputs/brl_0a_closeout_evidence_v278.json` |
| `BRL-0-B` | `vNext+279` | replay execution report, canonical observation record, regression diff, and suite-root hash report | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS279.md`; `artifacts/agent_harness/v279/evidence_inputs/brl_0b_closeout_evidence_v279.json` |
| `BRL-0-C` | `vNext+280` | impact-cone sentinel selection, bounded no-regression certificate, stale-lock report, and replay integration handoff | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS280.md`; `artifacts/agent_harness/v280/evidence_inputs/brl_0c_closeout_evidence_v280.json` |

## Shipped Surface Set

`BRL-0` shipped these behavioral replay lock surfaces in
`packages/adeu_behavioral_replay_lock`:

- `repo_behavioral_replay_manifest@1`
- `repo_behavioral_probe_contract@1`
- `repo_behavioral_canonicalization_profile@1`
- `repo_behavioral_observation_hash@1`
- `repo_behavioral_replay_manifest_validation_report@1`
- `repo_behavioral_replay_lock_non_authority_guardrail@1`
- `repo_behavioral_replay_execution_report@1`
- `repo_behavioral_observation_record@1`
- `repo_behavioral_regression_diff@1`
- `repo_behavioral_suite_root_hash_report@1`
- `repo_behavioral_impact_cone_selection_report@1`
- `repo_behavioral_no_regression_certificate@1`
- `repo_behavioral_lock_staleness_report@1`
- `repo_behavioral_replay_integration_handoff@1`

The family stayed in the deterministic behavioral replay lane. It did not
claim product truth, HOB closure, OTB transition legality, official-eval
readiness, future-family selection, source patching authority, release
authority, or recursive policy amendment.

## Alignment Judgment

`BRL-0-A` made replay manifests and their protected behavioral surfaces
first-class objects. It validated probe contracts, canonicalization profiles,
expected observation hashes, owner-surface rows, suite-root hashes, lifecycle
state, and non-authority guardrails before replay evidence could be consumed.

`BRL-0-B` consumed released A records and executed only manifest-declared probe
contracts against a supplied candidate artifact. It captured raw and canonical
observation surfaces, emitted expected-vs-actual regression diffs, computed
suite-root hash reports, and kept all outputs report-only rather than patch,
certificate, product, or official-eval authority.

`BRL-0-C` consumed released A/B records plus declared owner-surface scope to
select existing sentinels, report stale locks, emit bounded no-regression
certificates, and constrain downstream handoffs. It hardened mixed
covered/uncovered owner-surface selection, missing-scope blockers, and
staleness report identity checks during review.

The three slices align:

- A defines and validates the locked replay theorem.
- B replays that theorem against a candidate and records behavioral diffs.
- C chooses preservation scope, blocks stale or incomplete evidence, and emits
  bounded replay-preservation certificates and handoffs.
- All slices preserve the same non-authority boundary:
  replay-lock records may constrain downstream phases but do not mint semantic
  truth, product truth, implementation authority, official-eval authority,
  HOB closure, OTB transition legality, release authority, or future-family
  selection.

## Deferred Surfaces

These surfaces remain outside `BRL-0` and require later explicit selection if
they become necessary:

- actual ProgramBench workflow integration;
- product implementation patching;
- official result governance;
- HOB subtree closure;
- OTB transition enforcement;
- worker dispatch;
- release authority;
- future-family selection;
- recursive policy amendment.

## Final Family Decision

- `BRL-0` is closed on `main` as the deterministic Behavioral Replay Lock
  family for selected A/B/C replay manifest, replay execution/diff,
  preservation certificate, stale-lock, and handoff surfaces.
- Future selectors may consume `BRL-0` surfaces as deterministic behavioral
  replay and bounded preservation evidence substrate, but this closeout does
  not select or authorize any next family.
- Downstream phases must preserve the `BRL-0` authority boundary: replay locks
  may validate, replay, diff, select sentinels, report staleness, and constrain
  handoffs; they do not patch, productize, evaluate officially, close HOB
  obligations, authorize OTB transitions, release, amend recursive policy, or
  select future work.
