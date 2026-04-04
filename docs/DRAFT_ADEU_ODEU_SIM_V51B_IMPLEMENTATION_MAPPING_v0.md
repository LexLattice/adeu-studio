# Draft ADEU ODEU Sim V51B Implementation Mapping v0

Status: support note for the `V51-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro `odeu-sandbox-app` prototype should be used as shaping evidence while the live
repo-owned `V51-B` implementation is re-authored as a bounded API consumer over the
released `V51-A` kernel.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS125.md`
- `examples/external_prototypes/odeu-sandbox-app/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the prototype's use of explicit `scenario` and `seed` request inputs
- the idea of a route-local snapshot over released kernel state
- the prototype's single-run snapshot idea, but not its mutable long-lived sim object
- the high-level summary groupings already visible in the prototype API payload:
  - meta
  - config
  - lane summary
  - institution / metrics summary
  - action / event / evidence counts

## Re-Author With Repo Alignment

- re-author the live surface under `apps/api/src/adeu_api/`
- make the route stateless and non-persistent over the released `V51-A` kernel
- require the released stateless helper path:
  - `run_canonical_scenario(...)`
- reuse the released summary helpers:
  - `summarize_lane_state(...)`
  - `summarize_action_counts(...)`
- replace the prototype reset/step/state trilogy with one bounded `POST /odeu-sim/run`
  surface
- project released kernel facts into one summary-only JSON contract with:
  - full released metric payload
  - exact three-key lane summary
  - sparse observed-only action counts
- add typed fail-closed invalid-request and kernel-mismatch postures
- keep request/response hashing and deterministic fixture replay explicit

## Defer To Later Slice

- browser UI and static assets to `V51-C`
- any persistent session or stepwise control surface to later family work
- broader route catalog, streaming, websockets, or storage
- richer agent/network payloads beyond the bounded summary projection

## Do Not Import

- the prototype `api.py` wholesale into live repo paths
- `app.state.sim` mutable session state
- direct `ODEUSimulation.reset()/step()` route orchestration
- the prototype static mount or root `FileResponse`
- permissive CORS/static-app setup as if it were released API doctrine
- scenario override dictionaries or mutable per-request patch payloads
