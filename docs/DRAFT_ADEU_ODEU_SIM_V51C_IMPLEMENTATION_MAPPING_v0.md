# Draft ADEU ODEU Sim V51C Implementation Mapping v0

Status: support note for the `V51-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro `odeu-sandbox-app` prototype should be used as shaping evidence while the live
repo-owned `V51-C` implementation is re-authored as one bounded `apps/web` consumer
over the released `V51-A` kernel plus `V51-B` API stack.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS126.md`
- `examples/external_prototypes/odeu-sandbox-app/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the prototype’s high-level summary groupings for a first browser surface:
  - regime/meta badge
  - scenario selection
  - metric summary
  - lane summary
  - action/event/evidence counts
- the two starter scenarios:
  - `healthy_baseline`
  - `weak_d`
- the use of a visible summary response over one run rather than hidden background
  state

## Re-Author With Repo Alignment

- re-author the live surface under:
  - `apps/web/src/app/odeu-sim/`
- consume the released `POST /odeu-sim/run` API only
- use `apps/web/src/app/lib/api-base.ts` or one route-local helper layered over it
- keep the web layer subordinate to released `V51-B` request/response law
- keep the initial interaction law idle-first with defaults prefilled and user-triggered
  run only
- render the released summary payload only:
  - meta/config snapshot
  - full config snapshot payload
  - full metric payload
  - exact three-key lane summary
  - sparse observed-only action counts
  - event/evidence/sanction counts
- carry released `response_hash` through the bounded view model
- add route smoke coverage and one minimal interaction test in repo-native web tests
- add one enforceable no-kernel-import check for `apps/web/src/app/odeu-sim/`

## Defer To Later Slice

- prototype-style reset/step/start/pause controls
- parameter override sliders and richer control panels
- network graph visualization
- event log, report list, and evidence list panels
- persistent browser state or replay sessions
- broader product routing or richer simulation workbench posture

## Do Not Import

- `static/index.html` wholesale into `apps/web`
- `static/app.js` wholesale into `apps/web`
- `static/style.css` wholesale into `apps/web`
- the prototype’s mutable control surface as if it were released doctrine
- any direct browser-side simulation object or direct kernel import into live web code
