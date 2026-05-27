## Section 1: Current shipped capability map

The repo already has both halves of the problem, but not the composition.

One half is the live resident harness that already exists in `packages/urm_runtime/src/urm_runtime/copilot.py`, `apps/api/src/adeu_api/urm_routes.py`, and `apps/web/src/app/copilot/page.tsx`. That path is real: it has sessions, event streams, approvals, and a session-level `writes_allowed` mode. Its live authority, though, is still coarse. It is a harness capability surface, not the `V56`/`V57` resident-action law.

The other half is the shipped `agentic_de` governance/effect stack in `packages/adeu_agentic_de`. As shipped, `V56` is real and closed as an artifact family:

* `models.py` defines the packet, morph IR, interaction contract, action proposal, checkpoint, taxonomy, runtime state, ticket, conformance, harvest, calibration, and migration surfaces.
* `checker.py` can actually build the `V56-A` checkpoint/diagnostics/conformance chain and the `V56-B` runtime-state/ticket chain.
* But `V56-A` is structurally dry-run only: the checkpoint stays `dry_run_only=True`, `action_ticket_issuable=False`, `live_effect_authorized=False`.
* `V56-B` can issue an `agentic_de_action_ticket@1`, and the shipped reference ticket is exact-class `local_write` with `ticket_duration_mode = "single_step_local"`.
* Even then, the shipped `V56-B` conformance still records `executed_or_observed_effect = "no_live_effect"` and `live_effect_present = false`.
* `V56-C` is advisory-only by construction. Its harvest/calibration/migration outputs explicitly do not change live behavior by default.

`V57` is also real and closed, but only over one bounded exemplar:

* `run_agentic_de_local_effect_v57a()` is the first actual file mutation path in this family.
* The mutation is hard-bounded to `artifacts/agentic_de/v57/local_effect/`.
* The shipped reference exemplar is centered on `runtime/reference_patch_candidate.diff`.
* The helper supports only the narrow `local_write` subset `create_new` or `append_only`, and the shipped observed/restored lineage is centered on `create_new`.
* `V57-B` is not general rollback. It is one lineage-bound compensating remove of the observed `create_new` artifact.
* `V57-C` is explicitly advisory, candidate-only, path-level only, and non-generalizing.

So the repo can do this today: it can generate the governance artifacts, issue a bounded local ticket, and separately run one observed/restored sandbox-local exemplar with typed evidence.

What it cannot do today is more important: it cannot run one real resident turn through that stack as the governing live path. The `apps/api/scripts/*v56*` and `*v57*` seams are still thin manual runners over committed fixtures and evidence paths. There is no shipped harness-owned turn state machine that says: this live session admitted this packet, externalized this proposal, resolved this checkpoint, issued this exact ticket, invoked this exact observed effect, and closed the turn on that basis alone.

A subtle repo-specific sign of that gap is in `local_effect.py`: the helper clears and recreates the sandbox runtime tree on each call. That proves a bounded effect primitive. It does not yet prove a persistent resident workspace path.

## Section 2: Actual missing layer

The missing layer is not “more formalization” and not “more action classes.”

It is a lawful live-harness composition layer.

More precisely: the repo lacks a family that composes the already shipped outer live harness capability surfaces with the already shipped inner `V56`/`V57` resident-action surfaces, without collapsing them into one coarse write permission.

Today there is a real live harness path, but its live authority is session-level and coarse: `writes_allowed`, approval tokens, and capability-policy actions in `urm_runtime`. Separately, there is a real `V56`/`V57` artifact stack, but it is still package-first and script-first. The bridge between them is manual.

That is why the next missing capability is not “another exemplar.” It is:

* an admitted live-turn history surface,
* an artifact-authoritative turn state machine,
* an explicit ticket-to-effect handoff,
* and a reintegration law back into the live turn result.

This is exactly where the support doctrine matters. The repo already has the right conceptual warnings:

* closure must be based on admitted packet history, not hidden bridge state;
* no compensatory scalar is allowed to become the primary closure basis;
* the classifier is adjudicative only;
* imported lineage may inform but may not self-authenticate into native witness;
* membrane coherence is not enough unless the result is lawfully reintegrable into full execution.

In repo terms, that means the current committed fixtures, lane-drift records, and closeout evidence are baseline and drift-guard material. They are not the native witness for a current live turn. A current live turn needs its own current packet, current proposal, current checkpoint/ticket, and current pre/post observed state. Without that distinction, the harness would start laundering prior committed artifacts into live entitlement.

## Section 3: Recommended next family and why

Yes: the highest-leverage next family should be a **bounded live harness-integration family over the shipped `V56`/`V57` surfaces**.

Not more breadth. Not a broader local-effect family. Not dispatch. Not execute. Not a generic policy rewrite.

### What the next family should be

I would treat it as a **new family name over the existing `agentic_de_*` lineage**, not as “more `V56`” or “more `V57`.”

That is the right split because:

* `V56` already owns proposal/checkpoint/ticket law.
* `V57` already owns observed/restored local-effect evidence law.
* the missing role is different: live harness enactment plus reintegration.

So the lineage should stay `agentic_de_*`, and primary package ownership should remain near `packages/adeu_agentic_de`, but the family role should be new and explicit.

### What it should own

Narrowly, it should own only four things.

First, **live-turn admission**: snapshot the relevant live harness facts into an explicit admitted turn record. In the current repo, that means at least the session identity, active mode facts that matter, repo root / `cwd`, designated sandbox root, and the exact selected live path.

Second, **the harness transition machine**: the explicit states and transitions from packet admission to proposal externalization to checkpoint/ticket resolution to observed effect to turn closeout.

Third, **the ticket-to-effect handoff**: the exact law by which a shipped `V56-B` ticket can invoke the shipped `V57-A` local-write exemplar in a real live session, with no extra authority appearing in the harness.

Fourth, **reintegration**: how the observed result re-enters the six-lane turn report without observation minting broader intended truth, and without the harness silently relying on hidden memory or ambient session state.

### What it should explicitly not own

It should not own:

* new checkpoint or ticket semantics,
* new `local_write` semantics,
* class widening,
* `local_reversible_execute`,
* stronger execute,
* delegated or external dispatch,
* delegated worker execution already owned by `V48`,
* constitutional family linting already owned by `V55`,
* product/UI rollout as an authority source,
* hidden-cognition proxies,
* or any use of `V56-C` / `V57-C` advisory outputs as live entitlements.

### Why this is the highest-leverage move

Because the repo’s actual gap is no longer representational. It is compositional.

The strongest evidence of that is that the repo already has:

* a real live copilot harness with coarse mode/approval surfaces, and
* a real bounded resident-action governance/effect stack with one observed/restored exemplar.

What is missing is the lawful bridge between them.

That bridge is also exactly where the constitutional risk lives. If the integration is done carelessly, the harness will become the hidden sovereign:

* `writes_allowed` will get read as “local_write authorized,”
* session approval will get read as “ticket equivalent,”
* prior hardening/calibration records will get read as current-turn permission,
* and one sandbox exemplar will get laundered into general repo mutation authority.

A bounded harness-integration family solves the actual next problem while keeping the authority wall visible.

### Exact interface to other families and docs

`V55`: stays where it is. It should lint the new family’s surfaces and release posture, but it is not a live action gate.

`V56`: remains the sole owner of packet/proposal/checkpoint/ticket law.

`V57`: remains the sole owner of observed/restored local-effect evidence and path-level hardening advice.

`V48`: stays entirely out of scope. No dispatch handoff belongs here.

The practical harness flow and six-lane loop docs should be used as **shaping doctrine**, not as runtime authority. What should be imported from them is the state-machine discipline and lane separation, not the specific prose workflow.

### Pairwise default vs higher-arity reserve

For the first harness family, pairwise remains the right default.

The target action is still one single-step local ticketed `local_write/create_new` exemplar under a designated sandbox root. That can remain pairwise if the family externalizes the only ambient live facts that matter:

* live session capability snapshot,
* repo root,
* designated sandbox root,
* exact ticket,
* exact target path,
* explicit pre/post state.

Higher-arity should stay reserved. It becomes necessary only if identical pairwise profiles can still yield different operational outcomes for the target act. The current create-new sandbox exemplar does not force that conclusion. Dispatch and richer execute paths probably will. This one does not.

## Section 4: Alternative paths rejected and why

Breadth widening should be deferred across all three items you named.

### Second local-write exemplar: defer

A second exemplar does not solve the real gap. It would just add another isolated observed path before the repo has proved that the live harness can carry even the first one without hidden sovereignty.

It would also encourage semantic laundering. The repo already knows one thing lawfully: one observed/restored `create_new` exemplar in one designated sandbox root. A second exemplar too early would tempt the reading “the harness now owns local_write generally.” It does not.

### `local_reversible_execute`: defer harder

The repo has already told you not to do this yet. `V56-C` explicitly keeps `local_reversible_execute` as selected-but-unexercised and not selected for escalation.

Conceptually this is also the wrong next move. Execute semantics are much more sensitive to masked interior degrees of freedom than the current create-new file exemplar. Reintegration is harder, native witness is trickier, and pairwise adequacy is less obvious.

### Dispatch integration: strongly defer

Dispatch crosses the family wall into `V48`.

It is also the place where higher-arity pressure becomes much more plausible: parent session state, handoff envelope, worker execution, reconciliation, and observed effect all become jointly relevant. That is exactly the opposite of the smallest lawful next family.

### Generic live-harness write-mode reuse: reject

The repo already has coarse live harness authority in URM copilot. Reusing that as the carrier for this family would be a mistake.

Especially: do not alias this family onto the current broad `writes_allowed` + approval posture or onto broader actions like `adeu.apply_patch` in `urm.capability.lattice.v1.json`. That would silently widen from one sandbox-local create-new exemplar to a different and broader mutation surface.

## Section 5: Proposed starter slice

The best first starter slice is:

**one real URM copilot turn, one exact `V56-B` local-write ticket, one exact `V57-A` observed `create_new` effect, no auto-restore, no class widening.**

Concretely, the starter slice should do this.

1. Start from the existing live copilot session path, not a new ad hoc harness. But before any effectful step, snapshot the relevant live harness facts into an admitted turn record. The key point is that outer session state must stop being ambient.

2. Externalize the resident action through the shipped `V56` chain. The harness must not let the model “just do the write.” It must first produce the packet/proposal/checkpoint/ticket lineage.

3. Treat any outer harness write mode as necessary at most, never sufficient. In other words: outer live mode is an operability precondition, not the entitlement. The entitlement is still the exact `V56-B` ticket.

4. Freeze the starter effect to the exact shipped exemplar:

   * exact action class: `local_write`
   * exact write kind: `create_new`
   * exact designated root: `artifacts/agentic_de/v57/local_effect/`
   * exact starter target centered on the shipped `runtime/reference_patch_candidate.diff` path
   * exact scope posture: single-step local only

5. Preserve the current fresh-sandbox semantics from `local_effect.py` rather than weakening them. The helper’s runtime-tree reset should be treated as an explicit precondition of the starter live path, not as hidden setup. That keeps reintegration tractable.

6. Invoke only `V57-A` in the starter slice. Do **not** auto-call `V57-B` restoration. A compensating restore is another live act and should remain an explicit later state, not hidden cleanup.

7. Close the turn with a reintegration report that keeps the six-lane discipline intact:

   * observed effect is native witness,
   * interpretation of what that effect means remains separate,
   * advisory registers remain advisory,
   * and any blocked or residual posture stays explicit.

A likely narrow path ladder after that is:

* **A:** live harness bind for the shipped `V56-B -> V57-A` create-new path,
* **B:** explicit restoration as a separate harness state using shipped `V57-B`,
* **C:** replay/drift hardening over the same exact path, with `V57-C` still advisory only.

## Section 6: Key constraints / non-goals

This family needs a harder anti-drift wall than the positive scope statement.

The critical constraints are:

* **`writes_allowed` is not a `V56` ticket.** Outer harness capability must never collapse into inner action entitlement.
* **`V56-C` and `V57-C` are not live permission.** Their advisory outputs may inform, but may not authorize.
* **One create-new exemplar is not class-level `local_write`.** No generalization from the observed/restored path.
* **Transcript and event stream are not native witness.** They are coordination and observability surfaces. The authoritative effect witness is the `V57` pre/post observation chain.
* **Committed fixtures and prior closeout evidence are not current-turn witness.** They are release baselines and drift guards.
* **No scalar hardening/confidence score may close the action.** Closure stays typed, blocking-first, and artifact-based.
* **No hidden bridge state.** Identical admitted turn history under identical declared policy must produce identical transition eligibility.
* **No automatic cleanup or retry behavior that is not externalized.** Hidden compensators are hidden sovereignty.
* **No reuse of broad repo-mutation surfaces.** This family is not `adeu.apply_patch`, not repo-authority write mode, not product rollout.
* **No move into `V48`.** Dispatch, worker execution, and delegated reconciliation stay out.

The main constitutional risks are exactly the ones you named:

* hidden sovereignty in the harness,
* silent authority widening,
* advisory surfaces used as live entitlements,
* laundering broader authority from one exemplar path,
* and mistaking pairwise coherence for action adequacy when reintegration has not actually been shown.

## Section 7: Open conceptual questions that still need maintainer judgment

1. **Outer harness authority shape:** should the starter path reuse the existing URM `writes_allowed` / approval posture as an outer precondition, or should it introduce a narrower dedicated live capability so the session never enters a broader write mode at all?

2. **Exact starter freeze:** should the first live slice freeze only the exact target path, or also freeze the payload shape to the shipped patch-candidate exemplar? My judgment leans toward freezing both as much as possible.

3. **Fresh sandbox law:** should the first live harness path preserve the current “fresh sandbox per turn” semantics from `local_effect.py`, or is there already appetite for explicit persistent sandbox continuity? I would keep freshness for the first slice.

4. **Restoration placement:** should `V57-B` integration be a separate explicit cleanup turn/state, or a later same-turn optional phase? I would keep it separate at first to avoid hidden compensators.

5. **Minimal new surface count:** does the family need only a turn-admission/state surface plus a reintegration-closeout surface, or is one additional explicit handoff surface needed between ticket issuance and observed effect?

6. **Family-contract formality:** is this the right family to introduce a compact first-class family contract artifact for harness integration, or should that remain implicit in architecture + fixtures for one more bounded turn?

My bottom-line judgment is firm: the smallest lawful next family is a **post-`V57` live harness-integration/reintegration family over the shipped `V56`/`V57` surfaces**, wired into the existing live copilot path as a narrower inner action lane, with breadth widening deferred until that one path is operationally real and constitutionally stable.
