## 1. Executive judgment

I inspected the shipped V55–V59 family code, tests, and harness artifacts; `packages/urm_runtime/`; `packages/adeu_agentic_de/`; `packages/adeu_constitutional_coherence/`; `packages/adeu_odeu_sim/`; `apps/api/scripts/`; `apps/api/src/adeu_api/urm_routes.py`; `apps/web/src/app/copilot/page.tsx`; `apps/gpt54-codex-workbench/`; and the architecture/support docs you named.

The repo is already past the “planning prose only” stage. It has:

* a real resident Codex runtime and control plane,
* a real governed live-act ladder through V56/V57/V58/V59,
* real evidence artifacts through `artifacts/agent_harness/v163`,
* real user surfaces in the web copilot and the GPT-5.4 desktop workbench.

The repo is **not** yet a semantically governed autonomous loop after seed-intent handoff. The key missing layers are **not** more local-effect hardening and **not** immediate worker/dispatch widening. The missing layers are:

1. a **continuation / residual-intent kernel**, and
2. a **governed communication-surface architecture**.

That is the real architectural gap.

The current repo already has a long-lived Codex session path, but it does **not** yet have a long-lived governed task identity. It already has persistence, but not lawful continuation. It already has chat/control surfaces, but not a communication membrane that prevents those surfaces from silently minting authority.

So the clean descent from the target end state is:

* **V60**: continuation / residual-intent kernel,
* **V61**: governed communication surfaces + resident bridge office,
* **V62**: custom connector admission / external assistant bridge,
* **V63**: remote ODEU-governed operator UX / phone control plane,
* **later**: repo-bound writable-surface authority widening,
* **later still**: V48-based delegated export / worker integration.

A central design rule follows from the current repo state: **do not widen V56 tickets into standing multi-step authority**. The existing `ticket_duration_mode` is deliberately `single_step_local`. The future autonomous loop should be built by chaining fresh, current-turn, single-step governed acts under a new continuation kernel, not by minting longer-lived tickets.

---

## 2. Current implemented architecture map

### Shipped family stack that is materially real

**V55 — constitutional coherence**
In `packages/adeu_constitutional_coherence/`, V55 is real and tested. It checks a bounded admitted seed-artifact set and produces coherence / descendant-trial / governance-migration outputs. It matters as constitutional lint and migration pressure, but it is not the live runtime authority owner.

**V56 — resident-agent interaction governance**
In `packages/adeu_agentic_de/models.py` and `checker.py`, V56 is a real packet/proposal/checkpoint/ticket ladder. The key live objects already exist:

* `AgenticDeActionProposal`
* `AgenticDeMembraneCheckpoint`
* `AgenticDeActionTicket`

This is not vague planning. The models explicitly encode non-entitling proposals, dry-run-only checkpoints, and live-effect-authorizing tickets. The selected live ticket classes are still narrow, and the ticket duration is explicitly `single_step_local`.

**V57 — local effect observation / restoration / hardening**
In `packages/adeu_agentic_de/local_effect.py`, V57 is real over one designated bounded local surface. It already owns observed effect, compensating restoration, and advisory hardening over an exact path under an exact sandbox root.

**V58 — live harness integration**
In `packages/adeu_agentic_de/models.py` and `checker.py`, V58 is real. It binds one live `CopilotTurnSnapshot` into:

* live-turn admission,
* explicit handoff from governance lineage to selected effect,
* explicit reintegration.

The important point is that V58 already encodes current-turn witness discipline. The reintegration reports carry field-origin and dependence tags, and the family explicitly refuses transcript/event-stream self-promotion into native witness.

**V59 — persistent workspace continuity**
In `packages/adeu_agentic_de/workspace_continuity.py`, V59 is also real. The repo is already beyond the V59-A planning state. The code, tests, and harness artifacts show that **V59-A, V59-B, and V59-C are shipped**. The continuity root, occupancy classification, governed lineage marker, restoration handoff, restoration reintegration, and advisory hardening ladder are present.

That matters because `docs/DRAFT_NEXT_ARC_OPTIONS_v42.md` is no longer a trustworthy current-state summary. It is historically useful, but the code and `artifacts/agent_harness/v161` through `v163` are ahead of it.

### Other already-built infra that materially matters

**URM runtime is real control-plane infrastructure, not placeholder code.**
`packages/urm_runtime/` already provides:

* long-lived Codex-backed copilot sessions,
* approvals and write-mode toggling,
* role registry and child-role spawning,
* visibility / topology / orchestration state surfaces,
* connector snapshotting and exposure mapping,
* persistent SQLite-backed runtime storage,
* app-server integration.

The important files here are not decorative:

* `copilot.py`
* `app_server.py`
* `models.py`
* `roles.py`
* `orchestration_state.py`
* `worker_visibility.py`
* `connector_exposure_mapping.py`
* `storage.py`

This is already a real runtime substrate for a resident agent.

**API routes are already present for those surfaces.**
`apps/api/src/adeu_api/urm_routes.py` exposes real routes for copilot sessions, approvals, workers, policy profiles, tools, visibility/topology, and connector snapshots. The control plane exists.

**The current user surfaces are real.**
Two matter most:

* `apps/web/src/app/copilot/page.tsx`
* `apps/gpt54-codex-workbench/`

The desktop GPT-5.4 workbench is especially important. It already embodies the doctrine that transcript is primary, evidence must stay reachable, write posture must stay explicit, and review handoffs stay advisory.

**V48 is real, but later-stage relevant.**
The worker / dispatch / bridge family is present through `packages/adeu_agent_harness/` and `packages/adeu_semantic_forms/src/adeu_semantic_forms/bridge_v48.py`. It is useful for later delegated export and worker-boundary law. It is not the next missing layer for the target loop.

**V51 is real, but currently shaping rather than governing live runtime.**
`packages/adeu_odeu_sim/` provides the ODEU simulation kernel, lane-crossing contracts, world state, actions, regimes, and API/browser ladder. It matters as a semantic support layer, not as the current runtime authority owner.

**`apps/api/scripts/` is important evidence infrastructure.**
These scripts are not the missing autonomy kernel, but they matter because they operationalize the shipped family slices and keep them replayable. The `run_agentic_de_*` and `evaluate_agentic_de_*` scripts prove that the V56–V59 ladders are executable and evidence-bearing, not merely declared.

### What the repo already contributes toward the target

* The repo already knows how to admit one live turn into a governed act.
* The repo already knows how to bind that act to a bounded local effect.
* The repo already knows how to reintegrate results with origin discipline.
* The repo already knows how to carry governed continuity over a persistent exact region.
* The repo already knows how to host a long-lived Codex runtime and show it to a human.

What it does **not** yet know is how to convert a human seed intent into a governed task identity that can lawfully continue across turns.

---

## 3. Target end-state architecture

The target architecture should be layered like this.

### Layer A — constitutional / coherence layer

This remains V55 plus policy/profile/lock discipline. It answers whether the loop’s governing surfaces remain constitutionally coherent. It is not the live next-act owner.

### Layer B — act-governance layer

This remains V56. It owns packet, proposal, checkpoint, ticket, and conformance law for any externally effective act. It should stay the sole owner of that ladder.

### Layer C — effect / reintegration / continuity layer

This remains V57/V58/V59.

* V57 owns bounded observed/restored local effect.
* V58 owns live-turn admission/handoff/reintegration.
* V59 owns persistent workspace continuity and continuity-safe restoration over the admitted region.

This layer should keep current-turn witness explicit and keep prior state contextual rather than sovereign.

### Layer D — continuation / residual-intent layer

This is missing. It should become the kernel that converts seed intent and reintegration results into lawful next-step continuation. This layer does not execute effects directly. It decides whether to:

* continue,
* descend into a governed act,
* communicate,
* await authority,
* stop,
* block,
* escalate.

### Layer E — communication-governance layer

This is also missing. It should govern all human-facing and assistant-facing communication surfaces as typed, provenance-bearing packets. This layer must ensure:

* conversation is not permission,
* connector traffic is not witness,
* UI transcripts do not silently become authority,
* Codex can speak inside the loop without becoming a hidden sovereign.

### Layer F — surface adapter layer

This should split into two later families, because the trust models differ:

* **connector bridge** for the future ChatGPT/custom-connector path,
* **remote operator UX** for the phone-accessible ADEU-owned surface.

Both consume the same communication law; neither owns that law.

### Layer G — later repo-widening / delegation layer

Only after the above exists should the repo widen:

* first into broader repo-bound writable-surface authority,
* later into delegated worker/export law via V48.

### Human / Codex / connector / remote-UX relationship

The clean relationship is:

* the **human** speaks through governed ingress surfaces,
* the **resident Codex session** lives inside the loop as the operational agent,
* the **same Codex session may also act as the bridge office**, but only through explicit office binding,
* the **connector** and **remote phone UX** are transport/control surfaces that feed the communication layer,
* **URM** remains the runtime control-plane owner for sessions, approvals, capabilities, topology, and persistence.

That means Codex can be the primary communication bridge without becoming the hidden constitutional office or uncontrolled permission source.

---

## 4. Gap analysis

### What is materially real now

Materially real:

* V55–V59 code, tests, and harness artifacts,
* URM resident Codex sessions,
* approvals and write toggling,
* connector snapshot/exposure infra,
* worker visibility/topology law,
* web copilot,
* GPT-5.4 desktop workbench.

### What is exemplar-grade but real

Exemplar-grade, but real:

* the live act path is still extremely narrow,
* the continuity-bound writable surface is still basically one exact lineage around `runtime/reference_patch_candidate.diff`,
* the current effect family proves the governance ladder, not broad repo work.

### What is still advisory only

Advisory only:

* V55 outputs,
* V56C/V57C/V58C/V59C hardening/calibration/migration outputs,
* workbench review outputs,
* most support docs.

### What is absent

Absent:

* seed-intent charterization,
* residual-intent carrier,
* semantic continuation identity,
* next-act decision kernel,
* typed communication-governance surfaces,
* explicit Codex office split between operational actor and bridge,
* typed connector message law,
* remote ODEU-governed phone/operator surface,
* broader repo-bound writable-surface authority,
* delegated export law under current continuity semantics.

### Distance from three important thresholds

**1. Governed exemplar loop**
The repo is fairly close here, and in one sense already has it. It can perform one governed live turn over one exact selected local lineage with reintegration and continuity restoration. But it still assumes the lineage is already assembled. It is not yet seed-intent-native.

**2. Useful repo-bound micro-worker**
The repo is mid-distance here. Runtime, policy, workers, and user surfaces exist, but the writable surface is still exemplar-bound and there is no lawful continuation kernel.

**3. Closed autonomous reliable loop**
The repo is still meaningfully short of this. The blocker is not missing runtime plumbing. The blocker is the absence of a kernel that owns:

* task charter,
* residualized continuation,
* continue/stop/block/escalate decisions,
* governed communication turns.

A concrete sign of that gap is in the current runtime messaging surface: `CopilotSessionSendRequest` accepts a generic `message: dict[str, Any]`, and the current web copilot sends a generic `copilot.user_message` payload. That is transport-shaped, not semantically governed task ingress. Likewise, connector support today is snapshot/exposure infrastructure, not a governed conversation bridge.

---

## 5. Recommended remaining family roadmap

I would split the remaining work into one core semantic-closure pair, then two later
branches that both depend on that core.

### V60 — continuation / residual-intent kernel

**Why it must be a separate family**
V59 owns continuity of a selected work surface. It does not own semantic task
continuation. URM owns sessions and approvals. It does not own seed-intent meaning or
lawful next-step selection. The repo needs a family whose sole job is to turn “what
the task still is” into “what the loop may do next.”

**What it owns**

* bounded task-law compilation,
* seed-intent to charter compilation,
* residual-intent derivation,
* continuation identity,
* continue / descend / block / stop / escalate decisions,
* lawful chaining of repeated single-step local acts.

**What it must not own**

* raw chat-native ingress semantics,
* connector transport,
* remote UX,
* broader repo-write widening,
* V48 worker/export semantics,
* a new act-ticket ontology.

**What it consumes**

* V56 proposals/checkpoints/tickets,
* V58 reintegration,
* V59 continuity status,
* URM approvals/capabilities/session state,
* six-lane and membrane support doctrine,
* `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`,
* `docs/DRAFT_WCPGC_CORE_AND_STRICT_V0_v0.md`.

**First slice**

One typed starter seed-intent record over the already shipped V59 exact
continuity-bound surface. Keep `ticket_duration_mode = single_step_local`. The new
loop should continue by issuing a fresh current-turn act each time, not by stretching
ticket duration.

The important boundary is:

* the starter seed intent is a typed artifact / bounded ingress record,
* not raw transcript semantics,
* not connector traffic,
* not generic chat memory.

`TaskResidual` should stay explicit here as a derived continuation artifact produced
from reintegration and declared policy. It is not human-authored task law and it does
not mint standing authority.

**Explicit deferrals**

* multi-worker autonomy,
* broader repo writes,
* multi-target continuity,
* connector-originated control,
* complex planning trees.

---

### V61 — communication-surface governance + resident bridge office

**Why it must be separate**
Communication is now first-class. It is not execution, not continuity, and not just UI. The repo already has live chat-like surfaces, so this family must retro-govern existing ones before new ones arrive.

**What it owns**

* typed communication ingress and egress packets,
* provenance and speaker typing,
* surface-class typing,
* office binding between resident Codex actor and bridge Codex actor,
* message interpretation and rewitness gates,
* rules for when the loop owes a status message, question, escalation, or approval request.

**What it must not own**

* connector-specific transport plumbing,
* phone UX rendering,
* act-ticket law,
* repo-write authority.

**What it consumes**

* V60 continuation decisions,
* V58 origin discipline,
* URM session/event surfaces,
* vertical-alignment office doctrine,
* current desktop/web surface lessons.

**First slice**

Retrofit the current `/copilot` UI and `apps/gpt54-codex-workbench` so they no longer behave as semantically open transcript pipes. They should emit and consume typed communication packets while remaining non-authority-minting.

**Explicit deferrals**

* rich media/attachment semantics,
* multi-party thread arbitration,
* broad social/protocol semantics.

---

### V62 — connector admission / external assistant bridge

**Why it must be separate**
A future ChatGPT/custom connector is not just another chat box. It is a multi-principal surface containing at least:

* the human,
* the ADEU resident bridge,
* the external assistant/runtime around the connector.

That requires its own trust model.

**What it owns**

* connector admission records,
* connector message packets,
* freshness/capability binding to connector snapshots,
* separation of `human_via_connector` from `external_assistant_via_connector`,
* fail-closed defaults for connector-originated authority.

**What it must not own**

* continuation law,
* office law,
* repo execution authority,
* phone UX.

**What it consumes**

* the existing connector snapshot and exposure machinery in `urm_runtime`,
* V61 communication packets,
* URM capability/profile state.

**First slice**

Read/communicate-only connector bridge. Allow Codex to communicate outward and receive human connector traffic inward as typed packets. Treat external assistant traffic as advisory only. No connector-originated execution authority.

**Explicit deferrals**

* direct execution from connector traffic,
* connector-native witness promotion,
* autonomous connector-to-connector coordination.

---

### V63 — remote ODEU-governed operator UX / phone control plane

**Why it must be separate**
The ADEU-owned phone-accessible surface is not the same thing as the external connector. It is an operator/control plane, not a foreign assistant bridge.

**What it owns**

* remote operator session law,
* phone-safe task/ask/evidence view models,
* explicit operator commands such as pause, continue, approve, answer, inspect, escalate,
* remote notification / acknowledgement surfaces.

**What it must not own**

* continuation semantics,
* connector semantics,
* act-ticket law,
* broader repo execution.

**What it consumes**

* V60 loop state,
* V61 communication packets,
* URM approval/session state,
* current workbench doctrine.

**First slice**

A read-mostly remote dashboard with:

* status,
* asks/blockers,
* evidence reachability,
* message ingress,
* explicit approval / continue / pause / escalate controls.

No direct repo mutation UI.

**Explicit deferrals**

* free-form command execution,
* direct file editing,
* broad shell/terminal control from phone.

---

### V64 — repo-bound writable-surface authority

This is the first widening family after the target loop exists.

**Why separate**
The repo currently proves governance over one exact exemplar write lineage. Broadening writable authority is a different problem from continuation or communication.

**What it owns**

* selected subtree/file-set writable-surface descriptors,
* bounded repo write leases,
* compatibility with V59 continuity regions beyond the single exact file.

**What it must not own**

* communication semantics,
* connector semantics,
* continuation semantics,
* worker export.

**First slice**

One selected subtree or file-set lease, still fail-closed and explicit.

---

### V65 — delegated export / worker reconciliation under V48

This is later than V64.

**Why separate**
Delegated/exported work is not the same as local repo-surface authority. V48 already exists and should be consumed, not reinvented.

**What it owns**

* scoped export artifacts,
* worker-boundary reconciliation back into the loop,
* V48 handoff semantics under the V60/V61 loop state.

**What it must not own**

* seed-intent or communication law,
* phone UX,
* connector trust law.

**First slice**

One delegated subtask export under explicit scoped export and re-entry, with no direct user boundary for workers.

---

## 6. Required module / surface map

These are the concrete missing modules and artifacts.

### Continuation core

**`TaskCharterPacket`**
Normalizes the seed intent into a governed task assignment: scope, completion tests, stop conditions, import requirements, communication obligations. This is the task law for the loop.

**`TaskResidualPacket`**
Carries what remains live after each reintegration: current frontier, pending obligations, blockers by fact ref, defeat records, open approvals, owed communications. It is a derived artifact, not standing permission.

**`LoopStateLedger`**
Binds together charter ref, residual ref, resident session ref, last reintegration ref, continuity-region ref, open approval refs, and communication thread refs. This is the canonical loop state, not the transcript.

**`ContinuationPrefixIdentity`**
Defines continuation by something like `(task_id, charter_ref, prefix_hash, last_reintegration_ref)`. This prevents “successful prior turns” from becoming ambient permission.

**`ContinuationDecisionKernel`**
The kernel that evaluates loop state and emits a bounded next-step verdict.

**`ContinuationDecisionRecord`**
The explicit output of that kernel. It should be able to say things like:

* descend into governed act,
* emit bridge message,
* await human response,
* await approval,
* stop complete,
* stop blocked,
* escalate.

### Communication governance

**`SurfaceAuthorityDescriptor`**
Classifies a surface as communication, observability, advisory, authority-request, execution, or witness-candidate. This prevents surface collapse.

**`CommunicationIngressPacket`**
Typed inbound message with source surface, principal class, speaker class, provenance, and intended interpretation posture.

**`CommunicationEgressPacket`**
Typed outbound message from the bridge office, with target surface and posture.

**`IngressInterpretationRecord`**
Explicitly interprets an inbound message as one of a small set of loop-relevant kinds, such as:

* seed intent,
* clarification response,
* authority response,
* status request,
* charter-amendment candidate,
* advisory only.

This is how communication can affect continuation without becoming ambient authority.

**`ResidentBridgeOfficeBinding`**
Binds the resident Codex runtime to two explicit offices:

* operational resident agent,
* communication bridge.

The same model session may occupy both, but every emission must be office-tagged.

**`MessagePromotionGate` / `RewitnessRecord`**
The only lawful path by which communication content can become governance-relevant witness. Default posture: messages stay non-authoritative.

### Connector and remote surfaces

**`ConnectorAdmissionRecord`**
Binds a connector to session, provider, capability snapshot, freshness bounds, and allowed exposure posture.

**`ConnectorMessagePacket`**
Typed message entering or leaving through the custom connector. Must distinguish at minimum:

* human-via-connector,
* external-assistant-via-connector,
* connector-system event,
* resident-bridge egress.

**`RemoteOperatorSessionRecord`**
Governed session for the phone-accessible ADEU surface.

**`RemoteOperatorCommandPacket`**
Explicit bounded remote controls such as pause, continue, approve, answer, escalate.

### Later widening

**`RepoWorkSurfaceAuthorityLease`**
The future object that defines broader repo writable-surface authority without turning continuity into standing permission.

**`ScopedExportArtifact`**
The future object that carries work out to a delegated worker or back in from one under V48 law.

---

## 7. Support-doc to runtime map

### Already embodied in runtime or code families

**`ARCHITECTURE_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_FAMILY_v0.md`**
Substantially embodied in V56.

**`ARCHITECTURE_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_FAMILY_v0.md`**
Substantially embodied in V57.

**`ARCHITECTURE_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_FAMILY_v0.md`**
Substantially embodied in V58.

**`ARCHITECTURE_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_FAMILY_v0.md`**
Mostly embodied in V59, though the doc lags the fact that V59-B and V59-C are already shipped.

**`docs/support/endogenous grounding. md`**
Largely promoted already. Its practical warning about the harness becoming a hidden sovereign is one of the things V58 now directly hardens against.

**`docs/support/endogenous cross-lane alignment ... 3rd pass.md`**
Partly promoted already through V58/V59 field-origin tags, dependence tags, root-origin summaries, and reintegration witness discipline.

**`docs/support/DRAFT_ADEU_CODEX_DESKTOP_WORKBENCH_v0.md`**
Partly embodied in `apps/gpt54-codex-workbench/`. The workbench is real, but its doctrine is still surface doctrine, not yet runtime communication law.

### Maps directly to the next missing families

**`docs/support/ODEU_MEMBRANE_ARCHITECTURE.md`**
This should drive V60. The missing runtime equivalents are exactly the membrane outputs that are not yet first-class in code: residual register, rejection/block log, escalation queue, structured reproposal demand.

**`docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`**
This should also drive V60. It is the cleanest support-level bridge for why the
continuation kernel must become a first-class runtime/governance surface rather than
remaining prompt prose or transcript habit.

**`docs/DRAFT_WCPGC_CORE_AND_STRICT_V0_v0.md`**
This should also drive V60. Its strongest immediate contribution is the split between
`TaskCharter` and `TaskResidual`, plus continuity by charter/prefix identity rather
than prose memory, and the strict replayable packet law needed for starter
continuation surfaces.

**`docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`**
This should shape V60 decision records and V61 communication closeout discipline.

**`docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED.md`**
This is the main support-layer bridge for V61/V62/V63. The big missing runtime move is office law: shared public access does not imply shared office; communication access does not imply authority.

**`docs/formal/asir/ASIRKernelConnector.md`**
This is a later-shaping support reference for connector/gating formalization once
V62 is selected. It should not drive `V60` directly, but it is relevant to later
connector-side adjudication and projection law.

**`docs/OPERATOR_REFERENCE_v0.md`**
This is a later-shaping support reference for `V63`. It should not drive `V60`
directly, but it is useful for later operator-surface practical constraints.

### Should remain support-only for now

**`docs/support/ODEU AS A COUPLED SEMANTIC HYPERSPACE WITH LAWFUL MORPHISMS_v2.md`**
Useful shaping doctrine, but too broad to promote wholesale. Extract only the parts needed for concrete packet transforms.

**The broader ODEU simulation stack around V51**
Keep as shaping/reference until V60–V63 need a specific runtime contract from it.

**More speculative higher-arity and social-protocol extensions**
Do not promote before the pairwise loop is closed.

### Important ordering conclusion

The support docs point to a clear dependency order:

1. promote residualized continuation,
2. then promote office-governed communication surfaces,
3. then branch from that core into:
   * connector and remote-UX transport/control families, and
   * execution-widening families such as repo-bound writable authority and delegated
     export.

That means the clean shape after `V61` is a branching dependency cone, not one rigid
serial ladder.

---

## 8. Seed-intent to autonomous-loop lifecycle

Here is the concrete target lifecycle.

### Stage 1 — seed intent arrives

The human can enter intent from:

* the existing workbench,
* the existing web copilot,
* the future custom connector,
* the future phone UX.

But it does **not** enter the loop as raw transcript truth. It first becomes a `CommunicationIngressPacket`.

### Stage 2 — ingress is interpreted

V61 produces an `IngressInterpretationRecord`. At this point the packet is classified, for example, as:

* seed intent,
* clarification response,
* authority response,
* status request,
* charter-amendment candidate,
* advisory-only message.

Only the interpreted packet can affect loop state.

### Stage 3 — charter and residual are created

For seed intent, V60 compiles:

* a `TaskCharterPacket`,
* an initial `TaskResidualPacket`,
* a `LoopStateLedger`,
* a binding to a resident URM Codex session.

This is the real handoff from human seed intent into the governed loop.

### Stage 4 — continuation kernel selects next posture

V60 evaluates:

* charter,
* residual,
* current approvals/capabilities,
* continuity-region state,
* latest reintegration,
* open blockers,
* owed communications.

It emits a `ContinuationDecisionRecord`.

### Stage 5A — if the next act is communication

V61 emits a `CommunicationEgressPacket` through the active surface. This is how Codex remains the primary bridge with the human while staying inside the governed loop.

Typical outcomes here are:

* status update,
* clarification question,
* approval request,
* escalation notice,
* completion report.

### Stage 5B — if the next act is an externally effective act

The loop descends into the already shipped ladder:

* V56 proposal/checkpoint/ticket,
* V58 live-turn admission/handoff,
* V57 or V59 selected local effect / continuity-bound restore,
* V58/V59 reintegration.

Each act is still current-turn and single-step. No prior success becomes standing authority.

### Stage 6 — reintegration updates continuation

After reintegration, V60 derives a fresh residual. This is where the loop law lives:

* some obligations are marked satisfied,
* some remain pending,
* some are blocked,
* some communications become owed,
* some escalation conditions are triggered.

### Stage 7 — loop either continues, pauses, stops, or escalates

The kernel can now decide to:

* continue to another governed act,
* await human response,
* await approval,
* stop complete,
* stop blocked,
* escalate to the human/operator.

That is what makes the loop closed. Closed here does not mean “human never re-enters.” It means continuation, stopping, blocking, and escalation all have explicit native owners.

### Stage 8 — connector and phone surfaces plug in as transport/control only

The future connector and phone app do not bypass the lifecycle. They only add alternative ingress and egress surfaces into V61.

### Stage 9 — any message-to-witness promotion is explicit

If a human or external assistant message needs to become governance-relevant evidence, that happens through a rewitness gate. It does not happen because the message “was in the conversation.”

---

## 9. Recommended sequencing

The clean sequence from the current repo state is:

### Next

Build **V60** first.

Reason: until the repo has charter/residual/continuation ownership, every other surface widening risks creating a chat-shaped pseudo-loop rather than a governed loop.

### Immediately after

Build **V61** second, and use it to retrofit the **existing** communication surfaces first:

* `apps/web/src/app/copilot/page.tsx`
* `apps/gpt54-codex-workbench/`

Reason: those surfaces already exist. Leaving them semantically open while adding new connector/phone surfaces would multiply hidden sovereign channels.

### After The Core

After `V60` / `V61`, the roadmap can branch.

**Surface branch**

Build **V62** and **V63** as sibling families on top of `V61`.

Because URM already has connector snapshot machinery, `V62` may land slightly earlier.
But `V63` should be designed from the same packet and office contract, not as a
separate product invention.

**Execution-widening branch**

Build **V64** for broader repo-bound work-surface authority and **V65** for
`V48`-based delegated export and worker reconciliation when execution reach becomes
the priority.

### What should remain deferred

Defer all of this until after V60/V61:

* broader repo write widening,
* ticket duration widening,
* connector-originated execution,
* phone-native direct mutation controls,
* higher-arity autonomous worker meshes.

### What must not be widened too early

Do not widen:

* V59 into a generic autonomy family,
* the existing transcript surfaces into de facto task law,
* connector snapshots into conversation authority,
* workspace continuity into standing permission,
* `writes_allowed` into semantic entitlement.

---

## 10. Risks and anti-patterns

The main ways to ruin this architecture are straightforward.

* **Turning V59 into “the autonomy family.”**
  V59 owns continuity of a selected work surface, not residual intent or communication governance.

* **Confusing persistence with continuation.**
  A long-lived URM session is not a governed task identity.

* **Confusing conversation with permission.**
  Raw message arrival must not modify execution authority by default.

* **Confusing connector traffic with witness.**
  Connector surfaces must remain typed and provenance-bearing, with fail-closed promotion rules.

* **Collapsing Codex’s offices.**
  The same session may act as resident agent and bridge, but those offices must be explicit and logged.

* **Letting the phone surface become a hidden sovereign UI.**
  Mobile convenience is exactly where implicit authority drift becomes tempting.

* **Widening to V48/dispatch too early.**
  That exports ambiguity into the worker plane before the local loop is lawfully closed.

* **Letting the model “just decide” continuation.**
  Hidden cognition is not a kernel. The continuation law needs explicit records and bounded verdicts.

* **Allowing advisory outputs to self-promote.**
  V55C/V56C/V57C/V58C/V59C and review outputs must stay advisory unless later explicitly promoted.

---

## 11. Final recommendation

The cleanest roadmap from the current repo state is this:

The repo already has a real governed act ladder and a real resident Codex runtime. Do **not** respond by widening V59 or by jumping to worker/dispatch autonomy. Instead, recognize that the missing architecture is now semantic, not infrastructural.

Build a **continuation / residual-intent kernel** next. Then build a **communication-surface governance family** that retrofits the existing web and desktop surfaces and makes Codex a lawful bridge rather than a sovereign chat stream. After that, split surface transport into two distinct families: **connector bridge** and **remote operator UX**. Only once that is stable should the repo widen writable repo surfaces and delegated worker export.

In one sentence: **close the semantic loop first, then govern the communication
membrane, then branch into surface transport and execution widening, then widen
execution scope only where selected.**
