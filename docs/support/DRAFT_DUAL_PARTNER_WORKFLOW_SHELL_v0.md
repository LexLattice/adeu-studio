# A. Direct verdict

The standalone shell is a **dual-partner workflow shell** for coordinating day-to-day implementation work between:

* **Codex** as the repo-coupled implementation partner.
* **ChatGPT** as the deliberation, review, reframing, and world-model partner.
* **A middle control plane** that binds projects, surfaces, threads, files, prompts, and handoff points.

It is **not** a mini ADEU Studio. It is not the main place to expose every ADEU-native orchestration primitive, custom fork knob, harness switch, constitutional control, or meta-orchestrator experiment.

The central product claim is:

> Codex and ChatGPT occupy different cognitive offices. The shell should preserve their different postures and make the handoff between them deliberate, project-bound, and low-friction.

That means the app should not try to become one unified super-chat. The asymmetry is the product.

Codex should remain familiar and implementation-oriented. ChatGPT should remain familiar and deliberation-oriented. The control plane should reduce scavenging, thread confusion, prompt repetition, file-handoff mistakes, and context drift.

---

# B. Product boundary

## 1. Standalone shell

The standalone shell should optimize for **real daily workflow**.

Its job is to answer:

> “For this project, which Codex implementation surface and which ChatGPT deliberation/review threads belong together, and how do I move artifacts between them without losing context?”

The standalone shell should own:

* Project definitions.
* Workspace attachment.
* Codex surface binding.
* Multiple ChatGPT thread bindings.
* Thread roles.
* Prompt templates.
* Watched file rules.
* Review artifact staging.
* Handoff queues.
* File preview and lightweight work tree.
* Provider configuration at a practical level.

It should not become the full ADEU lab.

## 2. `odeu` / ADEU-native experimental shell

The `odeu` track is where immature ADEU-native ideas belong first.

It should own:

* Deep Codex fork controls.
* Harness-specific controls.
* Bounded Codex experiments.
* Meta-orchestrator posture experiments.
* Constitutional runtime control.
* Experimental relay automation.
* Provider-fork internals.
* Multi-agent control schemes.
* ADEU-native instrumentation and traces.

This is the right place to test whether a custom Codex runtime can evolve into a deeper meta-orchestrator. But those controls should not dominate the standalone shell until they have proven clear workflow value.

## 3. ADEU Studio long-term open provider platform

ADEU Studio is the broader long-term platform.

It may eventually own:

* Multiple coding-agent providers.
* Multiple review-agent providers.
* Provider registry.
* Runtime capability negotiation.
* Cross-provider orchestration.
* Deep audit trails.
* Long-horizon project memory.
* Rich governance layers.
* Team/multi-user abstractions.
* Plugin ecosystems.

The standalone shell can later consume mature pieces from ADEU Studio, but it should not become ADEU Studio prematurely.

The boundary should look like this:

| Layer            | Purpose                             | Current posture                          |
| ---------------- | ----------------------------------- | ---------------------------------------- |
| Standalone shell | Daily dual-partner workflow         | Ship practical workflow improvements now |
| `odeu`           | ADEU-native experimentation         | Keep advanced/fork/harness controls here |
| ADEU Studio      | Long-term provider/control platform | Do not force into standalone v1/v2       |

---

# C. Surface doctrine

## Codex surface

The Codex surface is the **implementation companion**.

It should feel like a normal Codex-style work surface:

* Repo-coupled.
* Patch-oriented.
* Actionable.
* Implementation-focused.
* Tight feedback loop.
* Familiar chat/input posture.
* Capable of using a local fallback surface, a Codex app-server URL, a CLI-backed surface, or a future provider surface.

The standalone shell should not over-customize Codex into a meta-control dashboard. The left plane should preserve the feeling of “I am working with my coding agent.”

Appropriate Codex-side features:

* Vanilla Codex-compatible chat surface.
* Project/workspace binding.
* Optional model/reasoning controls.
* Optional provider profile.
* Optional custom fork settings in an advanced drawer.
* Future command execution hooks through the WSL backend.
* Future paste-back target for ChatGPT feedback.

Inappropriate as default standalone behavior:

* Forcing every implementation action through a novel ADEU control UX.
* Exposing deep fork internals as primary controls.
* Making Codex just one tab in a generic chat router.

## ChatGPT surface

The ChatGPT surface is the **review/world-model companion**.

It should remain the real ChatGPT conversation panel as much as practical.

Its value is different from Codex:

* Loose brainstorming.
* Reframing.
* Critique.
* Architecture review.
* Research synthesis.
* World-modeling.
* Sanity checks.
* Alternate viewpoints.

The shell should reduce ChatGPT scavenging by binding specific threads to the current project and role. It should not replace ChatGPT with a fake API-backed chat unless a future provider explicitly supports that role.

Appropriate ChatGPT-side features:

* Real embedded ChatGPT thread.
* Multiple thread bindings per project.
* Role-specific thread selection.
* Best-effort chrome reduction.
* Best-effort dark mode.
* Settings/account access surfaced from the control plane.
* Prompt/file handoff helpers.

Inappropriate as default standalone behavior:

* Pretending consumer ChatGPT has an official existing-thread automation API.
* Turning ChatGPT into a generic message endpoint.
* Flattening ChatGPT and Codex into equivalent chat tabs.

## Control plane

The control plane is the **bounded orchestration surface**.

It is not a chat.

It owns:

* Which project is active.
* Which workspace is attached.
* Which Codex surface belongs to the project.
* Which ChatGPT threads belong to the project.
* Which ChatGPT thread role is active.
* Which file/artifact is selected.
* Which prompt template applies.
* Which handoff is staged.
* Which relay action is available.

The control plane should make workflow state visible and intentional.

The middle plane should answer:

> “Where am I? Which cognitive partner am I talking to? Which thread is the right one? What artifact am I handing off? What should happen next?”

It should not answer:

> “Can I replace both Codex and ChatGPT with a third chat?”

---

# D. Feature priority table

| Feature                                                     |  Standalone shell now | `odeu` track for now | Later promotion candidate | Rationale                                                |
| ----------------------------------------------------------- | --------------------: | -------------------: | ------------------------: | -------------------------------------------------------- |
| Project-bound ChatGPT review thread                         |                   Yes |                   No |              Already core | Highest current workflow value                           |
| Multiple ChatGPT threads per project                        |                   Yes |                   No |              Already core | Reduces history scavenging and wrong-thread errors       |
| Thread roles: review, brainstorming, architecture, research |                   Yes |                   No |              Already core | Preserves cognitive posture differences                  |
| Project tree/sidebar                                        |                   Yes |                   No |              Already core | Shell-owned project identity                             |
| WSL workspace attachment                                    |                   Yes |                   No |              Already core | Workspace truth should be repo-native                    |
| Work tree and file preview                                  |                   Yes |                   No |              Already core | Supports handoff without becoming an IDE                 |
| Prompt templates per thread role                            |                   Yes |                   No |              Already core | Reduces repetitive prompt typing                         |
| Handoff packet staging                                      |                   Yes |                   No |            Immediate next | Practical bridge between surfaces                        |
| Watched review artifact queue                               |                   Yes |                   No |            Immediate next | Directly addresses current manual churn                  |
| Manual copy/open/upload helpers                             |                   Yes |                   No |            Immediate next | Safe low-risk workflow acceleration                      |
| Automatic ChatGPT file upload                               |                    No |                Maybe |                     Later | Browser automation is brittle; start with assisted relay |
| Automatic ChatGPT response capture                          |                    No |                Maybe |                     Later | Needs careful browser-surface handling                   |
| Paste-back to Codex with header                             |    Partial/manual now |                Maybe |                     Later | Useful after response capture is reliable                |
| Codex provider profile                                      |          Yes, minimal |                   No |              Expand later | Keep Codex familiar but configurable                     |
| Custom Codex fork selection                                 | Yes, advanced setting |                  Yes |              Expand later | Treat as provider specialization                         |
| Deep fork internals                                         |                    No |                  Yes |         Only after proven | Not the standalone product thesis                        |
| ADEU harness controls                                       |                    No |                  Yes |                     Maybe | Belongs in experimental track first                      |
| Meta-orchestrator controls                                  |                    No |                  Yes |                     Maybe | Too immature for daily workflow shell                    |
| Constitutional runtime knobs                                |                    No |                  Yes |                     Maybe | Would dominate the control plane prematurely             |
| Multi-agent choreography                                    |                    No |                  Yes |                     Later | Useful only after dual-partner workflow is stable        |
| Unified generic chat router                                 |                    No |                   No |            Probably avoid | Violates surface doctrine                                |
| Cloud sync / multi-user                                     |                    No |                   No |                     Later | Not needed for current workflow                          |
| Full IDE/editor                                             |                    No |                   No |               Maybe never | Work tree/preview is enough for this shell               |

The standalone shell should ship **workflow binding and handoff features**, not deep ADEU control features.

---

# E. Control-plane model

The control plane should represent relationships explicitly.

The model should move from:

```ts
Project -> one ChatGPT review URL
```

to:

```ts
Project
  -> Workspace
  -> ImplementationBinding
  -> ChatThreadBindings[]
  -> FlowProfiles[]
  -> HandoffState
```

## Project

A project is the shell-owned workflow identity.

It is not merely a folder. It is the unit that says:

> “This workspace, this Codex surface, and these ChatGPT threads belong together.”

Suggested shape:

```ts
type Project = {
  id: string;
  name: string;

  workspace: WorkspaceBinding;

  implementationBinding: ImplementationBinding;

  chatThreads: ChatThreadBinding[];

  flowProfiles: FlowProfile[];

  handoff: HandoffState;

  createdAt: string;
  updatedAt: string;
};
```

## Workspace binding

This remains the canonical workspace source.

For WSL:

```ts
type WslWorkspaceBinding = {
  kind: "wsl";
  distro: string;
  linuxPath: string;
  label?: string;
};
```

For local/dev:

```ts
type LocalWorkspaceBinding = {
  kind: "local";
  localPath: string;
  label?: string;
};
```

The current WSL backend architecture fits this doctrine well. It should remain infrastructure, not product identity.

## Implementation binding

This is the Codex-side binding.

```ts
type ImplementationBinding = {
  provider: "codex-compatible" | "custom-codex-fork" | "other";
  mode: "local-fallback" | "url" | "cli-backed" | "app-server";
  target?: string;

  providerProfileId?: string;

  displayName?: string;
};
```

Examples:

```json
{
  "provider": "codex-compatible",
  "mode": "local-fallback",
  "displayName": "Local Codex companion"
}
```

```json
{
  "provider": "custom-codex-fork",
  "mode": "app-server",
  "target": "http://localhost:4888",
  "providerProfileId": "codex-fork-adeu-default",
  "displayName": "Custom Codex fork"
}
```

The important point: the provider is configurable, but the **surface posture** remains Codex-like.

## Multiple ChatGPT thread bindings

This is the most important next model change.

A project should have many ChatGPT threads, each with a role.

```ts
type ChatThreadRole =
  | "review"
  | "brainstorming"
  | "architecture"
  | "research"
  | "debugging"
  | "planning"
  | "custom";

type ChatThreadBinding = {
  id: string;
  role: ChatThreadRole;
  title: string;
  url: string;

  isPrimary?: boolean;
  pinned?: boolean;
  archived?: boolean;

  notes?: string;

  promptTemplateId?: string;

  lastOpenedAt?: string;
  createdAt: string;
  updatedAt: string;
};
```

Example:

```json
{
  "id": "thread_review_main",
  "role": "review",
  "title": "ADEU Studio implementation review",
  "url": "https://chatgpt.com/c/...",
  "isPrimary": true,
  "pinned": true,
  "notes": "Main review thread for Codex-produced markdown artifacts."
}
```

```json
{
  "id": "thread_architecture",
  "role": "architecture",
  "title": "ADEU architecture deliberation",
  "url": "https://chatgpt.com/c/...",
  "pinned": true,
  "notes": "Use for higher-level design tradeoffs, not patch review."
}
```

```json
{
  "id": "thread_research",
  "role": "research",
  "title": "Protocol and Electron research",
  "url": "https://chatgpt.com/c/...",
  "notes": "Use when external facts, docs, or API behavior matter."
}
```

The control plane should show these as a **thread deck**, not as browser history.

Suggested middle-plane section:

```text
ChatGPT Threads
────────────────────────
★ Review          ADEU implementation review
  Architecture    Shell/WSL architecture
  Brainstorming   Product doctrine
  Research        Electron / WSL docs
```

Clicking one changes the right plane to that thread.

The app should also support:

* `primaryReviewThreadId`
* `lastActiveThreadId`
* `defaultThreadByRole`
* archived threads
* thread notes
* optional role-specific prompt templates

## Flow profiles

Flow profiles should be lightweight and role-aware.

```ts
type FlowProfile = {
  id: string;
  name: string;

  appliesToThreadRole?: ChatThreadRole;

  watchedFilePatterns: string[];

  reviewPromptTemplate: string;

  returnHeader: string;

  handoffMode: "manual" | "assisted" | "automated-experimental";
};
```

Example:

```json
{
  "id": "flow_patch_review",
  "name": "Patch review",
  "appliesToThreadRole": "review",
  "watchedFilePatterns": [
    "**/*REVIEW*.md",
    "**/*review*.md",
    "artifacts/**/*.md"
  ],
  "reviewPromptTemplate": "Review this Codex artifact for correctness, risks, missing checks, and concrete next actions. Return concise feedback I can paste back into Codex.",
  "returnHeader": "GPT feedback",
  "handoffMode": "assisted"
}
```

## Relay and handoff points

The control plane should represent handoffs explicitly.

Do not begin with full automation. Begin with visible, human-confirmed handoff objects.

```ts
type HandoffItem = {
  id: string;

  projectId: string;
  source: "codex" | "workspace" | "human";
  targetThreadId: string;

  kind: "file-review" | "text-review" | "architecture-question" | "research-question";

  fileRelPath?: string;
  title: string;

  promptText: string;

  status:
    | "staged"
    | "copied"
    | "opened-thread"
    | "submitted-manually"
    | "response-pending"
    | "response-captured"
    | "pasted-back"
    | "dismissed";

  createdAt: string;
  updatedAt: string;
};
```

The control plane UI should include:

```text
Handoff Queue
────────────────────────
[Review] artifacts/codex-review-2026-04-21.md
Target: Review thread
Actions: Open thread | Copy prompt | Reveal file | Mark submitted
```

This is the right bridge between manual workflow and future automation.

It avoids pretending that ChatGPT upload/send automation is reliable before it is.

---

# F. Provider model

The standalone shell should use a **default Codex-compatible posture**.

The baseline should be:

```text
“I have a familiar Codex implementation companion bound to this project.”
```

Provider details should be secondary.

## Provider profile

Suggested model:

```ts
type ProviderProfile = {
  id: string;
  name: string;

  family: "codex-compatible" | "custom-codex-fork" | "other";

  mode: "local-fallback" | "url" | "cli" | "app-server";

  target?: string;

  capabilities?: {
    supportsModelSelection?: boolean;
    supportsReasoningControl?: boolean;
    supportsCommandExecution?: boolean;
    supportsPatchApply?: boolean;
    supportsWorkspaceAwareness?: boolean;
    supportsCustomHarness?: boolean;
  };

  advancedSettings?: Record<string, unknown>;
};
```

## UI posture

The Codex plane should expose normal implementation controls first:

```text
Model
Reasoning
Workspace
Send
```

Advanced provider settings should live behind:

```text
Implementation Provider
  Provider: Codex-compatible
  Mode: Local fallback / URL / CLI / App server

Advanced
  Custom fork settings
  Harness path
  Runtime flags
  Environment
```

The custom Codex fork should appear as:

```text
Provider: Custom Codex fork
```

not as:

```text
This app is the custom Codex fork control environment
```

That distinction matters.

## Fork-native settings

Fork-native settings should be:

* discoverable when available
* hidden by default
* grouped under provider settings
* capability-driven
* not rendered as top-level product navigation

Good:

```text
Advanced provider settings
- Runtime binary
- Harness profile
- Reasoning preset
- Extra environment variables
```

Bad:

```text
Main nav:
- Constitutional harness
- Meta-orchestrator
- Fork trace controls
- ADEU runtime graph
- Prompt governance kernel
```

The standalone shell may support the fork, but should not make the fork its identity.

---

# G. Roadmap

## Stage 1 — Project/thread binding correction

Goal:

> Make the shell excellent at remembering which ChatGPT threads belong to which project.

Implement:

* Multiple ChatGPT thread bindings per project.
* Thread roles:

  * review
  * brainstorming
  * architecture
  * research
  * debugging
  * planning
  * custom
* Thread deck in the control plane.
* Add/edit/remove/archive thread bindings.
* Mark primary review thread.
* Last active thread per project.
* Open selected thread in right plane.
* Preserve current single `reviewThreadUrl` by migrating it to a `review` thread binding.

Migration:

```ts
surfaceBinding.chatgpt.reviewThreadUrl
```

becomes:

```ts
chatThreads: [
  {
    role: "review",
    title: "Primary review",
    url: oldReviewThreadUrl,
    isPrimary: true
  }
]
```

This is the highest-value next implementation.

## Stage 2 — Role-aware prompt templates

Goal:

> Make each ChatGPT thread role feel intentional.

Implement:

* Prompt templates scoped by role.
* Default template for review.
* Default template for architecture.
* Default template for brainstorming.
* Default template for research.
* Copy prompt button.
* Template preview.
* Selected-file interpolation.

Example placeholders:

```text
{{project.name}}
{{workspace.path}}
{{file.relPath}}
{{file.contents}}
{{thread.role}}
{{returnHeader}}
```

Keep this manual/copy-assisted first.

## Stage 3 — Handoff queue

Goal:

> Replace ad hoc copy/paste with explicit staged handoffs.

Implement:

* Handoff queue in control plane.
* Stage selected file for review.
* Stage freeform architecture question.
* Target a specific ChatGPT thread binding.
* Copy prompt.
* Open target thread.
* Mark submitted.
* Mark response pasted back.
* Preserve handoff history per project.

This gives the shell a real workflow spine without brittle browser automation.

## Stage 4 — Watched artifact queue

Goal:

> Reduce file explorer scavenging.

Implement:

* WSL/backend watcher for configured patterns.
* Show newly produced review markdown files.
* Debounce changes.
* “Stage for review” action.
* “Ignore” action.
* “Open preview” action.

This directly targets the original workflow pain:

```text
Codex produces markdown -> user finds it -> drags it into ChatGPT
```

The shell should instead say:

```text
New review artifact found.
Target: Review thread.
Actions: Preview | Copy prompt | Open thread
```

## Stage 5 — Assisted relay, not full automation

Goal:

> Remove mechanical friction while keeping the human in control.

Implement:

* Copy prompt.
* Copy file path.
* Open ChatGPT target thread.
* Optional open file in OS.
* Optional drag/drop helper if feasible.
* Optional paste helper into Codex.
* Status tracking.

Avoid as default:

* automatic ChatGPT upload
* automatic submit
* automatic response scraping
* automatic paste-back

Those can be experimental toggles later.

## Stage 6 — Provider profiles

Goal:

> Let the Codex side evolve without making provider specialization the product.

Implement:

* Provider profile editor.
* Codex-compatible default.
* Custom Codex fork profile.
* URL/app-server mode.
* CLI/backend mode.
* Capability display.
* Advanced settings drawer.
* Provider-specific env/config fields.

Do not let this displace thread binding and handoff workflow as the main product.

## Stage 7 — Experimental automation bridge

Goal:

> Promote only proven relay automation from `odeu`.

Implement only after stages 1–5 are stable:

* Browser-surface-assisted ChatGPT upload.
* Browser-surface-assisted prompt insertion.
* Response capture.
* Paste-back to Codex.
* Explicit “experimental automation” toggle.
* Failure visibility.
* Manual fallback always available.

This should remain opt-in.

## Stage 8 — Mature ADEU feature promotion

Goal:

> Bring over only the ADEU-native controls that clearly improve daily workflow.

Candidates:

* Safe command profiles.
* Runtime capability discovery.
* Provider health checks.
* Structured traces for failed handoffs.
* Better artifact classification.
* Review quality profiles.

Still defer:

* full meta-orchestrator UI
* constitutional runtime laboratory
* deep fork trace graph
* multi-agent choreography as default UX

---

# H. Explicit tradeoffs

## What is being deferred

The standalone shell should defer:

* Deep ADEU-native controls.
* Full meta-orchestrator UX.
* Custom Codex fork internals as primary navigation.
* Multi-agent orchestration.
* Consumer ChatGPT automation as a default behavior.
* Full IDE/editor functionality.
* Cloud sync.
* Team workflows.
* General provider marketplace behavior.
* Unified generic chat interface.

These may be valuable, but they do not solve the current highest-value standalone problem.

The current highest-value problem is:

> “For this project, which Codex work surface and which ChatGPT deliberation/review threads belong together, and how do I move the right artifact to the right thread with minimal friction?”

## Why not merge standalone and `odeu` too early

Merging the tracks too early would create a product that is worse at both jobs.

The standalone shell needs to be calm, familiar, and workflow-reducing. It should help the human do real work today.

The `odeu` track needs freedom to be weird, experimental, and control-heavy. It should explore whether Codex can become a bounded meta-orchestrator under ADEU harness constraints.

Those goals have different UX needs.

Standalone wants:

```text
familiar surfaces
low friction
thread binding
handoff clarity
minimal cognitive overhead
```

`odeu` wants:

```text
instrumentation
deep controls
experimental runtime surfaces
harness visibility
orchestration knobs
```

Putting both into one maturity model would make the standalone shell feel like an unfinished lab, while making the lab too constrained by daily-product expectations.

## Why preserving distinct partner surfaces is worth the complexity

The complexity is justified because the surfaces do different cognitive work.

A unified chat would be simpler structurally, but weaker cognitively.

Codex is valuable because it is close to the repo, implementation loop, patch, command context, and execution details.

ChatGPT is valuable because it can step back, reframe, critique, generalize, compare, and hold a broader world model.

The human uses them differently:

```text
With Codex:
“Implement this.”
“Patch this.”
“Check this failure.”
“Continue the repo task.”

With ChatGPT:
“Review this.”
“Does this architecture make sense?”
“What am I missing?”
“Reframe the tradeoff.”
“Compare possible directions.”
```

The control plane should make those differences visible rather than hiding them.

The standalone shell becomes valuable when it says:

```text
You are in Project X.
Your implementation partner is here.
Your review thread is here.
Your architecture thread is here.
Your research thread is here.
This file is ready for review.
This prompt is the right one.
This is the handoff state.
```

That is the product.

Not a mini ADEU Studio.

Not a generic chat router.

Not a full IDE.

A deliberate, project-bound, dual-partner workflow shell.
