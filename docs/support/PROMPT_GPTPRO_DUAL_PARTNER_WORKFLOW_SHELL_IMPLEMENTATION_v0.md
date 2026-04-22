# Draft GPTPro Dual-Partner Workflow Shell Implementation Prompt v0

Status: support prompt artifact.

Authority layer: support only.

Use this prompt when asking GPTPro to implement the next serious standalone-shell
pass from the current doctrine and product architecture.

---

You are working on the standalone review shell inside this repo.

This is **not** an ADEU Studio implementation pass.
It is **not** a request to expose every ADEU-native orchestration primitive.
It is **not** a request to turn the app into a unified generic super-chat.

You are implementing the next serious pass of a **dual-partner workflow shell**.

## Read these repo documents first

Treat these as the controlling support-layer design references:

- `docs/support/DRAFT_DUAL_PARTNER_WORKFLOW_SHELL_v0.md`
- `docs/support/DRAFT_CODEX_REVIEW_SHELL_TWO_TRACK_DOCTRINE_v0.md`
- `docs/support/DRAFT_CODEX_REVIEW_SHELL_STANDALONE_PRODUCT_ARCHITECTURE_v0.md`
- `docs/support/DRAFT_GPTPRO_STANDALONE_REVIEW_SHELL_REALIGNMENT_PROMPT_v0.md`

Also inspect the current app implementation:

- `apps/codex-review-shell/`
- especially:
  - `apps/codex-review-shell/src/main.js`
  - `apps/codex-review-shell/src/main/workspace-backend.js`
  - `apps/codex-review-shell/src/backend/wsl-agent.js`
  - `apps/codex-review-shell/src/preload.js`
  - `apps/codex-review-shell/src/renderer/app.js`
  - `apps/codex-review-shell/WSL_HOST_ARCHITECTURE.md`

## Current product thesis

The standalone shell is a **dual-partner workflow shell** for coordinating:

- Codex as the repo-coupled implementation partner
- ChatGPT as the deliberation / review / reframing / world-model partner
- a middle control plane that binds projects, surfaces, threads, files, prompts,
  and handoff points

The product thesis is:

> Codex and ChatGPT occupy different cognitive offices. The shell should preserve
> their different postures and make the handoff between them deliberate,
> project-bound, and low-friction.

So:

- do **not** flatten the app into one generic chat surface
- keep the Codex pane familiar and implementation-oriented
- keep the ChatGPT pane familiar and deliberation-oriented
- make the control plane the bounded workflow spine

## Important product boundary

Do not optimize this pass for:

- deep ADEU-native harness controls
- meta-orchestrator posture
- constitutional runtime laboratory controls
- multi-agent choreography
- fork internals as primary navigation
- brittle browser automation as default behavior

Those belong first in the `odeu` experimental track.

The standalone app should optimize for the highest current workflow problem:

> For this project, which Codex surface and which ChatGPT threads belong together,
> and how do I move the right artifact to the right thread with minimal friction?

## Current app baseline

Assume the repo already contains:

- the current Electron three-plane shell
- WSL workspace backend architecture
- maximize / restore geometry fix
- current project model
- current Codex surface
- current embedded ChatGPT surface

Preserve that baseline where possible.

Do not regress:

- the WSL host/backend model
- the maximize / restore fix
- the familiar Codex pane posture
- the real embedded ChatGPT pane

## What I want you to implement now

Do **not** try to implement the full roadmap at once.

Implement the **first serious product pass**:

### 1. Project-bound multiple ChatGPT thread bindings

Replace the single-review-thread posture with a real project-bound thread deck.

Target model:

- each project may have multiple ChatGPT thread bindings
- each thread has a role
- roles should include at least:
  - `review`
  - `brainstorming`
  - `architecture`
  - `research`
  - `debugging`
  - `planning`
  - `custom`
- each thread should store:
  - id
  - role
  - title
  - url
  - notes
  - `isPrimary`
  - `pinned`
  - `archived`
  - timestamps

Required behavior:

- add / edit / remove / archive thread bindings per project
- mark one primary review thread
- remember last active thread
- switch the right pane to the selected thread
- render the thread deck in the middle control plane

### 2. Migration from old single-thread config

If the current project/config model stores only one ChatGPT review URL, migrate it
forward safely into:

- one `review` thread binding
- marked primary

The migration must be explicit and fail closed on malformed config.

### 3. Role-aware prompt templates

Add prompt templates scoped by ChatGPT thread role.

Minimum target:

- review
- architecture
- brainstorming
- research

Support:

- template preview
- copy prompt action
- placeholder interpolation for at least:
  - project name
  - workspace path
  - selected file path
  - selected file contents where appropriate
  - thread role
  - return header

Keep this copy-assisted first.
Do not require browser injection or automation as the main path.

### 4. Explicit handoff queue

Implement a real control-plane handoff queue rather than ad hoc copy/paste only.

Minimum target object kinds:

- file review
- text review
- architecture question
- research question

Each handoff item should carry:

- project id
- source
- target thread id
- kind
- optional file relative path
- title
- prompt text
- status
- timestamps

Minimum statuses:

- `staged`
- `copied`
- `opened-thread`
- `submitted-manually`
- `response-pending`
- `response-captured`
- `pasted-back`
- `dismissed`

Minimum actions:

- stage selected file for handoff
- target specific thread
- open target thread
- copy prompt
- reveal file
- mark submitted
- mark pasted back

The point is to give the app a visible workflow spine without pretending ChatGPT
automation is already reliable.

### 5. Lightweight watched artifact queue

Use the workspace backend to support configured watched file patterns.

Minimum target:

- configure watched file patterns per flow profile or project
- show newly detected matching files in the control plane
- actions:
  - preview
  - stage for review
  - ignore

This should directly address the current manual pain:

- Codex produces review markdown
- user scavenges for it manually
- user manually finds the right ChatGPT thread

### 6. Keep provider specialization secondary

Keep the Codex side mostly familiar.

Provider/fork support is allowed, but it should remain secondary.

Good:

- provider selector
- provider profile
- advanced provider drawer
- custom fork settings under advanced/provider area

Bad:

- turning provider internals into the main product navigation
- making the app identity “the custom fork dashboard”

## Explicit non-goals for this pass

Do not implement these as the mainline path in this pass:

- automatic ChatGPT upload
- automatic ChatGPT submit
- automatic ChatGPT response scraping
- automatic paste-back to Codex
- deep ADEU harness controls
- meta-orchestrator control plane
- multi-agent orchestration UX
- unified generic chat router
- full IDE/editor
- cloud sync / team workflow

You may leave careful scaffolding for later, but do not center this pass on those.

## UX constraints

Keep the current high-level product shape:

- left pane = Codex implementation companion
- middle pane = control plane
- right pane = ChatGPT review / world-model companion

The middle plane should now become meaningfully stronger.

It should answer:

- which project is active
- which workspace is attached
- which Codex binding is active
- which ChatGPT threads belong to this project
- which thread role is active
- which prompt template applies
- which handoffs are staged
- which review artifacts are waiting

The app should still feel calm and practical, not like an unfinished lab.

## Technical expectations

Build on the current app architecture rather than replacing it wholesale.

Expected areas to update:

- project/config model
- preload bridge
- renderer state model
- control-plane UI
- workspace backend APIs
- optional watcher support
- migration logic
- documentation

The WSL workspace backend should remain the canonical workspace truth for WSL
projects.

If you add file watching or file preview improvements, route them through the
backend architecture rather than bypassing it.

## Deliverables

I want:

1. updated app implementation under `apps/codex-review-shell`
2. updated support note describing this version and the product boundary
3. small zip of just the app code
4. larger zip of the modified repo snapshot
5. short run instructions
6. a concise explanation of:
   - what was implemented
   - what was intentionally deferred
   - where the control-plane model changed

## Validation expectations

At minimum:

- syntax checks pass
- smoke checks pass
- project config migration works for the old single-thread shape
- multiple ChatGPT thread bindings per project work
- selecting a thread changes the right pane target correctly
- handoff queue works end-to-end in manual/copy-assisted mode
- watched file queue works for at least one configured pattern
- maximize / restore still behaves correctly

## Output quality bar

Do not give me a vague redesign.
Do not give me a generic product brainstorm.
Do not try to solve the entire future roadmap in one pass.

Implement the strongest bounded pass that makes the standalone shell genuinely better
at the real dual-partner workflow right now.

The app should come out of this pass more useful for actual day-to-day work, not just
more conceptually interesting.

---

Use the dual-partner workflow doctrine as the controlling frame for the
implementation.
