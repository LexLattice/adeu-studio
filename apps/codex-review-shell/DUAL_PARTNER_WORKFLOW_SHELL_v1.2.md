# Codex Review Shell v1.2 — Dual-Partner Workflow Pass

Status: implementation support note.

This version keeps the standalone shell bounded: it is not ADEU Studio, not the `odeu` experimental harness, and not a unified generic super-chat. It is a dual-partner workflow shell that coordinates familiar Codex and ChatGPT surfaces through an explicit control plane.

## Product boundary

The standalone shell optimizes for day-to-day implementation/review flow:

- bind one project to the correct implementation surface
- bind the same project to multiple relevant ChatGPT threads
- reduce scavenging through unrelated ChatGPT history
- stage handoffs visibly before any brittle automation
- keep the WSL workspace backend as the source of workspace truth

The `odeu`/ADEU-native track remains the right place for deep harness controls, meta-orchestrator experiments, constitutional runtime knobs, and custom fork internals as primary navigation.

## Surface doctrine retained

- **Left plane: Codex implementation companion.** Keep the surface familiar and patch/repo oriented. The local fallback remains Codex-style; a real provider URL can still replace it.
- **Middle plane: workflow control plane.** This is not a chat. It owns project/thread bindings, active role, prompt templates, handoffs, watched artifacts, work tree, and backend status.
- **Right plane: ChatGPT deliberation/review companion.** This remains the real embedded ChatGPT web surface with best-effort chrome/dark handling.

## v1.2 model changes

### Multiple ChatGPT thread bindings

Each project now carries a `chatThreads` deck:

```json
{
  "id": "thread_review_primary",
  "role": "review",
  "title": "Primary review",
  "url": "https://chatgpt.com/c/...",
  "notes": "Main project review thread",
  "isPrimary": true,
  "pinned": true,
  "archived": false,
  "createdAt": "...",
  "updatedAt": "...",
  "lastOpenedAt": "..."
}
```

Supported roles:

- `review`
- `brainstorming`
- `architecture`
- `research`
- `debugging`
- `planning`
- `custom`

The project also tracks:

```json
{
  "activeChatThreadId": "thread_review_primary",
  "lastActiveThreadId": "thread_review_primary"
}
```

Selecting a thread in the middle plane loads that URL into the right ChatGPT pane.

### Legacy migration

Old configs that only have:

```json
"surfaceBinding": {
  "chatgpt": {
    "reviewThreadUrl": "https://chatgpt.com/c/..."
  }
}
```

are normalized into one primary `review` thread. Malformed or unsafe thread URLs fail closed to `https://chatgpt.com/` rather than loading arbitrary protocol targets.

The legacy `surfaceBinding.chatgpt.reviewThreadUrl` field is still mirrored to the primary review thread URL for compatibility, but the thread deck is now the real control-plane model.

### Role-aware prompt templates

Projects now carry role-scoped `promptTemplates` for at least:

- review
- architecture
- brainstorming
- research

The control plane previews and copies the active role prompt with placeholder interpolation:

- `{{project.name}}`
- `{{workspace.path}}`
- `{{file.relPath}}`
- `{{file.contents}}`
- `{{thread.role}}`
- `{{returnHeader}}`

This remains copy-assisted. It does not inject into ChatGPT.

### Handoff queue

Projects now carry visible manual handoff items:

```json
{
  "id": "handoff_...",
  "projectId": "project_...",
  "source": "workspace",
  "targetThreadId": "thread_review_primary",
  "kind": "file-review",
  "fileRelPath": "artifacts/review.md",
  "title": "Review artifacts/review.md",
  "promptText": "...",
  "status": "staged",
  "createdAt": "...",
  "updatedAt": "..."
}
```

Supported kinds:

- `file-review`
- `text-review`
- `architecture-question`
- `research-question`

Supported statuses:

- `staged`
- `copied`
- `opened-thread`
- `submitted-manually`
- `response-pending`
- `response-captured`
- `pasted-back`
- `dismissed`

The middle plane can stage selected files, copy prompts, open target threads, reveal files, mark submitted, mark pasted back, or dismiss.

### Watched artifact queue

The workspace backend now supports `listMatchingFiles` over configured watched patterns. The control plane scans through the backend session and shows matching review artifacts with actions:

- preview
- stage for review
- ignore

This directly targets the old loop where Codex produces a review markdown file and the human scavenges through file explorer before finding the right ChatGPT thread.

## Backend changes

The WSL/local backend agent now supports:

- `listMatchingFiles`
- `resolvePath`

Existing work tree and file preview still route through the backend. WSL workspace truth remains canonical on the Linux side.

## Intentionally deferred

This pass deliberately does not implement:

- automatic ChatGPT file upload
- automatic ChatGPT submit
- response scraping
- automatic paste-back to Codex
- deep ADEU harness controls
- meta-orchestrator UX
- full IDE/editor behavior
- cloud/team sync

Those remain later promotion candidates, preferably after the visible handoff model proves stable.

## Validation

Run from `apps/codex-review-shell`:

```bash
npm run validate
```

The smoke path validates legacy single-thread migration, malformed ChatGPT URL fail-closed behavior, backend protocol, tree listing, file preview, watched-pattern scan, and path resolution.
