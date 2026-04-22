const bridge = window.workspaceShell;

const MIN_WIDTHS = {
  left: 330,
  middle: 430,
  right: 350,
  splitter: 8,
};

const THREAD_ROLES = ["review", "brainstorming", "architecture", "research", "debugging", "planning", "custom"];
const ROLE_LABELS = {
  review: "Review",
  brainstorming: "Brainstorming",
  architecture: "Architecture",
  research: "Research",
  debugging: "Debugging",
  planning: "Planning",
  custom: "Custom",
};
const HANDOFF_KINDS = {
  "file-review": "File review",
  "text-review": "Text review",
  "architecture-question": "Architecture question",
  "research-question": "Research question",
};
const ACTIVE_HANDOFF_STATUSES = new Set(["staged", "copied", "opened-thread", "submitted-manually", "response-pending", "response-captured"]);

const state = {
  config: null,
  configPath: "",
  repoRoot: "",
  surfaceEvents: {
    codex: { type: "idle" },
    chatgpt: { type: "idle" },
  },
  drawerMode: "edit",
  threadDrawerMode: "edit",
  currentWidths: { left: 0, middle: 0, right: 0 },
  layoutFrame: 0,
  lastLayoutSignature: "",
  selectedFileRelPath: "",
  selectedFilePreview: null,
  workspaceStatuses: {},
  watchedArtifacts: [],
};

const els = {
  appShell: document.getElementById("appShell"),
  selectedProjectName: document.getElementById("selectedProjectName"),
  repoPath: document.getElementById("repoPath"),
  workspacePath: document.getElementById("workspacePath"),
  backendStatus: document.getElementById("backendStatus"),
  bindingStatus: document.getElementById("bindingStatus"),
  activeThreadStatus: document.getElementById("activeThreadStatus"),
  projectList: document.getElementById("projectList"),
  projectCount: document.getElementById("projectCount"),
  threadDeck: document.getElementById("threadDeck"),
  threadCount: document.getElementById("threadCount"),
  addThreadButton: document.getElementById("addThreadButton"),
  configPath: document.getElementById("configPath"),
  codexSlot: document.getElementById("codexSlot"),
  chatgptSlot: document.getElementById("chatgptSlot"),
  leftSplitter: document.getElementById("leftSplitter"),
  rightSplitter: document.getElementById("rightSplitter"),
  codexStatus: document.getElementById("codexStatus"),
  chatgptStatus: document.getElementById("chatgptStatus"),
  lastEvent: document.getElementById("lastEvent"),
  addProjectButton: document.getElementById("addProjectButton"),
  editProjectButton: document.getElementById("editProjectButton"),
  copyPromptButton: document.getElementById("copyPromptButton"),
  copyHeaderButton: document.getElementById("copyHeaderButton"),
  reloadCodexButton: document.getElementById("reloadCodexButton"),
  reloadChatButton: document.getElementById("reloadChatButton"),
  externalChatButton: document.getElementById("externalChatButton"),
  forceDarkButton: document.getElementById("forceDarkButton"),
  chatSettingsButton: document.getElementById("chatSettingsButton"),
  promptRoleLabel: document.getElementById("promptRoleLabel"),
  activePromptPreview: document.getElementById("activePromptPreview"),
  handoffTargetThreadSelect: document.getElementById("handoffTargetThreadSelect"),
  stageSelectedFileButton: document.getElementById("stageSelectedFileButton"),
  stagePreviewButton: document.getElementById("stagePreviewButton"),
  stageTextReviewButton: document.getElementById("stageTextReviewButton"),
  stageArchitectureQuestionButton: document.getElementById("stageArchitectureQuestionButton"),
  stageResearchQuestionButton: document.getElementById("stageResearchQuestionButton"),
  handoffQueue: document.getElementById("handoffQueue"),
  handoffCount: document.getElementById("handoffCount"),
  watchedArtifactList: document.getElementById("watchedArtifactList"),
  watchedCount: document.getElementById("watchedCount"),
  refreshWatchedButton: document.getElementById("refreshWatchedButton"),
  watchedRulesPreview: document.getElementById("watchedRulesPreview"),
  returnHeaderPreview: document.getElementById("returnHeaderPreview"),
  refreshWorkTreeButton: document.getElementById("refreshWorkTreeButton"),
  workTree: document.getElementById("workTree"),
  previewPath: document.getElementById("previewPath"),
  previewMeta: document.getElementById("previewMeta"),
  filePreview: document.getElementById("filePreview"),
  drawer: document.getElementById("projectDrawer"),
  drawerTitle: document.getElementById("drawerTitle"),
  form: document.getElementById("projectForm"),
  closeDrawerButton: document.getElementById("closeDrawerButton"),
  cancelProjectButton: document.getElementById("cancelProjectButton"),
  chooseRepoButton: document.getElementById("chooseRepoButton"),
  deleteProjectButton: document.getElementById("deleteProjectButton"),
  projectIdInput: document.getElementById("projectIdInput"),
  projectNameInput: document.getElementById("projectNameInput"),
  repoPathInput: document.getElementById("repoPathInput"),
  workspaceKindInput: document.getElementById("workspaceKindInput"),
  workspaceLabelInput: document.getElementById("workspaceLabelInput"),
  wslDistroInput: document.getElementById("wslDistroInput"),
  wslLinuxPathInput: document.getElementById("wslLinuxPathInput"),
  codexModeInput: document.getElementById("codexModeInput"),
  codexLabelInput: document.getElementById("codexLabelInput"),
  codexTargetInput: document.getElementById("codexTargetInput"),
  chatgptUrlInput: document.getElementById("chatgptUrlInput"),
  reduceChromeInput: document.getElementById("reduceChromeInput"),
  reviewPromptInput: document.getElementById("reviewPromptInput"),
  architecturePromptInput: document.getElementById("architecturePromptInput"),
  brainstormingPromptInput: document.getElementById("brainstormingPromptInput"),
  researchPromptInput: document.getElementById("researchPromptInput"),
  watchedPatternsInput: document.getElementById("watchedPatternsInput"),
  returnHeaderInput: document.getElementById("returnHeaderInput"),
  threadDrawer: document.getElementById("threadDrawer"),
  threadForm: document.getElementById("threadForm"),
  threadDrawerTitle: document.getElementById("threadDrawerTitle"),
  closeThreadDrawerButton: document.getElementById("closeThreadDrawerButton"),
  cancelThreadButton: document.getElementById("cancelThreadButton"),
  deleteThreadButton: document.getElementById("deleteThreadButton"),
  threadIdInput: document.getElementById("threadIdInput"),
  threadRoleInput: document.getElementById("threadRoleInput"),
  threadTitleInput: document.getElementById("threadTitleInput"),
  threadUrlInput: document.getElementById("threadUrlInput"),
  threadNotesInput: document.getElementById("threadNotesInput"),
  threadPrimaryInput: document.getElementById("threadPrimaryInput"),
  threadPinnedInput: document.getElementById("threadPinnedInput"),
  threadArchivedInput: document.getElementById("threadArchivedInput"),
};

function activeProject() {
  if (!state.config) return null;
  return state.config.projects.find((project) => project.id === state.config.selectedProjectId) ?? state.config.projects[0] ?? null;
}

function createId(prefix = "item") {
  const id = crypto.randomUUID ? crypto.randomUUID().replace(/-/g, "").slice(0, 12) : `${Date.now().toString(36)}${Math.random().toString(36).slice(2, 8)}`;
  return `${prefix}_${id}`;
}

function nowIso() {
  return new Date().toISOString();
}

function shortPath(value) {
  const text = String(value ?? "");
  if (text.length <= 64) return text;
  return `${text.slice(0, 28)}…${text.slice(-32)}`;
}

function clamp(value, min, max) {
  if (max < min) return min;
  return Math.min(max, Math.max(min, value));
}

function roleLabel(role) {
  return ROLE_LABELS[role] || ROLE_LABELS.custom;
}

function defaultPromptText(role) {
  const templates = {
    review:
      "Review {{file.relPath}} for project {{project.name}}. Focus on correctness, risks, missing checks, and concrete next actions. Return concise feedback under the header {{returnHeader}}.\n\nSelected file contents:\n{{file.contents}}",
    architecture:
      "For project {{project.name}}, evaluate this architecture question in the {{thread.role}} thread. Identify tradeoffs, risks, invariants, and a recommended next move.\n\nContext/file: {{file.relPath}}\n{{file.contents}}",
    brainstorming:
      "Brainstorm options for project {{project.name}} without collapsing into implementation yet. Reframe the problem, list promising directions, and call out unknowns.\n\nContext/file: {{file.relPath}}\n{{file.contents}}",
    research:
      "Research/synthesize the question for project {{project.name}}. Separate confirmed facts, assumptions, risks, and follow-up checks.\n\nContext/file: {{file.relPath}}\n{{file.contents}}",
    debugging:
      "Help debug project {{project.name}}. Triage symptoms, likely causes, evidence to collect, and next actions.\n\nContext/file: {{file.relPath}}\n{{file.contents}}",
    planning:
      "Plan the next implementation steps for project {{project.name}}. Keep Codex as the implementation partner and return an actionable sequence.\n\nContext/file: {{file.relPath}}\n{{file.contents}}",
    custom:
      "Use the {{thread.role}} ChatGPT thread for project {{project.name}}.\n\nContext/file: {{file.relPath}}\n{{file.contents}}",
  };
  return templates[role] || templates.custom;
}

function defaultPromptTemplates() {
  return Object.fromEntries(
    THREAD_ROLES.map((role) => [
      role,
      { id: `template_${role}`, role, title: `${roleLabel(role)} prompt`, text: defaultPromptText(role), updatedAt: nowIso() },
    ]),
  );
}

function projectWorkspace(project) {
  const workspace = project?.workspace;
  if (workspace?.kind === "wsl") {
    return {
      kind: "wsl",
      distro: workspace.distro || "",
      linuxPath: workspace.linuxPath || "/home",
      label: workspace.label || "WSL workspace",
    };
  }
  return {
    kind: "local",
    localPath: workspace?.localPath || project?.repoPath || state.repoRoot || "",
    label: workspace?.label || "Local workspace",
  };
}

function workspaceSummary(project) {
  const workspace = projectWorkspace(project);
  if (workspace.kind === "wsl") return `WSL ${workspace.distro || "default"}:${workspace.linuxPath}`;
  return `Local ${workspace.localPath}`;
}

function workspaceRootValue(project) {
  const workspace = projectWorkspace(project);
  return workspace.kind === "wsl" ? workspace.linuxPath : workspace.localPath;
}

function chatThreads(project) {
  return Array.isArray(project?.chatThreads) ? project.chatThreads : [];
}

function primaryReviewThread(project) {
  const threads = chatThreads(project);
  return (
    threads.find((thread) => thread.role === "review" && thread.isPrimary && !thread.archived) ||
    threads.find((thread) => thread.role === "review" && thread.isPrimary) ||
    threads.find((thread) => thread.role === "review" && !thread.archived) ||
    threads.find((thread) => !thread.archived) ||
    threads[0] ||
    null
  );
}

function activeThread(project = activeProject()) {
  const threads = chatThreads(project);
  return (
    threads.find((thread) => thread.id === project?.activeChatThreadId && !thread.archived) ||
    threads.find((thread) => thread.id === project?.lastActiveThreadId && !thread.archived) ||
    primaryReviewThread(project)
  );
}

function threadById(project, threadId) {
  return chatThreads(project).find((thread) => thread.id === threadId) || null;
}

function sortedThreads(project, includeArchived = true) {
  const order = Object.fromEntries(THREAD_ROLES.map((role, index) => [role, index]));
  return chatThreads(project)
    .filter((thread) => includeArchived || !thread.archived)
    .slice()
    .sort((a, b) => {
      if (a.archived !== b.archived) return a.archived ? 1 : -1;
      if (a.pinned !== b.pinned) return a.pinned ? -1 : 1;
      if (a.isPrimary !== b.isPrimary) return a.isPrimary ? -1 : 1;
      return (order[a.role] ?? 99) - (order[b.role] ?? 99) || a.title.localeCompare(b.title);
    });
}

function promptTemplates(project) {
  return { ...defaultPromptTemplates(), ...(project?.promptTemplates || {}) };
}

function templateForThread(project, thread) {
  const templates = promptTemplates(project);
  const role = thread?.role || "review";
  return templates[role]?.text || templates.review?.text || defaultPromptText(role);
}

function selectedFileContents() {
  if (!state.selectedFilePreview || state.selectedFilePreview.binary) return "";
  return state.selectedFilePreview.text || "";
}

function interpolatePrompt(template, options = {}) {
  const project = options.project || activeProject();
  const thread = options.thread || activeThread(project);
  const fileRelPath = options.fileRelPath ?? state.selectedFileRelPath ?? "";
  const fileContents = options.fileContents ?? selectedFileContents();
  const replacements = {
    "project.name": project?.name || "",
    "workspace.path": workspaceRootValue(project) || "",
    "file.relPath": fileRelPath || "No file selected",
    "file.contents": fileContents || "",
    "thread.role": roleLabel(thread?.role || "review"),
    returnHeader: project?.flowProfile?.returnHeader || "GPT feedback",
  };
  return String(template || "").replace(/{{\s*([^}]+?)\s*}}/g, (_match, key) => replacements[key] ?? "");
}

function activePromptText(project = activeProject(), thread = activeThread(project)) {
  return interpolatePrompt(templateForThread(project, thread), { project, thread });
}

function backendStatusText(project) {
  if (!project) return "backend detached";
  const status = state.workspaceStatuses[project.id];
  if (!status) return "backend attaching…";
  const transport = status.transport ? ` · ${status.transport}` : "";
  if (status.status === "attached") return `backend attached${transport}`;
  if (status.status === "failed") return `backend failed${status.lastError ? ` · ${status.lastError}` : ""}`;
  if (status.status === "closed") return `backend closed${status.lastError ? ` · ${status.lastError}` : ""}`;
  return `backend ${status.status || "unknown"}${transport}`;
}

function updateWorkspaceFieldVisibility() {
  const kind = els.workspaceKindInput?.value || "local";
  for (const element of document.querySelectorAll("[data-workspace-kind]")) {
    element.hidden = element.getAttribute("data-workspace-kind") !== kind;
  }
}

function setLastEvent(message) {
  els.lastEvent.textContent = message;
  els.lastEvent.title = message;
}

function formatBytes(bytes) {
  const number = Number(bytes) || 0;
  if (number < 1024) return `${number} B`;
  if (number < 1024 * 1024) return `${(number / 1024).toFixed(1)} KB`;
  return `${(number / (1024 * 1024)).toFixed(1)} MB`;
}

function formatTime(value) {
  if (!value) return "";
  try {
    return new Date(value).toLocaleString(undefined, { month: "short", day: "numeric", hour: "2-digit", minute: "2-digit" });
  } catch {
    return String(value);
  }
}

function surfaceStatusLabel(event) {
  if (!event || event.type === "idle") return "idle";
  if (event.type === "loading") return "loading";
  if (event.type === "loaded") return event.title ? `loaded · ${event.title}` : "loaded";
  if (event.type === "load-failed") return "load failed";
  if (event.type === "navigation-blocked") return "blocked navigation";
  if (event.type === "settings-opened") return "settings requested";
  if (event.type === "settings-open-failed") return "settings failed";
  return event.type;
}

function renderStatus() {
  for (const [surface, element] of [
    ["codex", els.codexStatus],
    ["chatgpt", els.chatgptStatus],
  ]) {
    const event = state.surfaceEvents[surface] ?? { type: "idle" };
    element.textContent = surfaceStatusLabel(event);
    element.title = event.title || event.url || event.type || "idle";
    element.className = "status-dot";
    if (event.type === "loading") element.classList.add("loading");
    if (event.type === "loaded") element.classList.add("loaded");
    if (event.type === "load-failed") element.classList.add("failed");
    if (event.type === "navigation-blocked") element.classList.add("blocked");
    if (event.type === "settings-opened") element.classList.add("settings-opened");
    if (event.type === "settings-open-failed") element.classList.add("settings-open-failed");
  }
}

function renderProjectList() {
  const config = state.config;
  if (!config) return;
  els.projectCount.textContent = String(config.projects.length);
  els.projectList.innerHTML = "";
  for (const project of config.projects) {
    const current = activeThread(project);
    const button = document.createElement("button");
    button.type = "button";
    button.className = `project-item${project.id === config.selectedProjectId ? " active" : ""}`;
    button.innerHTML = `
      <strong></strong>
      <span class="truncate mono"></span>
      <span class="truncate"></span>
    `;
    button.querySelector("strong").textContent = project.name;
    button.querySelectorAll("span")[0].textContent = shortPath(workspaceSummary(project));
    button.querySelectorAll("span")[1].textContent = `${chatThreads(project).filter((thread) => !thread.archived).length} ChatGPT threads · ${current?.title || "No active thread"}`;
    button.addEventListener("click", () => selectProject(project.id));
    els.projectList.appendChild(button);
  }
}

function renderSelectedProject() {
  const project = activeProject();
  if (!project) return;
  const codex = project.surfaceBinding.codex;
  const workspace = projectWorkspace(project);
  const workspaceText = workspaceSummary(project);
  const currentThread = activeThread(project);
  const nonArchivedThreads = chatThreads(project).filter((thread) => !thread.archived);

  els.selectedProjectName.textContent = project.name;
  els.repoPath.textContent = project.repoPath;
  els.repoPath.title = project.repoPath;
  els.workspacePath.textContent = workspaceText;
  els.workspacePath.title = workspaceText;
  els.backendStatus.textContent = backendStatusText(project);
  els.backendStatus.title = backendStatusText(project);
  els.bindingStatus.textContent = `${workspace.kind.toUpperCase()} · ${codex.mode} Codex · ${nonArchivedThreads.length} ChatGPT threads`;
  els.activeThreadStatus.textContent = currentThread ? `Active ${roleLabel(currentThread.role)} · ${currentThread.title}` : "No active ChatGPT thread";
  els.activeThreadStatus.title = currentThread?.url || "";
  els.watchedRulesPreview.textContent = (project.flowProfile?.watchedFilePatterns || []).join("\n");
  els.returnHeaderPreview.textContent = project.flowProfile?.returnHeader || "GPT feedback";
}

function renderThreadDeck() {
  const project = activeProject();
  if (!project) return;
  const active = activeThread(project);
  const threads = sortedThreads(project, true);
  const activeCount = threads.filter((thread) => !thread.archived).length;
  els.threadCount.textContent = String(activeCount);
  els.threadDeck.innerHTML = "";

  if (!threads.length) {
    els.threadDeck.innerHTML = `<div class="empty-state">No ChatGPT threads are bound to this project yet.</div>`;
    return;
  }

  for (const thread of threads) {
    const row = document.createElement("div");
    row.className = `thread-item${thread.id === active?.id ? " active" : ""}${thread.archived ? " archived" : ""}`;
    row.innerHTML = `
      <button class="thread-main" type="button">
        <span class="thread-topline">
          <span class="role-badge"></span>
          <strong class="truncate"></strong>
        </span>
        <span class="thread-meta truncate"></span>
        <span class="thread-notes truncate"></span>
      </button>
      <div class="thread-actions">
        <button class="ghost small open-thread" type="button">Open</button>
        <button class="ghost small edit-thread" type="button">Edit</button>
      </div>
    `;
    row.querySelector(".role-badge").textContent = `${thread.isPrimary ? "★ " : ""}${roleLabel(thread.role)}${thread.pinned ? " · pinned" : ""}${thread.archived ? " · archived" : ""}`;
    row.querySelector("strong").textContent = thread.title;
    row.querySelector(".thread-meta").textContent = shortPath(thread.url);
    row.querySelector(".thread-notes").textContent = thread.notes || (thread.lastOpenedAt ? `Last opened ${formatTime(thread.lastOpenedAt)}` : "No notes");
    row.querySelector(".thread-main").addEventListener("click", () => selectThread(thread.id));
    row.querySelector(".open-thread").addEventListener("click", () => selectThread(thread.id));
    row.querySelector(".edit-thread").addEventListener("click", () => openThreadDrawer("edit", thread.id));
    els.threadDeck.appendChild(row);
  }
}

function renderHandoffTargetSelect() {
  const project = activeProject();
  if (!project) return;
  const current = activeThread(project);
  const previous = els.handoffTargetThreadSelect.value;
  els.handoffTargetThreadSelect.innerHTML = "";
  for (const thread of sortedThreads(project, false)) {
    const option = document.createElement("option");
    option.value = thread.id;
    option.textContent = `${roleLabel(thread.role)} · ${thread.title}`;
    els.handoffTargetThreadSelect.appendChild(option);
  }
  els.handoffTargetThreadSelect.value = previous || current?.id || primaryReviewThread(project)?.id || "";
}

function renderPromptPreview() {
  const project = activeProject();
  const thread = activeThread(project);
  const prompt = activePromptText(project, thread);
  els.promptRoleLabel.textContent = thread ? `${roleLabel(thread.role)} prompt · ${thread.title}` : "Active thread prompt";
  els.activePromptPreview.textContent = prompt || "No prompt template configured.";
}

function renderHandoffQueue() {
  const project = activeProject();
  if (!project) return;
  const handoffs = Array.isArray(project.handoffs) ? project.handoffs : [];
  const activeHandoffs = handoffs.filter((item) => ACTIVE_HANDOFF_STATUSES.has(item.status));
  els.handoffCount.textContent = String(activeHandoffs.length);
  els.handoffQueue.innerHTML = "";

  if (!handoffs.length) {
    els.handoffQueue.innerHTML = `<div class="empty-state">No handoffs staged. Select a file or stage a question to create one.</div>`;
    return;
  }

  for (const item of handoffs.slice().sort((a, b) => String(b.updatedAt).localeCompare(String(a.updatedAt)))) {
    const thread = threadById(project, item.targetThreadId);
    const row = document.createElement("article");
    row.className = `handoff-item status-${item.status}`;
    row.innerHTML = `
      <div class="handoff-summary">
        <span class="role-badge"></span>
        <strong class="truncate"></strong>
        <span class="handoff-meta truncate"></span>
        <span class="handoff-prompt-preview"></span>
      </div>
      <div class="handoff-actions">
        <button class="ghost small open-handoff" type="button">Open thread</button>
        <button class="ghost small copy-handoff" type="button">Copy prompt</button>
        <button class="ghost small reveal-handoff" type="button">Reveal file</button>
        <button class="ghost small submitted-handoff" type="button">Mark submitted</button>
        <button class="ghost small pasted-handoff" type="button">Mark pasted back</button>
        <button class="ghost small dismiss-handoff" type="button">Dismiss</button>
      </div>
    `;
    row.querySelector(".role-badge").textContent = `${HANDOFF_KINDS[item.kind] || item.kind} · ${item.status}`;
    row.querySelector("strong").textContent = item.title;
    row.querySelector(".handoff-meta").textContent = `Target: ${thread ? `${roleLabel(thread.role)} · ${thread.title}` : "missing thread"}${item.fileRelPath ? ` · ${item.fileRelPath}` : ""}`;
    row.querySelector(".handoff-prompt-preview").textContent = item.promptText;
    row.querySelector(".open-handoff").addEventListener("click", () => openHandoffThread(item.id));
    row.querySelector(".copy-handoff").addEventListener("click", () => copyHandoffPrompt(item.id));
    row.querySelector(".reveal-handoff").disabled = !item.fileRelPath;
    row.querySelector(".reveal-handoff").addEventListener("click", () => revealHandoffFile(item.id));
    row.querySelector(".submitted-handoff").addEventListener("click", () => updateHandoffStatus(item.id, "submitted-manually"));
    row.querySelector(".pasted-handoff").addEventListener("click", () => updateHandoffStatus(item.id, "pasted-back"));
    row.querySelector(".dismiss-handoff").addEventListener("click", () => updateHandoffStatus(item.id, "dismissed"));
    els.handoffQueue.appendChild(row);
  }
}

function renderWatchedArtifacts() {
  els.watchedCount.textContent = String(state.watchedArtifacts.length);
  els.watchedArtifactList.innerHTML = "";
  if (!state.watchedArtifacts.length) {
    els.watchedArtifactList.innerHTML = `<div class="empty-state">No matching review artifacts detected. Scan uses configured watched patterns through the workspace backend.</div>`;
    return;
  }
  for (const artifact of state.watchedArtifacts) {
    const row = document.createElement("article");
    row.className = "artifact-item";
    row.innerHTML = `
      <div class="artifact-summary">
        <strong class="truncate"></strong>
        <span class="artifact-meta"></span>
      </div>
      <div class="artifact-actions">
        <button class="ghost small preview-artifact" type="button">Preview</button>
        <button class="primary small stage-artifact" type="button">Stage for review</button>
        <button class="ghost small ignore-artifact" type="button">Ignore</button>
      </div>
    `;
    row.querySelector("strong").textContent = artifact.relPath;
    row.querySelector(".artifact-meta").textContent = `${formatBytes(artifact.size)}${artifact.mtime ? ` · ${formatTime(artifact.mtime)}` : ""}`;
    row.querySelector(".preview-artifact").addEventListener("click", () => previewFile(artifact.relPath));
    row.querySelector(".stage-artifact").addEventListener("click", () => stageFileHandoff(artifact.relPath, primaryReviewThread(activeProject())?.id, "workspace"));
    row.querySelector(".ignore-artifact").addEventListener("click", () => ignoreWatchedArtifact(artifact.relPath));
    els.watchedArtifactList.appendChild(row);
  }
}

function render() {
  if (!state.config) return;
  els.configPath.textContent = state.configPath;
  els.configPath.title = state.configPath;
  renderProjectList();
  renderSelectedProject();
  renderThreadDeck();
  renderHandoffTargetSelect();
  renderPromptPreview();
  renderHandoffQueue();
  renderWatchedArtifacts();
  renderStatus();
  scheduleResizeBurst();
}

function getUiRatios() {
  const ui = state.config?.ui ?? {};
  return {
    leftRatio: Number.isFinite(Number(ui.leftRatio)) ? Number(ui.leftRatio) : 0.34,
    middleRatio: Number.isFinite(Number(ui.middleRatio)) ? Number(ui.middleRatio) : 0.3,
  };
}

function computePlaneWidths() {
  const rect = els.appShell.getBoundingClientRect();
  const split = MIN_WIDTHS.splitter;
  const total = Math.max(1, Math.round(rect.width) - split * 2);
  const ratios = getUiRatios();

  const minSum = MIN_WIDTHS.left + MIN_WIDTHS.middle + MIN_WIDTHS.right;
  if (total <= minSum) {
    const scale = total / minSum;
    const left = Math.max(280, Math.floor(MIN_WIDTHS.left * scale));
    const middle = Math.max(340, Math.floor(MIN_WIDTHS.middle * scale));
    const right = Math.max(280, total - left - middle);
    return { left, middle, right, total };
  }

  let left = Math.round(total * ratios.leftRatio);
  left = clamp(left, MIN_WIDTHS.left, total - MIN_WIDTHS.middle - MIN_WIDTHS.right);

  let middle = Math.round(total * ratios.middleRatio);
  middle = clamp(middle, MIN_WIDTHS.middle, total - left - MIN_WIDTHS.right);

  let right = total - left - middle;
  if (right < MIN_WIDTHS.right) {
    const deficit = MIN_WIDTHS.right - right;
    const middleCanGive = Math.max(0, middle - MIN_WIDTHS.middle);
    const giveFromMiddle = Math.min(deficit, middleCanGive);
    middle -= giveFromMiddle;
    left = Math.max(MIN_WIDTHS.left, left - (deficit - giveFromMiddle));
    right = total - left - middle;
  }

  return { left, middle, right, total };
}

function applyPlaneWidths() {
  const widths = computePlaneWidths();
  state.currentWidths = widths;
  document.documentElement.style.setProperty("--left-plane-width", `${widths.left}px`);
  document.documentElement.style.setProperty("--control-plane-width", `${widths.middle}px`);
  return widths;
}

function rectToBounds(rect) {
  return {
    x: Math.round(rect.left),
    y: Math.round(rect.top),
    width: Math.max(1, Math.round(rect.width)),
    height: Math.max(1, Math.round(rect.height)),
  };
}

function sendSurfaceLayout() {
  if (!bridge || !els.codexSlot || !els.chatgptSlot) return;
  const codex = rectToBounds(els.codexSlot.getBoundingClientRect());
  const chatgpt = rectToBounds(els.chatgptSlot.getBoundingClientRect());
  const signature = `${codex.x},${codex.y},${codex.width},${codex.height}|${chatgpt.x},${chatgpt.y},${chatgpt.width},${chatgpt.height}`;
  if (signature === state.lastLayoutSignature) return;
  state.lastLayoutSignature = signature;
  bridge.setSurfaceLayout({ codex, chatgpt }).catch((error) => {
    console.error("Unable to set surface layout", error);
  });
}

function performLayout() {
  applyPlaneWidths();
  sendSurfaceLayout();
}

function scheduleLayout() {
  if (state.layoutFrame) cancelAnimationFrame(state.layoutFrame);
  state.layoutFrame = requestAnimationFrame(() => {
    state.layoutFrame = 0;
    performLayout();
  });
}

function scheduleResizeBurst() {
  state.lastLayoutSignature = "";
  for (const delay of [0, 16, 48, 110, 240, 480]) setTimeout(scheduleLayout, delay);
}

async function saveConfig(config) {
  const result = await bridge.saveConfig(config);
  state.config = result.config;
  state.configPath = result.configPath;
  render();
  return result.config;
}

async function selectProject(projectId) {
  const previous = state.config?.selectedProjectId;
  state.surfaceEvents.codex = { type: "loading" };
  state.surfaceEvents.chatgpt = { type: "loading" };
  renderStatus();
  const result = await bridge.selectProject(projectId);
  state.config = result.config;
  state.selectedFileRelPath = "";
  state.selectedFilePreview = null;
  render();
  const project = activeProject();
  setLastEvent(`Selected ${project?.name ?? projectId}.`);
  if (project && bridge.attachWorkspace) {
    setLastEvent(`Attaching workspace: ${workspaceSummary(project)}…`);
    try {
      const status = await bridge.attachWorkspace(project.id);
      state.workspaceStatuses[project.id] = status;
      renderSelectedProject();
    } catch (error) {
      state.workspaceStatuses[project.id] = { status: "failed", lastError: error.message };
      renderSelectedProject();
    }
  }
  await loadWorkTreeRoot();
  await loadWatchedArtifacts();
  if (previous !== projectId) scheduleResizeBurst();
}

async function selectThread(threadId) {
  const project = activeProject();
  if (!project || !threadId) return;
  const thread = threadById(project, threadId);
  if (!thread) return;
  if (thread.archived) {
    setLastEvent(`Archived thread not opened: ${thread.title}.`);
    return;
  }
  state.surfaceEvents.chatgpt = { type: "loading" };
  renderStatus();
  try {
    const result = await bridge.selectChatThread(project.id, threadId);
    state.config = result.config;
    render();
    setLastEvent(`Opened ${roleLabel(result.thread?.role)} thread: ${result.thread?.title}.`);
  } catch (error) {
    setLastEvent(`Thread open failed: ${error.message}`);
  }
}

function openDrawer(mode) {
  const project = mode === "new" ? null : activeProject();
  state.drawerMode = mode;
  els.drawer.classList.add("open");
  els.drawer.setAttribute("aria-hidden", "false");
  bridge.setSurfaceVisible(false).catch(() => {});
  els.drawerTitle.textContent = mode === "new" ? "New project" : "Edit project";
  els.deleteProjectButton.style.display = mode === "new" ? "none" : "inline-flex";

  const now = nowIso();
  const draft = project ?? {
    id: createId("project"),
    name: "New project",
    repoPath: state.repoRoot || "",
    workspace: { kind: "local", localPath: state.repoRoot || "", label: "Local workspace" },
    surfaceBinding: {
      codex: { mode: "local", target: "codex://local-workspace", label: "Local Codex lane" },
      chatgpt: { reviewThreadUrl: "https://chatgpt.com/", reduceChrome: true },
    },
    chatThreads: [
      {
        id: "thread_review_primary",
        role: "review",
        title: "Primary review",
        url: "https://chatgpt.com/",
        notes: "Main project-bound ChatGPT review thread.",
        isPrimary: true,
        pinned: true,
        archived: false,
        createdAt: now,
        updatedAt: now,
      },
    ],
    activeChatThreadId: "thread_review_primary",
    promptTemplates: defaultPromptTemplates(),
    flowProfile: {
      reviewPromptTemplate: defaultPromptText("review"),
      watchedFilePatterns: ["**/*REVIEW*.md", "**/*review*.md", "artifacts/**/*.md"],
      returnHeader: "GPT feedback",
      handoffMode: "assisted",
    },
    handoffs: [],
    ignoredWatchedArtifactPaths: [],
    createdAt: now,
    updatedAt: now,
  };

  const workspace = projectWorkspace(draft);
  const templates = promptTemplates(draft);
  const primary = primaryReviewThread(draft);
  els.projectIdInput.value = draft.id;
  els.projectNameInput.value = draft.name;
  els.workspaceKindInput.value = workspace.kind;
  els.workspaceLabelInput.value = workspace.label || "";
  els.repoPathInput.value = workspace.kind === "local" ? workspace.localPath : draft.repoPath;
  els.wslDistroInput.value = workspace.kind === "wsl" ? workspace.distro : "";
  els.wslLinuxPathInput.value = workspace.kind === "wsl" ? workspace.linuxPath : "";
  updateWorkspaceFieldVisibility();
  els.codexModeInput.value = draft.surfaceBinding.codex.mode;
  els.codexLabelInput.value = draft.surfaceBinding.codex.label;
  els.codexTargetInput.value = draft.surfaceBinding.codex.target;
  els.chatgptUrlInput.value = primary?.url || draft.surfaceBinding.chatgpt.reviewThreadUrl || "https://chatgpt.com/";
  els.reduceChromeInput.checked = draft.surfaceBinding.chatgpt.reduceChrome !== false;
  els.reviewPromptInput.value = templates.review?.text || draft.flowProfile.reviewPromptTemplate;
  els.architecturePromptInput.value = templates.architecture?.text || defaultPromptText("architecture");
  els.brainstormingPromptInput.value = templates.brainstorming?.text || defaultPromptText("brainstorming");
  els.researchPromptInput.value = templates.research?.text || defaultPromptText("research");
  els.watchedPatternsInput.value = (draft.flowProfile.watchedFilePatterns || []).join(", ");
  els.returnHeaderInput.value = draft.flowProfile.returnHeader || "GPT feedback";
  setTimeout(() => els.projectNameInput.focus(), 0);
}

function closeDrawer() {
  els.drawer.classList.remove("open");
  els.drawer.setAttribute("aria-hidden", "true");
  bridge.setSurfaceVisible(true).then(scheduleResizeBurst).catch(scheduleResizeBurst);
}

function closeThreadDrawer() {
  els.threadDrawer.classList.remove("open");
  els.threadDrawer.setAttribute("aria-hidden", "true");
  bridge.setSurfaceVisible(true).then(scheduleResizeBurst).catch(scheduleResizeBurst);
}

function normalizeHttpsUrl(value) {
  const text = String(value || "").trim() || "https://chatgpt.com/";
  try {
    const url = new URL(text);
    if (url.protocol !== "https:") return "https://chatgpt.com/";
    return url.toString();
  } catch {
    return "https://chatgpt.com/";
  }
}

function projectFromForm() {
  const existing = state.config?.projects.find((project) => project.id === els.projectIdInput.value);
  const now = nowIso();
  const workspaceKind = els.workspaceKindInput.value || "local";
  const workspaceLabel = els.workspaceLabelInput.value.trim();
  const localPath = els.repoPathInput.value.trim();
  const linuxPathInput = els.wslLinuxPathInput.value.trim() || "/home";
  const linuxPath = linuxPathInput.startsWith("/") ? linuxPathInput : `/${linuxPathInput}`;
  const workspace = workspaceKind === "wsl"
    ? { kind: "wsl", distro: els.wslDistroInput.value.trim(), linuxPath, label: workspaceLabel || "WSL workspace" }
    : { kind: "local", localPath, label: workspaceLabel || "Local workspace" };
  const repoPath = workspace.kind === "wsl" ? `wsl:${workspace.distro || "default"}:${workspace.linuxPath}` : workspace.localPath;
  const templates = { ...defaultPromptTemplates(), ...(existing?.promptTemplates || {}) };
  templates.review = { ...(templates.review || {}), role: "review", text: els.reviewPromptInput.value.trim() || defaultPromptText("review"), updatedAt: now };
  templates.architecture = { ...(templates.architecture || {}), role: "architecture", text: els.architecturePromptInput.value.trim() || defaultPromptText("architecture"), updatedAt: now };
  templates.brainstorming = { ...(templates.brainstorming || {}), role: "brainstorming", text: els.brainstormingPromptInput.value.trim() || defaultPromptText("brainstorming"), updatedAt: now };
  templates.research = { ...(templates.research || {}), role: "research", text: els.researchPromptInput.value.trim() || defaultPromptText("research"), updatedAt: now };

  const primaryUrl = normalizeHttpsUrl(els.chatgptUrlInput.value.trim());
  let threads = chatThreads(existing).slice();
  if (!threads.length) {
    threads = [
      {
        id: "thread_review_primary",
        role: "review",
        title: "Primary review",
        url: primaryUrl,
        notes: "Main project-bound ChatGPT review thread.",
        isPrimary: true,
        pinned: true,
        archived: false,
        createdAt: now,
        updatedAt: now,
      },
    ];
  }
  const currentPrimary = threads.find((thread) => thread.role === "review" && thread.isPrimary) || threads.find((thread) => thread.role === "review");
  if (currentPrimary) {
    threads = threads.map((thread) => {
      if (thread.id !== currentPrimary.id) return thread.role === "review" ? { ...thread, isPrimary: false } : thread;
      return { ...thread, role: "review", url: primaryUrl, isPrimary: true, archived: false, updatedAt: now };
    });
  }

  return {
    id: els.projectIdInput.value || createId("project"),
    name: els.projectNameInput.value.trim() || "Untitled project",
    repoPath,
    workspace,
    surfaceBinding: {
      codex: {
        mode: els.codexModeInput.value,
        target: els.codexTargetInput.value.trim(),
        label: els.codexLabelInput.value.trim() || "Codex target",
      },
      chatgpt: {
        reviewThreadUrl: primaryUrl,
        reduceChrome: els.reduceChromeInput.checked,
      },
    },
    chatThreads: threads,
    activeChatThreadId: existing?.activeChatThreadId || currentPrimary?.id || threads[0]?.id,
    lastActiveThreadId: existing?.lastActiveThreadId || existing?.activeChatThreadId || currentPrimary?.id || threads[0]?.id,
    promptTemplates: templates,
    flowProfile: {
      reviewPromptTemplate: templates.review.text,
      watchedFilePatterns: els.watchedPatternsInput.value.split(",").map((item) => item.trim()).filter(Boolean),
      returnHeader: els.returnHeaderInput.value.trim() || "GPT feedback",
      handoffMode: "assisted",
    },
    handoffs: existing?.handoffs || [],
    ignoredWatchedArtifactPaths: existing?.ignoredWatchedArtifactPaths || [],
    createdAt: existing?.createdAt ?? now,
    updatedAt: now,
  };
}

async function handleProjectFormSubmit(event) {
  event.preventDefault();
  if (!state.config) return;
  const project = projectFromForm();
  const existingIndex = state.config.projects.findIndex((item) => item.id === project.id);
  const projects = [...state.config.projects];
  if (existingIndex >= 0) projects[existingIndex] = project;
  else projects.push(project);
  await saveConfig({ ...state.config, selectedProjectId: project.id, projects });
  closeDrawer();
  await selectProject(project.id);
  setLastEvent(`Saved project binding for ${project.name}.`);
}

async function deleteSelectedProject() {
  if (!state.config) return;
  const project = activeProject();
  if (!project) return;
  const confirmed = confirm(`Delete project binding "${project.name}"? This does not delete files or chats.`);
  if (!confirmed) return;
  const projects = state.config.projects.filter((item) => item.id !== project.id);
  if (!projects.length) {
    alert("At least one project binding is required.");
    return;
  }
  const nextSelected = projects[0].id;
  await saveConfig({ ...state.config, selectedProjectId: nextSelected, projects });
  closeDrawer();
  await selectProject(nextSelected);
  setLastEvent(`Deleted binding for ${project.name}.`);
}

function openThreadDrawer(mode, threadId = "") {
  const project = activeProject();
  if (!project) return;
  state.threadDrawerMode = mode;
  const now = nowIso();
  const draft = mode === "new"
    ? {
        id: createId("thread"),
        role: "review",
        title: "New ChatGPT thread",
        url: "https://chatgpt.com/",
        notes: "",
        isPrimary: false,
        pinned: false,
        archived: false,
        createdAt: now,
        updatedAt: now,
      }
    : threadById(project, threadId) || activeThread(project);
  if (!draft) return;
  els.threadDrawer.classList.add("open");
  els.threadDrawer.setAttribute("aria-hidden", "false");
  bridge.setSurfaceVisible(false).catch(() => {});
  els.threadDrawerTitle.textContent = mode === "new" ? "Add ChatGPT thread" : "Edit ChatGPT thread";
  els.deleteThreadButton.style.display = mode === "new" ? "none" : "inline-flex";
  els.threadIdInput.value = draft.id;
  els.threadRoleInput.value = draft.role || "review";
  els.threadTitleInput.value = draft.title || "";
  els.threadUrlInput.value = draft.url || "https://chatgpt.com/";
  els.threadNotesInput.value = draft.notes || "";
  els.threadPrimaryInput.checked = Boolean(draft.isPrimary);
  els.threadPinnedInput.checked = Boolean(draft.pinned);
  els.threadArchivedInput.checked = Boolean(draft.archived);
  setTimeout(() => els.threadTitleInput.focus(), 0);
}

function threadFromForm() {
  const existing = threadById(activeProject(), els.threadIdInput.value);
  const now = nowIso();
  const role = THREAD_ROLES.includes(els.threadRoleInput.value) ? els.threadRoleInput.value : "custom";
  return {
    id: els.threadIdInput.value || createId("thread"),
    role,
    title: els.threadTitleInput.value.trim() || `${roleLabel(role)} thread`,
    url: normalizeHttpsUrl(els.threadUrlInput.value.trim()),
    notes: els.threadNotesInput.value.trim(),
    isPrimary: role === "review" && els.threadPrimaryInput.checked,
    pinned: els.threadPinnedInput.checked,
    archived: els.threadArchivedInput.checked,
    createdAt: existing?.createdAt || now,
    updatedAt: now,
    lastOpenedAt: existing?.lastOpenedAt || "",
  };
}

function normalizeThreadSet(threads) {
  const normalized = threads.map((thread) => ({ ...thread, isPrimary: thread.role === "review" ? Boolean(thread.isPrimary) : false }));
  let primary = normalized.find((thread) => thread.role === "review" && thread.isPrimary && !thread.archived) || normalized.find((thread) => thread.role === "review" && !thread.archived);
  if (!primary) primary = normalized.find((thread) => thread.role === "review") || normalized.find((thread) => !thread.archived) || normalized[0];
  if (primary) {
    for (const thread of normalized) thread.isPrimary = thread.id === primary.id && thread.role === "review";
  }
  return normalized;
}

async function handleThreadFormSubmit(event) {
  event.preventDefault();
  const project = activeProject();
  if (!project || !state.config) return;
  const thread = threadFromForm();
  let threads = chatThreads(project).slice();
  const existingIndex = threads.findIndex((item) => item.id === thread.id);
  if (existingIndex >= 0) threads[existingIndex] = thread;
  else threads.push(thread);
  if (thread.isPrimary) threads = threads.map((item) => ({ ...item, isPrimary: item.id === thread.id && item.role === "review" }));
  threads = normalizeThreadSet(threads);
  const activeId = !thread.archived ? thread.id : activeThread({ ...project, chatThreads: threads })?.id;
  const primary = primaryReviewThread({ ...project, chatThreads: threads });
  const updatedProject = {
    ...project,
    chatThreads: threads,
    activeChatThreadId: activeId,
    lastActiveThreadId: activeId,
    surfaceBinding: {
      ...project.surfaceBinding,
      chatgpt: { ...project.surfaceBinding.chatgpt, reviewThreadUrl: primary?.url || "https://chatgpt.com/" },
    },
    updatedAt: nowIso(),
  };
  const projects = state.config.projects.map((item) => (item.id === project.id ? updatedProject : item));
  await saveConfig({ ...state.config, projects });
  closeThreadDrawer();
  if (activeId) await selectThread(activeId);
  setLastEvent(`Saved ChatGPT thread binding: ${thread.title}.`);
}

async function deleteThreadFromDrawer() {
  const project = activeProject();
  if (!project || !state.config) return;
  const threadId = els.threadIdInput.value;
  const thread = threadById(project, threadId);
  if (!thread) return;
  const nonArchived = chatThreads(project).filter((item) => !item.archived);
  if (nonArchived.length <= 1) {
    alert("At least one active ChatGPT thread is required for a project.");
    return;
  }
  const confirmed = confirm(`Remove ChatGPT thread binding "${thread.title}"? This does not delete the ChatGPT conversation.`);
  if (!confirmed) return;
  const threads = normalizeThreadSet(chatThreads(project).filter((item) => item.id !== threadId));
  const activeId = activeThread({ ...project, chatThreads: threads })?.id;
  const primary = primaryReviewThread({ ...project, chatThreads: threads });
  const updatedProject = {
    ...project,
    chatThreads: threads,
    activeChatThreadId: activeId,
    lastActiveThreadId: activeId,
    surfaceBinding: { ...project.surfaceBinding, chatgpt: { ...project.surfaceBinding.chatgpt, reviewThreadUrl: primary?.url || "https://chatgpt.com/" } },
    updatedAt: nowIso(),
  };
  await saveConfig({ ...state.config, projects: state.config.projects.map((item) => (item.id === project.id ? updatedProject : item)) });
  closeThreadDrawer();
  if (activeId) await selectThread(activeId);
  setLastEvent(`Removed thread binding: ${thread.title}.`);
}

async function copyActivePrompt() {
  const project = activeProject();
  if (!project) return;
  const prompt = activePromptText(project, activeThread(project));
  await bridge.copyText(prompt);
  setLastEvent("Active role-aware prompt copied to clipboard.");
}

async function copyReturnHeader() {
  const project = activeProject();
  if (!project) return;
  await bridge.copyText(project.flowProfile?.returnHeader || "GPT feedback");
  setLastEvent("Return header copied to clipboard.");
}

function targetThreadForKind(kind) {
  const project = activeProject();
  if (!project) return null;
  const selected = threadById(project, els.handoffTargetThreadSelect.value);
  if (kind === "architecture-question") return chatThreads(project).find((thread) => thread.role === "architecture" && !thread.archived) || selected || activeThread(project);
  if (kind === "research-question") return chatThreads(project).find((thread) => thread.role === "research" && !thread.archived) || selected || activeThread(project);
  return selected || activeThread(project) || primaryReviewThread(project);
}

function makeHandoff({ kind, title, promptText, targetThreadId, fileRelPath = "", source = "human" }) {
  const project = activeProject();
  const now = nowIso();
  return {
    id: createId("handoff"),
    projectId: project.id,
    source,
    targetThreadId,
    kind,
    fileRelPath,
    title,
    promptText,
    status: "staged",
    createdAt: now,
    updatedAt: now,
  };
}

async function addHandoff(item) {
  const project = activeProject();
  if (!project || !state.config) return;
  const updatedProject = { ...project, handoffs: [item, ...(project.handoffs || [])], updatedAt: nowIso() };
  await saveConfig({ ...state.config, projects: state.config.projects.map((candidate) => (candidate.id === project.id ? updatedProject : candidate)) });
  setLastEvent(`Staged handoff: ${item.title}.`);
}

async function stageFileHandoff(relPath = state.selectedFileRelPath, targetThreadId = "", source = "workspace") {
  const project = activeProject();
  if (!project || !relPath) {
    setLastEvent("Select a file before staging a file review handoff.");
    return;
  }
  if (!state.selectedFilePreview || state.selectedFilePreview.relPath !== relPath) {
    try {
      const preview = await bridge.readProjectFile(project.id, relPath);
      state.selectedFilePreview = preview;
    } catch (error) {
      setLastEvent(`Unable to read file for handoff: ${error.message}`);
    }
  }
  const thread = threadById(project, targetThreadId) || targetThreadForKind("file-review");
  if (!thread) return;
  const prompt = interpolatePrompt(templateForThread(project, thread), {
    project,
    thread,
    fileRelPath: relPath,
    fileContents: selectedFileContents(),
  });
  await addHandoff(
    makeHandoff({
      kind: "file-review",
      source,
      targetThreadId: thread.id,
      fileRelPath: relPath,
      title: `Review ${relPath}`,
      promptText: prompt,
    }),
  );
}

async function stageQuestion(kind) {
  const project = activeProject();
  if (!project) return;
  const question = prompt(kind === "architecture-question" ? "Architecture question to stage:" : kind === "research-question" ? "Research question to stage:" : "Text review prompt to stage:");
  if (!question || !question.trim()) return;
  const thread = targetThreadForKind(kind);
  if (!thread) return;
  const base = interpolatePrompt(templateForThread(project, thread), { project, thread });
  const promptText = `${question.trim()}\n\n---\n\n${base}`;
  await addHandoff(
    makeHandoff({
      kind,
      source: "human",
      targetThreadId: thread.id,
      title: question.trim().slice(0, 90),
      promptText,
    }),
  );
}

async function updateHandoffStatus(handoffId, status) {
  const project = activeProject();
  if (!project || !state.config) return;
  const updatedProject = {
    ...project,
    handoffs: (project.handoffs || []).map((item) => (item.id === handoffId ? { ...item, status, updatedAt: nowIso() } : item)),
    updatedAt: nowIso(),
  };
  await saveConfig({ ...state.config, projects: state.config.projects.map((candidate) => (candidate.id === project.id ? updatedProject : candidate)) });
  setLastEvent(`Handoff marked ${status}.`);
}

function handoffById(project, handoffId) {
  return (project?.handoffs || []).find((item) => item.id === handoffId) || null;
}

async function openHandoffThread(handoffId) {
  const project = activeProject();
  const item = handoffById(project, handoffId);
  if (!item) return;
  await selectThread(item.targetThreadId);
  await updateHandoffStatus(handoffId, "opened-thread");
}

async function copyHandoffPrompt(handoffId) {
  const project = activeProject();
  const item = handoffById(project, handoffId);
  if (!item) return;
  await bridge.copyText(item.promptText);
  await updateHandoffStatus(handoffId, "copied");
}

async function revealHandoffFile(handoffId) {
  const project = activeProject();
  const item = handoffById(project, handoffId);
  if (!project || !item?.fileRelPath) return;
  try {
    const result = await bridge.revealProjectFile(project.id, item.fileRelPath);
    setLastEvent(`Reveal file requested via ${result.method}.`);
  } catch (error) {
    setLastEvent(`Reveal file failed: ${error.message}`);
  }
}

async function ignoreWatchedArtifact(relPath) {
  const project = activeProject();
  if (!project || !state.config) return;
  const ignored = Array.from(new Set([...(project.ignoredWatchedArtifactPaths || []), relPath]));
  const updatedProject = { ...project, ignoredWatchedArtifactPaths: ignored, updatedAt: nowIso() };
  await saveConfig({ ...state.config, projects: state.config.projects.map((item) => (item.id === project.id ? updatedProject : item)) });
  await loadWatchedArtifacts();
  setLastEvent(`Ignored watched artifact: ${relPath}.`);
}

async function loadWatchedArtifacts() {
  const project = activeProject();
  if (!project) return;
  try {
    const result = await bridge.listWatchedArtifacts(project.id);
    state.watchedArtifacts = result.entries || [];
    renderWatchedArtifacts();
    setLastEvent(`Watched artifact scan found ${state.watchedArtifacts.length} matching files.`);
  } catch (error) {
    state.watchedArtifacts = [];
    renderWatchedArtifacts();
    setLastEvent(`Watched artifact scan failed: ${error.message}`);
  }
}

function beginDrag(splitterName, event) {
  if (!state.config) return;
  event.preventDefault();
  const drag = { splitterName, pointerId: event.pointerId, startX: event.clientX, startWidths: { ...state.currentWidths } };
  document.body.classList.add("dragging");
  bridge.setSurfaceVisible(false).catch(() => {});

  const move = (moveEvent) => {
    const rect = els.appShell.getBoundingClientRect();
    const total = Math.max(1, Math.round(rect.width) - MIN_WIDTHS.splitter * 2);
    let left = drag.startWidths.left;
    let middle = drag.startWidths.middle;

    if (splitterName === "left") {
      left = clamp(moveEvent.clientX - rect.left, MIN_WIDTHS.left, total - MIN_WIDTHS.middle - MIN_WIDTHS.right);
      middle = clamp(middle, MIN_WIDTHS.middle, total - left - MIN_WIDTHS.right);
    } else {
      middle = clamp(moveEvent.clientX - rect.left - left - MIN_WIDTHS.splitter, MIN_WIDTHS.middle, total - left - MIN_WIDTHS.right);
    }

    const right = total - left - middle;
    state.currentWidths = { left, middle, right, total };
    state.config = {
      ...state.config,
      ui: { ...(state.config.ui ?? {}), leftRatio: left / total, middleRatio: middle / total },
    };
    document.documentElement.style.setProperty("--left-plane-width", `${Math.round(left)}px`);
    document.documentElement.style.setProperty("--control-plane-width", `${Math.round(middle)}px`);
  };

  const stop = async () => {
    window.removeEventListener("pointermove", move);
    window.removeEventListener("pointerup", stop);
    window.removeEventListener("pointercancel", stop);
    document.body.classList.remove("dragging");
    await saveConfig(state.config);
    bridge.setSurfaceVisible(true).then(scheduleResizeBurst).catch(scheduleResizeBurst);
  };

  window.addEventListener("pointermove", move);
  window.addEventListener("pointerup", stop);
  window.addEventListener("pointercancel", stop);
}

function renderTreeEntries(container, entries) {
  if (!entries.length) {
    const empty = document.createElement("div");
    empty.className = "empty-state";
    empty.textContent = "No visible files in this directory.";
    container.appendChild(empty);
    return;
  }

  for (const entry of entries) {
    const wrapper = document.createElement("div");
    wrapper.className = "tree-node";

    const row = document.createElement("button");
    row.type = "button";
    row.className = `tree-row ${entry.type}`;
    row.dataset.relPath = entry.relPath;
    row.innerHTML = `<span class="twisty"></span><span class="truncate mono"></span>`;
    row.querySelector(".twisty").textContent = entry.type === "dir" ? "▸" : entry.type === "file" ? "•" : "◇";
    row.querySelector(".truncate").textContent = entry.name;
    row.title = entry.relPath;

    const children = document.createElement("div");
    children.className = "tree-children";
    children.hidden = true;

    row.addEventListener("click", () => {
      if (entry.type === "dir") toggleDirectory(entry, row, children);
      else if (entry.type === "file") previewFile(entry.relPath, row);
      else setLastEvent(`Preview unavailable for ${entry.type}: ${entry.relPath}`);
    });

    wrapper.appendChild(row);
    wrapper.appendChild(children);
    container.appendChild(wrapper);
  }
}

async function loadWorkTreeRoot() {
  const project = activeProject();
  if (!project) return;
  els.workTree.innerHTML = `<div class="empty-state">Loading ${project.name}…</div>`;
  resetPreview("Select a text/code file from the work tree.");
  try {
    const result = await bridge.listWorkTree(project.id, "");
    els.workTree.innerHTML = "";
    renderTreeEntries(els.workTree, result.entries);
    if (result.skipped) {
      const skipped = document.createElement("div");
      skipped.className = "empty-state";
      skipped.textContent = `${result.skipped} heavy or extra entries hidden for responsiveness.`;
      els.workTree.appendChild(skipped);
    }
    setLastEvent(`Loaded work tree for ${project.name}.`);
  } catch (error) {
    els.workTree.innerHTML = `<div class="empty-state"></div>`;
    els.workTree.querySelector(".empty-state").textContent = `Work tree error: ${error.message}`;
    setLastEvent(`Work tree error: ${error.message}`);
  }
}

async function toggleDirectory(entry, row, children) {
  if (children.dataset.loaded === "true") {
    children.hidden = !children.hidden;
    row.querySelector(".twisty").textContent = children.hidden ? "▸" : "▾";
    return;
  }

  const project = activeProject();
  if (!project) return;
  row.querySelector(".twisty").textContent = "…";
  children.hidden = false;
  children.innerHTML = `<div class="empty-state">Loading…</div>`;
  try {
    const result = await bridge.listWorkTree(project.id, entry.relPath);
    children.innerHTML = "";
    renderTreeEntries(children, result.entries);
    if (result.skipped) {
      const skipped = document.createElement("div");
      skipped.className = "empty-state";
      skipped.textContent = `${result.skipped} entries hidden.`;
      children.appendChild(skipped);
    }
    children.dataset.loaded = "true";
    row.querySelector(".twisty").textContent = "▾";
  } catch (error) {
    children.innerHTML = `<div class="empty-state"></div>`;
    children.querySelector(".empty-state").textContent = error.message;
    row.querySelector(".twisty").textContent = "!";
  }
}

function resetPreview(message) {
  state.selectedFileRelPath = "";
  state.selectedFilePreview = null;
  els.previewPath.textContent = "No file selected";
  els.previewPath.title = "";
  els.previewMeta.textContent = "—";
  els.filePreview.textContent = message;
  renderPromptPreview();
}

async function previewFile(relPath, row) {
  const project = activeProject();
  if (!project) return;
  for (const selected of els.workTree.querySelectorAll(".tree-row.selected")) selected.classList.remove("selected");
  row?.classList.add("selected");
  state.selectedFileRelPath = relPath;
  els.previewPath.textContent = relPath;
  els.previewPath.title = relPath;
  els.previewMeta.textContent = "loading…";
  els.filePreview.textContent = "Loading preview…";

  try {
    const result = await bridge.readProjectFile(project.id, relPath);
    state.selectedFilePreview = result;
    state.selectedFileRelPath = result.relPath;
    els.previewPath.textContent = result.relPath;
    els.previewPath.title = result.absolutePath;
    els.previewMeta.textContent = `${formatBytes(result.size)}${result.truncated ? ` · first ${formatBytes(result.limit)}` : ""}`;
    if (result.binary) {
      els.filePreview.textContent = "Binary or non-text file. Preview intentionally disabled.";
    } else {
      els.filePreview.textContent = `${result.truncated ? "/* Preview truncated for responsiveness. */\n\n" : ""}${result.text}`;
    }
    renderPromptPreview();
    setLastEvent(`Previewing ${result.relPath}.`);
  } catch (error) {
    els.previewMeta.textContent = "error";
    els.filePreview.textContent = error.message;
    setLastEvent(`Preview error: ${error.message}`);
  }
}

function bindEvents() {
  els.addProjectButton.addEventListener("click", () => openDrawer("new"));
  els.editProjectButton.addEventListener("click", () => openDrawer("edit"));
  els.closeDrawerButton.addEventListener("click", closeDrawer);
  els.cancelProjectButton.addEventListener("click", closeDrawer);
  els.form.addEventListener("submit", handleProjectFormSubmit);
  els.deleteProjectButton.addEventListener("click", deleteSelectedProject);
  els.chooseRepoButton.addEventListener("click", async () => {
    const selected = await bridge.chooseDirectory();
    if (selected) els.repoPathInput.value = selected;
  });
  els.workspaceKindInput.addEventListener("change", updateWorkspaceFieldVisibility);
  els.addThreadButton.addEventListener("click", () => openThreadDrawer("new"));
  els.threadForm.addEventListener("submit", handleThreadFormSubmit);
  els.closeThreadDrawerButton.addEventListener("click", closeThreadDrawer);
  els.cancelThreadButton.addEventListener("click", closeThreadDrawer);
  els.deleteThreadButton.addEventListener("click", deleteThreadFromDrawer);
  els.threadRoleInput.addEventListener("change", () => {
    if (els.threadRoleInput.value !== "review") els.threadPrimaryInput.checked = false;
  });
  els.copyPromptButton.addEventListener("click", copyActivePrompt);
  els.copyHeaderButton.addEventListener("click", copyReturnHeader);
  els.stageSelectedFileButton.addEventListener("click", () => stageFileHandoff());
  els.stagePreviewButton.addEventListener("click", () => stageFileHandoff());
  els.stageTextReviewButton.addEventListener("click", () => stageQuestion("text-review"));
  els.stageArchitectureQuestionButton.addEventListener("click", () => stageQuestion("architecture-question"));
  els.stageResearchQuestionButton.addEventListener("click", () => stageQuestion("research-question"));
  els.reloadCodexButton.addEventListener("click", () => bridge.reloadSurface("codex"));
  els.reloadChatButton.addEventListener("click", () => bridge.reloadSurface("chatgpt"));
  els.externalChatButton.addEventListener("click", () => bridge.openSurfaceExternal("chatgpt"));
  els.forceDarkButton.addEventListener("click", async () => {
    await bridge.forceChatgptDark();
    setLastEvent("Requested best-effort ChatGPT dark mode.");
  });
  els.chatSettingsButton.addEventListener("click", async () => {
    const result = await bridge.openChatgptSettings();
    setLastEvent(result.ok ? `Requested ChatGPT settings (${result.method}).` : `ChatGPT settings failed (${result.method}).`);
  });
  els.refreshWorkTreeButton.addEventListener("click", loadWorkTreeRoot);
  els.refreshWatchedButton.addEventListener("click", loadWatchedArtifacts);

  els.leftSplitter.addEventListener("pointerdown", (event) => beginDrag("left", event));
  els.rightSplitter.addEventListener("pointerdown", (event) => beginDrag("right", event));

  window.addEventListener("resize", scheduleResizeBurst);
  if (window.visualViewport) window.visualViewport.addEventListener("resize", scheduleResizeBurst);
  document.addEventListener("visibilitychange", () => {
    if (!document.hidden) scheduleResizeBurst();
  });
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape" && els.threadDrawer.classList.contains("open")) closeThreadDrawer();
    else if (event.key === "Escape" && els.drawer.classList.contains("open")) closeDrawer();
  });

  const resizeObserver = new ResizeObserver(scheduleResizeBurst);
  resizeObserver.observe(els.appShell);
  resizeObserver.observe(els.codexSlot);
  resizeObserver.observe(els.chatgptSlot);

  bridge.onSurfaceEvent((event) => {
    if (event.surface === "codex" || event.surface === "chatgpt") {
      state.surfaceEvents[event.surface] = event;
      renderStatus();
      if (event.type === "loaded") setLastEvent(`${event.surface} loaded: ${event.title || event.url || "ready"}`);
      if (event.type === "load-failed") setLastEvent(`${event.surface} load failed: ${event.errorDescription}`);
      if (event.type === "navigation-blocked") setLastEvent(`${event.surface} blocked navigation: ${event.url}`);
      if (event.type === "settings-opened") setLastEvent(`ChatGPT settings requested via ${event.method}.`);
      if (event.type === "settings-open-failed") setLastEvent(`ChatGPT settings request failed via ${event.method}.`);
    }
  });

  bridge.onShellEvent((event) => {
    if (event.type === "layout-request") scheduleResizeBurst();
    if (event.type === "backend-status" && event.session?.projectId) {
      state.workspaceStatuses[event.session.projectId] = event.session;
      renderSelectedProject();
      if (event.error) setLastEvent(`Workspace backend error: ${event.error}`);
      else if (event.session.status === "attached") setLastEvent(`Workspace backend attached: ${event.session.transport}`);
      else if (event.session.status === "failed") setLastEvent(`Workspace backend failed: ${event.session.lastError || "unknown"}`);
    }
  });
}

async function init() {
  if (!bridge) {
    document.body.innerHTML = "<main style='padding:24px;color:white'>Electron preload bridge is unavailable.</main>";
    return;
  }
  bindEvents();
  const result = await bridge.loadConfig();
  state.config = result.config;
  state.configPath = result.configPath;
  state.repoRoot = result.repoRoot;
  render();
  await selectProject(state.config.selectedProjectId);
}

init().catch((error) => {
  console.error(error);
  setLastEvent(`Startup error: ${error.message}`);
});
